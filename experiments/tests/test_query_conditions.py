from __future__ import annotations

import networkx as nx
import numpy as np
import pytest

from query_conditions import (
    LaplacianAnalyzer,
    analyze_operating_point,
    controlled_corridor,
    extract_injection_and_controls,
    weighted_laplacian,
)


class FakeNetwork:
    def __init__(self, buses, loads=(), generators=()) -> None:
        self.buses = list(buses)
        self.loads = list(loads)
        self.generators = list(generators)


def labelled_graph(graph: nx.Graph, offset: int = 1) -> nx.Graph:
    graph = graph.copy()
    nx.set_node_attributes(
        graph, {node: str(node + offset) for node in graph.nodes()}, "bus_id"
    )
    return graph


def analyzer_for(graph: nx.Graph, scale: float = 1.0) -> LaplacianAnalyzer:
    graph = labelled_graph(graph)
    weights = {tuple(sorted(edge)): scale for edge in graph.edges()}
    return LaplacianAnalyzer(weighted_laplacian(len(graph), weights), graph)


def test_easy_eigenvector_is_not_effectively_ill_conditioned() -> None:
    result = controlled_corridor(12, "easy-eigenvector")["base_rhs"]
    assert result["kappa"] > 10
    assert result["primary_condition"] == "fail"


def test_sparse_corridor_injection_activates_low_spectrum() -> None:
    result = controlled_corridor(12, "sparse-endpoints")["base_rhs"]
    assert result["primary_condition"] == "pass"
    assert result["solver_residual"] < 1e-10


def test_constructed_hard_pair_activates_full_conditioning() -> None:
    result = controlled_corridor(12, "hard-pair-plus")["base_rhs"]
    assert result["primary_condition"] == "pass"


def test_repeated_positive_eigenvalues_are_supported() -> None:
    analyzer = analyzer_for(nx.cycle_graph(6))
    rhs = np.array([1.0, -1.0, 0.0, 0.0, 0.0, 0.0])
    result = analyzer.analyze_rhs(rhs)
    assert result["status"] == "computed"
    assert result["spectral_orthogonality_residual"] < 1e-10


def test_disconnected_graph_is_rejected_by_spectral_validation() -> None:
    graph = labelled_graph(nx.disjoint_union(nx.path_graph(3), nx.path_graph(2)))
    weights = {tuple(sorted(edge)): 1.0 for edge in graph.edges()}
    with pytest.raises(ValueError, match="one zero mode"):
        LaplacianAnalyzer(weighted_laplacian(len(graph), weights), graph)


def test_nonpositive_weight_is_never_corrected() -> None:
    with pytest.raises(ValueError, match="positive weights"):
        weighted_laplacian(2, {(0, 1): -1.0})


def test_multiple_reference_buses_use_lowest_recorded_id() -> None:
    graph = labelled_graph(nx.path_graph(3), offset=10)
    network = FakeNetwork(
        buses=[
            {"id": 10, "kind": "REF"},
            {"id": 11, "kind": "PQ"},
            {"id": 12, "kind": "REF"},
        ],
        loads=[{"bus": 11, "p": 2.0, "in_service": True}],
        generators=[
            {
                "bus": 12,
                "pg": 1.0,
                "pmin": 0.0,
                "pmax": 2.0,
                "in_service": True,
            }
        ],
    )
    result = extract_injection_and_controls(network, graph)
    assert result["reference_bus_ids"] == [10, 12]
    assert result["reference_bus_id"] == 10
    assert result["post_balance_residual"] == pytest.approx(0.0)


def test_missing_headroom_excludes_generator_control() -> None:
    graph = labelled_graph(nx.path_graph(2))
    network = FakeNetwork(
        buses=[{"id": 1, "kind": "REF"}, {"id": 2, "kind": "PQ"}],
        generators=[{"bus": 1, "pg": 1.0, "in_service": True}],
    )
    result = extract_injection_and_controls(network, graph)
    assert result["generator_controls"] == []


def test_uniform_weight_scaling_preserves_condition_metrics() -> None:
    first = analyzer_for(nx.path_graph(8), scale=1.0)
    second = analyzer_for(nx.path_graph(8), scale=7.0)
    rhs = np.zeros(8)
    rhs[0], rhs[-1] = 1.0, -1.0
    first_result = first.analyze_rhs(rhs)
    second_result = second.analyze_rhs(rhs)
    assert first_result["kappa"] == pytest.approx(second_result["kappa"])
    assert first_result["filtering_factor"] == pytest.approx(
        second_result["filtering_factor"]
    )


def test_relabeling_preserves_base_metrics() -> None:
    graph = nx.path_graph(7)
    first = analyzer_for(graph)
    permutation = {node: 6 - node for node in graph.nodes()}
    relabeled = nx.relabel_nodes(graph, permutation)
    second = analyzer_for(relabeled)
    rhs = np.arange(7, dtype=float) - 3
    relabeled_rhs = np.array([rhs[permutation[node]] for node in range(7)])
    first_result = first.analyze_rhs(rhs)
    second_result = second.analyze_rhs(relabeled_rhs)
    assert first_result["kappa"] == pytest.approx(second_result["kappa"])
    assert first_result["rhs_solution_state_distance"] == pytest.approx(
        second_result["rhs_solution_state_distance"]
    )


def test_restricted_hard_pair_stays_in_admissible_subspace() -> None:
    analyzer = analyzer_for(nx.path_graph(9))
    result = analyzer.analyze_subspace([0, 3, 8])
    assert result["status"] == "computed"
    assert result["hard_pair_subspace_residual"] < 1e-10
    assert result["singular_value_residual_max"] < 1e-10
    assert result["singular_value_residual_min"] < 1e-10
    assert result["hard_pair_input_state_distance"] == pytest.approx(
        result["hard_pair_expected_input_state_distance"]
    )
    assert result["hard_pair_solution_state_distance"] == pytest.approx(2**0.5)


def test_degenerate_control_space_is_unavailable() -> None:
    analyzer = analyzer_for(nx.path_graph(4))
    assert analyzer.analyze_subspace([0])["status"] == "unavailable"


def test_operating_point_reports_both_admissible_subspaces() -> None:
    graph = labelled_graph(nx.path_graph(4))
    analyzer = analyzer_for(nx.path_graph(4))
    network = FakeNetwork(
        buses=[
            {"id": 1, "kind": "REF"},
            {"id": 2, "kind": "PQ"},
            {"id": 3, "kind": "PQ"},
            {"id": 4, "kind": "PQ"},
        ],
        loads=[{"bus": 3, "p": 1.0, "in_service": True}],
        generators=[
            {
                "bus": bus,
                "pg": 0.5,
                "pmin": 0.0,
                "pmax": 1.0,
                "in_service": True,
            }
            for bus in (1, 2, 4)
        ],
    )
    result = analyze_operating_point(network, graph, analyzer)
    assert result["base_rhs"]["status"] == "computed"
    assert result["grounded_slack_sensitivity"]["status"] == "computed"
    assert result["grounded_slack_sensitivity"]["slacks"][0]["slack_bus_id"] == "1"
    assert result["generator_redispatch"]["status"] == "computed"
    assert result["generator_load_redispatch"]["status"] == "computed"


def test_dense_and_sparse_eigen_implementations_agree() -> None:
    graph = labelled_graph(nx.path_graph(101))
    weights = {tuple(sorted(edge)): 1.0 for edge in graph.edges()}
    matrix = weighted_laplacian(len(graph), weights)
    dense = LaplacianAnalyzer(matrix, graph, dense_limit=200)
    sparse = LaplacianAnalyzer(matrix, graph, dense_limit=50)
    assert sparse.lambda_two == pytest.approx(dense.lambda_two, rel=1e-6)
    assert sparse.lambda_maximum == pytest.approx(dense.lambda_maximum, rel=1e-8)
