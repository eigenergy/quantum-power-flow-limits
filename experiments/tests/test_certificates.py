from __future__ import annotations

import json
from pathlib import Path

import networkx as nx
import pymetis
import pytest

from run_conditions import (
    count_crossings,
    crossing_key,
    normalized_largest_component,
    series_reactance_audit,
    separator_certificate,
    segment_relation,
    validate_separator,
    validate_tree_decomposition,
    write_table,
)


EXPERIMENT_DIR = Path(__file__).resolve().parents[1]


class FakeNetwork:
    def __init__(self, graph: nx.Graph) -> None:
        self._graph = graph
        self.buses = list(graph.nodes())
        self.branches = [
            {"in_service": True},
            {"in_service": True},
            {"in_service": False},
        ]

    def to_networkx(self) -> nx.Graph:
        return self._graph.copy()


def test_separator_certificate_on_path() -> None:
    graph = nx.path_graph(40)
    certificate = separator_certificate(graph)
    assert certificate["holds"]
    assert certificate["s"] <= 2


def test_separator_validator_rejects_uncovered_vertex() -> None:
    graph = nx.path_graph(4)
    with pytest.raises(ValueError, match="cover"):
        validate_separator(graph, {0}, {1}, {2})


def test_separator_validator_rejects_a_b_edge() -> None:
    graph = nx.path_graph(3)
    with pytest.raises(ValueError, match="A-B"):
        validate_separator(graph, {0}, {2}, {1})


def test_separator_validator_rejects_overlapping_parts() -> None:
    graph = nx.path_graph(3)
    with pytest.raises(ValueError, match="not disjoint"):
        validate_separator(graph, {0, 1}, {1}, {2})


def test_separator_beta_matches_asymmetric_paper_definition() -> None:
    graph = nx.path_graph(6)
    result = validate_separator(graph, {0, 1}, {2}, {3, 4, 5})
    assert result["beta_numerator"] == 3
    assert result["beta_denominator"] == 6


def test_separator_recomputes_metis_cut_objective(monkeypatch) -> None:
    def fake_partition(*args, **kwargs):
        return -99, [0, 0, 1, 1]

    monkeypatch.setattr(pymetis, "part_graph", fake_partition)
    certificate = separator_certificate(nx.path_graph(4))
    assert certificate["edge_cut"] == 1


@pytest.mark.parametrize(
    ("graph", "expected"),
    [
        (nx.path_graph(20), True),
        (nx.grid_2d_graph(5, 5), True),
        (nx.complete_graph(5), False),
        (nx.complete_bipartite_graph(3, 3), False),
    ],
)
def test_planarity_examples(graph: nx.Graph, expected: bool) -> None:
    assert nx.check_planarity(graph, counterexample=False)[0] is expected


def test_parallel_edges_and_self_loops_do_not_change_simple_topology() -> None:
    graph = nx.MultiGraph()
    graph.add_edges_from([(0, 1), (0, 1), (1, 2), (2, 2)])
    simple = nx.Graph(graph)
    simple.remove_edges_from(nx.selfloop_edges(simple))
    assert sorted(simple.edges()) == [(0, 1), (1, 2)]


def test_largest_component_policy() -> None:
    graph = nx.Graph([(0, 1), (1, 2), (10, 11)])
    largest = max(nx.connected_components(graph), key=len)
    assert largest == {0, 1, 2}


def test_normalization_collapses_parallel_edges_and_removes_loops() -> None:
    graph = nx.MultiGraph()
    graph.add_nodes_from([10, 20, 30, 40])
    graph.add_edges_from([(10, 20), (10, 20), (20, 30), (30, 30)])
    normalized, metadata = normalized_largest_component(FakeNetwork(graph))
    assert sorted(normalized.edges()) == [(0, 1), (1, 2)]
    assert metadata["parsed_buses"] == 4
    assert metadata["components"] == 2
    assert metadata["excluded_buses"] == 1


def test_series_reactance_audit_rejects_nonpositive_branch() -> None:
    graph = nx.Graph([(0, 1), (1, 2)])
    nx.set_node_attributes(graph, {0: 10, 1: 20, 2: 30}, "bus_id")
    network = FakeNetwork(graph)
    network.branches = [
        {"in_service": True, "from_id": 10, "to_id": 20, "x": 0.5},
        {"in_service": True, "from_id": 20, "to_id": 30, "x": -0.25},
    ]
    result = series_reactance_audit(network, graph)
    assert result["negative_reactances"] == 1
    assert result["maximum_branch_degree"] == 2
    assert not result["positive_weight_assumption_holds"]


def test_valid_elimination_tree_decomposition() -> None:
    graph = nx.path_graph(4)
    order = [0, 1, 2, 3]
    bags = [{0, 1}, {1, 2}, {2, 3}, {3}]
    result = validate_tree_decomposition(graph, order, bags)
    assert result["upper_bound"] == 1


def test_invalid_elimination_tree_decomposition() -> None:
    graph = nx.cycle_graph(4)
    order = [0, 1, 2, 3]
    bags = [{0, 1}, {1, 2}, {2, 3}, {3}]
    with pytest.raises(ValueError, match="cover an edge"):
        validate_tree_decomposition(graph, order, bags)


def test_tree_decomposition_rejects_nonpermutation() -> None:
    graph = nx.path_graph(3)
    with pytest.raises(ValueError, match="permutation"):
        validate_tree_decomposition(graph, [0, 0, 2], [{0}, {1}, {2}])


def test_tree_decomposition_rejects_running_intersection_failure() -> None:
    graph = nx.Graph([(0, 1), (0, 2), (1, 3)])
    order = [0, 1, 2, 3]
    bags = [{0, 1, 2}, {1, 3}, {2}, {3}]
    with pytest.raises(ValueError, match="running intersection"):
        validate_tree_decomposition(graph, order, bags)


def test_crossing_counter() -> None:
    graph = nx.Graph([(0, 1), (2, 3)])
    positions = [(0, 0), (10, 10), (0, 10), (10, 0)]
    result = count_crossings(graph, positions, limit=2, chunk_size=1)
    assert result == {"crossings": 1, "crossings_at_least": 1, "complete": True}


def test_crossing_counter_accepts_edgeless_graph() -> None:
    result = count_crossings(nx.empty_graph(2), [(0, 0), (1, 1)], limit=0)
    assert result == {"crossings": 0, "crossings_at_least": 0, "complete": True}


def test_crossing_counter_stops_after_limit() -> None:
    graph = nx.Graph([(0, 1), (2, 3)])
    positions = [(0, 0), (10, 10), (0, 10), (10, 0)]
    result = count_crossings(graph, positions, limit=0, chunk_size=1)
    assert result["complete"] is False
    assert result["crossings_at_least"] == 1


def test_crossing_counter_rejects_nonproper_touch() -> None:
    graph = nx.Graph([(0, 1), (2, 3)])
    positions = [(0, 0), (10, 0), (5, 0), (5, 5)]
    with pytest.raises(ValueError, match="nonproper"):
        count_crossings(graph, positions, limit=10)


def test_crossing_counter_rejects_triple_crossing() -> None:
    graph = nx.Graph([(0, 1), (2, 3), (4, 5)])
    positions = [(0, 5), (10, 5), (5, 0), (5, 10), (0, 0), (10, 10)]
    with pytest.raises(ValueError, match="triple crossing"):
        count_crossings(graph, positions, limit=10, chunk_size=1)


def test_crossing_key_is_exact_and_order_independent() -> None:
    horizontal = ((0, 5), (10, 5))
    vertical = ((5, 0), (5, 10))
    assert crossing_key(*horizontal, *vertical) == (5, 5, 1)
    assert crossing_key(*vertical, *horizontal) == (5, 5, 1)


@pytest.mark.parametrize(
    ("segments", "expected"),
    [
        (((0, 0), (4, 4), (0, 4), (4, 0)), "proper"),
        (((0, 0), (4, 0), (4, 0), (4, 4)), "touch"),
        (((0, 0), (1, 0), (2, 0), (3, 0)), "disjoint"),
    ],
)
def test_segment_relation_examples(segments, expected: str) -> None:
    assert segment_relation(*segments) == expected


def test_crossing_counter_accepts_large_exact_integer_coordinates() -> None:
    graph = nx.Graph([(0, 1)])
    positions = [(0, 0), (2**53, 0)]
    assert count_crossings(graph, positions, limit=0)["crossings"] == 0


def test_crossing_counter_rejects_coordinates_outside_float_range() -> None:
    graph = nx.Graph([(0, 1)])
    positions = [(0, 0), (10**400, 0)]
    with pytest.raises((OverflowError, ValueError)):
        count_crossings(graph, positions, limit=0)


def test_table_generator_matches_committed_table(tmp_path: Path) -> None:
    results = json.loads((EXPERIMENT_DIR / "results.json").read_text())
    generated = tmp_path / "conditions_table.tex"
    write_table(results, generated)
    assert generated.read_bytes() == (EXPERIMENT_DIR / "conditions_table.tex").read_bytes()
