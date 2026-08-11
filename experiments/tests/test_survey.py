from __future__ import annotations

import math
from pathlib import Path

import networkx as nx
import pytest

from run_survey import (
    branch_weight_data,
    geographic_positions,
    near_planarity_from_positions,
    pglib_cases,
    spectral_condition_number,
    topology_signature,
)


class FakeNetwork:
    def __init__(self, branches: list[dict], layer: dict | None = None) -> None:
        self.branches = branches
        self._layer = layer

    def geo_layer(self) -> dict:
        if self._layer is None:
            raise ValueError("no coordinates")
        return self._layer


def graph_with_bus_ids(edges: list[tuple[int, int]]) -> nx.Graph:
    graph = nx.Graph(edges)
    nx.set_node_attributes(graph, {node: str(10 + node) for node in graph}, "bus_id")
    return graph


def test_topology_signature_is_invariant_to_node_and_edge_order() -> None:
    first = graph_with_bus_ids([(0, 1), (1, 2)])
    second = nx.Graph()
    second.add_nodes_from([(8, {"bus_id": "12"}), (7, {"bus_id": "11"}), (6, {"bus_id": "10"})])
    second.add_edges_from([(7, 6), (8, 7)])
    assert topology_signature(first) == topology_signature(second)


def test_branch_weights_aggregate_parallel_lines() -> None:
    graph = graph_with_bus_ids([(0, 1), (1, 2)])
    network = FakeNetwork(
        [
            {"in_service": True, "from_id": 10, "to_id": 11, "x": 0.5},
            {"in_service": True, "from_id": 11, "to_id": 10, "x": 0.25},
            {"in_service": True, "from_id": 11, "to_id": 12, "x": 1.0},
            {"in_service": False, "from_id": 10, "to_id": 12, "x": 0.1},
        ]
    )
    weights, metadata = branch_weight_data(network, graph)
    assert weights == {(0, 1): 6.0, (1, 2): 1.0}
    assert metadata["maximum_branch_degree"] == 3
    assert metadata["missing_simple_edges"] == 0
    assert metadata["usable"]


def test_branch_weights_detect_unrepresented_edge() -> None:
    graph = graph_with_bus_ids([(0, 1), (1, 2)])
    network = FakeNetwork(
        [{"in_service": True, "from_id": 10, "to_id": 11, "x": 0.5}]
    )
    _, metadata = branch_weight_data(network, graph)
    assert metadata["missing_simple_edges"] == 1
    assert not metadata["usable"]


def test_geographic_positions_require_every_retained_bus() -> None:
    graph = graph_with_bus_ids([(0, 1)])
    layer = {
        "powerio_geo": {"space": "diagram"},
        "features": [
            {
                "properties": {"target": "bus", "id": "10"},
                "geometry": {"type": "Point", "coordinates": [1.0, 2.0]},
            }
        ],
    }
    positions, metadata = geographic_positions(FakeNetwork([], layer), graph)
    assert positions is None
    assert metadata == {
        "available": False,
        "located_buses": 1,
        "coordinate_space": "diagram",
    }


def test_geographic_positions_are_distinct_for_coincident_buses() -> None:
    graph = graph_with_bus_ids([(0, 1)])
    layer = {
        "powerio_geo": {"space": "diagram"},
        "features": [
            {
                "properties": {"target": "bus", "id": bus_id},
                "geometry": {"type": "Point", "coordinates": [1.0, 2.0]},
            }
            for bus_id in ("10", "11")
        ],
    }
    positions, metadata = geographic_positions(FakeNetwork([], layer), graph)
    assert metadata["available"]
    assert positions is not None
    assert len(set(positions)) == 2


def test_near_planarity_uses_exact_threshold() -> None:
    graph = nx.Graph([(0, 1), (2, 3)])
    positions = [(0, 0), (10, 10), (0, 10), (10, 0)]
    result = near_planarity_from_positions(graph, positions, "test")
    assert result["crossing_limit"] == -1
    assert result["crossings_at_least"] == 1
    assert not result["complete"]
    assert not result["holds"]


def test_dense_spectrum_matches_path_laplacian() -> None:
    graph = nx.path_graph(4)
    weights = {edge: 1.0 for edge in graph.edges()}
    result = spectral_condition_number(graph, weights, maximum_n=10)
    assert result["status"] == "computed"
    assert result["lambda_two"] == pytest.approx(2 - 2**0.5)
    assert result["lambda_maximum"] == pytest.approx(2 + 2**0.5)


def test_sparse_spectrum_projects_out_constant_nullspace() -> None:
    graph = nx.path_graph(101)
    weights = {edge: 1.0 for edge in graph.edges()}
    result = spectral_condition_number(graph, weights, maximum_n=200)
    assert result["status"] == "computed"
    assert result["lambda_two"] == pytest.approx(
        2 - 2 * math.cos(math.pi / 101), rel=1e-5
    )
    assert result["null_residual"] < 1e-12


def test_pglib_discovery_excludes_api_and_sad_subdirectories(tmp_path: Path) -> None:
    root = tmp_path / "pglib-opf"
    (root / "api").mkdir(parents=True)
    (root / "sad").mkdir()
    (root / "pglib_opf_case14_ieee.m").touch()
    (root / "api" / "pglib_opf_case14_ieee__api.m").touch()
    (root / "sad" / "pglib_opf_case14_ieee__sad.m").touch()
    cases = pglib_cases(tmp_path)
    assert [case["key"] for case in cases] == ["pglib_opf_case14_ieee"]
