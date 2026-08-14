#!/usr/bin/env python3
"""Generate verified structural certificates and the paper's TeX table."""

from __future__ import annotations

import argparse
import hashlib
import json
import math
from pathlib import Path
import shlex
import shutil
import subprocess
import sys
import tempfile
import tomllib
from typing import Iterable, Sequence

import networkx as nx
import numpy as np
import pymetis
import scipy
import shapely
from shapely import STRtree, box

from publication_policy import (
    DEFAULT_POLICY_PATH,
    environment_errors,
    graphviz_version,
    load_policy,
    provenance_errors,
    repository_provenance,
)


SCRIPT_DIR = Path(__file__).resolve().parent
SEPARATOR_SEED = 42
GRAPHVIZ_START = "42"
GRAPHVIZ_OVERLAP = "scale"
EXPECTED_POWERIO_VERSION = "0.7.3"


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def stable_hash_ints(values: Iterable[int]) -> str:
    digest = hashlib.sha256()
    for value in values:
        digest.update(f"{value}\n".encode())
    return digest.hexdigest()


def command_output(command: Sequence[str], cwd: Path | None = None) -> str:
    return subprocess.run(
        command,
        cwd=cwd,
        check=True,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    ).stdout.strip()


def command_version(command: Sequence[str]) -> str:
    process = subprocess.run(
        command,
        check=True,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    return (process.stdout + process.stderr).strip()


def load_cases(path: Path) -> list[dict]:
    with path.open("rb") as stream:
        document = tomllib.load(stream)
    return document["case"]


def normalized_largest_component(network) -> tuple[nx.Graph, dict]:
    raw_graph = network.to_networkx()
    if raw_graph.is_directed():
        raise ValueError("PowerIO returned a directed branch graph")
    raw_graph = nx.Graph(raw_graph)
    raw_graph.remove_edges_from(nx.selfloop_edges(raw_graph))
    components = sorted(nx.connected_components(raw_graph), key=lambda c: (-len(c), min(c)))
    if not components:
        raise ValueError("parsed network contains no buses")
    largest = raw_graph.subgraph(components[0]).copy()
    ordered_nodes = sorted(largest.nodes())
    graph = nx.convert_node_labels_to_integers(
        largest, ordering="sorted", label_attribute="bus_id"
    )
    if sorted(graph.nodes()) != list(range(graph.number_of_nodes())):
        raise AssertionError("node normalization failed")
    active_branches = sum(bool(branch["in_service"]) for branch in network.branches)
    metadata = {
        "parsed_buses": len(network.buses),
        "active_branches": active_branches,
        "simple_edges": graph.number_of_edges(),
        "components": len(components),
        "largest_component_buses": graph.number_of_nodes(),
        "excluded_buses": len(network.buses) - graph.number_of_nodes(),
        "bus_order_hash": stable_hash_ints(ordered_nodes),
    }
    return graph, metadata


def series_reactance_audit(network, graph: nx.Graph) -> dict:
    """Check the positive branch weight assumption on the retained component."""
    retained = {int(graph.nodes[node]["bus_id"]) for node in graph.nodes()}
    degree = {bus_id: 0 for bus_id in retained}
    positive_weights = []
    negative = 0
    zero = 0
    nonfinite = 0
    retained_active = 0
    for branch in network.branches:
        if not branch["in_service"]:
            continue
        source = int(branch["from_id"])
        target = int(branch["to_id"])
        if source not in retained or target not in retained or source == target:
            continue
        retained_active += 1
        degree[source] += 1
        degree[target] += 1
        reactance = float(branch["x"])
        if not math.isfinite(reactance):
            nonfinite += 1
        elif reactance < 0:
            negative += 1
        elif reactance == 0:
            zero += 1
        else:
            positive_weights.append(1.0 / reactance)
    nonpositive = negative + zero + nonfinite
    result = {
        "model": "b_e = 1/x_e on each retained active ordinary branch",
        "retained_active_branches": retained_active,
        "positive_reactances": len(positive_weights),
        "negative_reactances": negative,
        "zero_reactances": zero,
        "nonfinite_reactances": nonfinite,
        "nonpositive_reactances": nonpositive,
        "maximum_branch_degree": max(degree.values(), default=0),
        "positive_weight_assumption_holds": nonpositive == 0,
    }
    if nonpositive == 0 and positive_weights:
        mean_weight = math.fsum(positive_weights) / len(positive_weights)
        maximum_weight = max(positive_weights)
        result.update(
            {
                "mean_susceptance": mean_weight,
                "maximum_susceptance": maximum_weight,
                "mean_to_maximum_ratio": mean_weight / maximum_weight,
            }
        )
    return result


def validate_separator(
    graph: nx.Graph, a: set[int], separator: set[int], b: set[int]
) -> dict:
    all_nodes = set(graph.nodes())
    if a & separator or a & b or separator & b:
        raise ValueError("separator partition is not disjoint")
    if a | separator | b != all_nodes:
        raise ValueError("separator partition does not cover the graph")
    for u, v in graph.edges():
        if (u in a and v in b) or (v in a and u in b):
            raise ValueError("separator leaves an A-B edge")
    n = graph.number_of_nodes()
    minimum_side = min(len(a | separator), len(b))
    return {
        "s": len(separator),
        "beta_numerator": minimum_side,
        "beta_denominator": n,
        "beta": minimum_side / n,
        "partition_hash": hashlib.sha256(
            (
                "A:" + ",".join(map(str, sorted(a)))
                + "\nX:" + ",".join(map(str, sorted(separator)))
                + "\nB:" + ",".join(map(str, sorted(b)))
            ).encode()
        ).hexdigest(),
    }


def separator_partition(graph: nx.Graph) -> tuple[set[int], set[int], set[int], int]:
    # Preserve PowerIO's branch order. METIS is deterministic for a fixed CSR
    # ordering, and the case hash plus PowerIO version fix that ordering.
    adjacency = [list(graph.neighbors(node)) for node in graph.nodes()]
    options = pymetis.Options(
        seed=SEPARATOR_SEED,
        ncuts=8,
        niter=20,
        contig=1,
        minconn=1,
        ufactor=30,
    )
    _, membership = pymetis.part_graph(
        2, adjacency=adjacency, options=options
    )
    sides = [
        {node for node, part in enumerate(membership) if part == side}
        for side in (0, 1)
    ]
    boundaries = []
    for side in (0, 1):
        other = 1 - side
        boundaries.append(
            {
                node
                for node in sides[side]
                if any(neighbor in sides[other] for neighbor in graph.neighbors(node))
            }
        )
    chosen = min((0, 1), key=lambda side: (len(boundaries[side]), side))
    a = sides[chosen] - boundaries[chosen]
    separator = boundaries[chosen]
    b = sides[1 - chosen]
    # Recompute the cut from the returned membership. Some valid inputs make
    # METIS's reported objective overflow even though its partition is valid.
    edge_cut = sum(membership[u] != membership[v] for u, v in graph.edges())
    return a, separator, b, edge_cut


def separator_certificate(graph: nx.Graph) -> dict:
    a, separator, b, edge_cut = separator_partition(graph)
    result = validate_separator(graph, a, separator, b)
    n = graph.number_of_nodes()
    result.update(
        {
            "edge_cut": edge_cut,
            "seed": SEPARATOR_SEED,
            "s_limit": math.isqrt(8 * n),
            "holds": 4 * result["beta_numerator"] >= n
            and result["s"] ** 2 <= 8 * n,
        }
    )
    return result


def validate_tree_decomposition(
    graph: nx.Graph, order: list[int], bags: list[set[int]]
) -> dict:
    n = graph.number_of_nodes()
    if len(order) != n or len(set(order)) != n or set(order) != set(graph.nodes()):
        raise ValueError("elimination ordering is not a vertex permutation")
    if len(bags) != n:
        raise ValueError("tree decomposition has the wrong bag count")
    position = {vertex: index for index, vertex in enumerate(order)}
    for index, bag in enumerate(bags):
        vertex = order[index]
        if vertex not in bag:
            raise ValueError("elimination bag omits its vertex")
        if any(position[item] < index for item in bag if item != vertex):
            raise ValueError("elimination bag contains an earlier vertex")
    for u, v in graph.edges():
        early, late = (u, v) if position[u] < position[v] else (v, u)
        if late not in bags[position[early]]:
            raise ValueError("tree decomposition does not cover an edge")
    for index, bag in enumerate(bags[:-1]):
        vertex = order[index]
        later = bag - {vertex}
        if not later:
            continue
        parent_vertex = min(later, key=position.__getitem__)
        parent_index = position[parent_vertex]
        if not later <= bags[parent_index]:
            raise ValueError("tree decomposition violates running intersection")
    width = max((len(bag) - 1 for bag in bags), default=0)
    digest = hashlib.sha256()
    for vertex, bag in zip(order, bags, strict=True):
        digest.update(f"{vertex}:".encode())
        digest.update(",".join(map(str, sorted(bag))).encode())
        digest.update(b"\n")
    return {
        "upper_bound": width,
        "ordering_hash": stable_hash_ints(order),
        "decomposition_hash": digest.hexdigest(),
        "holds": 4 * (width + 1) <= n,
    }


def treewidth_certificate(graph: nx.Graph, julia_helper: Path) -> dict:
    with tempfile.TemporaryDirectory(prefix="treewidth-certificate-") as temp_dir:
        temp_path = Path(temp_dir)
        edge_path = temp_path / "edges.txt"
        output_path = temp_path / "decomposition.txt"
        with edge_path.open("w", encoding="ascii") as stream:
            for u, v in sorted(graph.edges()):
                stream.write(f"{u} {v}\n")
        subprocess.run(
            [
                "julia",
                "--startup-file=no",
                str(julia_helper),
                str(graph.number_of_nodes()),
                str(edge_path),
                str(output_path),
            ],
            check=True,
        )
        with output_path.open(encoding="ascii") as stream:
            order_line = stream.readline().split()
            if not order_line or order_line[0] != "order":
                raise ValueError("Julia helper returned no ordering")
            order = [int(value) for value in order_line[1:]]
            bags = []
            for line in stream:
                fields = line.split()
                if not fields or fields[0] != "bag":
                    raise ValueError("Julia helper returned an invalid bag")
                bags.append({int(value) for value in fields[1:]})
    return validate_tree_decomposition(graph, order, bags)


def graphviz_positions(graph: nx.Graph) -> tuple[list[tuple[int, int]], str]:
    executable = shutil.which("sfdp")
    if executable is None:
        raise RuntimeError("sfdp is not installed")
    lines = [
        "strict graph G {",
        f'graph [start="{GRAPHVIZ_START}", overlap="{GRAPHVIZ_OVERLAP}"];',
        'node [shape="point", width="0.01", height="0.01", label=""];',
    ]
    lines.extend(f"v{node};" for node in graph.nodes())
    lines.extend(f"v{u} -- v{v};" for u, v in graph.edges())
    lines.append("}")
    process = subprocess.run(
        [
            executable,
            "-Tplain",
            f"-Gstart={GRAPHVIZ_START}",
            f"-Goverlap={GRAPHVIZ_OVERLAP}",
        ],
        input="\n".join(lines),
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=True,
        timeout=600,
    )
    base_positions: dict[int, tuple[int, int]] = {}
    for line in process.stdout.splitlines():
        fields = shlex.split(line)
        if fields and fields[0] == "node":
            node = int(fields[1][1:])
            x = int(round(float(fields[2]) * 1_000_000))
            y = int(round(float(fields[3]) * 1_000_000))
            base_positions[node] = (x, y)
    if len(base_positions) != graph.number_of_nodes():
        raise ValueError("sfdp did not return every vertex position")
    jitter_modulus = 1_000_003
    positions = []
    for node in graph.nodes():
        base_x, base_y = base_positions[node]
        jitter_x = (node * 2654435761 + 1013904223) % jitter_modulus
        jitter_y = (node * node * 2246822519 + node * 3266489917 + 17) % jitter_modulus
        positions.append(
            (
                base_x * jitter_modulus + jitter_x,
                base_y * jitter_modulus + jitter_y,
            )
        )
    if len(set(positions)) != graph.number_of_nodes():
        raise ValueError("deterministic coordinate perturbation did not separate vertices")
    version = graphviz_version(command_version([executable, "-V"]))
    if version is None:
        raise ValueError("could not parse the sfdp version banner")
    return positions, version


def orientation(a: tuple[int, int], b: tuple[int, int], c: tuple[int, int]) -> int:
    return (b[0] - a[0]) * (c[1] - a[1]) - (b[1] - a[1]) * (c[0] - a[0])


def on_segment(a: tuple[int, int], b: tuple[int, int], p: tuple[int, int]) -> bool:
    return (
        orientation(a, b, p) == 0
        and min(a[0], b[0]) <= p[0] <= max(a[0], b[0])
        and min(a[1], b[1]) <= p[1] <= max(a[1], b[1])
    )


def segment_relation(
    a: tuple[int, int],
    b: tuple[int, int],
    c: tuple[int, int],
    d: tuple[int, int],
) -> str:
    o1 = orientation(a, b, c)
    o2 = orientation(a, b, d)
    o3 = orientation(c, d, a)
    o4 = orientation(c, d, b)
    if ((o1 > 0 > o2) or (o2 > 0 > o1)) and (
        (o3 > 0 > o4) or (o4 > 0 > o3)
    ):
        return "proper"
    touches = (
        (o1 == 0 and on_segment(a, b, c))
        or (o2 == 0 and on_segment(a, b, d))
        or (o3 == 0 and on_segment(c, d, a))
        or (o4 == 0 and on_segment(c, d, b))
    )
    return "touch" if touches else "disjoint"


def count_crossings(
    graph: nx.Graph,
    positions: Sequence[tuple[int, int]],
    limit: int,
    chunk_size: int = 1024,
) -> dict:
    edges = list(graph.edges())
    if not edges:
        return {"crossings": 0, "crossings_at_least": 0, "complete": True}
    bounds = []
    for u, v in edges:
        min_x, max_x = sorted((positions[u][0], positions[v][0]))
        min_y, max_y = sorted((positions[u][1], positions[v][1]))
        float_bounds = tuple(map(float, (min_x, min_y, max_x, max_y)))
        if not all(math.isfinite(value) for value in float_bounds):
            raise ValueError("coordinates exceed the finite float64 range")
        bounds.append(
            (
                math.nextafter(float_bounds[0], -math.inf),
                math.nextafter(float_bounds[1], -math.inf),
                math.nextafter(float_bounds[2], math.inf),
                math.nextafter(float_bounds[3], math.inf),
            )
        )
    bounds_array = np.array(bounds, dtype=np.float64)
    geometries = box(
        bounds_array[:, 0],
        bounds_array[:, 1],
        bounds_array[:, 2],
        bounds_array[:, 3],
    )
    tree = STRtree(geometries)
    crossings = 0
    for start in range(0, len(edges), chunk_size):
        stop = min(start + chunk_size, len(edges))
        pairs = tree.query(geometries[start:stop])
        for local_index, other_index in zip(pairs[0], pairs[1], strict=True):
            edge_index = start + int(local_index)
            other_index = int(other_index)
            if other_index <= edge_index:
                continue
            u, v = edges[edge_index]
            x, y = edges[other_index]
            relation = segment_relation(
                positions[u], positions[v], positions[x], positions[y]
            )
            shared = {u, v} & {x, y}
            if shared:
                if relation == "proper":
                    raise ValueError("incident straight edges cross away from their endpoint")
                if relation == "touch":
                    common = next(iter(shared))
                    other_a = v if u == common else u
                    other_b = y if x == common else x
                    if orientation(positions[common], positions[other_a], positions[other_b]) == 0:
                        vector_a = (
                            positions[other_a][0] - positions[common][0],
                            positions[other_a][1] - positions[common][1],
                        )
                        vector_b = (
                            positions[other_b][0] - positions[common][0],
                            positions[other_b][1] - positions[common][1],
                        )
                        if vector_a[0] * vector_b[0] + vector_a[1] * vector_b[1] > 0:
                            raise ValueError("incident straight edges overlap")
                continue
            if relation == "proper":
                crossings += 1
                if crossings > limit:
                    return {
                        "crossings": None,
                        "crossings_at_least": crossings,
                        "complete": False,
                    }
            elif relation == "touch":
                raise ValueError("drawing has a nonproper edge intersection")
    return {"crossings": crossings, "crossings_at_least": crossings, "complete": True}


def near_planar_certificate(graph: nx.Graph) -> dict:
    n = graph.number_of_nodes()
    numerator = n * n - 1152 * n
    crossing_limit = numerator // 1152 if numerator >= 0 else -1
    try:
        positions, graphviz_version = graphviz_positions(graph)
        count = count_crossings(graph, positions, crossing_limit)
    except (RuntimeError, ValueError, subprocess.SubprocessError) as error:
        return {
            "marker": "unavailable",
            "holds": False,
            "reason": str(error),
            "crossing_limit": crossing_limit,
        }
    result = {
        **count,
        "crossing_limit": crossing_limit,
        "graphviz_start": GRAPHVIZ_START,
        "graphviz_overlap": GRAPHVIZ_OVERLAP,
        "graphviz_version": graphviz_version,
        "position_hash": hashlib.sha256(
            "\n".join(f"{x},{y}" for x, y in positions).encode()
        ).hexdigest(),
    }
    result["holds"] = bool(
        count["complete"]
        and count["crossings"] is not None
        and 1152 * (n + count["crossings"]) <= n * n
    )
    result["marker"] = "check" if result["holds"] else "unavailable"
    return result


def marker(value: str) -> str:
    return {
        "check": r"$\checkmark$",
        "cross": r"$\times$",
        "unavailable": "--",
    }[value]


def write_table(results: dict, output_path: Path) -> None:
    structural_rows = []
    for case in results["cases"]:
        near = marker(case["near_planar"]["marker"])
        separator = marker("check" if case["separator"]["holds"] else "unavailable")
        treewidth = marker("check" if case["treewidth"]["holds"] else "unavailable")
        weights = marker(
            "check"
            if case["series_reactance"]["positive_weight_assumption_holds"]
            else "cross"
        )
        structural_rows.append(
            f'{case["label"]} & {case["graph"]["largest_component_buses"]:,} '
            f'& {weights} & {near} & {separator}~{case["separator"]["s"]} '
            f'& {treewidth}~{case["treewidth"]["upper_bound"]} \\\\'
        )
    table = "\n".join(
        [
            r"\begin{table}[t]",
            r"\caption{Structural conditions. A cross in Positive $b_e$ means the weighted Laplacian model does not apply.}",
            r"\label{tab:conditions}",
            r"\centering",
            r"\setlength{\tabcolsep}{2.2pt}",
            r"\begin{tabular}{lcccrrr}",
            r"\hline",
            r"Case & $n$ & Positive $b_e$ & Near Plan. & Sep. $s$ & $\operatorname{tw}\leq U$ \\",
            r"\hline",
            *structural_rows,
            r"\hline",
            r"\end{tabular}",
            r"\end{table}",
            "",
        ]
    )
    output_path.write_text(table, encoding="ascii")


def environment_metadata(powerio_root: Path) -> dict:
    import powerio

    source_commit = command_output(["git", "rev-parse", "HEAD"], cwd=powerio_root)
    version_commit = command_output(
        ["git", "rev-list", "-n", "1", f"v{powerio.__version__}"], cwd=powerio_root
    )
    if source_commit != version_commit:
        raise RuntimeError(
            f"PowerIO source is at {source_commit}, but imported version "
            f"{powerio.__version__} corresponds to {version_commit}"
        )
    tracked_status = command_output(
        ["git", "status", "--porcelain", "--untracked-files=no"], cwd=powerio_root
    )
    status = command_output(
        ["git", "status", "--porcelain", "--untracked-files=all"], cwd=powerio_root
    )
    sfdp = shutil.which("sfdp")
    graphviz = command_version([sfdp, "-V"]) if sfdp else None
    return {
        "powerio_version": powerio.__version__,
        "powerio_commit": source_commit,
        "powerio_tracked_dirty": bool(tracked_status),
        "powerio_dirty": bool(status),
        "python": sys.version.split()[0],
        "uv": command_output(["uv", "--version"]).split()[1],
        "networkx": nx.__version__,
        "numpy": np.__version__,
        "pymetis": pymetis.version,
        "scipy": scipy.__version__,
        "shapely": shapely.__version__,
        "julia": command_output(["julia", "--version"]).split()[-1],
        "graphviz": graphviz_version(graphviz),
    }


def run_case(case: dict, datasets_root: Path) -> dict:
    import powerio

    case_path = datasets_root / case["path"]
    if not case_path.is_file():
        raise FileNotFoundError(case_path)
    print(f'[{case["label"]}] parsing with PowerIO', flush=True)
    network = powerio.parse_file(case_path)
    graph, graph_metadata = normalized_largest_component(network)
    reactance = series_reactance_audit(network, graph)
    print(f'[{case["label"]}] exact planarity', flush=True)
    planar = nx.check_planarity(graph, counterexample=False)[0]
    print(f'[{case["label"]}] balanced separator', flush=True)
    separator = separator_certificate(graph)
    print(f'[{case["label"]}] treewidth certificate', flush=True)
    treewidth = treewidth_certificate(graph, SCRIPT_DIR / "treewidth_bound.jl")
    print(f'[{case["label"]}] near planarity drawing', flush=True)
    near_planar = near_planar_certificate(graph)
    result = {
        "key": case["key"],
        "label": case["label"],
        "source_path": case["path"],
        "source_sha256": sha256_file(case_path),
        "graph": graph_metadata,
        "series_reactance": reactance,
        "planar": bool(planar),
        "near_planar": near_planar,
        "separator": separator,
        "treewidth": treewidth,
    }
    expected = {
        "source_sha256": result["source_sha256"],
        "n": graph.number_of_nodes(),
        "active_branches": graph_metadata["active_branches"],
        "simple_edges": graph_metadata["simple_edges"],
        "components": graph_metadata["components"],
        "excluded_buses": graph_metadata["excluded_buses"],
        "nonpositive_reactances": reactance["nonpositive_reactances"],
        "separator": separator["s"],
        "treewidth_upper": treewidth["upper_bound"],
    }
    for field, actual in expected.items():
        configured = case[f"expected_{field}"]
        if actual != configured:
            raise AssertionError(
                f'{case["label"]}: expected {field}={configured!r}, got {actual!r}'
            )
    if planar:
        raise AssertionError(f'{case["label"]}: planarity regression')
    return result


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--powerio-root", type=Path, required=True)
    parser.add_argument("--datasets-root", type=Path, required=True)
    parser.add_argument(
        "--expected-powerio-version", default=EXPECTED_POWERIO_VERSION
    )
    parser.add_argument("--case", action="append", dest="case_keys")
    parser.add_argument("--output", type=Path, default=SCRIPT_DIR / "results.json")
    parser.add_argument(
        "--table-output", type=Path, default=SCRIPT_DIR / "conditions_table.tex"
    )
    parser.add_argument("--publication", action="store_true")
    parser.add_argument("--publication-policy", type=Path, default=DEFAULT_POLICY_PATH)
    return parser.parse_args()


def main() -> None:
    import powerio

    args = parse_args()
    if powerio.__version__ != args.expected_powerio_version:
        raise RuntimeError(
            f"expected PowerIO {args.expected_powerio_version}, got {powerio.__version__}"
        )
    policy = load_policy(args.publication_policy)
    environment = environment_metadata(args.powerio_root.resolve())
    if args.publication:
        errors = environment_errors(environment, policy) + provenance_errors(policy)
        if errors:
            raise RuntimeError("\n".join(errors))
    cases = load_cases(SCRIPT_DIR / "cases.toml")
    if args.publication and tuple(case["key"] for case in cases) != policy.core_keys:
        raise ValueError("core case coverage differs from publication policy")
    if args.case_keys:
        requested = set(args.case_keys)
        cases = [case for case in cases if case["key"] in requested]
        missing = requested - {case["key"] for case in cases}
        if missing:
            raise ValueError(f"unknown case keys: {sorted(missing)}")
    results = {
        "schema_version": 1,
        "criteria": {
            "near_planar": "1152 * (n + c_hat) <= n^2",
            "separator": "beta >= 1/4 and s^2 <= 8n",
            "treewidth": "4 * (U + 1) <= n",
        },
        "parameters": dict(policy.algorithms),
        "environment": environment,
        "publication_policy_sha256": policy.source_sha256,
        "provenance": repository_provenance(policy),
        "cases": [run_case(case, args.datasets_root.resolve()) for case in cases],
    }
    serialized = json.dumps(results, indent=2, sort_keys=True) + "\n"
    args.output.write_text(serialized, encoding="utf-8")
    write_table(results, args.table_output)


if __name__ == "__main__":
    main()
