#!/usr/bin/env python3
"""Survey structural and conditioning claims across the available case corpus."""

from __future__ import annotations

import argparse
from collections import defaultdict
import hashlib
import json
import math
from pathlib import Path
import subprocess
import tomllib

import networkx as nx
import numpy as np
from scipy import sparse
from scipy.sparse import linalg as sparse_linalg

from run_conditions import (
    count_crossings,
    environment_metadata,
    graphviz_positions,
    normalized_largest_component,
    separator_certificate,
    separator_partition,
    sha256_file,
    treewidth_certificate,
)
from query_conditions import (
    LaplacianAnalyzer,
    analyze_operating_point,
    controlled_corridor,
    extract_injection_and_controls,
    weighted_laplacian,
)
from publication_policy import (
    DEFAULT_POLICY_PATH,
    environment_errors,
    load_policy,
    provenance_errors,
    repository_provenance,
)


SCRIPT_DIR = Path(__file__).resolve().parent


def topology_signature(graph: nx.Graph) -> str:
    """Hash original bus ids and the simple undirected edge set."""
    bus_ids = {node: str(graph.nodes[node]["bus_id"]) for node in graph.nodes()}
    digest = hashlib.sha256()
    for bus_id in sorted(bus_ids.values()):
        digest.update(f"v:{bus_id}\n".encode())
    edges = sorted(tuple(sorted((bus_ids[u], bus_ids[v]))) for u, v in graph.edges())
    for u, v in edges:
        digest.update(f"e:{u}:{v}\n".encode())
    return digest.hexdigest()


def geographic_positions(network, graph: nx.Graph) -> tuple[list[tuple[int, int]] | None, dict]:
    """Return a deterministic general position drawing from case coordinates."""
    try:
        layer = network.geo_layer()
    except ValueError:
        return None, {"available": False, "located_buses": 0}
    coordinates = {}
    for feature in layer["features"]:
        properties = feature.get("properties", {})
        geometry = feature.get("geometry", {})
        if properties.get("target") == "bus" and geometry.get("type") == "Point":
            coordinates[str(properties.get("id"))] = geometry["coordinates"]
    located = sum(str(graph.nodes[node]["bus_id"]) in coordinates for node in graph.nodes())
    metadata = {
        "available": located == graph.number_of_nodes(),
        "located_buses": located,
        "coordinate_space": layer.get("powerio_geo", {}).get("space"),
    }
    if not metadata["available"]:
        return None, metadata
    modulus = 1_000_003
    positions = []
    for node in graph.nodes():
        x, y = coordinates[str(graph.nodes[node]["bus_id"])]
        base_x = int(round(float(x) * 1_000_000_000))
        base_y = int(round(float(y) * 1_000_000_000))
        jitter_x = (node * 2_654_435_761 + 1_013_904_223) % modulus
        jitter_y = (node * node * 2_246_822_519 + node * 3_266_489_917 + 17) % modulus
        positions.append((base_x * modulus + jitter_x, base_y * modulus + jitter_y))
    if len(set(positions)) != graph.number_of_nodes():
        raise ValueError("geographic coordinate perturbation did not separate vertices")
    return positions, metadata


def near_planarity_from_positions(
    graph: nx.Graph, positions: list[tuple[int, int]], source: str
) -> dict:
    n = graph.number_of_nodes()
    numerator = n * n - 1152 * n
    crossing_limit = numerator // 1152 if numerator >= 0 else -1
    count = count_crossings(graph, positions, crossing_limit)
    result = {
        **count,
        "crossing_limit": crossing_limit,
        "drawing_source": source,
        "positions": [[x, y] for x, y in positions],
        "position_hash": hashlib.sha256(
            "\n".join(f"{x},{y}" for x, y in positions).encode()
        ).hexdigest(),
    }
    result["holds"] = bool(
        count["complete"]
        and count["crossings"] is not None
        and 1152 * (n + count["crossings"]) <= n * n
    )
    result["status"] = (
        "certificate-found" if result["holds"] else "threshold-exceeded"
    )
    return result


def branch_weight_data(network, graph: nx.Graph) -> tuple[dict[tuple[int, int], float], dict]:
    """Aggregate positive series susceptances over parallel active branches."""
    node_for_bus = {int(graph.nodes[node]["bus_id"]): node for node in graph.nodes()}
    weights: dict[tuple[int, int], float] = defaultdict(float)
    invalid_reactance = 0
    self_loops = 0
    outside_component = 0
    active_branches = 0
    multigraph_degree = [0] * graph.number_of_nodes()
    for branch in network.branches:
        if not branch["in_service"]:
            continue
        active_branches += 1
        source = int(branch["from_id"])
        target = int(branch["to_id"])
        if source not in node_for_bus or target not in node_for_bus:
            outside_component += 1
            continue
        u = node_for_bus[source]
        v = node_for_bus[target]
        if u == v:
            self_loops += 1
            continue
        x = float(branch["x"])
        if not math.isfinite(x) or x <= 0:
            invalid_reactance += 1
            continue
        edge = (u, v) if u < v else (v, u)
        weights[edge] += 1.0 / x
        multigraph_degree[u] += 1
        multigraph_degree[v] += 1
    graph_edges = {(u, v) if u < v else (v, u) for u, v in graph.edges()}
    missing_edges = len(graph_edges - set(weights))
    metadata = {
        "active_branches": active_branches,
        "outside_largest_component": outside_component,
        "self_loops": self_loops,
        "nonpositive_or_nonfinite_reactance": invalid_reactance,
        "weighted_simple_edges": len(weights),
        "missing_simple_edges": missing_edges,
        "maximum_branch_degree": max(multigraph_degree, default=0),
        "usable": invalid_reactance == 0 and missing_edges == 0 and bool(weights),
    }
    return dict(weights), metadata


def conditioning_bounds(network, graph: nx.Graph) -> dict:
    weights, metadata = branch_weight_data(network, graph)
    result = {"weight_model": "b_e = 1/x_e for each active ordinary branch", **metadata}
    if not metadata["usable"]:
        return result
    a, separator, b, _ = separator_partition(graph)
    side = a | separator
    boundary_weight = sum(
        weight for (u, v), weight in weights.items() if (u in side) != (v in side)
    )
    total_weight = sum(weights.values())
    maximum_weight = max(weights.values())
    n = graph.number_of_nodes()
    beta = min(len(side), len(b)) / n
    s = len(separator)
    degree = metadata["maximum_branch_degree"]
    result.update(
        {
            "total_weight": total_weight,
            "boundary_weight": boundary_weight,
            "maximum_aggregated_weight": maximum_weight,
            "beta": beta,
            "separator_size": s,
            "weighted_cut_lower_bound": (
                2 * beta * (1 - beta) * max(total_weight, n * maximum_weight)
                / boundary_weight
            ),
            "separator_count_lower_bound": (
                2 * beta * (1 - beta) * total_weight / (s * degree * maximum_weight)
            ),
        }
    )
    return result


def spectral_condition_number(
    graph: nx.Graph, weights: dict[tuple[int, int], float], maximum_n: int
) -> dict:
    n = graph.number_of_nodes()
    if n > maximum_n:
        return {"status": "skipped-size", "maximum_n": maximum_n}
    rows: list[int] = []
    columns: list[int] = []
    values: list[float] = []
    diagonal = np.zeros(n)
    for (u, v), weight in weights.items():
        rows.extend((u, v))
        columns.extend((v, u))
        values.extend((-weight, -weight))
        diagonal[u] += weight
        diagonal[v] += weight
    laplacian = sparse.coo_matrix((values, (rows, columns)), shape=(n, n)).tocsr()
    laplacian = laplacian + sparse.diags(diagonal)
    method = "dense-eigh"
    try:
        if n <= 100:
            eigenvalues, eigenvectors = np.linalg.eigh(laplacian.toarray())
            lambda_zero = float(eigenvalues[0])
            lambda_two = float(eigenvalues[1])
            lambda_maximum = float(eigenvalues[-1])
            vector_two = eigenvectors[:, 1]
            vector_maximum = eigenvectors[:, -1]
        else:
            generator = np.random.default_rng(42)
            deterministic_start = generator.standard_normal(n)
            largest_values, largest_vectors = sparse_linalg.eigsh(
                laplacian,
                k=1,
                which="LA",
                v0=deterministic_start,
                tol=1e-10,
                maxiter=max(10_000, 20 * n),
            )
            lambda_maximum = float(largest_values[0])
            scale = max(1.0, lambda_maximum)
            ones = np.ones(n)
            nullspace_shift = 2 * scale
            shifted_laplacian = sparse_linalg.LinearOperator(
                (n, n),
                matvec=lambda vector: (
                    laplacian @ vector
                    + nullspace_shift * float(np.mean(vector)) * ones
                ),
                dtype=np.float64,
            )
            low_start = generator.standard_normal(n)
            low_start -= np.mean(low_start)
            small_values, small_vectors = sparse_linalg.eigsh(
                shifted_laplacian,
                k=1,
                which="SA",
                v0=low_start,
                tol=1e-9,
                maxiter=max(10_000, 20 * n),
            )
            lambda_zero = 0.0
            lambda_two = float(small_values[0])
            vector_two = small_vectors[:, 0]
            vector_maximum = largest_vectors[:, 0]
            method = "eigsh-nullspace-shifted"
    except sparse_linalg.ArpackNoConvergence as error:
        return {"status": "no-convergence", "converged_eigenvalues": error.eigenvalues.tolist()}
    scale = max(1.0, lambda_maximum)
    residual_two = float(np.linalg.norm(laplacian @ vector_two - lambda_two * vector_two) / scale)
    residual_maximum = float(
        np.linalg.norm(laplacian @ vector_maximum - lambda_maximum * vector_maximum) / scale
    )
    null_residual = float(
        np.linalg.norm(laplacian @ np.ones(n)) / (scale * math.sqrt(n))
    )
    if (
        lambda_two <= 0
        or abs(lambda_zero) > 1e-8 * scale
        or null_residual > 1e-10
        or residual_two > 1e-7
        or residual_maximum > 1e-7
    ):
        return {
            "status": "invalid-spectrum",
            "method": method,
            "lambda_zero": lambda_zero,
            "lambda_two": lambda_two,
            "lambda_maximum": lambda_maximum,
            "null_residual": null_residual,
            "relative_residual_lambda_two": residual_two,
            "relative_residual_lambda_maximum": residual_maximum,
        }
    return {
        "status": "computed",
        "method": method,
        "lambda_zero": lambda_zero,
        "lambda_two": lambda_two,
        "lambda_maximum": lambda_maximum,
        "pseudo_condition_number": lambda_maximum / lambda_two,
        "null_residual": null_residual,
        "relative_residual_lambda_two": residual_two,
        "relative_residual_lambda_maximum": residual_maximum,
    }


def analyze_network(
    label: str,
    path: Path,
    julia_helper: Path,
    spectral_max_n: int,
    skip_treewidth: bool,
    skip_near_planar: bool,
) -> tuple[dict, object, nx.Graph, LaplacianAnalyzer | None]:
    import powerio

    network = powerio.parse_file(path)
    graph, graph_metadata = normalized_largest_component(network)
    planar = bool(nx.check_planarity(graph, counterexample=False)[0])
    separator = separator_certificate(graph)
    treewidth = None if skip_treewidth else treewidth_certificate(graph, julia_helper)
    positions, geo = geographic_positions(network, graph)
    near_planar = None
    if not skip_near_planar:
        if graph.number_of_nodes() < 1152:
            near_planar = {
                "status": "inapplicable-size",
                "minimum_buses": 1152,
                "holds": False,
            }
        else:
            source = "case-geography"
            drawing_version = None
            try:
                if positions is None:
                    positions, drawing_version = graphviz_positions(graph)
                    source = "graphviz-sfdp"
                near_planar = near_planarity_from_positions(graph, positions, source)
                if drawing_version is not None:
                    near_planar["drawing_tool_version"] = drawing_version
            except (RuntimeError, ValueError, subprocess.SubprocessError) as error:
                near_planar = {
                    "status": "unavailable",
                    "drawing_source": source,
                    "holds": False,
                    "reason": str(error),
                }
    bounds = conditioning_bounds(network, graph)
    weights, _ = branch_weight_data(network, graph)
    analyzer = None
    if not bounds["usable"]:
        spectrum = {"status": "skipped-weight-model"}
        proposition3 = {
            "status": "unavailable",
            "reason": "positive series susceptance model does not apply",
        }
    elif graph.number_of_nodes() > spectral_max_n:
        spectrum = {"status": "skipped-size", "maximum_n": spectral_max_n}
        extracted = extract_injection_and_controls(network, graph)
        proposition3 = {
            "status": "indeterminate",
            "reason": "spectral size limit",
            "extraction": {
                key: value for key, value in extracted.items() if key != "injection"
            },
        }
    else:
        analyzer = LaplacianAnalyzer(
            weighted_laplacian(graph.number_of_nodes(), weights), graph
        )
        spectrum = {
            "status": "computed",
            "method": analyzer.spectral_method,
            "lambda_zero": 0.0,
            "lambda_two": analyzer.lambda_two,
            "lambda_maximum": analyzer.lambda_maximum,
            "pseudo_condition_number": analyzer.kappa,
            "null_residual": analyzer.null_residual,
            "relative_residual_lambda_two": analyzer.residual_two,
            "relative_residual_lambda_maximum": analyzer.residual_maximum,
            "orthogonality_residual": analyzer.orthogonality_residual,
        }
        proposition3 = analyze_operating_point(network, graph, analyzer)
    result = {
        "label": label,
        "source_path": str(path),
        "source_sha256": sha256_file(path),
        "graph": graph_metadata,
        "topology_sha256": topology_signature(graph),
        "planar": planar,
        "separator": separator,
        "treewidth": treewidth,
        "geography": geo,
        "near_planar": near_planar,
        "conditioning": bounds,
        "spectrum": spectrum,
        "proposition3": proposition3,
    }
    return result, network, graph, analyzer


def compare_case(
    path: Path,
    reported_path: str,
    expected_signature: str,
    analyzer: LaplacianAnalyzer | None = None,
) -> dict:
    import powerio

    try:
        network = powerio.parse_file(path)
        graph, metadata = normalized_largest_component(network)
        signature = topology_signature(graph)
        result = {
            "path": reported_path,
            "parsed": True,
            "matches_primary_topology": signature == expected_signature,
            "topology_sha256": signature,
            "graph": metadata,
        }
        if signature != expected_signature:
            result["proposition3"] = {
                "status": "unavailable",
                "reason": "variant topology differs from primary",
            }
        elif analyzer is None:
            extracted = extract_injection_and_controls(network, graph)
            result["proposition3"] = {
                "status": "indeterminate",
                "reason": "primary spectral analysis unavailable",
                "extraction": {
                    key: value for key, value in extracted.items() if key != "injection"
                },
            }
        else:
            result["proposition3"] = analyze_operating_point(network, graph, analyzer)
        return result
    except Exception as error:
        return {"path": reported_path, "parsed": False, "error": str(error)}


def parse_display(path: Path, reported_path: str) -> dict:
    import powerio

    try:
        display = powerio.parse_display_file(path)
        count = len(display.data.substations) if display.kind == "powerworld" else None
        return {
            "path": reported_path,
            "parsed": True,
            "kind": display.kind,
            "substations": count,
        }
    except Exception as error:
        return {"path": reported_path, "parsed": False, "error": str(error)}


def pglib_cases(root: Path) -> list[dict]:
    return [
        {
            "key": path.stem,
            "label": path.stem.removeprefix("pglib_opf_case"),
            "primary": str(path.relative_to(root)),
        }
        for path in sorted((root / "pglib-opf").glob("pglib_opf_case*.m"))
    ]


def load_extra_cases(path: Path) -> list[dict]:
    with path.open("rb") as stream:
        return tomllib.load(stream)["case"]


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--powerio-root", type=Path, required=True)
    parser.add_argument("--datasets-root", type=Path, required=True)
    parser.add_argument("--expected-powerio-version", default="0.7.3")
    parser.add_argument("--spectral-max-n", type=int, default=8_000)
    parser.add_argument("--skip-treewidth", action="store_true")
    parser.add_argument("--skip-near-planar", action="store_true")
    parser.add_argument("--skip-pglib-variants", action="store_true")
    parser.add_argument("--case", action="append", dest="case_keys")
    parser.add_argument(
        "--output", type=Path, default=SCRIPT_DIR / "results" / "corpus-survey.json"
    )
    parser.add_argument("--publication", action="store_true")
    parser.add_argument("--publication-policy", type=Path, default=DEFAULT_POLICY_PATH)
    return parser.parse_args()


def main() -> None:
    import powerio

    args = parse_args()
    policy = load_policy(args.publication_policy)
    if powerio.__version__ != args.expected_powerio_version:
        raise RuntimeError(
            f"expected PowerIO {args.expected_powerio_version}, got {powerio.__version__}"
        )
    if args.publication and (
        args.skip_treewidth
        or args.skip_near_planar
        or args.skip_pglib_variants
        or args.case_keys
    ):
        raise ValueError("publication survey does not permit skipped or selected analyses")
    if args.publication and args.spectral_max_n != policy.spectral_max_n:
        raise ValueError(
            f"publication spectral cutoff must be {policy.spectral_max_n}"
        )
    environment = environment_metadata(args.powerio_root.resolve())
    if args.publication:
        errors = environment_errors(environment, policy) + provenance_errors(policy)
        if errors:
            raise RuntimeError("\n".join(errors))
    datasets_root = args.datasets_root.resolve()
    canonical_pglib = pglib_cases(datasets_root)
    extra_cases = load_extra_cases(SCRIPT_DIR / "survey_cases.toml")
    if args.publication:
        if tuple(case["key"] for case in canonical_pglib) != policy.pglib_keys:
            raise ValueError("PGLib case coverage differs from publication policy")
        if tuple(case["key"] for case in extra_cases) != policy.extra_keys:
            raise ValueError("extra case coverage differs from publication policy")
    cases = canonical_pglib + extra_cases
    if args.case_keys:
        requested = set(args.case_keys)
        cases = [case for case in cases if case["key"] in requested]
        missing = requested - {case["key"] for case in cases}
        if missing:
            raise ValueError(f"unknown case keys: {sorted(missing)}")
    results = []
    failures = []
    for index, case in enumerate(cases, 1):
        path = datasets_root / case["primary"]
        print(f"[{index}/{len(cases)}] {case['label']}: {path}", flush=True)
        try:
            result, _, graph, analyzer = analyze_network(
                case["label"],
                path,
                SCRIPT_DIR / "treewidth_bound.jl",
                args.spectral_max_n,
                args.skip_treewidth,
                args.skip_near_planar,
            )
            result["key"] = case["key"]
            result["source_path"] = case["primary"]
            comparisons = [
                compare_case(
                    datasets_root / equivalent,
                    equivalent,
                    result["topology_sha256"],
                    analyzer,
                )
                for equivalent in case.get("equivalent", [])
            ]
            if case["key"].startswith("pglib_opf_case") and not args.skip_pglib_variants:
                stem = Path(case["primary"]).stem
                comparisons.extend(
                    compare_case(
                        datasets_root / "pglib-opf" / folder / f"{stem}__{suffix}.m",
                        f"pglib-opf/{folder}/{stem}__{suffix}.m",
                        result["topology_sha256"],
                        analyzer,
                    )
                    for folder, suffix in (("api", "api"), ("sad", "sad"))
                )
            result["equivalent_formats"] = comparisons
            result["display_files"] = [
                parse_display(datasets_root / display, display)
                for display in case.get("display", [])
            ]
            results.append(result)
        except Exception as error:
            failures.append(
                {"key": case["key"], "path": case["primary"], "error": str(error)}
            )
    document = {
        "schema_version": 2,
        "environment": environment,
        "parameters": dict(policy.algorithms),
        "publication_policy_sha256": policy.source_sha256,
        "provenance": repository_provenance(policy),
        "scope": {
            "pglib_canonical_cases": len(canonical_pglib),
            "pglib_variants_per_case": 0 if args.skip_pglib_variants else 2,
            "extra_cases": len(extra_cases),
            "primary_cases": len(cases),
            "pglib_variant_files": (
                0 if args.skip_pglib_variants else 2 * len(canonical_pglib)
            ),
            "spectral_max_n": args.spectral_max_n,
            "near_planarity_min_n": policy.near_planarity_min_n,
            "treewidth_enabled": not args.skip_treewidth,
            "near_planarity_enabled": not args.skip_near_planar,
            "right_hand_side_analysis": True,
        },
        "cases": results,
        "controlled_corridors": [
            controlled_corridor(length, kind)
            for length in (8, 16, 32)
            for kind in ("easy-eigenvector", "sparse-endpoints", "hard-pair-plus")
        ],
        "failures": failures,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(document, indent=2, sort_keys=True) + "\n")
    if failures:
        raise RuntimeError(f"{len(failures)} case(s) failed; see {args.output}")


if __name__ == "__main__":
    main()
