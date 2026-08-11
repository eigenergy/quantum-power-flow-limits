#!/usr/bin/env python3
"""Validate corpus survey results and derive deterministic publication files."""

from __future__ import annotations

import argparse
from collections import Counter
import gzip
import hashlib
import io
import json
import math
from pathlib import Path, PureWindowsPath
import re
from typing import Any, Iterable

from publication_policy import (
    DEFAULT_POLICY_PATH,
    EXPERIMENT_DIR,
    PublicationPolicy,
    environment_errors,
    graphviz_version,
    load_policy,
    provenance_errors,
)


SHA256_PATTERN = re.compile(r"[0-9a-f]{64}")
FORBIDDEN_PUBLICATION_FIELDS = {
    "created_at",
    "duration_seconds",
    "elapsed_seconds",
    "generated_at",
    "timestamp",
    "wall_seconds",
}
PATH_FIELDS = {"path", "source_path"}
NEAR_COMPLETE_STATUSES = {"certificate-found", "threshold-exceeded"}


def _is_absolute_path(value: str) -> bool:
    return Path(value).is_absolute() or PureWindowsPath(value).is_absolute()


def _contains_absolute_path(value: str) -> bool:
    for token in value.split():
        candidate = token.strip("'\"()[]{}<>,;:")
        if candidate != "/" and _is_absolute_path(candidate):
            return True
    return False


def _walk(document: Any, location: str = "root") -> Iterable[tuple[str, str, Any]]:
    if isinstance(document, dict):
        for key, value in document.items():
            child = f"{location}.{key}"
            yield child, key, value
            yield from _walk(value, child)
    elif isinstance(document, list):
        for index, value in enumerate(document):
            yield from _walk(value, f"{location}[{index}]")


def _position_hash(positions: list[list[int]]) -> str:
    return hashlib.sha256(
        "\n".join(f"{position[0]},{position[1]}" for position in positions).encode()
    ).hexdigest()


def _validate_near_planarity(case: dict, errors: list[str]) -> None:
    key = case["key"]
    n = case["graph"]["largest_component_buses"]
    near = case.get("near_planar")
    if near is None:
        return
    status = near.get("status")
    if status == "inapplicable-size":
        if near.get("holds") is not False:
            errors.append(f"{key}: inapplicable near planarity result claims to hold")
        return
    if status == "unavailable":
        if near.get("holds") is not False or not near.get("reason"):
            errors.append(f"{key}: unavailable near planarity result lacks a reason")
        return
    if status is not None and status not in NEAR_COMPLETE_STATUSES:
        errors.append(f"{key}: unknown near planarity status {status!r}")
        return
    try:
        near_holds = bool(
            near["complete"]
            and near["crossings"] is not None
            and 1152 * (n + near["crossings"]) <= n * n
        )
    except KeyError as error:
        errors.append(f"{key}: incomplete near planarity result ({error.args[0]})")
        return
    if near.get("holds") != near_holds:
        errors.append(f"{key}: inconsistent near planar verdict")
    expected_status = "certificate-found" if near_holds else "threshold-exceeded"
    if status is not None and status != expected_status:
        errors.append(f"{key}: inconsistent near planarity status")
    positions = near.get("positions")
    if positions is not None:
        valid_positions = (
            isinstance(positions, list)
            and len(positions) == n
            and all(
                isinstance(position, list)
                and len(position) == 2
                and all(isinstance(value, int) for value in position)
                for position in positions
            )
        )
        if not valid_positions:
            errors.append(f"{key}: invalid retained drawing coordinates")
        elif near.get("position_hash") != _position_hash(positions):
            errors.append(f"{key}: drawing coordinate hash mismatch")


def _validate_operating_point(case: dict, errors: list[str]) -> None:
    key = case["key"]
    proposition3 = case.get("proposition3")
    if proposition3 is None:
        errors.append(f"{key}: missing operating point analysis")
        return
    if proposition3.get("status") != "computed":
        if proposition3.get("status") in {"unavailable", "indeterminate"} and not proposition3.get(
            "reason"
        ):
            errors.append(f"{key}: unavailable operating point analysis lacks a reason")
        return
    base = proposition3["base_rhs"]
    grounded = proposition3.get("grounded_slack_sensitivity")
    if grounded is None:
        errors.append(f"{key}: missing grounded slack sensitivity")
    elif grounded["status"] == "computed":
        for slack in grounded["slacks"]:
            if max(slack["residual_minimum"], slack["residual_maximum"]) > 1e-7:
                errors.append(f"{key}: grounded slack residual exceeds tolerance")
    if base["status"] == "computed":
        for field in (
            "solver_residual",
            "second_solver_residual",
            "spectral_residual_lambda_two",
            "spectral_residual_lambda_maximum",
        ):
            if base[field] > 1e-7:
                errors.append(f"{key}: {field} exceeds tolerance")
    for name in ("generator_redispatch", "generator_load_redispatch"):
        restricted = proposition3[name]
        if restricted["status"] != "computed":
            continue
        if max(
            restricted["restricted_solve_residual"],
            restricted["singular_value_residual_max"],
            restricted["singular_value_residual_min"],
            restricted["hard_pair_subspace_residual"],
        ) > 1e-7:
            errors.append(f"{key}: {name} residual exceeds tolerance")
        if restricted.get("hard_pair", {}).get("status") == "computed":
            if abs(
                restricted["hard_pair_input_state_distance"]
                - restricted["hard_pair_expected_input_state_distance"]
            ) > 1e-7:
                errors.append(f"{key}: {name} input hard pair mismatch")
            if abs(
                restricted["hard_pair_solution_state_distance"]
                - restricted["hard_pair_expected_solution_state_distance"]
            ) > 1e-7:
                errors.append(f"{key}: {name} solution hard pair mismatch")


def _publication_errors(
    document: dict,
    policy: PublicationPolicy,
    *,
    verify_policy_files: bool,
) -> list[str]:
    errors: list[str] = []
    scope = document.get("scope", {})
    expected_scope = {
        "pglib_canonical_cases": len(policy.pglib_keys),
        "pglib_variants_per_case": policy.pglib_variants_per_case,
        "extra_cases": len(policy.extra_keys),
        "primary_cases": policy.primary_cases,
        "pglib_variant_files": policy.pglib_variant_files,
        "spectral_max_n": policy.spectral_max_n,
        "near_planarity_min_n": policy.near_planarity_min_n,
        "treewidth_enabled": True,
        "near_planarity_enabled": True,
        "right_hand_side_analysis": True,
    }
    for field, expected in expected_scope.items():
        actual = scope.get(field)
        if actual != expected:
            errors.append(f"scope {field}: expected {expected}, got {actual}")

    cases = document.get("cases", [])
    keys = [case.get("key") for case in cases]
    if keys != list(policy.primary_keys):
        missing = sorted(set(policy.primary_keys) - set(keys))
        extra = sorted(set(keys) - set(policy.primary_keys))
        if missing:
            errors.append(f"missing primary cases: {missing}")
        if extra:
            errors.append(f"unexpected primary cases: {extra}")
        if not missing and not extra:
            errors.append("primary case order differs from publication policy")
    if len(keys) != len(set(keys)):
        errors.append("duplicate primary case keys")

    for location, field, value in _walk(document):
        if field in FORBIDDEN_PUBLICATION_FIELDS:
            errors.append(f"{location}: nondeterministic field is not permitted")
        if field in PATH_FIELDS and isinstance(value, str) and _is_absolute_path(value):
            errors.append(f"{location}: absolute path is not permitted")
        elif isinstance(value, str) and _contains_absolute_path(value):
            errors.append(f"{location}: absolute path fragment is not permitted")

    recorded_provenance = document.get("provenance")
    if recorded_provenance != dict(policy.provenance):
        errors.append("artifact provenance does not match publication policy")
    if document.get("publication_policy_sha256") != policy.source_sha256:
        errors.append("artifact publication policy hash does not match")
    if document.get("parameters") != dict(policy.algorithms):
        errors.append("artifact algorithm parameters do not match publication policy")
    if verify_policy_files:
        errors.extend(provenance_errors(policy))
    errors.extend(environment_errors(document.get("environment", {}), policy))

    for case in cases:
        key = case.get("key", "<missing-key>")
        source_hash = case.get("source_sha256")
        if not isinstance(source_hash, str) or SHA256_PATTERN.fullmatch(source_hash) is None:
            errors.append(f"{key}: missing or invalid source SHA-256")
        graph = case.get("graph", {})
        n = graph.get("largest_component_buses")
        excluded = graph.get("excluded_buses")
        if not isinstance(excluded, int) or excluded < 0:
            errors.append(f"{key}: missing excluded bus count")
        if case.get("treewidth") is None:
            errors.append(f"{key}: treewidth analysis is null")
        near = case.get("near_planar")
        if near is None:
            errors.append(f"{key}: near planarity analysis is null")
        elif isinstance(n, int) and n < policy.near_planarity_min_n:
            if near.get("status") != "inapplicable-size":
                errors.append(f"{key}: small case must be marked inapplicable-size")
        else:
            status = near.get("status")
            if status not in NEAR_COMPLETE_STATUSES:
                errors.append(f"{key}: required near planarity test is incomplete")
            positions = near.get("positions")
            if not isinstance(positions, list) or len(positions) != n:
                errors.append(f"{key}: required drawing coordinates were not retained")
            if near.get("drawing_source") == "graphviz-sfdp":
                actual = graphviz_version(near.get("drawing_tool_version"))
                if actual != policy.versions["graphviz"]:
                    errors.append(f"{key}: drawing Graphviz version drift")

        separator = case.get("separator", {})
        if separator.get("beta_denominator") != n:
            errors.append(f"{key}: separator denominator differs from retained buses")

    corridors = document.get("controlled_corridors")
    if not isinstance(corridors, list) or len(corridors) != 9:
        errors.append("expected all nine controlled corridor diagnostics")
    return errors


def validate(
    document: dict,
    *,
    publication: bool = False,
    policy: PublicationPolicy | None = None,
    verify_policy_files: bool = True,
) -> dict:
    """Validate one survey document and return its derived count summary."""
    errors: list[str] = []
    cases = document.get("cases")
    if not isinstance(cases, list):
        raise ValueError("survey cases must be a list")
    if document.get("schema_version") != 2:
        errors.append("expected corpus schema version 2")
    failures = document.get("failures")
    if not isinstance(failures, list):
        errors.append("survey failures must be a list")
    elif failures:
        errors.append(f"survey contains {len(failures)} case failures")
    environment = document.get("environment", {})
    if environment.get("powerio_version") != "0.7.3":
        errors.append("survey did not use PowerIO 0.7.3")
    if environment.get("powerio_tracked_dirty"):
        errors.append("PowerIO source had tracked modifications")

    keys = [case.get("key") for case in cases]
    if len(keys) != len(set(keys)):
        errors.append("survey contains duplicate case keys")
    pglib = [case for case in cases if str(case.get("key", "")).startswith("pglib_opf_case")]
    expected_pglib = document.get("scope", {}).get("pglib_canonical_cases")
    if len(pglib) != expected_pglib:
        errors.append(f"expected {expected_pglib} PGLib cases, found {len(pglib)}")

    comparisons = []
    for case in cases:
        key = case.get("key", "<missing-key>")
        try:
            n = case["graph"]["largest_component_buses"]
            if _is_absolute_path(case["source_path"]):
                errors.append(f"{key}: absolute source path")
            separator = case["separator"]
            separator_holds = (
                4 * separator["beta_numerator"] >= n and separator["s"] ** 2 <= 8 * n
            )
            if separator["holds"] != separator_holds:
                errors.append(f"{key}: inconsistent separator verdict")
            treewidth = case["treewidth"]
            if treewidth is not None:
                treewidth_holds = 4 * (treewidth["upper_bound"] + 1) <= n
                if treewidth["holds"] != treewidth_holds:
                    errors.append(f"{key}: inconsistent treewidth verdict")
            _validate_near_planarity(case, errors)
            spectrum = case["spectrum"]
            if spectrum["status"] == "computed":
                if spectrum["lambda_two"] <= 0:
                    errors.append(f"{key}: nonpositive lambda2")
                if max(
                    spectrum["null_residual"],
                    spectrum["relative_residual_lambda_two"],
                    spectrum["relative_residual_lambda_maximum"],
                ) > 1e-7:
                    errors.append(f"{key}: spectral residual exceeds tolerance")
                conditioning = case["conditioning"]
                for name in ("weighted_cut_lower_bound", "separator_count_lower_bound"):
                    if conditioning[name] > spectrum["pseudo_condition_number"] * (1 + 1e-7):
                        errors.append(f"{key}: {name} exceeds spectral estimate")
            _validate_operating_point(case, errors)
            case_comparisons = case["equivalent_formats"]
            comparisons.extend((case, comparison) for comparison in case_comparisons)
        except (KeyError, TypeError) as error:
            errors.append(f"{key}: malformed case result ({error})")

    variants_per_case = document.get("scope", {}).get("pglib_variants_per_case")
    for case in pglib:
        variants = case.get("equivalent_formats", [])
        if len(variants) != variants_per_case:
            errors.append(f"{case['key']}: incomplete PGLib variant coverage")
        for variant in variants:
            if not variant.get("parsed") or not variant.get("matches_primary_topology"):
                errors.append(f"{case['key']}: PGLib variant mismatch at {variant.get('path')}")
            if "proposition3" not in variant:
                errors.append(f"{case['key']}: variant lacks right hand side analysis")

    if publication:
        policy = policy or load_policy()
        errors.extend(
            _publication_errors(
                document,
                policy,
                verify_policy_files=verify_policy_files,
            )
        )
    if errors:
        raise ValueError("\n".join(dict.fromkeys(errors)))

    spectra = Counter(case["spectrum"]["status"] for case in cases)
    non_pglib_comparisons = [
        comparison
        for case, comparison in comparisons
        if not case["key"].startswith("pglib_opf_case")
    ]
    computed = [case for case in cases if case["spectrum"]["status"] == "computed"]
    operating_points = [
        case["proposition3"]
        for case in cases
        if case.get("proposition3", {}).get("status") == "computed"
    ]
    pglib_operating_points = [
        case["proposition3"]
        for case in pglib
        if case.get("proposition3", {}).get("status") == "computed"
    ]
    generator_points = [
        point["generator_redispatch"]
        for point in operating_points
        if point["generator_redispatch"]["status"] == "computed"
    ]
    generator_load_points = [
        point["generator_load_redispatch"]
        for point in operating_points
        if point["generator_load_redispatch"]["status"] == "computed"
    ]
    bound_ratios = [
        case["spectrum"]["pseudo_condition_number"]
        / case["conditioning"]["weighted_cut_lower_bound"]
        for case in computed
    ]
    completed_near = [
        case
        for case in cases
        if case.get("near_planar") is not None
        and case["near_planar"].get("status") != "inapplicable-size"
        and case["near_planar"].get("status") != "unavailable"
    ]
    required_near = [
        case for case in cases if case["graph"]["largest_component_buses"] >= 1152
    ]
    pglib_keys = {case["key"] for case in pglib}
    pglib_completed_near = [
        case for case in completed_near if case["key"] in pglib_keys
    ]
    pglib_required_near = [
        case for case in required_near if case["key"] in pglib_keys
    ]
    return {
        "cases": len(cases),
        "pglib_canonical": len(pglib),
        "pglib_variant_files": sum(len(case["equivalent_formats"]) for case in pglib),
        "planar": sum(case["planar"] for case in cases),
        "pglib_planar": sum(case["planar"] for case in pglib),
        "separator_condition_holds": sum(case["separator"]["holds"] for case in cases),
        "pglib_separator_condition_holds": sum(
            case["separator"]["holds"] for case in pglib
        ),
        "treewidth_tested": sum(case["treewidth"] is not None for case in cases),
        "treewidth_condition_holds": sum(
            case["treewidth"] is not None and case["treewidth"]["holds"] for case in cases
        ),
        "pglib_treewidth_tested": sum(
            case["treewidth"] is not None for case in pglib
        ),
        "pglib_treewidth_condition_holds": sum(
            case["treewidth"] is not None and case["treewidth"]["holds"]
            for case in pglib
        ),
        "near_planar_required": len(required_near),
        "near_planar_tested": len(completed_near),
        "near_planar_condition_holds": sum(
            case["near_planar"]["holds"] for case in completed_near
        ),
        "pglib_near_planar_required": len(pglib_required_near),
        "pglib_near_planar_tested": len(pglib_completed_near),
        "pglib_near_planar_condition_holds": sum(
            case["near_planar"]["holds"] for case in pglib_completed_near
        ),
        "geographic_drawings_used": sum(
            case.get("near_planar") is not None
            and case["near_planar"].get("drawing_source") == "case-geography"
            for case in cases
        ),
        "weight_model_usable": sum(case["conditioning"]["usable"] for case in cases),
        "pglib_weight_model_usable": sum(
            case["conditioning"]["usable"] for case in pglib
        ),
        "spectra": dict(sorted(spectra.items())),
        "largest_spectral_condition_estimate": max(
            (case["spectrum"]["pseudo_condition_number"] for case in computed),
            default=None,
        ),
        "median_spectral_to_cut_bound_ratio": np_median(bound_ratios),
        "non_pglib_format_comparisons": len(non_pglib_comparisons),
        "non_pglib_format_mismatches": sum(
            not comparison["parsed"] or not comparison["matches_primary_topology"]
            for comparison in non_pglib_comparisons
        ),
        "base_rhs_tested": len(operating_points),
        "base_rhs_primary_pass": sum(
            point["base_rhs"].get("primary_condition") == "pass"
            for point in operating_points
        ),
        "pglib_base_rhs_tested": len(pglib_operating_points),
        "pglib_base_rhs_pass": sum(
            point["base_rhs"].get("primary_condition") == "pass"
            for point in pglib_operating_points
        ),
        "generator_subspace_tested": len(generator_points),
        "generator_subspace_pass": sum(
            point.get("condition") == "pass" for point in generator_points
        ),
        "generator_load_subspace_tested": len(generator_load_points),
        "generator_load_subspace_pass": sum(
            point.get("condition") == "pass" for point in generator_load_points
        ),
    }


def validate_core(
    document: dict,
    policy: PublicationPolicy,
    *,
    verify_policy_files: bool = True,
) -> None:
    """Check the five case input used by the deterministic core table."""
    errors = []
    if document.get("schema_version") != 1:
        errors.append("expected core schema version 1")
    cases = document.get("cases", [])
    keys = [case.get("key") for case in cases]
    if keys != list(policy.core_keys):
        errors.append("core case coverage differs from publication policy")
    if len(keys) != len(set(keys)):
        errors.append("duplicate core case keys")
    errors.extend(environment_errors(document.get("environment", {}), policy))
    if document.get("provenance") != dict(policy.provenance):
        errors.append("core provenance does not match publication policy")
    if document.get("publication_policy_sha256") != policy.source_sha256:
        errors.append("core publication policy hash does not match")
    if document.get("parameters") != dict(policy.algorithms):
        errors.append("core algorithm parameters do not match publication policy")
    if verify_policy_files:
        errors.extend(provenance_errors(policy))
    for location, field, value in _walk(document):
        if field in FORBIDDEN_PUBLICATION_FIELDS:
            errors.append(f"{location}: nondeterministic field is not permitted")
        if field in PATH_FIELDS and isinstance(value, str) and _is_absolute_path(value):
            errors.append(f"{location}: absolute path is not permitted")
        elif isinstance(value, str) and _contains_absolute_path(value):
            errors.append(f"{location}: absolute path fragment is not permitted")
    for case in cases:
        key = case.get("key", "<missing-key>")
        if SHA256_PATTERN.fullmatch(str(case.get("source_sha256", ""))) is None:
            errors.append(f"{key}: missing or invalid source SHA-256")
        if case.get("treewidth") is None or case.get("near_planar") is None:
            errors.append(f"{key}: missing structural analysis")
        if not isinstance(case.get("graph", {}).get("excluded_buses"), int):
            errors.append(f"{key}: missing excluded bus count")
    if errors:
        raise ValueError("\n".join(dict.fromkeys(errors)))


def np_median(values: list[float]) -> float | None:
    if not values:
        return None
    ordered = sorted(values)
    middle = len(ordered) // 2
    if len(ordered) % 2:
        return ordered[middle]
    return math.fsum(ordered[middle - 1 : middle + 1]) / 2


def render_summary(summary: dict) -> bytes:
    return (json.dumps(summary, indent=2, sort_keys=True, allow_nan=False) + "\n").encode()


def render_summary_table(summary: dict) -> bytes:
    rows = [
        ("Primary cases", summary["cases"], summary["cases"]),
        ("PGLib variants", summary["pglib_variant_files"], summary["pglib_variant_files"]),
        ("Planar", summary["planar"], summary["cases"]),
        ("PGLib planar", summary["pglib_planar"], summary["pglib_canonical"]),
        ("Separator certificate", summary["separator_condition_holds"], summary["cases"]),
        (
            "PGLib separator certificate",
            summary["pglib_separator_condition_holds"],
            summary["pglib_canonical"],
        ),
        (
            "Treewidth certificate",
            summary["treewidth_condition_holds"],
            summary["treewidth_tested"],
        ),
        (
            "PGLib treewidth certificate",
            summary["pglib_treewidth_condition_holds"],
            summary["pglib_treewidth_tested"],
        ),
        (
            "Near planar certificate",
            summary["near_planar_condition_holds"],
            summary["near_planar_tested"],
        ),
        (
            "PGLib near planar certificate",
            summary["pglib_near_planar_condition_holds"],
            summary["pglib_near_planar_tested"],
        ),
        ("Positive weight model", summary["weight_model_usable"], summary["cases"]),
        (
            "PGLib positive weight model",
            summary["pglib_weight_model_usable"],
            summary["pglib_canonical"],
        ),
        ("Base injection diagnostic", summary["base_rhs_primary_pass"], summary["base_rhs_tested"]),
        (
            "PGLib base injection diagnostic",
            summary["pglib_base_rhs_pass"],
            summary["pglib_base_rhs_tested"],
        ),
        (
            "Generator diagnostic",
            summary["generator_subspace_pass"],
            summary["generator_subspace_tested"],
        ),
        (
            "Generator and load diagnostic",
            summary["generator_load_subspace_pass"],
            summary["generator_load_subspace_tested"],
        ),
    ]
    lines = [
        r"\begin{tabular}{lrr}",
        r"\hline",
        r"Analysis & Holds & Tested \\",
        r"\hline",
        *(f"{label} & {holds} & {tested} \\\\" for label, holds, tested in rows),
        r"\hline",
        r"\end{tabular}",
        "",
    ]
    return "\n".join(lines).encode("ascii")


def canonical_artifact(document: dict) -> bytes:
    return (
        json.dumps(
            document,
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=True,
            allow_nan=False,
        )
        + "\n"
    ).encode()


def deterministic_gzip(payload: bytes) -> bytes:
    output = io.BytesIO()
    with gzip.GzipFile(
        filename="",
        mode="wb",
        compresslevel=9,
        fileobj=output,
        mtime=0,
    ) as stream:
        stream.write(payload)
    return output.getvalue()


def sha256_manifest(payload: bytes, filename: str) -> bytes:
    return f"{hashlib.sha256(payload).hexdigest()}  {filename}\n".encode("ascii")


def _write_or_check(path: Path, expected: bytes, check: bool) -> None:
    if check:
        if not path.is_file():
            raise ValueError(f"missing derived publication file: {path}")
        if path.read_bytes() != expected:
            raise ValueError(f"derived publication file drift: {path}")
        return
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(expected)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("--summary-output", type=Path)
    parser.add_argument("--table-output", type=Path)
    parser.add_argument("--compressed-output", type=Path)
    parser.add_argument("--sha256-output", type=Path)
    parser.add_argument("--core-input", type=Path)
    parser.add_argument("--publication", action="store_true")
    parser.add_argument("--publication-policy", type=Path, default=DEFAULT_POLICY_PATH)
    parser.add_argument("--check-derived", action="store_true")
    args = parser.parse_args()

    policy = load_policy(args.publication_policy)
    if args.publication and args.core_input is None:
        parser.error("--publication requires --core-input")
    document = json.loads(args.input.read_text())
    summary = validate(document, publication=args.publication, policy=policy)
    if args.core_input is not None:
        validate_core(json.loads(args.core_input.read_text()), policy)

    rendered_summary = render_summary(summary)
    rendered_table = render_summary_table(summary)
    compressed = deterministic_gzip(canonical_artifact(document))
    compressed_path = args.compressed_output
    artifacts = (
        (args.summary_output, rendered_summary),
        (args.table_output, rendered_table),
        (compressed_path, compressed),
        (
            args.sha256_output,
            sha256_manifest(
                compressed,
                compressed_path.name if compressed_path is not None else "corpus-survey.json.gz",
            ),
        ),
    )
    for path, content in artifacts:
        if path is not None:
            _write_or_check(path, content, args.check_derived)
    print(rendered_summary.decode(), end="")


if __name__ == "__main__":
    main()
