#!/usr/bin/env python3
"""Validate the retained PGLib evidence and render the manuscript table."""

from __future__ import annotations

import argparse
import gzip
import hashlib
import json
from pathlib import Path
import re
from typing import Any

from publication_policy import environment_errors, load_policy


EXPERIMENT_DIR = Path(__file__).resolve().parent
DEFAULT_INPUT = EXPERIMENT_DIR / "results" / "pglib-structural.json"
DEFAULT_TABLE = EXPERIMENT_DIR / "results" / "pglib-corpus-summary.tex"
SHA256_PATTERN = re.compile(r"[0-9a-f]{64}")
SOURCE_SNAPSHOT_SHA256 = "8b720c757d0d3c6ee0399c01cf8e43eb711b8d1f13874fa7af2adbcf538fe03a"
PGLIB_KEYS = (
    "pglib_opf_case10000_goc",
    "pglib_opf_case10192_epigrids",
    "pglib_opf_case10480_goc",
    "pglib_opf_case118_ieee",
    "pglib_opf_case1354_pegase",
    "pglib_opf_case13659_pegase",
    "pglib_opf_case14_ieee",
    "pglib_opf_case162_ieee_dtc",
    "pglib_opf_case179_goc",
    "pglib_opf_case1803_snem",
    "pglib_opf_case1888_rte",
    "pglib_opf_case19402_goc",
    "pglib_opf_case1951_rte",
    "pglib_opf_case197_snem",
    "pglib_opf_case2000_goc",
    "pglib_opf_case200_activ",
    "pglib_opf_case20758_epigrids",
    "pglib_opf_case2312_goc",
    "pglib_opf_case2383wp_k",
    "pglib_opf_case240_pserc",
    "pglib_opf_case24464_goc",
    "pglib_opf_case24_ieee_rts",
    "pglib_opf_case2736sp_k",
    "pglib_opf_case2737sop_k",
    "pglib_opf_case2742_goc",
    "pglib_opf_case2746wop_k",
    "pglib_opf_case2746wp_k",
    "pglib_opf_case2848_rte",
    "pglib_opf_case2853_sdet",
    "pglib_opf_case2868_rte",
    "pglib_opf_case2869_pegase",
    "pglib_opf_case30000_goc",
    "pglib_opf_case300_ieee",
    "pglib_opf_case3012wp_k",
    "pglib_opf_case3022_goc",
    "pglib_opf_case30_as",
    "pglib_opf_case30_ieee",
    "pglib_opf_case3120sp_k",
    "pglib_opf_case3375wp_k",
    "pglib_opf_case3970_goc",
    "pglib_opf_case39_epri",
    "pglib_opf_case3_lmbd",
    "pglib_opf_case4020_goc",
    "pglib_opf_case4601_goc",
    "pglib_opf_case4619_goc",
    "pglib_opf_case4661_sdet",
    "pglib_opf_case4837_goc",
    "pglib_opf_case4917_goc",
    "pglib_opf_case500_goc",
    "pglib_opf_case5658_epigrids",
    "pglib_opf_case57_ieee",
    "pglib_opf_case588_sdet",
    "pglib_opf_case5_pjm",
    "pglib_opf_case60_c",
    "pglib_opf_case6468_rte",
    "pglib_opf_case6470_rte",
    "pglib_opf_case6495_rte",
    "pglib_opf_case6515_rte",
    "pglib_opf_case7336_epigrids",
    "pglib_opf_case73_ieee_rts",
    "pglib_opf_case78484_epigrids",
    "pglib_opf_case793_goc",
    "pglib_opf_case8387_pegase",
    "pglib_opf_case89_pegase",
    "pglib_opf_case9241_pegase",
    "pglib_opf_case9591_goc",
)

EXPECTED_SUMMARY = {
    "cases": 66,
    "balanced_separator": 66,
    "direct_metis_separator": 61,
    "treewidth": 64,
    "near_planar": 39,
    "near_planar_tested": 45,
    "planar": 9,
    "positive_weight_model": 46,
    "positive_direct_metis_separator": 46,
    "positive_direct_metis_separator_tested": 46,
    "base_operating_point": 35,
    "base_operating_point_tested": 36,
}


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load_json(path: Path) -> dict[str, Any]:
    if path.suffix == ".gz":
        stream = gzip.open(path, "rt", encoding="utf-8")
    else:
        stream = path.open("rt", encoding="utf-8")
    with stream:
        return json.load(stream)


def canonical_json(document: dict[str, Any]) -> bytes:
    return (json.dumps(document, indent=2, sort_keys=True, allow_nan=False) + "\n").encode()


def direct_separator_holds(case: dict[str, Any]) -> bool:
    n = case["graph"]["largest_component_buses"]
    separator = case["separator"]
    return 4 * separator["beta_numerator"] >= n and separator["size"] ** 2 <= 8 * n


def treewidth_holds(case: dict[str, Any]) -> bool:
    n = case["graph"]["largest_component_buses"]
    return 4 * (case["treewidth"]["upper_bound"] + 1) <= n


def treewidth_separator_holds(case: dict[str, Any]) -> bool:
    n = case["graph"]["largest_component_buses"]
    width = case["treewidth"]["upper_bound"]
    return treewidth_holds(case) and (width + 1) ** 2 <= 8 * n


def balanced_separator_holds(case: dict[str, Any]) -> bool:
    return direct_separator_holds(case) or treewidth_separator_holds(case)


def near_planar_tested(case: dict[str, Any]) -> bool:
    return case["near_planar"]["status"] != "inapplicable-size"


def base_operating_point_tested(case: dict[str, Any]) -> bool:
    return case["base_operating_point"]["status"] == "computed"


def summarize(document: dict[str, Any]) -> dict[str, int]:
    cases = document["cases"]
    positive = [case for case in cases if case["positive_weight_model"]]
    tested_near = [case for case in cases if near_planar_tested(case)]
    tested_base = [case for case in cases if base_operating_point_tested(case)]
    return {
        "cases": len(cases),
        "balanced_separator": sum(balanced_separator_holds(case) for case in cases),
        "direct_metis_separator": sum(direct_separator_holds(case) for case in cases),
        "treewidth": sum(treewidth_holds(case) for case in cases),
        "near_planar": sum(case["near_planar"]["holds"] for case in tested_near),
        "near_planar_tested": len(tested_near),
        "planar": sum(case["planar"] for case in cases),
        "positive_weight_model": len(positive),
        "positive_direct_metis_separator": sum(
            direct_separator_holds(case) for case in positive
        ),
        "positive_direct_metis_separator_tested": len(positive),
        "base_operating_point": sum(
            case["base_operating_point"]["verdict"] == "pass" for case in tested_base
        ),
        "base_operating_point_tested": len(tested_base),
    }


def validate(document: dict[str, Any]) -> dict[str, int]:
    errors: list[str] = []
    if document.get("schema_version") != 1:
        errors.append("expected PGLib evidence schema version 1")
    if document.get("source_snapshot_sha256") != SOURCE_SNAPSHOT_SHA256:
        errors.append("unexpected source snapshot SHA-256")
    policy = load_policy()
    errors.extend(environment_errors(document.get("environment", {}), policy))
    if document.get("parameters") != dict(policy.algorithms):
        errors.append("PGLib algorithm parameters differ from the manuscript policy")
    cases = document.get("cases")
    if not isinstance(cases, list):
        raise ValueError("PGLib evidence cases must be a list")
    keys = tuple(case.get("key") for case in cases)
    if keys != PGLIB_KEYS:
        errors.append("PGLib case coverage or order differs from the canonical list")
    for case in cases:
        key = case.get("key", "<missing-key>")
        source_path = case.get("source_path")
        if not isinstance(source_path, str) or not source_path.startswith("pglib-opf/"):
            errors.append(f"{key}: invalid source path")
        source_hash = case.get("source_sha256")
        if not isinstance(source_hash, str) or SHA256_PATTERN.fullmatch(source_hash) is None:
            errors.append(f"{key}: invalid source SHA-256")
        graph = case.get("graph", {})
        n = graph.get("largest_component_buses")
        if not isinstance(n, int) or n < 2:
            errors.append(f"{key}: invalid retained bus count")
            continue
        separator = case.get("separator", {})
        if separator.get("beta_denominator") != n:
            errors.append(f"{key}: separator denominator differs from retained buses")
        if separator.get("holds") is not direct_separator_holds(case):
            errors.append(f"{key}: inconsistent direct separator verdict")
        if case.get("treewidth", {}).get("holds") is not treewidth_holds(case):
            errors.append(f"{key}: inconsistent treewidth verdict")
        near = case.get("near_planar", {})
        if n < 1152:
            if near.get("status") != "inapplicable-size" or near.get("holds") is not False:
                errors.append(f"{key}: invalid small-case near planar status")
        else:
            complete = near.get("complete") is True
            crossings = near.get("crossings")
            expected = bool(
                complete
                and isinstance(crossings, int)
                and 1152 * (n + crossings) <= n * n
            )
            if near.get("holds") is not expected:
                errors.append(f"{key}: inconsistent near planar verdict")
            expected_status = "certificate-found" if expected else "threshold-exceeded"
            if near.get("status") != expected_status:
                errors.append(f"{key}: inconsistent near planar status")
        base = case.get("base_operating_point", {})
        if base.get("status") == "computed":
            if base.get("verdict") not in {"pass", "fail", "indeterminate"}:
                errors.append(f"{key}: invalid base operating point verdict")
        elif base.get("status") != "not-tested":
            errors.append(f"{key}: invalid base operating point status")
    summary = summarize(document)
    if summary != EXPECTED_SUMMARY:
        errors.append(f"PGLib summary differs from the reviewed counts: {summary!r}")
    if errors:
        raise ValueError("\n".join(errors))
    return summary


def percent(holds: int, tested: int) -> str:
    return f"{100 * holds / tested:.1f}"


def render_table(summary: dict[str, int]) -> bytes:
    return f"""\\begin{{table}}[!t]
  \\centering
  \\caption{{Structural certificates and operating point diagnostics for the
    66 canonical PGLib v23.07 cases.}}
  \\label{{tab:pglib-corpus-summary}}
  \\begin{{tabular}}{{@{{}}p{{0.55\\linewidth}}rr@{{}}}}
    \\toprule
    Check & Satisfies/tested & Percent \\\\
    \\midrule
    Balanced separator certificate\\textsuperscript{{a}}
      & ${summary['balanced_separator']}/{summary['cases']}$ & ${percent(summary['balanced_separator'], summary['cases'])}\\%$ \\\\
    Direct METIS separator certificate
      & ${summary['direct_metis_separator']}/{summary['cases']}$ & ${percent(summary['direct_metis_separator'], summary['cases'])}\\%$ \\\\
    Validated tree decomposition sufficient condition
      & ${summary['treewidth']}/{summary['cases']}$ & ${percent(summary['treewidth'], summary['cases'])}\\%$ \\\\
    Qualifying near planar drawing\\textsuperscript{{b}}
      & ${summary['near_planar']}/{summary['near_planar_tested']}$ & ${percent(summary['near_planar'], summary['near_planar_tested'])}\\%$ \\\\
    Exactly planar topology
      & ${summary['planar']}/{summary['cases']}$ & ${percent(summary['planar'], summary['cases'])}\\%$ \\\\
    Direct positive susceptance model applicable\\textsuperscript{{c}}
      & ${summary['positive_weight_model']}/{summary['cases']}$ & ${percent(summary['positive_weight_model'], summary['cases'])}\\%$ \\\\
    Direct METIS separator among positive model cases
      & ${summary['positive_direct_metis_separator']}/{summary['positive_direct_metis_separator_tested']}$ & ${percent(summary['positive_direct_metis_separator'], summary['positive_direct_metis_separator_tested'])}\\%$ \\\\
    Recorded base operating point diagnostic\\textsuperscript{{d}}
      & ${summary['base_operating_point']}/{summary['base_operating_point_tested']}$ & ${percent(summary['base_operating_point'], summary['base_operating_point_tested'])}\\%$ \\\\
    \\bottomrule
  \\end{{tabular}}

  \\vspace{{0.45em}}
  \\begin{{minipage}}{{0.92\\linewidth}}
    \\footnotesize
    \\textsuperscript{{a}}The balanced separator row accepts a direct METIS
    certificate or one implied by a validated tree decomposition.  In all 64
    decomposition cases counted here, $4(U+1)\\leq n$ and
    $(U+1)^2\\leq8n$; hence the treewidth separator theorem gives
    $\\beta\\geq1/4$ and $s\\leq U+1$.  Five cases pass only by this implication,
    while two small cases pass only by the direct certificate.

    \\smallskip
    \\textsuperscript{{b}}The near planar condition is applicable to the
    45 cases with at least 1,152 retained buses.  It requires a fully checked
    straight line drawing with crossing count $\\widehat c$ satisfying
    $1152(n+\\widehat c)\\leq n^2$.  The other 21 cases are below the minimum
    size at which this inequality can hold.  Failure of the tested drawing is
    not a proof that no qualifying drawing exists.

    \\smallskip
    \\textsuperscript{{c}}The direct model assigns $b_e=1/x_e$ to each active
    ordinary branch and requires every resulting edge weight to be finite and
    positive.  The conditional $46/46$ row shows that every case satisfying
    this weight model also has a direct METIS separator certificate.

    \\smallskip
    \\textsuperscript{{d}}The diagnostic was computed for the 36 PGLib cases with
    an applicable weight model and spectrum within the numerical size limit.
    A pass means
    $\\kappa_{{\\mathrm{{eff}}}}(0.01)/\\kappa\\geq 1/2$ for the recorded balanced base
    injection.  This is an operating point diagnostic, not a query lower bound.

    \\smallskip
    The certificate rows check finite sufficient conditions used by the
    structural theorems.  They support applicability to this corpus; they do
    not replace the theorem hypotheses or establish an asymptotic growth law.
  \\end{{minipage}}
\\end{{table}}
""".encode("ascii")


def project_survey(document: dict[str, Any], source_hash: str) -> dict[str, Any]:
    if source_hash != SOURCE_SNAPSHOT_SHA256:
        raise ValueError("survey snapshot differs from the reviewed source")
    by_key = {case["key"]: case for case in document["cases"]}
    cases = []
    for key in PGLIB_KEYS:
        source = by_key[key]
        graph = source["graph"]
        separator = source["separator"]
        treewidth = source["treewidth"]
        near = source["near_planar"]
        proposition3 = source.get("proposition3", {})
        base = proposition3.get("base_rhs", {})
        base_status = "computed" if base.get("status") == "computed" else "not-tested"
        cases.append(
            {
                "key": key,
                "source_path": source["source_path"],
                "source_sha256": source["source_sha256"],
                "graph": {
                    field: graph[field]
                    for field in (
                        "parsed_buses",
                        "active_branches",
                        "simple_edges",
                        "components",
                        "largest_component_buses",
                        "excluded_buses",
                        "bus_order_hash",
                    )
                },
                "planar": source["planar"],
                "separator": {
                    "beta_numerator": separator["beta_numerator"],
                    "beta_denominator": separator["beta_denominator"],
                    "size": separator["s"],
                    "holds": separator["holds"],
                    "partition_hash": separator["partition_hash"],
                },
                "treewidth": {
                    "upper_bound": treewidth["upper_bound"],
                    "holds": treewidth["holds"],
                    "ordering_hash": treewidth["ordering_hash"],
                    "decomposition_hash": treewidth["decomposition_hash"],
                },
                "near_planar": {
                    field: near.get(field)
                    for field in (
                        "status",
                        "complete",
                        "crossings",
                        "crossings_at_least",
                        "crossing_limit",
                        "holds",
                        "drawing_source",
                        "drawing_tool_version",
                        "position_hash",
                    )
                },
                "positive_weight_model": source["conditioning"]["usable"],
                "base_operating_point": {
                    "status": base_status,
                    "verdict": base.get("primary_condition") if base_status == "computed" else None,
                },
            }
        )
    return {
        "schema_version": 1,
        "source_snapshot_sha256": source_hash,
        "environment": document["environment"],
        "parameters": document["parameters"],
        "cases": cases,
    }


def write_or_check(path: Path, expected: bytes, check: bool) -> None:
    if check:
        if not path.is_file() or path.read_bytes() != expected:
            raise ValueError(f"derived file is stale: {path}")
        return
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(expected)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, default=DEFAULT_INPUT)
    parser.add_argument("--table-output", type=Path, default=DEFAULT_TABLE)
    parser.add_argument("--import-survey", type=Path)
    parser.add_argument("--check-derived", action="store_true")
    args = parser.parse_args()
    if args.import_survey is not None:
        source_hash = sha256_file(args.import_survey)
        document = project_survey(load_json(args.import_survey), source_hash)
        validate(document)
        write_or_check(args.input, canonical_json(document), args.check_derived)
    else:
        document = load_json(args.input)
    summary = validate(document)
    write_or_check(args.table_output, render_table(summary), args.check_derived)
    print(json.dumps(summary, sort_keys=True))


if __name__ == "__main__":
    main()
