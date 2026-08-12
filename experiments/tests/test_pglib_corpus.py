from __future__ import annotations

import json
from pathlib import Path

from pglib_corpus import (
    EXPECTED_SUMMARY,
    PGLIB_KEYS,
    balanced_separator_holds,
    render_table,
    summarize,
    validate,
)


EXPERIMENT_DIR = Path(__file__).resolve().parents[1]


def load_retained() -> dict:
    return json.loads(
        (EXPERIMENT_DIR / "results" / "pglib-structural.json").read_text()
    )


def test_retained_pglib_evidence_is_valid() -> None:
    assert validate(load_retained()) == EXPECTED_SUMMARY


def test_retained_pglib_case_coverage_is_exact() -> None:
    document = load_retained()
    assert tuple(case["key"] for case in document["cases"]) == PGLIB_KEYS


def test_generated_pglib_table_is_current() -> None:
    document = load_retained()
    expected = render_table(summarize(document))
    actual = (EXPERIMENT_DIR / "results" / "pglib-corpus-summary.tex").read_bytes()
    assert actual == expected


def test_treewidth_supplies_the_five_direct_separator_misses() -> None:
    document = load_retained()
    misses = [case for case in document["cases"] if not case["separator"]["holds"]]
    assert [case["key"] for case in misses] == [
        "pglib_opf_case1888_rte",
        "pglib_opf_case1951_rte",
        "pglib_opf_case2848_rte",
        "pglib_opf_case2868_rte",
        "pglib_opf_case3375wp_k",
    ]
    assert all(balanced_separator_holds(case) for case in misses)


def test_two_small_cases_pass_only_by_direct_separator() -> None:
    document = load_retained()
    by_key = {case["key"]: case for case in document["cases"]}
    for key in ("pglib_opf_case3_lmbd", "pglib_opf_case5_pjm"):
        case = by_key[key]
        assert case["separator"]["holds"]
        assert not case["treewidth"]["holds"]


def test_every_positive_model_case_has_a_direct_separator() -> None:
    document = load_retained()
    positive = [case for case in document["cases"] if case["positive_weight_model"]]
    assert len(positive) == 46
    assert all(case["separator"]["holds"] for case in positive)
