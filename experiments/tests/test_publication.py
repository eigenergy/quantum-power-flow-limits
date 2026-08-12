from __future__ import annotations

from copy import deepcopy
import json
from pathlib import Path

from publication_policy import (
    environment_errors,
    load_policy,
    provenance_errors,
)


EXPERIMENT_DIR = Path(__file__).resolve().parents[1]


def test_policy_names_only_the_five_manuscript_cases() -> None:
    policy = load_policy()
    assert policy.core_keys == (
        "texas7k",
        "pegase13k",
        "midwest24k",
        "goc30k",
        "epigrids78k",
    )
    assert policy.outputs == {
        "core_json": "results.json",
        "core_table": "conditions_table.tex",
    }


def test_pinned_repository_inputs_match_policy() -> None:
    assert provenance_errors(load_policy()) == []


def test_retained_result_matches_policy() -> None:
    policy = load_policy()
    result = json.loads((EXPERIMENT_DIR / "results.json").read_text())
    assert tuple(case["key"] for case in result["cases"]) == policy.core_keys
    assert result["publication_policy_sha256"] == policy.source_sha256
    assert result["provenance"] == policy.provenance
    assert result["parameters"] == policy.algorithms


def test_retained_result_has_only_core_scope() -> None:
    result = json.loads((EXPERIMENT_DIR / "results.json").read_text())
    assert set(result) == {
        "schema_version",
        "criteria",
        "parameters",
        "environment",
        "publication_policy_sha256",
        "provenance",
        "cases",
    }
    assert len(result["cases"]) == 5


def test_environment_contract_accepts_retained_result() -> None:
    policy = load_policy()
    result = json.loads((EXPERIMENT_DIR / "results.json").read_text())
    assert environment_errors(result["environment"], policy) == []


def test_environment_contract_rejects_version_drift() -> None:
    policy = load_policy()
    result = json.loads((EXPERIMENT_DIR / "results.json").read_text())
    environment = deepcopy(result["environment"])
    environment["scipy"] = "0.0.0"
    assert environment_errors(environment, policy) == [
        "scipy version drift: expected 1.18.0, got 0.0.0"
    ]


def test_environment_contract_rejects_dirty_powerio() -> None:
    policy = load_policy()
    result = json.loads((EXPERIMENT_DIR / "results.json").read_text())
    environment = deepcopy(result["environment"])
    environment["powerio_tracked_dirty"] = True
    assert "PowerIO source must have no tracked modifications" in environment_errors(
        environment, policy
    )


def test_table_declares_manuscript_column_layout() -> None:
    table = (EXPERIMENT_DIR / "conditions_table.tex").read_text()
    assert r"\begin{tabular}{lcccrr}" in table
    assert r"\begin{tabular}{lcccrrr}" not in table
    assert r"\begin{tabular}{lrrrrrr}" not in table
    assert r"$\hat c$: certified proper crossing count" in table
    assert r"Near Plan.: $1152(n+\hat c)\leq n^2$" in table
    assert r"Sep.: $\beta\geq1/4$ and $s^2\leq8n$" in table
    assert r"treewidth: $4(U+1)\leq n$" in table
    assert r"$\times$ means the positive weight model fails" in table
