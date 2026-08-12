from __future__ import annotations

from copy import deepcopy
from dataclasses import replace
import gzip
import hashlib
import json
from pathlib import Path

import pytest

from publication_policy import environment_errors, load_policy, provenance_errors
from validate_survey import (
    canonical_artifact,
    deterministic_gzip,
    render_summary,
    render_summary_table,
    sha256_manifest,
    validate,
)


EXPERIMENT_DIR = Path(__file__).resolve().parents[1]
RETAINED_GENERATION_POLICY = (
    EXPERIMENT_DIR / "results" / "corpus-generation-policy.toml"
)
RETAINED_CORPUS = EXPERIMENT_DIR / "results" / "corpus-survey.json.gz"


def relative_source(key: str) -> str:
    return f"corpus/{key}.m"


def small_case(key: str, variants: int) -> dict:
    return {
        "key": key,
        "label": key,
        "source_path": relative_source(key),
        "source_sha256": hashlib.sha256(key.encode()).hexdigest(),
        "graph": {
            "largest_component_buses": 100,
            "excluded_buses": 0,
        },
        "topology_sha256": hashlib.sha256(f"topology:{key}".encode()).hexdigest(),
        "planar": False,
        "separator": {
            "beta_numerator": 25,
            "beta_denominator": 100,
            "s": 1,
            "holds": True,
        },
        "treewidth": {"upper_bound": 1, "holds": True},
        "near_planar": {
            "status": "inapplicable-size",
            "minimum_buses": 1152,
            "holds": False,
        },
        "conditioning": {"usable": False},
        "spectrum": {"status": "skipped-weight-model"},
        "proposition3": {
            "status": "unavailable",
            "reason": "positive weight model does not apply",
        },
        "equivalent_formats": [
            {
                "path": f"pglib-opf/{folder}/{key}__{suffix}.m",
                "parsed": True,
                "matches_primary_topology": True,
                "proposition3": {
                    "status": "unavailable",
                    "reason": "positive weight model does not apply",
                },
            }
            for folder, suffix in (("api", "api"), ("sad", "sad"))[:variants]
        ],
        "display_files": [],
    }


@pytest.fixture
def policy():
    return load_policy()


@pytest.fixture
def publication_document(policy) -> dict:
    cases = [
        small_case(key, policy.pglib_variants_per_case)
        for key in policy.pglib_keys
    ] + [small_case(key, 0) for key in policy.extra_keys]
    return {
        "schema_version": 2,
        "environment": {
            "python": policy.versions["python"],
            "uv": policy.versions["uv"],
            "julia": policy.versions["julia"],
            "graphviz": policy.versions["graphviz"],
            "powerio_version": policy.versions["powerio"],
            "powerio_commit": policy.versions["powerio_commit"],
            "powerio_tracked_dirty": False,
            "powerio_dirty": False,
            "networkx": policy.versions["networkx"],
            "numpy": policy.versions["numpy"],
            "pymetis": policy.versions["pymetis"],
            "scipy": policy.versions["scipy"],
            "shapely": policy.versions["shapely"],
        },
        "parameters": dict(policy.algorithms),
        "publication_policy_sha256": policy.source_sha256,
        "provenance": dict(policy.provenance),
        "scope": {
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
        },
        "cases": cases,
        "controlled_corridors": [{} for _ in range(9)],
        "failures": [],
    }


def validate_publication(document: dict, policy) -> dict:
    return validate(
        document,
        publication=True,
        policy=policy,
        verify_policy_files=False,
    )


def make_large_graphviz_result(case: dict, version: str = "15.1.0") -> None:
    n = 1152
    positions = [[index, index * index + 1] for index in range(n)]
    position_hash = hashlib.sha256(
        "\n".join(f"{x},{y}" for x, y in positions).encode()
    ).hexdigest()
    case["graph"]["largest_component_buses"] = n
    case["separator"].update(
        {"beta_numerator": n // 4, "beta_denominator": n, "s": 1}
    )
    case["near_planar"] = {
        "status": "certificate-found",
        "complete": True,
        "crossings": 0,
        "crossings_at_least": 0,
        "crossing_limit": 0,
        "drawing_source": "graphviz-sfdp",
        "drawing_tool_version": version,
        "positions": positions,
        "position_hash": position_hash,
        "holds": True,
    }


def test_complete_publication_fixture_passes(publication_document, policy) -> None:
    summary = validate_publication(publication_document, policy)
    assert summary["cases"] == 78
    assert summary["pglib_variant_files"] == 132
    assert summary["treewidth_tested"] == 78
    assert summary["pglib_treewidth_tested"] == 66
    assert summary["pglib_separator_condition_holds"] == 66
    assert summary["pglib_weight_model_usable"] == 0
    assert summary["pglib_base_rhs_tested"] == 0


@pytest.mark.parametrize("field", ["treewidth_enabled", "near_planarity_enabled"])
def test_publication_rejects_disabled_analysis(
    publication_document, policy, field: str
) -> None:
    publication_document["scope"][field] = False
    with pytest.raises(ValueError, match=field):
        validate_publication(publication_document, policy)


def test_publication_rejects_missing_case(publication_document, policy) -> None:
    publication_document["cases"].pop()
    with pytest.raises(ValueError, match="missing primary cases"):
        validate_publication(publication_document, policy)


def test_publication_rejects_duplicate_case(publication_document, policy) -> None:
    publication_document["cases"][-1] = deepcopy(publication_document["cases"][0])
    with pytest.raises(ValueError, match="duplicate primary case keys"):
        validate_publication(publication_document, policy)


def test_publication_rejects_null_treewidth(publication_document, policy) -> None:
    publication_document["cases"][0]["treewidth"] = None
    with pytest.raises(ValueError, match="treewidth analysis is null"):
        validate_publication(publication_document, policy)


def test_publication_rejects_null_required_near_planarity(
    publication_document, policy
) -> None:
    case = publication_document["cases"][0]
    make_large_graphviz_result(case)
    case["near_planar"] = None
    with pytest.raises(ValueError, match="near planarity analysis is null"):
        validate_publication(publication_document, policy)


def test_publication_rejects_unavailable_required_near_planarity(
    publication_document, policy
) -> None:
    case = publication_document["cases"][0]
    make_large_graphviz_result(case)
    case["near_planar"] = {
        "status": "unavailable",
        "holds": False,
        "reason": "drawing failed",
    }
    with pytest.raises(ValueError, match="required near planarity test is incomplete"):
        validate_publication(publication_document, policy)


@pytest.mark.parametrize(
    ("path", "value"),
    [
        (("cases", 0, "source_path"), "/private/data/case.m"),
        (("cases", 0, "equivalent_formats", 0, "path"), "C:\\data\\case.m"),
    ],
)
def test_publication_rejects_absolute_paths(
    publication_document, policy, path: tuple, value: str
) -> None:
    target = publication_document
    for part in path[:-1]:
        target = target[part]
    target[path[-1]] = value
    with pytest.raises(ValueError, match="absolute path"):
        validate_publication(publication_document, policy)


def test_publication_rejects_absolute_path_in_error_text(
    publication_document, policy
) -> None:
    publication_document["cases"][0]["display_files"] = [
        {
            "path": "display/case.pwd",
            "parsed": False,
            "error": "failed to read /Users/example/private/case.pwd",
        }
    ]
    with pytest.raises(ValueError, match="absolute path fragment"):
        validate_publication(publication_document, policy)


@pytest.mark.parametrize("field", ["wall_seconds", "generated_at", "timestamp"])
def test_publication_rejects_timing_and_timestamp_fields(
    publication_document, policy, field: str
) -> None:
    publication_document["cases"][0][field] = 1
    with pytest.raises(ValueError, match="nondeterministic field"):
        validate_publication(publication_document, policy)


def test_publication_rejects_graphviz_drift(publication_document, policy) -> None:
    case = publication_document["cases"][0]
    make_large_graphviz_result(case, version="15.1.1")
    with pytest.raises(ValueError, match="drawing Graphviz version drift"):
        validate_publication(publication_document, policy)


def test_publication_rejects_environment_version_drift(
    publication_document, policy
) -> None:
    publication_document["environment"]["scipy"] = "1.17.0"
    with pytest.raises(ValueError, match="scipy version drift"):
        validate_publication(publication_document, policy)


def test_publication_rejects_dirty_powerio(publication_document, policy) -> None:
    publication_document["environment"]["powerio_tracked_dirty"] = True
    with pytest.raises(ValueError, match="tracked modifications"):
        validate_publication(publication_document, policy)


def test_publication_rejects_provenance_drift(publication_document, policy) -> None:
    publication_document["provenance"]["uv.lock"] = "0" * 64
    with pytest.raises(ValueError, match="artifact provenance"):
        validate_publication(publication_document, policy)


def test_publication_rejects_separator_denominator(
    publication_document, policy
) -> None:
    publication_document["cases"][0]["separator"]["beta_denominator"] = 99
    with pytest.raises(ValueError, match="separator denominator"):
        validate_publication(publication_document, policy)


def test_deterministic_gzip_and_sha(publication_document, policy) -> None:
    summary = validate_publication(publication_document, policy)
    canonical = canonical_artifact(publication_document)
    first = deterministic_gzip(canonical)
    second = deterministic_gzip(canonical)
    assert first == second
    assert gzip.decompress(first) == canonical
    manifest = sha256_manifest(first, "survey.json.gz")
    assert manifest == (
        f"{hashlib.sha256(first).hexdigest()}  survey.json.gz\n".encode()
    )
    assert render_summary(summary) == render_summary(summary)
    assert render_summary_table(summary) == render_summary_table(summary)


def test_summary_table_has_three_columns(publication_document, policy) -> None:
    summary = validate_publication(publication_document, policy)
    table = render_summary_table(summary).decode()
    assert r"\begin{tabular}{lrr}" in table
    assert "Primary cases & 78 & 78" in table


def test_pinned_repository_inputs_match_policy() -> None:
    assert provenance_errors(load_policy()) == []


def test_retained_corpus_generation_policy_is_pinned(policy) -> None:
    generation_policy = load_policy(RETAINED_GENERATION_POLICY)
    assert policy.retained_generation_policy_sha256 == (
        generation_policy.source_sha256
    )


def test_unpinned_generation_policy_is_rejected(publication_document, policy) -> None:
    generation_policy = replace(policy, source_sha256="0" * 64)
    with pytest.raises(ValueError, match="generation policy is not pinned"):
        validate(
            publication_document,
            publication=True,
            policy=policy,
            verify_policy_files=False,
            generation_policy=generation_policy,
        )


def test_retained_corpus_passes_current_semantic_validation(policy) -> None:
    generation_policy = load_policy(RETAINED_GENERATION_POLICY)
    document = json.loads(gzip.decompress(RETAINED_CORPUS.read_bytes()))
    with pytest.raises(ValueError, match="artifact provenance"):
        validate(document, publication=True, policy=policy)
    summary = validate(
        document,
        publication=True,
        policy=policy,
        generation_policy=generation_policy,
    )
    assert summary["cases"] == 78
    assert summary["treewidth_tested"] == 78


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
