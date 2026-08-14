#!/usr/bin/env python3
"""Validate the trusted claim manifest, Lean surfaces, and Comparator config."""

from __future__ import annotations

import argparse
from collections import Counter
import json
from pathlib import Path
import re
import sys
import tomllib


ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "paper_claims.toml"
CONFIG = ROOT / "comparator.json"
CHALLENGE = ROOT / "Challenge.lean"
DEFINITIONS = ROOT / "Challenge" / "Definitions.lean"
SOLUTION = ROOT / "PowerFlowLimits" / "PaperClaims.lean"
WORKFLOW = ROOT / ".github" / "workflows" / "verification.yml"

ALLOWED_STATUSES = {
    "proved",
    "proved-relative-to-cited-result",
    "empirical",
    "discussion-not-formalized",
}
EXPECTED_AXIOMS = ["propext", "Quot.sound", "Classical.choice"]
THEOREM_RE = re.compile(r"^theorem\s+([A-Za-z][A-Za-z0-9_]*)\b", re.MULTILINE)
SORRY_RE = re.compile(r"\bsorry\b")
EXPECTED_ACTIONS = Counter(
    {
        "actions/checkout@3d3c42e5aac5ba805825da76410c181273ba90b1": 3,
        "leanprover/lean-action@38fbc41a8c28c4cbaec22d7f7de508ec2e7c0dd9": 1,
        "actions/setup-go@b7ad1dad31e06c5925ef5d2fc7ad053ef454303e": 1,
        "actions/setup-python@5fda3b95a4ea91299a34e894583c3862153e4b97": 2,
    }
)
EXPECTED_TOOL_PINS = {
    "landrun": "5ed4a3db3a4ad930d577215c6b9abaa19df7f99f",
    "lean4export": "d065b0009aed0520e9e99752847a33b337661690",
    "Comparator": "71b52ec29e06d4b7d882726553b1ceb99a2499e0",
    "nanoda": "68d5ca9db226849b41a6fff59d796ff19d0a8840",
}
EXPECTED_NONFORMAL_CLAIMS = [
    ("numerical_corpus_survey", "empirical"),
    ("near_planar_extension", "discussion-not-formalized"),
    ("full_ac_newton_systems", "discussion-not-formalized"),
    ("full_opf_kkt_ipm_systems", "discussion-not-formalized"),
    ("complexity_class_statements", "discussion-not-formalized"),
    ("unit_commitment", "discussion-not-formalized"),
    ("hybrid_algorithms", "discussion-not-formalized"),
]


class ValidationError(Exception):
    """A claim surface invariant failed."""


def fail(message: str) -> None:
    raise ValidationError(message)


def load_manifest() -> dict[str, object]:
    with MANIFEST.open("rb") as stream:
        return tomllib.load(stream)


def expected_config(manifest: dict[str, object], names: list[str]) -> dict[str, object]:
    return {
        "challenge_module": manifest["challenge_module"],
        "solution_module": manifest["solution_module"],
        "theorem_names": names,
        "permitted_axioms": manifest["permitted_axioms"],
        "enable_nanoda": manifest["enable_nanoda"],
    }


def validate_manifest(manifest: dict[str, object]) -> list[str]:
    required = {
        "schema_version",
        "challenge_module",
        "solution_module",
        "expected_claim_count",
        "expected_nonformal_claim_count",
        "permitted_axioms",
        "enable_nanoda",
        "claim",
        "nonformal_claim",
    }
    missing = sorted(required - manifest.keys())
    if missing:
        fail(f"manifest missing keys: {', '.join(missing)}")
    unexpected = sorted(manifest.keys() - required)
    if unexpected:
        fail(f"manifest has unexpected keys: {', '.join(unexpected)}")
    if manifest["schema_version"] != 1:
        fail("unsupported manifest schema_version")
    if manifest["challenge_module"] != "Challenge":
        fail("challenge_module must be Challenge")
    if manifest["solution_module"] != "PowerFlowLimits.PaperClaims":
        fail("solution_module must be PowerFlowLimits.PaperClaims")
    if manifest["permitted_axioms"] != EXPECTED_AXIOMS:
        fail("permitted_axioms differs from the three reviewed standard axioms")
    if manifest["enable_nanoda"] is not True:
        fail("enable_nanoda must be true")

    claims = manifest["claim"]
    if not isinstance(claims, list):
        fail("claim must be an array of tables")
    expected_count = manifest["expected_claim_count"]
    if not isinstance(expected_count, int) or expected_count != 17:
        fail("expected_claim_count must be 17")
    if len(claims) != expected_count:
        fail(f"manifest contains {len(claims)} claims; expected {expected_count}")

    names: list[str] = []
    for position, claim in enumerate(claims, start=1):
        if not isinstance(claim, dict):
            fail(f"claim {position} is not a table")
        required_claim_keys = {"name", "status", "summary", "external_dependencies"}
        missing_claim_keys = sorted(required_claim_keys - claim.keys())
        if missing_claim_keys:
            fail(f"claim {position} missing keys: {', '.join(missing_claim_keys)}")
        unexpected_claim_keys = sorted(
            claim.keys() - required_claim_keys - {"citation", "interface"}
        )
        if unexpected_claim_keys:
            fail(f"claim {position} has unexpected keys: {', '.join(unexpected_claim_keys)}")
        name = claim["name"]
        status = claim["status"]
        summary = claim["summary"]
        dependencies = claim["external_dependencies"]
        if not isinstance(name, str) or not name.startswith("PaperClaims."):
            fail(f"claim {position} has an invalid name")
        if not isinstance(status, str) or status not in ALLOWED_STATUSES:
            fail(f"{name} has an invalid status")
        if not isinstance(summary, str) or not summary.strip():
            fail(f"{name} has an empty summary")
        if not isinstance(dependencies, list) or not all(
            isinstance(item, str) and item.strip() for item in dependencies
        ):
            fail(f"{name} has invalid external_dependencies")
        if status == "proved" and dependencies:
            fail(f"{name} is marked proved but lists external dependencies")
        if status == "proved-relative-to-cited-result" and not dependencies:
            fail(f"{name} is relative to a cited result but lists no dependency")
        citation = claim.get("citation")
        interface = claim.get("interface")
        if status == "proved-relative-to-cited-result":
            if not isinstance(citation, str) or not citation.strip():
                fail(f"{name} does not record its literature citation")
            if not isinstance(interface, str) or not interface.strip():
                fail(f"{name} does not name its Lean premise interface")
            interfaces = [item.strip() for item in interface.split(";")]
            if not all(
                re.fullmatch(r"PaperClaims\.[A-Za-z][A-Za-z0-9_]*", item)
                for item in interfaces
            ):
                fail(f"{name} has an invalid Lean premise interface")
        elif citation is not None or interface is not None:
            fail(f"{name} records cited-result metadata but is not marked relative")
        names.append(name)

    duplicates = sorted({name for name in names if names.count(name) > 1})
    if duplicates:
        fail(f"duplicate claim names: {', '.join(duplicates)}")

    nonformal_claims = manifest["nonformal_claim"]
    expected_nonformal_count = manifest["expected_nonformal_claim_count"]
    if expected_nonformal_count != len(EXPECTED_NONFORMAL_CLAIMS):
        fail(
            "expected_nonformal_claim_count differs from the reviewed nonformal ledger"
        )
    if not isinstance(nonformal_claims, list):
        fail("nonformal_claim must be an array of tables")
    if len(nonformal_claims) != expected_nonformal_count:
        fail(
            f"manifest contains {len(nonformal_claims)} nonformal claims; "
            f"expected {expected_nonformal_count}"
        )
    observed_nonformal: list[tuple[str, str]] = []
    for position, claim in enumerate(nonformal_claims, start=1):
        if not isinstance(claim, dict):
            fail(f"nonformal claim {position} is not a table")
        if set(claim) != {"name", "status", "summary"}:
            fail(f"nonformal claim {position} has invalid metadata keys")
        name = claim["name"]
        status = claim["status"]
        summary = claim["summary"]
        if not isinstance(name, str) or not re.fullmatch(
            r"[a-z][a-z0-9_]*", name
        ):
            fail(f"nonformal claim {position} has an invalid name")
        if not isinstance(status, str) or status not in {
            "empirical",
            "discussion-not-formalized",
        }:
            fail(f"{name} has an invalid nonformal status")
        if not isinstance(summary, str) or not summary.strip():
            fail(f"{name} has an empty summary")
        observed_nonformal.append((name, status))
    if observed_nonformal != EXPECTED_NONFORMAL_CLAIMS:
        fail("nonformal claim names, statuses, or order have drifted")
    return names


def validate_sources(names: list[str]) -> None:
    challenge_source = CHALLENGE.read_text(encoding="utf-8")
    definitions_source = DEFINITIONS.read_text(encoding="utf-8")
    solution_source = SOLUTION.read_text(encoding="utf-8")

    imports = re.findall(r"^import\s+([^\s]+)\s*$", challenge_source, re.MULTILINE)
    if imports != ["Challenge.Definitions"]:
        fail("Challenge.lean must import only Challenge.Definitions")
    if re.search(r"^import\s+PowerFlowLimits(?:\.|\s|$)", definitions_source, re.MULTILINE):
        fail("Challenge.Definitions imports the solution")
    if re.search(r"^import\s+Challenge(?:\.|\s|$)", solution_source, re.MULTILINE):
        fail("the solution imports the trusted challenge")

    expected_local_names = [name.removeprefix("PaperClaims.") for name in names]
    challenge_theorems = THEOREM_RE.findall(challenge_source)
    solution_theorems = THEOREM_RE.findall(solution_source)
    if challenge_theorems != expected_local_names:
        fail("Challenge.lean theorem declarations differ from the manifest or its order")
    if solution_theorems != expected_local_names:
        fail("PaperClaims.lean theorem declarations differ from the manifest or its order")

    solution_statements: dict[str, str] = {}
    for local_name in expected_local_names:
        pattern = re.compile(
            rf"^theorem\s+{re.escape(local_name)}\b.*?:= by", re.MULTILINE | re.DOTALL
        )
        challenge_match = pattern.search(challenge_source)
        solution_match = pattern.search(solution_source)
        if challenge_match is None or solution_match is None:
            fail(f"could not extract the statement of PaperClaims.{local_name}")
        challenge_statement = " ".join(challenge_match.group().split())
        solution_statement = " ".join(solution_match.group().split())
        if challenge_statement != solution_statement:
            fail(f"PaperClaims.{local_name} differs between Challenge and solution source")
        solution_statements[local_name] = solution_statement

    sorry_count = len(SORRY_RE.findall(challenge_source))
    if sorry_count != len(names):
        fail(f"Challenge.lean contains {sorry_count} sorry tokens; expected {len(names)}")
    for path, source in ((DEFINITIONS, definitions_source), (SOLUTION, solution_source)):
        if SORRY_RE.search(source):
            fail(f"{path.relative_to(ROOT)} contains sorry")
        if re.search(r"^(?:axiom|unsafe)\b", source, re.MULTILINE):
            fail(f"{path.relative_to(ROOT)} declares a custom axiom or unsafe declaration")

    manifest = load_manifest()
    public_structures = {
        "LiptonTarjanPartition",
        "ControlledPreparationHybridBound",
        "PureStateTomographyBound",
        "ClassicalSDDSolveBound",
        "DenseLoadingBound",
        "GraphHardPairCertificate",
    }
    for structure_name in public_structures:
        pattern = re.compile(
            rf"^structure\s+{re.escape(structure_name)}\b.*?"
            rf"(?=\n\n(?:/--|structure |theorem |end ))",
            re.MULTILINE | re.DOTALL,
        )
        challenge_match = pattern.search(definitions_source)
        solution_match = pattern.search(solution_source)
        if challenge_match is None or solution_match is None:
            fail(f"could not extract public structure {structure_name}")
        if challenge_match.group().strip() != solution_match.group().strip():
            fail(f"public structure {structure_name} differs between claim environments")
    for claim in manifest["claim"]:
        if claim["status"] != "proved-relative-to-cited-result":
            continue
        for interface in claim["interface"].split(";"):
            local_name = interface.strip().removeprefix("PaperClaims.")
            declaration = re.compile(rf"^structure\s+{re.escape(local_name)}\b", re.MULTILINE)
            if not declaration.search(definitions_source) or not declaration.search(
                solution_source
            ):
                fail(f"{claim['name']} names an interface absent from one claim environment")
            claim_local_name = claim["name"].removeprefix("PaperClaims.")
            if local_name not in solution_statements[claim_local_name]:
                fail(f"{claim['name']} does not consume its named interface {interface.strip()}")


def validate_or_write_config(
    manifest: dict[str, object], names: list[str], write: bool
) -> None:
    expected = expected_config(manifest, names)
    if write:
        CONFIG.write_text(json.dumps(expected, indent=2) + "\n", encoding="utf-8")
        return
    actual = json.loads(CONFIG.read_text(encoding="utf-8"))
    if actual != expected:
        fail("comparator.json has drifted from paper_claims.toml")
    if "definition_names" in actual:
        fail("definition holes are not permitted on the public theorem surface")


def validate_workflow() -> None:
    source = WORKFLOW.read_text(encoding="utf-8")
    actions = Counter(
        re.findall(r"^\s*uses:\s*([^\s#]+)\s*$", source, re.MULTILINE)
    )
    if actions != EXPECTED_ACTIONS:
        fail("verification workflow action pins have drifted")
    for tool, revision in EXPECTED_TOOL_PINS.items():
        if source.count(revision) != 1:
            fail(f"verification workflow {tool} pin is missing or duplicated")
    required_fragments = (
        "lake build PowerFlowLimits --wfail",
        "lake lint",
        "lake env leanchecker",
        "scripts/audit_lean_trust.py",
        "sudo systemd-run",
        "RestrictAddressFamilies=AF_UNIX",
        'cp "$GITHUB_WORKSPACE/lean-toolchain" "$RUNNER_TEMP/comparator/lean-toolchain"',
        "cargo build --locked --release",
        'LAKE_BIN="$(command -v lake)"',
        '"$LAKE_BIN" env "$RUNNER_TEMP/comparator/.lake/build/bin/comparator" comparator.json',
        "experiments/validate_survey.py",
        "--publication",
        "--check-derived",
    )
    missing = [fragment for fragment in required_fragments if fragment not in source]
    if missing:
        fail(f"verification workflow is missing required gates: {missing!r}")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--write-comparator",
        action="store_true",
        help="regenerate comparator.json from the reviewed manifest",
    )
    args = parser.parse_args()
    try:
        manifest = load_manifest()
        names = validate_manifest(manifest)
        validate_sources(names)
        validate_or_write_config(manifest, names, args.write_comparator)
        validate_workflow()
    except (OSError, json.JSONDecodeError, tomllib.TOMLDecodeError, ValidationError) as error:
        print(f"claim surface validation failed: {error}", file=sys.stderr)
        return 1
    action = "generated and validated" if args.write_comparator else "validated"
    print(f"{action} {len(names)} public theorem claims")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
