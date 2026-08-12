#!/usr/bin/env python3
"""Load and check the pinned policy for numerical publication artifacts."""

from __future__ import annotations

import argparse
from dataclasses import dataclass
import hashlib
from pathlib import Path
import re
import tomllib
from typing import Mapping


EXPERIMENT_DIR = Path(__file__).resolve().parent
DEFAULT_POLICY_PATH = EXPERIMENT_DIR / "publication.toml"
SHA256_PATTERN = re.compile(r"[0-9a-f]{64}")
GRAPHVIZ_BANNER_PATTERN = re.compile(r"\bgraphviz version ([0-9]+(?:\.[0-9]+){2})\b")


@dataclass(frozen=True)
class PublicationPolicy:
    """Typed view of ``publication.toml``."""

    schema_version: int
    source_sha256: str
    core_keys: tuple[str, ...]
    pglib_keys: tuple[str, ...]
    extra_keys: tuple[str, ...]
    pglib_variants_per_case: int
    spectral_max_n: int
    near_planarity_min_n: int
    versions: Mapping[str, str]
    algorithms: Mapping[str, int | str]
    provenance: Mapping[str, str]
    retained_generation_policy_sha256: str | None
    outputs: Mapping[str, str]

    @property
    def primary_keys(self) -> tuple[str, ...]:
        return self.pglib_keys + self.extra_keys

    @property
    def primary_cases(self) -> int:
        return len(self.primary_keys)

    @property
    def pglib_variant_files(self) -> int:
        return len(self.pglib_keys) * self.pglib_variants_per_case


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _string_tuple(table: dict, name: str) -> tuple[str, ...]:
    value = table.get(name)
    if not isinstance(value, list) or not all(isinstance(item, str) for item in value):
        raise ValueError(f"publication policy {name} must be an array of strings")
    if len(value) != len(set(value)):
        raise ValueError(f"publication policy {name} contains duplicate keys")
    return tuple(value)


def load_policy(path: Path = DEFAULT_POLICY_PATH) -> PublicationPolicy:
    with path.open("rb") as stream:
        document = tomllib.load(stream)
    coverage = document.get("coverage", {})
    policy = PublicationPolicy(
        schema_version=document.get("schema_version"),
        source_sha256=sha256_file(path),
        core_keys=_string_tuple(coverage, "core_keys"),
        pglib_keys=_string_tuple(coverage, "pglib_keys"),
        extra_keys=_string_tuple(coverage, "extra_keys"),
        pglib_variants_per_case=coverage.get("pglib_variants_per_case"),
        spectral_max_n=coverage.get("spectral_max_n"),
        near_planarity_min_n=coverage.get("near_planarity_min_n"),
        versions=document.get("versions", {}),
        algorithms=document.get("algorithms", {}),
        provenance=document.get("provenance", {}),
        retained_generation_policy_sha256=document.get("retained_artifacts", {}).get(
            "corpus_generation_policy_sha256"
        ),
        outputs=document.get("outputs", {}),
    )
    if policy.schema_version != 1:
        raise ValueError("expected publication policy schema version 1")
    if policy.pglib_variants_per_case != 2:
        raise ValueError("publication policy must require two PGLib variants per case")
    if policy.spectral_max_n <= 0 or policy.near_planarity_min_n <= 0:
        raise ValueError("publication policy cutoffs must be positive")
    if set(policy.core_keys) != {
        "texas7k",
        "pegase13k",
        "midwest24k",
        "goc30k",
        "epigrids78k",
    }:
        raise ValueError("publication policy must name the five canonical core cases")
    if len(policy.pglib_keys) != 66 or len(policy.extra_keys) != 12:
        raise ValueError("publication policy must name 66 PGLib and 12 extra cases")
    if set(policy.pglib_keys) & set(policy.extra_keys):
        raise ValueError("publication policy primary case groups overlap")
    required_versions = {
        "python",
        "uv",
        "julia",
        "graphviz",
        "powerio",
        "powerio_commit",
        "networkx",
        "numpy",
        "pymetis",
        "scipy",
        "shapely",
    }
    if set(policy.versions) != required_versions:
        raise ValueError("publication policy version keys do not match the required toolchain")
    if policy.algorithms != {
        "separator_seed": 42,
        "spectral_seed": 42,
        "graphviz_start": "42",
        "graphviz_overlap": "scale",
        "crossing_threshold_constant": 1152,
    }:
        raise ValueError("publication policy algorithm parameters differ from the contract")
    for relative_path, digest in policy.provenance.items():
        if Path(relative_path).is_absolute() or ".." in Path(relative_path).parts:
            raise ValueError(f"unsafe provenance path: {relative_path}")
        if not isinstance(digest, str) or SHA256_PATTERN.fullmatch(digest) is None:
            raise ValueError(f"invalid provenance SHA-256 for {relative_path}")
    if (
        policy.retained_generation_policy_sha256 is not None
        and SHA256_PATTERN.fullmatch(policy.retained_generation_policy_sha256) is None
    ):
        raise ValueError("invalid retained corpus generation policy SHA-256")
    return policy


def graphviz_version(value: str | None) -> str | None:
    """Extract a semantic version from either a version or an sfdp banner."""
    if value is None:
        return None
    if re.fullmatch(r"[0-9]+(?:\.[0-9]+){2}", value):
        return value
    match = GRAPHVIZ_BANNER_PATTERN.search(value)
    return match.group(1) if match else None


def repository_provenance(
    policy: PublicationPolicy, root: Path = EXPERIMENT_DIR
) -> dict[str, str]:
    """Hash every local input named by the policy."""
    hashes = {}
    for relative_path in policy.provenance:
        path = root / relative_path
        if not path.is_file():
            raise FileNotFoundError(path)
        hashes[relative_path] = sha256_file(path)
    return hashes


def provenance_errors(
    policy: PublicationPolicy, root: Path = EXPERIMENT_DIR
) -> list[str]:
    errors = []
    for relative_path, expected in policy.provenance.items():
        path = root / relative_path
        if not path.is_file():
            errors.append(f"missing provenance input: {relative_path}")
            continue
        actual = sha256_file(path)
        if actual != expected:
            errors.append(
                f"provenance drift for {relative_path}: expected {expected}, got {actual}"
            )
    return errors


def environment_errors(environment: dict, policy: PublicationPolicy) -> list[str]:
    """Compare recorded dependency versions with the immutable policy."""
    errors = []
    fields = {
        "python": "python",
        "uv": "uv",
        "julia": "julia",
        "powerio_version": "powerio",
        "powerio_commit": "powerio_commit",
        "networkx": "networkx",
        "numpy": "numpy",
        "pymetis": "pymetis",
        "scipy": "scipy",
        "shapely": "shapely",
    }
    for field, policy_key in fields.items():
        actual = environment.get(field)
        expected = policy.versions[policy_key]
        if actual != expected:
            errors.append(f"{field} version drift: expected {expected}, got {actual}")
    actual_graphviz = graphviz_version(environment.get("graphviz"))
    expected_graphviz = policy.versions["graphviz"]
    if actual_graphviz != expected_graphviz:
        errors.append(
            f"graphviz version drift: expected {expected_graphviz}, got {actual_graphviz}"
        )
    if environment.get("powerio_tracked_dirty") is not False:
        errors.append("PowerIO source must have no tracked modifications")
    if environment.get("powerio_dirty") is not False:
        errors.append("PowerIO source must have no untracked files or modifications")
    return errors


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--policy", type=Path, default=DEFAULT_POLICY_PATH)
    parser.add_argument("--check-files", action="store_true")
    parser.add_argument("--print-files", action="store_true")
    args = parser.parse_args()
    policy = load_policy(args.policy)
    current = repository_provenance(policy)
    if args.check_files:
        errors = provenance_errors(policy)
        if errors:
            raise SystemExit("\n".join(errors))
    if args.print_files:
        for path, digest in current.items():
            print(f'{path} = "{digest}"')


if __name__ == "__main__":
    main()
