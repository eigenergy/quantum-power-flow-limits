#!/usr/bin/env python3
"""Reject unreviewed trust mechanisms on the public Lean theorem surface."""

from __future__ import annotations

from pathlib import Path
import re
import subprocess
import sys
import tempfile
import tomllib


ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "paper_claims.toml"
ALLOWED_AXIOMS = {"propext", "Quot.sound", "Classical.choice"}
FORBIDDEN_TOKENS = {
    "sorry": re.compile(r"\bsorry\b"),
    "admit": re.compile(r"\badmit\b"),
    "sorryAx": re.compile(r"\bsorryAx\b"),
    "Lean.ofReduceBool": re.compile(r"\bLean\.ofReduceBool\b"),
}
TRUSTED_DECLARATION_RE = re.compile(
    r"^\s*(?:(?:private|protected)\s+)*(?:axiom|axioms|opaque|unsafe|partial|extern)\b",
    re.MULTILINE,
)
TRUSTED_ATTRIBUTE_RE = re.compile(
    r"@\[[^]]*\b(?:implemented_by|extern)\b[^]]*\]", re.MULTILINE
)
AUTO_MARKER_RE = re.compile(r"(?:^|\s)(?:BEGIN\s+|END\s+)?AUTO(?:MATED)?(?:\s|$)")
BACKUP_SUFFIXES = (".bak", ".orig", ".rej", ".swp", "~")
AXIOM_LINE_RE = re.compile(
    r"^'(?P<name>PaperClaims\.[A-Za-z0-9_]+)' depends on axioms: "
    r"\[(?P<axioms>[^]]*)\]$",
    re.MULTILINE,
)
NO_AXIOM_LINE_RE = re.compile(
    r"^'(?P<name>PaperClaims\.[A-Za-z0-9_]+)' does not depend on any axioms$",
    re.MULTILINE,
)


class AuditError(Exception):
    """A reviewed trust boundary was violated."""


def solution_sources() -> list[Path]:
    sources = sorted((ROOT / "PowerFlowLimits").rglob("*.lean"))
    umbrella = ROOT / "PowerFlowLimits.lean"
    if umbrella.exists():
        sources.append(umbrella)
    return sources


def strip_lean_comments(source: str) -> str:
    """Remove nested block comments and line comments before declaration scans."""
    result: list[str] = []
    index = 0
    depth = 0
    while index < len(source):
        if source.startswith("/-", index):
            depth += 1
            index += 2
        elif depth > 0 and source.startswith("-/", index):
            depth -= 1
            index += 2
        elif depth == 0 and source.startswith("--", index):
            newline = source.find("\n", index)
            if newline == -1:
                break
            result.append("\n")
            index = newline + 1
        elif depth == 0:
            result.append(source[index])
            index += 1
        else:
            if source[index] == "\n":
                result.append("\n")
            index += 1
    if depth != 0:
        raise AuditError("unterminated Lean block comment")
    return "".join(result)


def audit_sources() -> None:
    surface_files = list((ROOT / "PowerFlowLimits").rglob("*"))
    surface_files.extend((ROOT / "Challenge").rglob("*"))
    surface_files.extend(ROOT.glob("PowerFlowLimits.lean*"))
    surface_files.extend(ROOT.glob("Challenge.lean*"))
    backups = sorted(
        path.relative_to(ROOT)
        for path in surface_files
        if path.is_file() and path.name.endswith(BACKUP_SUFFIXES)
    )
    if backups:
        raise AuditError(
            "backup files on solution surface: "
            + ", ".join(str(path) for path in backups)
        )

    failures: list[str] = []
    public_sources = solution_sources()
    public_sources.extend(sorted((ROOT / "Challenge").rglob("*.lean")))
    public_sources.append(ROOT / "Challenge.lean")
    for path in public_sources:
        if AUTO_MARKER_RE.search(path.read_text(encoding="utf-8")):
            failures.append(f"{path.relative_to(ROOT)}: AUTO marker")
    for path in solution_sources():
        source = path.read_text(encoding="utf-8")
        relative = path.relative_to(ROOT)
        stripped = strip_lean_comments(source)
        for label, pattern in FORBIDDEN_TOKENS.items():
            if pattern.search(stripped):
                failures.append(f"{relative}: {label}")
        if TRUSTED_DECLARATION_RE.search(stripped):
            failures.append(f"{relative}: custom trusted declaration")
        if TRUSTED_ATTRIBUTE_RE.search(stripped):
            failures.append(f"{relative}: custom trusted implementation attribute")
    if failures:
        raise AuditError("; ".join(failures))


def claim_names() -> list[str]:
    with MANIFEST.open("rb") as stream:
        manifest = tomllib.load(stream)
    claims = manifest.get("claim")
    if not isinstance(claims, list):
        raise AuditError("claim manifest has no claim array")
    names = [claim.get("name") for claim in claims if isinstance(claim, dict)]
    if len(names) != len(claims) or not all(isinstance(name, str) for name in names):
        raise AuditError("claim manifest contains an invalid theorem name")
    return names


def audit_axiom_closure(names: list[str]) -> None:
    source = "import PowerFlowLimits.PaperClaims\n\n" + "\n".join(
        f"#print axioms {name}" for name in names
    )
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".lean", encoding="utf-8", delete=False
    ) as stream:
        stream.write(source)
        audit_path = Path(stream.name)
    try:
        result = subprocess.run(
            ["lake", "env", "lean", str(audit_path)],
            cwd=ROOT,
            check=False,
            capture_output=True,
            text=True,
        )
    finally:
        audit_path.unlink(missing_ok=True)
    if result.returncode != 0:
        details = (result.stdout + result.stderr).strip()
        raise AuditError(f"Lean axiom audit failed: {details}")

    observed: dict[str, set[str]] = {
        match.group("name"): {
            axiom.strip()
            for axiom in match.group("axioms").split(",")
            if axiom.strip()
        }
        for match in AXIOM_LINE_RE.finditer(result.stdout)
    }
    observed.update(
        {
            match.group("name"): set()
            for match in NO_AXIOM_LINE_RE.finditer(result.stdout)
        }
    )
    missing = [name for name in names if name not in observed]
    extra = sorted(set(observed) - set(names))
    if missing or extra:
        raise AuditError(
            f"axiom report theorem drift; missing={missing!r}, extra={extra!r}"
        )
    unexpected = {
        name: sorted(axioms - ALLOWED_AXIOMS)
        for name, axioms in observed.items()
        if axioms - ALLOWED_AXIOMS
    }
    if unexpected:
        raise AuditError(f"unpermitted theorem axioms: {unexpected!r}")


def main() -> int:
    try:
        audit_sources()
        names = claim_names()
        audit_axiom_closure(names)
    except (OSError, subprocess.SubprocessError, tomllib.TOMLDecodeError, AuditError) as error:
        print(f"Lean trust audit failed: {error}", file=sys.stderr)
        return 1
    print(
        f"audited {len(names)} theorem closures; only reviewed standard axioms are reachable"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
