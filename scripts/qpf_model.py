#!/usr/bin/env python3
"""Export a canonical QPFMODEL document from a MATPOWER case with PowerIO.

The exporter reads the pinned PowerIO surface only: ``parse_file``,
``len(network.buses)``, branch rows through ``in_service``, ``from_id``,
``to_id``, and ``x``, and ``to_networkx`` for the bus id universe. Every in
service branch contributes the exact binary64 weight ``1/x`` written as an
odd significand dyadic pair ``significand exponent``. The checker decodes
the pair back to the same rational, so no floating point value survives the
handoff.
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path


class ExportError(ValueError):
    """The case cannot be stated as one canonical positive weighted model."""


def dyadic(value: float) -> tuple[int, int]:
    """Exact odd significand dyadic decomposition of a positive finite binary64."""
    if not 0.0 < value < float("inf"):
        raise ExportError(f"weight {value!r} is not a positive finite number")
    significand, denominator = value.as_integer_ratio()
    exponent = 1 - denominator.bit_length()
    while significand % 2 == 0:
        significand //= 2
        exponent += 1
    return significand, exponent


def export_model(case: Path) -> str:
    import powerio

    network = powerio.parse_file(case)
    bus_count = len(network.buses)
    bus_ids = sorted(int(node) for node in network.to_networkx().nodes())
    if len(bus_ids) != bus_count:
        raise ExportError(
            f"case states {bus_count} buses but the branch graph has {len(bus_ids)} nodes"
        )
    index = {bus_id: position for position, bus_id in enumerate(bus_ids)}
    rows = []
    for position, branch in enumerate(network.branches):
        if not bool(branch["in_service"]):
            continue
        source = index.get(int(branch["from_id"]))
        target = index.get(int(branch["to_id"]))
        if source is None or target is None:
            raise ExportError(f"branch {position} references an unknown bus")
        if source == target:
            raise ExportError(f"branch {position} is a self loop")
        reactance = float(branch["x"])
        if not 0.0 < reactance < float("inf"):
            raise ExportError(
                f"branch {position} has nonpositive reactance {reactance!r}"
            )
        significand, exponent = dyadic(1.0 / reactance)
        rows.append(f"{source} {target} {significand} {exponent}")
    lines = [f"QPFMODEL 1 N {bus_count} M {len(rows)} BRANCHES", *rows, "END"]
    return "\n".join(lines) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Export a canonical QPFMODEL document from a MATPOWER case."
    )
    parser.add_argument("case", type=Path, help="MATPOWER case file")
    arguments = parser.parse_args()
    try:
        document = export_model(arguments.case)
    except ImportError:
        print("qpf_model: install the powerio package to export models", file=sys.stderr)
        return 2
    except ExportError as error:
        print(f"qpf_model: {error}", file=sys.stderr)
        return 2
    sys.stdout.write(document)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
