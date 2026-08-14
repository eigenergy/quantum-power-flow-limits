#!/usr/bin/env python3
"""Generate a cut certificate from a canonical qpf-model document."""

from __future__ import annotations

import argparse
from collections import deque
from fractions import Fraction
from pathlib import Path


def parse_model(path: Path) -> tuple[int, list[tuple[int, int, Fraction]]]:
    tokens = path.read_text(encoding="ascii").split()
    if len(tokens) < 8 or tokens[:3] != ["QPFMODEL", "1", "N"]:
        raise ValueError("unsupported model document")
    n = int(tokens[3])
    if tokens[4] != "M" or tokens[6] != "BRANCHES" or tokens[-1] != "END":
        raise ValueError("malformed model document")
    m = int(tokens[5])
    rows = tokens[7:-1]
    if len(rows) != 4 * m:
        raise ValueError("branch count does not match model document")
    branches = []
    for index in range(m):
        source, target, significand, exponent = map(int, rows[4 * index : 4 * index + 4])
        weight = Fraction(significand * 2**exponent) if exponent >= 0 else Fraction(
            significand, 2 ** (-exponent)
        )
        branches.append((source, target, weight))
    return n, branches


def bfs_order(n: int, branches: list[tuple[int, int, Fraction]]) -> list[int]:
    adjacency = [[] for _ in range(n)]
    for source, target, _ in branches:
        adjacency[source].append(target)
        adjacency[target].append(source)
    order: list[int] = []
    seen = {0}
    queue = deque([0])
    while queue:
        vertex = queue.popleft()
        order.append(vertex)
        for neighbor in sorted(adjacency[vertex]):
            if neighbor not in seen:
                seen.add(neighbor)
                queue.append(neighbor)
    if len(order) != n:
        raise ValueError("model is disconnected; generate one certificate per island")
    return order


def lower_bound(
    n: int, branches: list[tuple[int, int, Fraction]], side: set[int]
) -> Fraction:
    total = sum((weight for _, _, weight in branches), Fraction())
    cut = sum(
        (weight for source, target, weight in branches if (source in side) != (target in side)),
        Fraction(),
    )
    return Fraction(2 * len(side) * (n - len(side)), n * n) * total / cut


def generate(n: int, branches: list[tuple[int, int, Fraction]]) -> list[bool]:
    order = bfs_order(n, branches)
    best_side: set[int] | None = None
    best_bound = Fraction()
    side: set[int] = set()
    for vertex in order[:-1]:
        side.add(vertex)
        bound = lower_bound(n, branches, side)
        if best_side is None or bound > best_bound:
            best_side = side.copy()
            best_bound = bound
    assert best_side is not None
    return [vertex in best_side for vertex in range(n)]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("model", type=Path)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    n, branches = parse_model(args.model)
    side = generate(n, branches)
    text = f"QPFCERT 1 SIDE {n}\n" + " ".join("1" if item else "0" for item in side) + "\nEND\n"
    args.out.write_text(text, encoding="ascii")


if __name__ == "__main__":
    main()
