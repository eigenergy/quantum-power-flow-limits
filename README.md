# quantum-power-flow-limits

Lean 4 formalization for *Proving the Limits of Quantum Power Flow* by Cameron
Khanpour and Samuel Talkington.

The proof code under `PowerFlowLimits/` contains no `sorry`. The public surface
is the 18 declarations in `PowerFlowLimits/PaperClaims.lean`, with dependency
status recorded in `paper_claims.toml`. Comparator checks these declarations
against the independent statements in `Challenge.lean`; its 18 `sorry` tokens
are intentional statement placeholders, not proof holes.

## Scope

The formalization covers:

- weighted and topology only separator, treewidth, planar, near planar, and
  corridor condition number bounds;
- pathwise random weight bounds and the exact finite Hoeffding
  refinement, without a mean to maximum ratio assumption;
- grounded separator and corridor transfers and the exact trace correction;
- balanced QLS query, tomography, grid, corridor, and local observable bounds;
- the lossless unit voltage flat start AC active angle block and the positive
  DC optimal power flow barrier angle block.

For the near planar result, Lean constructs the planarized graph from a
crossing schedule and projects its separator to the original buses. Planarity
of that constructed graph and the vertex cost Lipton--Tarjan theorem are
explicit premises. No planarity axiom is added.

The broader Beyond DC discussion is not represented as a theorem about a full
AC Newton or optimal power flow KKT system.

## Files

- `PowerFlowLimits/PaperClaims.lean`: the 18 manuscript facing declarations
- `Challenge.lean`: independent statements used by Comparator
- `paper_claims.toml`: claim and dependency ledger
- `docs/claim-alignment.md`: claim by claim alignment notes
- `experiments/`: pinned five-case and PGLib corpus evidence and generated tables

## Verification

The repository uses Lean 4 and mathlib 4.28.0.

```sh
lake exe cache get
lake build PowerFlowLimits --wfail
lake build Challenge
lake lint
python3 scripts/check_paper_claims.py
python3 scripts/audit_lean_trust.py
```

CI also replays declarations with LeanChecker and checks the public theorem
surface with Comparator using the Lean and nanoda kernels. The reviewed axiom
closure is limited to `propext`, `Quot.sound`, and `Classical.choice`.

See `docs/proposition-3-recovery.md` for the query model and
`docs/lean-library-survey.md` for external theorem dependencies.
