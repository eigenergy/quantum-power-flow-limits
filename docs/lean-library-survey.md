# Lean library survey

Survey date: 6 August 2026. The repository is pinned to Lean and mathlib 4.28.0.

## Reused now

Mathlib supplies the parts that already match the letter's proof obligations:

- `Combinatorics.SimpleGraph` supplies ordinary connectivity, paths, spanning trees, and the
  connected edge-count theorem used to prove `m >= n - 1`. Its Laplacian kernel characterization
  is also reused to connect ordinary connectivity to the kernel of the positive weighted
  Laplacian.
- `Analysis.Matrix.Spectrum` supplies the finite-dimensional Hermitian spectral theorem used in
  the trace bound.
- `Analysis.Normed.Module.FiniteDimension` supplies the bounded-below characterization of an
  injective linear map used for spectral connectivity and grounded positive definiteness.
- `Probability.Moments.SubGaussian` supplies the independent sub-Gaussian sum tail bound used in
  Proposition 2.
- Mathlib has no tree decomposition, treewidth, graph planarity, or planar separator API in the
  pinned release. The repository now supplies the standard three tree decomposition axioms and
  proves the weighted centroid and balanced-bag theorem locally. Planarity and Lipton--Tarjan
  remain absent.

Project definitions are kept small and connected to these APIs. Manuscript-facing results are
duplicated as independent statements in `Challenge.lean` and replayed through Comparator.
The custom graph type is still needed because the manuscript uses positive weights, oriented
incidence data, and parallel branches, while mathlib's `SimpleGraph.lapMatrix` is unweighted.
Mathlib 4.28.0 also has no symmetric diagonal dominance predicate or sorted second-eigenvalue API
that matches the manuscript statements.

## Quantum libraries inspected

### Physlib and QuantumInfo

[Physlib](https://github.com/leanprover-community/physlib) is the maintained successor to
Lean-QuantumInfo. Commit `fa696f859970a19b53ea2b9513231fe243463c73` was inspected. It contains
useful states, channels, measurements, entropy, and hypothesis-testing infrastructure. It does not
contain a quantum linear system algorithm, a linear-in-condition-number QLS query lower bound, or
the tomography lower bound used by the letter. Some QuantumInfo modules also contain declarations
tagged `sorryful`; a dependency would have to import only axiom-clean modules.

Physlib currently targets Lean 4.32.0, so adding it would force an unrelated toolchain migration
from 4.28.0. No current proof obligation justifies that migration.

### Lean-QuantumAlg and CSLib

[Lean-QuantumAlg](https://github.com/QudeLeap/Lean-QuantumAlg) commit
`7e80846034b9e76fdeded711775a513a7d5ba917` provides circuit, oracle, QSP, QSVT, and resource-model
interfaces over [CSLib](https://github.com/leanprover/cslib). It has no QLS module or tomography
lower bound. Its public resource counts are explicitly attached through `Timed.trusted` and
`Profiled.trusted`; those annotations do not prove a query lower bound and cannot replace F1 or F2.
It targets Lean 4.31.0 and CSLib 4.31.0.

[Lean-QIT](https://github.com/QuAIR/Lean-QIT) commit
`bb3ada54fa451996df9e197c2be53c2625bc99a3` supplies operational quantum information coding
interfaces and verified capacity results. Its advertised scope does not include QLS query
complexity or state tomography sample complexity, and it targets Lean 4.30.0.

## Dependency decision

Do not vendor or add any of these packages yet. Their present modules do not discharge an open
claim, and all three require a toolchain migration. Revisit the decision when one provides a
kernel-clean theorem with the exact oracle, error, and success-probability model required by F1 or
F2. Until then, the cited query and tomography lower bounds enter as explicit hypotheses. Lean
verifies the hard pair, preparation oracle gap, target reachability, local observable gaps, and the
quantifier composition that yields the clean worst case product.

## Community practice applied

- Prefer mathlib declarations to local copies when an exact theorem exists.
- Keep definitions independent of proof implementation and expose small theorem surfaces.
- Use no custom axioms, `sorry`, or `proof_wanted` in proof modules.
- Check axiom closure, not just successful compilation.
- Pin dependencies and audit their actual imported modules before accepting a theorem as trusted.
- Separate an algorithm's proved semantics from unverified resource annotations.
- Use Comparator to check that audited statements and implementations are definitionally the same.
