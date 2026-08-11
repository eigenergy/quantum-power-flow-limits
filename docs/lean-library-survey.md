# Lean library survey

Survey date: 11 August 2026. The repository is pinned to Lean and mathlib
4.28.0.

## Mathlib dependencies

The manuscript proof reuses these mathlib components:

- `Combinatorics.SimpleGraph` for paths, connectivity, walks, spanning trees,
  and the connected edge count used to prove `m >= n - 1`;
- `Analysis.Matrix.Spectrum` for finite dimensional self adjoint spectral
  arguments;
- `Analysis.Normed.Module.FiniteDimension` for injective linear map and finite
  dimension facts used by spectral connectivity and the zero sum subspace;
- `Probability.Moments.SubGaussian` for the independent bounded sum tail bound
  in Proposition 2.

Mathlib 4.28.0 has no tree decomposition, treewidth, plane embedding, graph
planarity, or planar separator API matching the manuscript. The repository
defines the standard tree decomposition axioms and proves the weighted
centroid and balanced bag result locally.

## Planarization boundary

The absence of a plane embedding library does not leave the near planar graph
construction unproved. The repository defines:

- `PlanarizedVertex n c`;
- `CrossingSchedule` and each original branch route;
- `CrossingSchedule.planarizedGraph`;
- `VertexCostPartition`;
- the separator projection from the planarized graph to the original buses.

Lean proves the route walks, the `n + c` vertex count, bus weighted balance,
the factor two projected separator bound, absence of original branches between
the projected sides, and the final exact planar and near planar condition
bounds.

Two inputs remain explicit. `PlanarityPredicate` abstracts the missing
planarity API, and the caller supplies a certificate that the relevant graph
is planar. `LiptonTarjanVertexCostTheorem Planar` is a theorem valued premise
matching the vertex cost conclusion used by the proof. This keeps
Lipton–Tarjan as a cited literature dependency without adding an axiom or
assuming the completed original bus partition.

## Quantum libraries inspected

Physlib provides states, channels, measurements, entropy, and hypothesis
testing. Lean-QuantumAlg and CSLib provide circuit, oracle, QSP, QSVT, and
resource interfaces. Lean-QIT provides quantum information coding interfaces.
None supplies, on the repository's pinned toolchain, the QLS hybrid lower bound
or the pure state tomography query lower bound with the oracle, inverse access,
error, and success model used by Proposition 3.

The repository therefore keeps those cited results as explicit theorem
arguments. Lean verifies the balanced hard pair, controlled preparation
rotations, zero sum tomography dimension, target reachability, fixed schedule
cost composition, and local observable gaps around those arguments.

## Dependency decision

No additional quantum package is required for the manuscript branch. Adding
one of the inspected packages would require a toolchain migration without
discharging a current external premise. Reconsider this decision when a
package provides an axiom clean theorem with the exact public oracle model.

## Audit rules

- Prefer a mathlib theorem when its statement matches the required model.
- Keep cited results as typed theorem arguments, not local axioms.
- Keep definitions independent of proof implementation.
- Permit no `sorry` or `proof_wanted` in proof modules.
- Audit axiom closure in addition to compilation.
- Use Comparator to check the 18 public wrappers against independent
  statements.
