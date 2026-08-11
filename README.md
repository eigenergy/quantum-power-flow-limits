# quantum-power-flow-limits

Lean 4 formalization of the numbered claims in *The Limits of Quantum
Computers for Power Flow* by Cameron Khanpour and Samuel Talkington.

The proof modules under `PowerFlowLimits/` compile without `sorry`. Their axiom
closure is limited to `propext`, `Quot.sound`, and `Classical.choice`.
`Challenge.lean` contains 18 intentional statement placeholders used only by
Comparator; it is not part of the proof implementation.

`PowerFlowLimits/PaperClaims.lean` is the public claim surface. Its 18 wrappers
and their dependency statuses are fixed in `paper_claims.toml`. Comparator
checks those wrappers against the independent statements in `Challenge.lean`.

## Formalized scope

The repository proves the weighted Laplacian identities and cut bounds in
Lemma 1, Theorem 1, the treewidth and planar consequences in Corollary 1,
the corridor bound in Proposition 1, the random weight transfers in
Proposition 2, and the balanced worst case readout results in Proposition 3.
It also proves the grounded trace correction used by the paper.

The near planar result no longer assumes a completed separator of the original
grid. Lean defines a crossing schedule, constructs a graph on the original
buses and inserted crossing vertices, proves every original branch becomes a
route in that graph, and projects a vertex cost separator back to the original
buses. The projection proves cover, separation, balance on original buses, and
the factor two separator size bound. The remaining inputs are explicit:

- a planarity certificate for the constructed planarized graph;
- the vertex cost form of the Lipton–Tarjan separator theorem.

The repository represents the second item as the theorem valued premise
`LiptonTarjanVertexCostTheorem`. It adds no planarity axiom. The exact planar
and near planar public claims are therefore proved relative to Lipton–Tarjan,
with all graph construction and projection steps checked in Lean.

For random susceptances, the finite Hoeffding lemmas retain their exact
probability exponent without a mean ratio assumption. The public grid family
wrappers assume a constant `rho > 0` and the mean bound
`rho * m * b_max <= sum_e E[b_e]`. They return the uniform floor
`1 - exp(-2 * epsilon^2 * rho^2 * m)` used in the letter.

Proposition 3 is stated on the zero sum subspace. Lean proves that this real
Hilbert space has dimension `n - 1`, proves `n - 1 >= n / 2` for `n >= 2`, and
uses that dimension in the tomography premise. The fixed schedule theorems
take balanced targets by type rather than by a separate balance hypothesis.
The local observable wrapper combines the controlled preparation hybrid
premise with the total observable query count and returns both the solve query
lower bound and the nonzero gap estimate separation.

The flat start lossless AC active angle block and the DC optimal power flow
branch barrier angle Hessian are verified as positive weighted Laplacian
blocks. The broader Beyond DC conclusions remain discussion; the repository
does not claim a theorem about a complete AC Newton or optimal power flow KKT
system.

## Public claim surface

| Manuscript result | Public Lean wrapper | Status |
|---|---|---|
| Lemma 1 | `PaperClaims.lemma1_weightedCuts` | Proved |
| Theorem 1 | `PaperClaims.theorem1_separator` | Proved |
| Corollary 1(i) | `PaperClaims.corollary1_treewidth` | Proved |
| Corollary 1(ii) | `PaperClaims.corollary1_planarFromLiptonTarjan` | Relative to Lipton–Tarjan |
| Near planar extension | `PaperClaims.nearPlanarFromCrossingDrawing` | Relative to Lipton–Tarjan |
| Proposition 1 | `PaperClaims.proposition1_corridor` | Proved |
| Proposition 2, separators | `PaperClaims.proposition2_randomSeparator` | Proved |
| Proposition 2, treewidth | `PaperClaims.proposition2_randomTreewidth` | Proved |
| Proposition 2, planar | `PaperClaims.proposition2_randomPlanar` | Relative to Lipton–Tarjan |
| Proposition 2, corridor | `PaperClaims.proposition2_randomCorridor` | Proved |
| Proposition 3, hard pair | `PaperClaims.proposition3_balancedHardPair` | Proved |
| Proposition 3, fixed schedule | `PaperClaims.proposition3_fixedScheduleReadout` | Relative to cited quantum and classical bounds |
| Proposition 3, grid family | `PaperClaims.proposition3_gridReadout` | Relative to cited quantum and classical bounds |
| Proposition 3, corridor family | `PaperClaims.proposition3_corridorReadout` | Relative to cited quantum and classical bounds |
| Proposition 3, local observable | `PaperClaims.proposition3_localObservable` | Relative to the controlled hybrid bound |
| Grounded transfer | `PaperClaims.groundedConditioningTransfer` | Proved |
| Flat start AC block | `PaperClaims.flatStartACBlock` | Proved for the modeled block |
| DC optimal power flow barrier block | `PaperClaims.dcOpfBarrierBlock` | Proved for the modeled block |

## Repository layout

- `Graph.lean`, `Laplacian.lean`, `Connectivity.lean`, `Eigenvalues.lean`, and
  `CutBounds.lean` define the weighted graph model and prove Lemma 1.
- `Separators.lean` and `TreeDecomposition.lean` prove Theorem 1 and the
  treewidth consequence.
- `Planarization.lean` and `PlanarSeparator.lean` construct and project the
  planarization used by the planar and near planar claims.
- `Corridors.lean` and `Random.lean` prove Propositions 1 and 2.
- `QueryHardness.lean`, `SpectralHardPair.lean`, and `EndToEnd.lean` prove the
  balanced hard pair, target reachability, fixed schedule product, and local
  observable arithmetic used by Proposition 3.
- `Grounded.lean`, `ACPowerFlow.lean`, and `OptimalPowerFlow.lean` contain the
  grounded and modeled Beyond DC block results.
- `experiments/` contains the pinned five case generator, retained JSON, and
  the generated table used in `main_letter_v4.tex`.

See [the claim ledger](docs/claim-alignment.md),
[the Proposition 3 model](docs/proposition-3-recovery.md), and
[the dependency survey](docs/lean-library-survey.md) for the detailed boundary.

## Verification

The repository is pinned to Lean 4 and mathlib 4.28.0. Run:

```sh
lake exe cache get
lake build PowerFlowLimits --wfail
lake lint
lake build Challenge
python3 scripts/check_paper_claims.py
python3 scripts/audit_lean_trust.py
```

The Ubuntu verification workflow runs Comparator and both configured kernels
under the pinned isolation setup. A successful run checks statement identity,
axiom closure, the 18 claim manifest, and the intentional challenge count.

## Authors

Cameron Khanpour and Samuel Talkington. MIT license.
