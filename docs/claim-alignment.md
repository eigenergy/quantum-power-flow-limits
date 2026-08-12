# Public claim ledger

`PowerFlowLimits/PaperClaims.lean` exposes 18 manuscript claims. A claim marked
“relative” is a Lean proof from an explicit cited theorem premise; the cited
theorem is not represented as a local axiom.

| # | Manuscript claim | Public declaration | Status and boundary |
|---:|---|---|---|
| 1 | Lemma 1 | `PaperClaims.lemma1_weightedCuts` | Proved |
| 2 | Theorem 1 | `PaperClaims.theorem1_separator` | Proved from an explicit separator |
| 3 | Corollary 1(i) | `PaperClaims.corollary1_treewidth` | Proved from the standard tree decomposition axioms |
| 4 | Corollary 1(ii) | `PaperClaims.corollary1_planarFromLiptonTarjan` | Relative to the Lipton–Tarjan vertex cost theorem and a planarity certificate |
| 5 | Near planar extension | `PaperClaims.nearPlanarFromCrossingDrawing` | Relative to the same cited theorem and a certificate for the constructed planarization |
| 6 | Proposition 1 | `PaperClaims.proposition1_corridor` | Proved |
| 7 | Proposition 2, separator | `PaperClaims.proposition2_randomSeparator` | Proved with the exact Hoeffding exponent |
| 8 | Proposition 2, treewidth | `PaperClaims.proposition2_randomTreewidth` | Proved with the exact Hoeffding exponent |
| 9 | Proposition 2, planar | `PaperClaims.proposition2_randomPlanar` | Relative to Lipton–Tarjan, with the exact Hoeffding exponent |
| 10 | Proposition 2, corridor | `PaperClaims.proposition2_randomCorridor` | Proved with the exact Hoeffding exponent |
| 11 | Proposition 3, hard pair | `PaperClaims.proposition3_balancedHardPair` | Proved on the balanced subspace |
| 12 | Proposition 3, fixed schedule readout | `PaperClaims.proposition3_fixedScheduleReadout` | Relative to the cited hybrid, tomography, classical solve, and loading bounds |
| 13 | Proposition 3, grid readout | `PaperClaims.proposition3_gridReadout` | Relative to the same cited bounds |
| 14 | Proposition 3, corridor readout | `PaperClaims.proposition3_corridorReadout` | Relative to the same cited bounds |
| 15 | Proposition 3, local observable | `PaperClaims.proposition3_localObservable` | Relative to the controlled preparation hybrid bound; assumes a positive displayed gap |
| 16 | Grounded transfer | `PaperClaims.groundedConditioningTransfer` | Proved with the exact slack degree correction |
| 17 | Flat start AC block | `PaperClaims.flatStartACBlock` | Proved for the lossless unit voltage active angle block |
| 18 | DC optimal power flow barrier block | `PaperClaims.dcOpfBarrierBlock` | Proved for the two sided branch barrier angle Hessian |

## Planar and near planar construction

The repository proves the graph theoretic construction after a crossing
schedule has been supplied:

1. `PlanarizedVertex n c` is the disjoint sum of the `n` original buses and
   the `c` crossing vertices.
2. `CrossingSchedule` assigns two distinct carrier branches to each crossing
   and an ordered duplicate free crossing list to each branch.
3. `CrossingSchedule.planarizedGraph` joins consecutive vertices on each
   branch route. Lean proves the route endpoints, crossing membership, route
   walk, and `n + c` vertex count.
4. `busCost` gives weight `1/n` to original buses and zero to inserted crossing
   vertices. Its total weight is one, and it balances the original buses.
5. A planarized separator is projected by replacing each crossing separator
   vertex with one original endpoint from each carrier branch. Lean proves the
   projected separator has at most twice as many vertices, separates every
   original branch, covers the original buses, and leaves both sides with at
   most `2n/3` original buses.
6. `1152 * (n + c) <= n^2` implies the projected separator has size at most
   `n/6`, which supplies the final `5/36` condition number constant.

The caller supplies `Planar _ S.planarizedGraph` and a value of
`LiptonTarjanVertexCostTheorem Planar`. These are the only topological and
separator existence inputs. `PaperClaims.nearPlanarFromCrossingDrawing` is
therefore proved relative to Lipton–Tarjan, not conditional on an already
projected partition.

## Random susceptance quantifiers

The public Proposition 2 wrappers call `random_kappa_bound`,
`random_treewidth_kappa_bound`,
`random_kappa_bound_of_sqrt_separator_partition`, and
`random_corridor_kappa_bound` directly. Each wrapper retains the exact
Hoeffding probability

```text
1 - exp(-2 * epsilon^2 * (sum_e E[b_e])^2 / (m * b_max^2)).
```

No public Proposition 2 wrapper introduces `rho` or a mean to maximum ratio
premise. The separate exponential corollaries in `Random.lean` remain
available to clients that have such a uniform family assumption.

## Proposition 3 quantifiers

The hard inputs and all tomography targets inhabit `zeroSumSubspace n`. Lean
proves its finite dimension is `n - 1` and proves the elementary lower bound
`n - 1 >= n / 2` for `n >= 2`. The public readout wrappers no longer carry a
separate balance hypothesis.

`PaperClaims.proposition3_localObservable` receives the controlled preparation
hybrid premise, the number of queries used by one solve, the total observable
query count, and the premise that the estimator performs at least one solve.
It returns both the inherited solve lower bound

```text
solverGap * condition / hybridConstant <= observableQueries
```

and the `gamma/2` separation of the two estimates. The result applies to the
bus and branch rank one observables in the manuscript when `gamma > 0`.

## Discussion boundary

The flat start AC and DC optimal power flow wrappers prove the precise
Laplacian block identities used by the paper. Claims about complete nonlinear
AC Newton systems, complete optimal
power flow KKT systems, unit commitment, or hybrid algorithms remain
discussion in the letter and are not promoted to Lean theorems.

The five case numerical table is reproducible Python evidence. It is not one
of the 18 Comparator claims.

## Trust checks

The proof modules contain no `sorry` or `proof_wanted`. Their axiom closure is
limited to `propext`, `Quot.sound`, and `Classical.choice`. Comparator checks
the 18 declarations against `Challenge.lean`; `paper_claims.toml` records each
cited dependency and the verification scripts enforce the claim and challenge
counts.
