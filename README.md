# quantum-power-flow-limits

Lean 4 formalization of *Proving the Limits of Quantum Power Flow* (Cameron
Khanpour and Samuel Talkington), following the first revision of the letter.
Every theorem in `PowerFlowLimits/` compiles against mathlib with no `sorry`.
Every proof rests on only the standard axioms (`propext`, `Classical.choice`,
`Quot.sound`). `Challenge.lean` contains intentional `sorry` placeholders for
statement comparison and is not part of that claim.

`PowerFlowLimits/PaperClaims.lean` is the public claim surface. Its 32
wrappers and their statuses are fixed in `paper_claims.toml`. Cited
separator, quantum query, classical SDD solve, and dense loading results
enter as explicit theorem arguments. Lean checks every deduction from those
arguments. The same manifest freezes the empirical and discussion claims
that are not presented as Lean theorems.

The paper's susceptance Laplacian B = Aᵀ diag(b) A with b_e > 0 is
`G.laplacian (fun _ => 1)` for a `WeightedGraph G` whose weights are the
branch susceptances. λ₂ and λ_max are defined variationally (sSup and sInf
of Rayleigh bound sets), and κ₊ = λ_max/λ₂ is `effectiveConditionNumber`.
The grounded matrix B_r is `groundedLaplacian G r`, and κ₂(B_r) is
`groundedConditionNumber G r`.

## Numbering

The numbering follows the revised letter. Proposition 2 is the query lower
bound result, which was Proposition 3 in the submitted version. Proposition 3
is the new bound on the DC-OPF Newton system. The probabilistic Proposition 2
of the submitted version is no longer in the letter, because the topology
only bounds hold for every positive choice of susceptances. Its proof stays
in `Random.lean` as a library result outside the public claim surface. The
retained numerical survey still stores its query diagnostics under the key
`proposition3`.

## Statement correspondence

| Paper | Lean | File |
|---|---|---|
| Setup, κ₊ = ‖B‖₂‖B⁺‖₂ on balanced injections | `balanced_solve_norm_bounds` | `EnergyNorm.lean` |
| Setup, grounded matrix: interlacing, trace, half of Lemma 1(i) | `groundedEigenvalueMin_le_lambda2`, `totalWeight_le_grounded_trace`, `half_lemma1_le_groundedEigenvalueMax` | `Grounded.lean`, `GroundedTransfer.lean` |
| Setup, each bound holds for κ₂(B_r) with its constant halved | `groundedConditionNumber_ge_of_lambda2_mul_le`, `cut_totalWeight_bound_le_groundedConditionNumber`, `cut_edge_bound_le_groundedConditionNumber`, `grounded_separator_kappa_bound_combined`, `WeightedGraph.grounded_treewidth_kappa_bound_of_tree_decomposition`, `grounded_planar_kappa_bound_of_lipton_partition`, `grounded_corridor_kappa_bound_combined` | `Grounded.lean`, `GroundedTransfer.lean` |
| Fact (F3), energy norm and Euclidean accuracy | `euclidean_error_le_energy_error`, `euclidean_accuracy_of_scaled_energy_accuracy` | `EnergyNorm.lean` |
| Classical SDD structure | `WeightedGraph.unitLaplacian_isSDD` | `Laplacian.lean` |
| Lemma 1(i), trace form | `two_totalWeight_div_le_lambdaMax` | `Eigenvalues.lean` |
| Lemma 1(i), edge form | `two_mul_weight_le_lambdaMax`, `exists_maxWeight_lambdaMax_bound` | `Eigenvalues.lean` |
| Lemma 1(ii) | `lambda2_le_cut_div`, `lambda2_mul_le_cut` | `CutBounds.lean` |
| Lemma 1, eq. (1) | `kappaPlus_ge_totalWeight`, `kappaPlus_ge_edge`, `exists_maxWeight_kappa_bound` | `CutBounds.lean` |
| Theorem 1, both terms of the maximum | `separator_kappa_bound`, `separator_kappa_bound_topological`, `separator_kappa_bound_combined` | `Separators.lean` |
| Corollary 1(i), the (τ+1, 1/4) separation | `WeightedGraph.exists_quarter_separation_of_tree_decomposition` | `GroundedTransfer.lean` |
| Corollary 1(i), bound | `WeightedGraph.treewidth_kappa_bound_of_tree_decomposition_combined` | `TreeDecomposition.lean` |
| Corollary 1(i), centroid and bag existence | `RootedTreeDecomposition.exists_balanced_bag` | `TreeDecomposition.lean` |
| Connected edge count `m >= n - 1` | `WeightedGraph.card_sub_one_le_edges` | `Connectivity.lean` |
| Corollary 1(ii) | `planar_kappa_bound_from_lipton_tarjan_combined`, `sqrt_eight_mul_card_le_sixth` | `PlanarSeparator.lean`, `Separators.lean` |
| Near planar grids, separator of size 2√(8(n+c)) | `CrossingSchedule.exists_projectedNearPlanarPartition` | `PlanarSeparator.lean` |
| Near planar grids, bound | `CrossingSchedule.nearPlanar_kappa_bound_combined` | `PlanarSeparator.lean` |
| Proposition 1, maximum form and the bound 2β²n(ℓ-1) | `corridor_kappa_bound_combined_exact`, `corridor_topological_le_combined_exact`, `corridor_family_isBigOmega_quadratic` | `Corridors.lean` |
| The bounds need no line data and hold under any joint distribution | `separator_topological_bound_surely`, `corridor_topological_bound_surely` | `AnyDistribution.lean` |
| Proposition 2, hard pair p± and its solutions | `RHSQueryHardness.prepared_sqDistance`, `preparationOracle_gap_sq`, `solution_sqDistance`, `SpectralHardPair.exists_balancedModePair_laplacian_inverse` | `QueryHardness.lean`, `SpectralHardPair.lean` |
| Proposition 2, an output of accuracy ε < 1/√2 tells p₊ from p₋ | `RHSQueryHardness.hardPair_accurate_output_separates` | `InputDependent.lean` |
| Proposition 2(i), Ω(κ) queries | `RHSQueryHardness.hybrid_distance_le`, `rhs_query_lower_bound` | `QueryHardness.lean` |
| Proposition 2(ii), pipeline readout product | `normalized_rhs_reaches_every_target`, `clean_qls_worst_case_product` (+ `_grid`, `_corridor`), `clean_qls_grid_product_exceeds_nearly_linear` | `EndToEnd.lean` |
| Proposition 2(iii), bus and branch observables | `RHSQueryHardness.bus_observable_gap`, `branch_observable_gap`, `estimates_separated_of_quarter_gap` | `QueryHardness.lean` |
| Corridor lower bound versus classical upper bound | `worst_case_corridor_qls_exceeds_classical` | `EndToEnd.lean` |
| Instancewise query counterexample | `DiagonalQLSAlgorithm.zero_query_solver_at_arbitrary_condition` | `Counterexamples.lean` |
| Substituting κ = Ω(n) into the HHL criterion | `hhl_criterion_readout_bound`, `hhl_criterion_no_readout_level` | `InputDependent.lean` |
| Input dependent solvers, κ_eff = κ on p± | `inputDependentConditionNumber_le`, `inputDependentConditionNumber_hardPair` | `InputDependent.lean` |
| AC flat start, active power and angle block | `WeightedGraph.acAngleJacobian_flat_eq_laplacian` | `ACPowerFlow.lean` |
| AC flat start, off diagonal blocks vanish | `WeightedGraph.hasDerivAt_acActivePower_voltage_flat`, `WeightedGraph.hasDerivAt_acReactivePower_angle_flat` | `ACFlatStart.lean` |
| AC flat start, κ₂(J) ≥ κ₂(B_r) | `flatStart_blockDiagonal_condition_bound` | `ACFlatStart.lean` |
| DC-OPF, barrier Hessian is a weighted Laplacian | `WeightedGraph.dcOpfNetworkBlock_eq_laplacian` | `OptimalPowerFlow.lean` |
| DC-OPF, κ₂(L_w) ≥ β(1-β)n/(sΔ) | `WeightedGraph.dcOpfGroundedBlock_condition_bound` | `DcOpfNewton.lean` |
| Proposition 3, DC-OPF Newton system | `WeightedGraph.dcOpfNewton_condition_bound` | `DcOpfNewton.lean` |
| Submitted version, Proposition 2 (random susceptances) | `random_kappa_bound`, `random_corridor_kappa_bound` | `Random.lean` |

Two strengthenings beyond the paper are proved in full. Theorem 1 holds
with the denominator s·Δ·b_max replaced by the interface stiffness
Σ_{x∈X} d_x, which it always dominates (`separator_kappa_bound_sharp`).
λ_max ≥ d_i gives the hub bound κ₊ ≥ γ(1-γ)·n·d_i/b(∂S) for every node
(`kappaPlus_ge_weightedDegree`); this beats the paper's per-edge term at
any node with three or more comparably stiff branches.

## What is proved and what is hypothesized

Lemma 1, Theorem 1, Corollary 1(i), Proposition 1, and Proposition 3 are
proved from explicit hypotheses. `CombinatoriallyConnected` is ordinary path
connectivity of the underlying graph. The weighted drop map proves that
positive weights and ordinary connectivity imply `lambda2 > 0`. The numbered
conditioning theorems derive spectral positivity rather than assume it.

Corollary 1(i) is proved from a standard rooted tree decomposition,
including the weighted centroid argument that produces the balanced bag and
the greedy grouping that produces the separation. Corollary 1(ii) and the
near planar extension take the vertex cost form of the cited Lipton--Tarjan
theorem as an explicit premise, `LiptonTarjanVertexCostTheorem`, stated for
an abstract planarity predicate, because that theorem is not in mathlib.
Everything from that premise to the bound is proved, including the
planarization of a drawing with crossings and the projection of the
separator back to the original buses.

The grounded matrix needs no extra assumption. Interlacing, the trace bound
tr(B_r) ≥ b(E), and the retained endpoint of a heaviest branch give half of
Lemma 1(i), and `groundedConditionNumber_ge_of_lambda2_mul_le` turns every
Rayleigh upper bound on λ₂ into a lower bound on κ₂(B_r) with half the
constant.

Condition numbers of matrices that are not Laplacians are stated through
singular value bounds. If σmin‖z‖ ≤ ‖Kz‖ ≤ σmax‖z‖ for every z, the
theorems bound σmax/σmin from below. For an invertible matrix this is the
statement about κ₂, and for a singular matrix no positive σmin exists. This
is the form of Proposition 3 (`dcOpfNewton_condition_bound`), which holds for
every generation block, every generator map, and every positive choice of
the barrier weights, and of the AC flat start comparison
(`flatStart_blockDiagonal_condition_bound`). The latter uses the spectral
theorem to pass from singular value bounds of the symmetric positive
definite B_r to its eigenvalue condition number.

For each fixed connected Laplacian with distinct restricted extrema,
`SpectralHardPair.lean` constructs normalized extreme modes, the exact
inverse on the balanced subspace, the graph encoded preparation oracles,
and both hard input solve identities. The equal-extrema case has
`kappa_+ = 1` and is handled separately. The cited one-query hybrid result
then gives the worst case `Omega(kappa_+)` query lower bound. On corridor
families this is `Omega(n^2)`, which exceeds the nearly linear classical
upper bound. `hardPair_accurate_output_separates` proves the decision rule
of the proof: an output within relative accuracy ε < 1/√2 of one hard
solution is not within that accuracy of the other.

Write `U_p` for right hand side loading and `W_p` for coherent solution
state preparation. Pareek's QRAM estimate concerns the circuit depth of one
`U_p` call. The tomography lower bound counts calls to `W_p` and `W_p†`.
`clean_qls_worst_case_product` uses the hard pair to lower bound the fixed
number of `U_p` calls inside each `W_p`, then applies that schedule to the
tomography hard input. The readout treats `W_p` and `W_p†` as the opaque
oracle family quantified by the cited tomography theorem and is correct for
every valid extension. The tomography interface is instantiated directly on
the zero sum subspace, whose dimension is proved to be `n - 1`. The
elementary bound `n - 1 >= n / 2` preserves the stated
`tilde Omega(n kappa_+ / epsilon)` rate on one balanced injection.
`normalized_rhs_reaches_every_target` proves that every tomography target
direction is reachable by a normalized balanced right hand side.
`joint_hard_family_readout_lower_bound` uses one coded family throughout: a
fractional phase direct sum lower bound, Laplacian attenuation of the same
code, and a condition number comparison yield `Omega(n * kappa / epsilon)`
directly.

The effective condition number of input dependent solvers is defined as in
the letter's description. A cutoff μ is admissible for a solution direction
ψ at tolerance ε when the squared mass of ψ on the span of the eigenvectors
with eigenvalue below μ is at most ε², and κ_eff(ε) is λ_max divided by the
largest admissible cutoff. `inputDependentConditionNumber_hardPair` proves
κ_eff = κ₊ on both hard solutions for every ε < 1/√2. The count of PGLib
operating points with κ_eff(0.01) ≥ κ/2 is numerical evidence and is not a
Lean theorem.

The unit star witness is formalized on the full lossless space
`span(1)^perp`. Its balanced leaf space has dimension `n - 2` and
eigenvalue one; its radial mode has eigenvalue `n`. Local bus and branch
observable gaps are proved in `QueryHardness.lean`, and
`PaperClaims.proposition2_localObservable` composes their quarter-gap
distinction with the fixed solve schedule's `Omega(kappa)` right hand side
query bound. The DC OPF module derives the first and second directional
derivatives of the two-sided branch-flow log barrier and proves that its
angle Hessian is a positive weighted Laplacian at every strictly feasible
iterate.

The statements that remain outside Lean are the cited quantum query and
tomography theorems, the cited classical solver running times, the per
iteration cost discussion for Newton and interior point methods, and the
complexity class remarks on AC-OPF and unit commitment. They are listed in
`paper_claims.toml`.

See [`docs/claim-alignment.md`](docs/claim-alignment.md) for the claim
audit. The dependency audit is in
[`docs/lean-library-survey.md`](docs/lean-library-survey.md). The compiled
counterexamples to instancewise readings of the query bound are in
[`docs/query-lower-bound-counterexamples.md`](docs/query-lower-bound-counterexamples.md).
The recovery result and corpus conditions are in
[`docs/query-lower-bound-recovery.md`](docs/query-lower-bound-recovery.md).

## Layout

`PowerFlowLimits/Graph.lean` defines the oriented incidence structure,
endpoints, cuts, and degrees. `Laplacian.lean` builds the quadratic form
and voltage drop identities. `Connectivity.lean` connects path connectivity
to the kernel of the positive weighted Laplacian. `Eigenvalues.lean` defines
λ₂, λ_max, and κ₊ and proves the λ_max lower bounds, including the trace
bound through mathlib's spectral theorem. `EnergyNorm.lean` proves that κ₊
is the condition number on balanced injections and converts energy norm
accuracy into Euclidean accuracy. `CutBounds.lean` is Lemma 1;
`Separators.lean` is Theorem 1 and Corollary 1 with the topology only and
sharp variants; `TreeDecomposition.lean` builds the balanced bag;
`Planarization.lean` and `PlanarSeparator.lean` treat planar and near planar
grids; `Corridors.lean` is Proposition 1. `Grounded.lean` and
`GroundedTransfer.lean` prove the grounded matrix results.
`AnyDistribution.lean` states the topology only bounds for random line data,
and `Random.lean` keeps the Hoeffding result of the submitted version.
`BeyondDC.lean` proves uniform transfer under positive branch rescaling.
`EndToEnd.lean` contains target reachability, the fixed schedule product
theorem, its grid and corridor specializations, the direct corridor
comparison, QLS implementation accounting, the joint hard family product
theorem, and the classical comparison. `QueryHardness.lean` contains the
balanced star spectrum, coded attenuation identities, hard right hand
sides, and the local observable result. `SpectralHardPair.lean` constructs
those modes and the balanced inverse from an actual weighted graph.
`InputDependent.lean` proves the readout threshold, the effective condition
number result, and the HHL criterion arithmetic. `ACPowerFlow.lean` and
`ACFlatStart.lean` treat the first AC Newton system. `OptimalPowerFlow.lean`
and `DcOpfNewton.lean` treat the DC-OPF barrier block and Proposition 3.
`PaperClaims.lean` contains the 32 public wrappers. `experiments/` contains
the pinned 78 case publication survey, the validator, and the generated
summaries. The retained run covers all 66 canonical PGLib cases and 132
operating variants. Within the canonical PGLib cases, 61 separator
certificates and 64 treewidth certificates meet the stated thresholds, 39
of 45 required drawing tests meet the near planar threshold, 9 graphs are
exactly planar, and 46 support the direct positive susceptance model. These
are applicability diagnostics, not premises used to prove the universal
theorems.

## Building

Requires elan. From the repository root:

```
lake exe cache get
lake build PowerFlowLimits --wfail
lake lint
```

Toolchain: Lean 4 v4.28.0, mathlib v4.28.0.

## Computable obstruction certificates

`qpf-check` is a one sided checker for the full angle vector readout
policy. Acceptance means the exact cut lower bound on the DC Laplacian
condition number makes the policy's quantum lower bound strictly exceed its
classical SDD solve upper bound. Rejection is `INCONCLUSIVE`. It does not
certify quantum advantage, and it says nothing about easy right hand sides.

Build the Lean checker and run it on the retained vectors:

```sh
lake build qpf-check
lake exe qpf-check test-data/certificate/path4.model.qpf \
  test-data/certificate/full-readout.policy.qpf \
  test-data/certificate/path4.cut.qpf
```

The `qpf-model` exporter is a PowerIO development binary and is not in a
tagged PowerIO release yet. Set `POWERIO_ROOT` to a PowerIO checkout that
provides it, then generate and check a certificate:

```sh
scripts/qpf-cert case.m --out case.cut.qpf
scripts/qpf-check case.m policy.qpf case.cut.qpf
```

The wrapper reruns the PowerIO exporter for every check. The exporter
states each series susceptance b_e = 1/x_e as its binary64 bits, and the
checker decodes those bits as exact dyadic rationals. The checker never
recomputes `1/x` and never uses floating point arithmetic. The policy
records exact rational error, tomography, hybrid, and classical solve
constants. Example policy and certificate files are in
`test-data/certificate/`.

The executable accepts one connected positive weighted island. A
disconnected model, an invalid policy, an improper or zero weight cut, or
a failed inequality is `INCONCLUSIVE`, and every rejection prints a reason
line. A document that states a zero susceptance or an out of range
exponent, and any malformed document, is refused. Exit codes are 0 for
acceptance, 1 for `INCONCLUSIVE`, and 2 for malformed or unreadable input.
Per island aggregation and integer Rayleigh witnesses remain future
extensions; no component is silently discarded.

The executable kernel and parser are in `PowerFlowLimits/Certificate/`. The
soundness theorem `accepted_no_advantage_sound` states the PowerIO
correspondence assumptions explicitly and composes accepted cut bounds with
`kappaPlus_ge_totalWeight`. External query, tomography, and classical solve
results remain policy premises rather than axioms introduced by the
checker.

## Independent verification with Comparator

[`Challenge.lean`](Challenge.lean) contains exactly the 32 trusted theorem
statements. It imports only the independent, mathlib-based definitions in
`Challenge/Definitions.lean`. Comparator checks
`PowerFlowLimits/PaperClaims.lean` against that surface. The generated
settings are in [`comparator.json`](comparator.json).

First check that both modules build:

```
lake exe cache get
lake build PowerFlowLimits.PaperClaims Challenge.Definitions --wfail
lake build Challenge
python3 scripts/check_paper_claims.py
python3 scripts/audit_lean_trust.py
```

The Ubuntu verification workflow builds `landrun`, `lean4export`,
Comparator, and `nanoda` at immutable commits recorded in
[`.github/workflows/verification.yml`](.github/workflows/verification.yml).
It then runs Comparator under systemd isolation with both kernels enabled.
A matching local Linux installation can run:

```
systemd-run --property=RestrictAddressFamilies=AF_UNIX --user --pty \
  -E PATH="$PATH" --working-directory "$(pwd)" -- \
  bash -c 'lake env comparator comparator.json'
```

Success means that all declarations listed in `comparator.json` have
exactly the statements in `Challenge.lean`, are accepted by both kernels,
and use only `propext`, `Quot.sound`, and `Classical.choice`. The manifest
checker rejects a disabled `nanoda` setting.

On macOS, a local development wrapper can run the same comparison and
kernel replay without Linux sandbox isolation:

```
comparator-macos-unsafe comparator.json
```

The macOS command is a developer smoke test. Publication evidence requires
the Ubuntu job with real `landrun`, systemd isolation, and `nanoda`.

Project provenance, scope, fidelity notes, and declaration-level alignment
are recorded in [`formalization.yaml`](formalization.yaml).

## Authors

Cameron Khanpour and Samuel Talkington. MIT license.
