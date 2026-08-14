# quantum-power-flow-limits

Lean 4 formalization of the numbered claims in *The Limits of Quantum
Computers for Power Flow* (Cameron Khanpour and Samuel Talkington), including
the worst case balanced injection result in Proposition 3. Every theorem in
`PowerFlowLimits/` compiles against mathlib with no `sorry`, and
every proof rests on only the standard axioms (`propext`, `Classical.choice`,
`Quot.sound`). `Challenge.lean` contains intentional `sorry` placeholders for
statement comparison and is not part of that claim.

`PowerFlowLimits/PaperClaims.lean` is the public claim surface. Its 17 wrappers
and their statuses are fixed in `paper_claims.toml`. Cited separator, quantum query,
classical SDD solve, and dense loading results enter as explicit theorem arguments;
every deduction from those arguments is checked by Lean. The same manifest freezes seven
empirical or discussion claims that are not presented as Lean theorems.

The paper's susceptance Laplacian B = Aᵀ diag(b) A with b_e > 0 is
`G.laplacian (fun _ => 1)` for a `WeightedGraph G` whose weights are the
branch susceptances. λ₂ and λ_max are defined variationally (sSup and sInf of
Rayleigh bound sets), and κ₊ = λ_max/λ₂ is `effectiveConditionNumber`.

## Statement correspondence

| Paper | Lean | File |
|---|---|---|
| Lemma 1(i), trace form | `two_totalWeight_div_le_lambdaMax` | `Eigenvalues.lean` |
| Classical SDD structure | `WeightedGraph.unitLaplacian_isSDD` | `Laplacian.lean` |
| Connected edge count `m >= n - 1` | `WeightedGraph.card_sub_one_le_edges` | `Connectivity.lean` |
| Lemma 1(i), edge form | `two_mul_weight_le_lambdaMax` | `Eigenvalues.lean` |
| Lemma 1(i), maximum-edge form | `exists_maxWeight_lambdaMax_bound` | `Eigenvalues.lean` |
| Lemma 1(ii) | `lambda2_le_cut_div`, `lambda2_mul_le_cut` | `CutBounds.lean` |
| Lemma 1, eq. (2) | `kappaPlus_ge_totalWeight`, `kappaPlus_ge_edge` | `CutBounds.lean` |
| Lemma 1, eq. (2), maximum edge | `exists_maxWeight_kappa_bound` | `CutBounds.lean` |
| Theorem 1 | `separator_kappa_bound` | `Separators.lean` |
| Positive weight rescaling transfer | `positiveRescaling_separator_kappa_bound` | `BeyondDC.lean` |
| Corollary 1(i) | `WeightedGraph.treewidth_kappa_bound_of_tree_decomposition` | `TreeDecomposition.lean` |
| Corollary 1(i), greedy grouping | `exists_quarter_half_subcollection` | `Separators.lean` |
| Corollary 1(i), component partition | `treewidth_kappa_bound_of_component_partition` | `Separators.lean` |
| Corollary 1(i), balanced bag | `treewidth_kappa_bound_of_balanced_bag` | `Separators.lean` |
| Corollary 1(i), centroid and bag existence | `RootedTreeDecomposition.exists_balanced_bag` | `TreeDecomposition.lean` |
| Corollary 1(ii), conditional partition bound | `kappa_bound_of_sqrt_separator_partition` | `Separators.lean` |
| Corollary 1(ii), `n >= 288` arithmetic | `planar_kappa_bound_of_lipton_partition` | `Separators.lean` |
| near planar conditional partition bound | `kappa_bound_of_near_planar_partition` | `Separators.lean` |
| Proposition 1 | `corridor_kappa_bound_of_topology`, `corridor_family_isBigOmega_quadratic` | `Corridors.lean` |
| Proposition 1 path-weight consequence | `corridorWeight_le_length_mul_bmax` | `Corridors.lean` |
| Proposition 2 | `random_kappa_bound`, `random_corridor_kappa_bound` | `Random.lean` |
| Proposition 3(i), worst case balanced hard pair | `RHSQueryHardness.prepared_sqDistance`, `preparationOracle_gap_sq`, `solution_sqDistance`, `rhs_query_lower_bound` | `QueryHardness.lean` |
| Proposition 3(i), corridor lower bound versus classical upper bound | `worst_case_corridor_qls_exceeds_classical` | `EndToEnd.lean` |
| Proposition 3(i), target reachability on the balanced space | `normalized_rhs_reaches_every_target` | `EndToEnd.lean` |
| Proposition 3(i), recovered worst case readout product | `clean_qls_worst_case_product` (+ `_grid`, `_corridor`), `clean_qls_grid_product_exceeds_nearly_linear` | `EndToEnd.lean` |
| Proposition 3(i), QLS implementation product accounting | `e2e_query_lower_bound` (+ `_grid`, `_corridor`) | `EndToEnd.lean` |
| Proposition 3(i), joint hard family product lower bound | `joint_hard_family_readout_lower_bound` (+ `_grid`, `_corridor`), `joint_product_exceeds_classical` | `EndToEnd.lean` |
| Proposition 3(i), exact balanced star witness | `RHSQueryHardness.starLaplacianAction_fast`, `starLaplacianAction_slow`, `starLaplacian_rayleigh_lower`, `starLaplacian_rayleigh_upper` | `QueryHardness.lean` |
| Proposition 3 instancewise query counterexample | `DiagonalQLSAlgorithm.zero_query_solver_at_arbitrary_condition` | `Counterexamples.lean` |
| Proposition 3 balanced hard inputs and local observables | `RHSQueryHardness.balancedPrepared_sqDistance`, `balancedSolution_sqDistance`, `bus_observable_gap`, `branch_observable_gap`, `rhs_query_lower_bound` | `QueryHardness.lean` |
| Separate tomography and two-state diagnostics | `qls_state_readout_lower_bound` (+ `_grid`, `_corridor`), `corridor_rhs_oracle_exceeds_classical` | `EndToEnd.lean` |
| Flat start AC block | `WeightedGraph.acAngleJacobian_flat_eq_laplacian` | `ACPowerFlow.lean` |

Beyond the paper, two strengthenings are proved in full. Theorem 1 holds with
the denominator s·Δ·b_max replaced by the interface stiffness Σ_{x∈X} d_x,
which it always dominates (`separator_kappa_bound_sharp`), and λ_max ≥ d_i
gives the hub bound κ₊ ≥ γ(1-γ)·n·d_i/b(∂S) for every node
(`kappaPlus_ge_weightedDegree`), which beats the paper's per-edge term at any
node with three or more comparably stiff branches.

## What is proved and what is hypothesized

Lemma 1, Theorem 1, Proposition 1, and the separator event in Proposition 2
are proved from explicit hypotheses, including the Hoeffding concentration
step through mathlib's sub-Gaussian API. `CombinatoriallyConnected` is ordinary
path connectivity of the underlying graph. The weighted drop map proves that
positive weights and ordinary connectivity imply `lambda2 > 0`; the numbered
conditioning theorems now derive spectral positivity rather than assume it.

Corollary 1(i) is proved from a standard rooted tree decomposition, including the weighted
centroid argument that produces the balanced bag. Corollary 1(ii) takes the quantitative output
of the cited Lipton--Tarjan theorem as an explicit premise because that theorem is not in mathlib.
For each fixed connected Laplacian with distinct restricted extrema, `SpectralHardPair.lean`
constructs normalized extreme modes, the exact inverse on the balanced subspace, the graph
encoded preparation oracles, and both hard input solve identities. The equal-extrema case has
`kappa_+ = 1` and is handled separately. The cited one-query hybrid result then gives the worst
case `Omega(kappa_+)` query lower bound. On corridor families this is `Omega(n^2)`, which exceeds
the nearly linear classical upper bound. Write `U_p` for right hand side loading and `W_p`
for coherent solution state preparation. Pareek's QRAM estimate concerns the circuit depth of one
`U_p` call. The tomography lower bound counts calls to `W_p` and `W_p†`.
`clean_qls_worst_case_product` uses the hard pair to lower bound the fixed number of `U_p` calls
inside each `W_p`, then applies that schedule to the tomography hard input. The readout treats
`W_p` and `W_p†` as the opaque oracle family quantified by the cited tomography theorem and is
correct for every valid extension. The tomography interface is instantiated directly on the zero
sum subspace, whose dimension is proved to be `n - 1`; the elementary bound `n - 1 >= n / 2`
preserves the stated `tilde Omega(n kappa_+ / epsilon)` rate on one balanced injection.
`normalized_rhs_reaches_every_target` proves that every tomography target direction is reachable
by a normalized balanced right hand side. `joint_hard_family_readout_lower_bound`
uses one coded family throughout: a fractional phase direct sum lower bound, Laplacian attenuation
of the same code, and a condition number comparison yield `Omega(n * kappa / epsilon)` directly.
The unit star witness is formalized on the full lossless space `span(1)^perp`; its balanced leaf
space has dimension `n - 2`, eigenvalue one, and its radial mode has eigenvalue `n`. Local bus and
branch observable gaps are proved in `QueryHardness.lean`, and
`PaperClaims.proposition3_localObservable` composes their quarter-gap distinction with the fixed
solve schedule's `Omega(kappa)` right hand side query bound. The
grounded trace correction, Poincare separation, positive definiteness,
and corrected condition-number transfer are proved. The DC OPF module derives the first and second
directional derivatives of the two-sided branch-flow log barrier and proves that its angle Hessian
inherits the separator bound at every strictly feasible iterate. See
[`docs/claim-alignment.md`](docs/claim-alignment.md) for the claim audit.
The dependency audit is in [`docs/lean-library-survey.md`](docs/lean-library-survey.md).
The compiled counterexamples to Proposition 3's query inference are in
[`docs/query-lower-bound-counterexamples.md`](docs/query-lower-bound-counterexamples.md).
The recovery result and corpus conditions are in
[`docs/proposition-3-recovery.md`](docs/proposition-3-recovery.md).

## Layout

`PowerFlowLimits/Graph.lean` defines the oriented incidence structure,
endpoints, cuts, and degrees. `Laplacian.lean` builds the quadratic form and
voltage drop identities. `Connectivity.lean` connects path connectivity to
the kernel of the positive weighted Laplacian. `Grounded.lean` proves the
slack bus trace correction, Poincare separation, positive definiteness, and
grounded condition-number transfer. `Eigenvalues.lean` defines λ₂, λ_max, and κ₊ and
proves the λ_max lower bounds, including the trace bound through mathlib's
spectral theorem. `CutBounds.lean` is Lemma 1; `Separators.lean` is Theorem 1
and Corollary 1 plus the sharp variant; `Corridors.lean` is Proposition 1;
`Random.lean` proves the separator and corridor parts of Proposition 2;
`BeyondDC.lean` proves uniform transfer under positive branch rescaling;
`EndToEnd.lean` contains target reachability, the recovered fixed schedule product theorem, its grid
and corridor specializations, the direct corridor comparison, QLS implementation accounting, the
joint hard family product theorem, and the classical comparison.
`QueryHardness.lean` contains the balanced star spectrum, coded attenuation identities, hard right
hand sides, and local observable result. `SpectralHardPair.lean` constructs those modes and the
balanced inverse from an actual weighted graph. `PaperClaims.lean` contains the 17 public wrappers.
`experiments/` contains the pinned 78 case publication survey, validator, and generated summaries.
The retained run covers all 66 canonical PGLib cases and 132 operating variants. Within the
canonical PGLib cases, 61 separator certificates and 64 treewidth certificates meet the stated
thresholds, 39 of 45 required drawing tests meet the near planar threshold, 9 graphs are exactly
planar, and 46 support the direct positive susceptance model. These are applicability diagnostics,
not premises used to prove the universal theorems.

## Building

Requires elan. From the repository root:

```
lake exe cache get
lake build PowerFlowLimits --wfail
lake lint
```

Toolchain: Lean 4 v4.28.0, mathlib v4.28.0.

## Computable obstruction certificates

`qpf-check` is a one sided checker for the full angle vector readout policy. Acceptance means
that the exact cut lower bound on the DC Laplacian condition number makes the policy's quantum
lower bound strictly exceed its classical SDD solve upper bound. Rejection is `INCONCLUSIVE`; it
does not certify quantum advantage and says nothing about easy right hand sides.

Build the Lean checker and PowerIO exporter:

```sh
lake build qpf-check
cargo build --manifest-path /path/to/powerio/Cargo.toml \
  -p powerio-capi --features matrix --bin qpf-model
```

Generate and check a certificate:

```sh
scripts/qpf-cert case.m --out case.qpfcert
scripts/qpf-check case.m policy.qpf case.qpfcert
```

The wrapper reruns the pinned PowerIO `PaperPure` extractor for every check. Susceptances cross
the boundary as their binary64 bits and are decoded as exact dyadic rationals; the checker never
recomputes `1/x` and never uses floating point arithmetic. The policy records exact rational
error, tomography, hybrid, and classical solve constants. Example policy and certificate files
are in `test-data/certificate/`.

The current executable accepts one connected positive weighted island. A disconnected case,
zero reactance, nonfinite or nonpositive susceptance, malformed witness, or failed inequality is
`INCONCLUSIVE`. Per island case aggregation and integer Rayleigh witnesses remain future
extensions; no component is silently discarded.

The executable kernel and parser are in `PowerFlowLimits/Certificate/`. Its soundness theorem
`accepted_no_advantage_sound` states the PowerIO correspondence assumptions explicitly and
composes accepted cut bounds with `kappaPlus_ge_totalWeight`. External query, tomography, and
classical solve results remain policy premises rather than axioms introduced by the checker.

## Independent verification with Comparator

[`Challenge.lean`](Challenge.lean) contains exactly the 17 trusted theorem
statements. It imports only the independent, Mathlib-based definitions in
`Challenge/Definitions.lean`. Comparator checks
`PowerFlowLimits/PaperClaims.lean` against that surface. The generated settings
are in [`comparator.json`](comparator.json).

First check that both modules build:

```
lake exe cache get
lake build PowerFlowLimits.PaperClaims Challenge.Definitions --wfail
lake build Challenge
python3 scripts/check_paper_claims.py
python3 scripts/audit_lean_trust.py
```

The Ubuntu verification workflow builds `landrun`, `lean4export`, Comparator,
and `nanoda` at immutable commits recorded in
[`.github/workflows/verification.yml`](.github/workflows/verification.yml).
It then runs Comparator under systemd isolation with both kernels enabled.
A matching local Linux installation can run:

```
systemd-run --property=RestrictAddressFamilies=AF_UNIX --user --pty \
  -E PATH="$PATH" --working-directory "$(pwd)" -- \
  bash -c 'lake env comparator comparator.json'
```

Success means that all declarations listed in `comparator.json` have exactly
the statements in `Challenge.lean`, are accepted by both kernels, and use only
`propext`, `Quot.sound`, and `Classical.choice`. The manifest checker rejects a
disabled `nanoda` setting.

On macOS, a local development wrapper can run the same comparison and kernel
replay without Linux sandbox isolation:

```
comparator-macos-unsafe comparator.json
```

The macOS command is a developer smoke test. Publication evidence requires the
Ubuntu job with real `landrun`, systemd isolation, and `nanoda`.

Project provenance, scope, fidelity notes, and declaration-level alignment
are recorded in [`formalization.yaml`](formalization.yaml)

## Authors

Cameron Khanpour and Samuel Talkington. MIT license.
