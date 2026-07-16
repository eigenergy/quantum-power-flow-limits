# quantum-power-flow-limits

Lean 4 formalization of the numbered claims in *The Limits of Quantum
Computers for Power Flow* (Cameron Khanpour and Samuel Talkington). Every
theorem in the proof implementation compiles against mathlib with no `sorry`,
and every proof rests on only the standard axioms (`propext`,
`Classical.choice`, `Quot.sound`).

The paper's susceptance Laplacian B = Aᵀ diag(b) A with b_e > 0 is
`G.laplacian (fun _ => 1)` for a `WeightedGraph G` whose weights are the
branch susceptances. λ₂ and λ_max are defined variationally (sSup and sInf of
Rayleigh bound sets), and κ₊ = λ_max/λ₂ is `effectiveConditionNumber`.

## Statement correspondence

| Paper | Lean | File |
|---|---|---|
| Lemma 1(i), trace form | `two_totalWeight_div_le_lambdaMax` | `Eigenvalues.lean` |
| Lemma 1(i), edge form | `two_mul_weight_le_lambdaMax` | `Eigenvalues.lean` |
| Lemma 1(ii) | `lambda2_le_cut_div`, `lambda2_mul_le_cut` | `CutBounds.lean` |
| Lemma 1, eq. (2) | `kappaPlus_ge_totalWeight`, `kappaPlus_ge_edge` | `CutBounds.lean` |
| Theorem 1 | `separator_kappa_bound` | `Separators.lean` |
| Corollary 1(i) | `treewidth_kappa_bound` | `Separators.lean` |
| Corollary 1(ii) | `planar_kappa_bound` | `Separators.lean` |
| near-planar remark | `near_planar_kappa_bound` | `Separators.lean` |
| Proposition 1 | `corridor_kappa_bound` | `Corridors.lean` |
| Proposition 2 | `random_kappa_bound` | `Random.lean` |
| Proposition 3(i) | `e2e_query_lower_bound` (+ `_grid`, `_corridor`) | `EndToEnd.lean` |
| Proposition 3(ii) | `e2e_observable_lower_bound` | `EndToEnd.lean` |

Beyond the paper, two strengthenings are proved in full. Theorem 1 holds with
the denominator s·Δ·b_max replaced by the interface stiffness Σ_{x∈X} d_x,
which it always dominates (`separator_kappa_bound_sharp`), and λ_max ≥ d_i
gives the hub bound κ₊ ≥ γ(1-γ)·n·d_i/b(∂S) for every node
(`kappaPlus_ge_weightedDegree`), which beats the paper's per-edge term at any
node with three or more comparably stiff branches.

## What is proved and what is hypothesized

Lemma 1, Theorem 1, and Propositions 1 and 2 are proved unconditionally,
including the Hoeffding concentration step of Proposition 2 (through
mathlib's sub-Gaussian API). Two claims take cited inputs as hypotheses,
mirroring the paper's own proofs: Corollary 1 assumes the separator existence
(tree decomposition machinery and the Lipton–Tarjan separator theorem are not
in mathlib), and Proposition 3 assumes the quantum query facts (F1) and (F2);
its verified content is the arithmetic chaining. Proposition 2 additionally
records pointwise boundedness, per-outcome connectivity, and 0 < m,
0 < s·Δ·b_max as explicit regularity hypotheses.

## Layout

`PowerFlowLimits/Graph.lean` defines the oriented incidence structure,
endpoints, cuts, and degrees. `Laplacian.lean` builds the quadratic form and
voltage drop identities. `Eigenvalues.lean` defines λ₂, λ_max, and κ₊ and
proves the λ_max lower bounds, including the trace bound through mathlib's
spectral theorem. `CutBounds.lean` is Lemma 1; `Separators.lean` is Theorem 1
and Corollary 1 plus the sharp variant; `Corridors.lean` is Proposition 1;
`Random.lean` is Proposition 2; `EndToEnd.lean` is Proposition 3.

## Building

Requires elan. From the repository root:

```
lake exe cache get
lake build
```

Toolchain: Lean 4 v4.28.0, mathlib v4.28.0.

## Independent verification with Comparator

[`Challenge.lean`](Challenge.lean) is the small, trusted statement surface for
the manuscript results. It imports only Mathlib and repeats the
project-specific definitions needed to read those statements. The existing
`PowerFlowLimits` module is the solution checked against it. The settings are
in [`comparator.json`](comparator.json).

First check that both modules build:

```
lake exe cache get
lake build Challenge PowerFlowLimits
```

To run [Comparator](https://github.com/leanprover/comparator), install
`landrun` from its `main` branch and build both `lean4export` and Comparator at
tag `v4.28.0`, matching this repository's Lean toolchain. Put the three
binaries on `PATH`. On a Linux system with user `systemd`, run Comparator using
its currently recommended sandbox wrapper:

```
systemd-run --property=RestrictAddressFamilies=~AF_UNIX --user --pty \
  -E PATH="$PATH" --working-directory "$(pwd)" -- \
  bash -c 'lake env comparator comparator.json'
```

Success means that all declarations listed in `comparator.json` have exactly
the statements in `Challenge.lean`, are accepted by the Lean kernel, and use
only `propext`, `Quot.sound`, and `Classical.choice`. Comparator's optional
independent `nanoda` kernel can be enabled by installing it and changing
`enable_nanoda` in the config.

Project provenance, scope, fidelity notes, and declaration-level alignment
are recorded in [`formalization.yaml`](formalization.yaml)

## Authors

Cameron Khanpour and Samuel Talkington. MIT license.
