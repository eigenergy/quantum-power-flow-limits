# Proposition 3 recovery

## Outcome

The worst case product in Proposition 3 is recovered for the QLS plus tomography
architecture used in the original proof. Fix a connected positive weighted Laplacian `B`, and put
`d = n - 1`. For every clean QLS readout procedure that succeeds on every normalized injection in
`span(1)^perp`, there is one normalized balanced injection `p` with total query cost

```text
tilde Omega(d * kappa_+(B) / epsilon).
```

Here clean means precisely the reusable oracle interface assumed by the cited tomography theorem:
for fixed `B`, the solver exposes a controlled solution preparation unitary `W_p` and its inverse,
implemented by one coherent circuit with a fixed query schedule `q_B` independent of `p`; the
readout treats these as the opaque preparation-oracle family quantified by the tomography theorem
and is correct for every valid unitary extension; and every internal query is counted. An adaptive
procedure must be coherently padded before it can supply this unitary and its inverse.

The multiplication is valid because the two lower bounds do not select two costs that depend on two
unrelated inputs. The balanced two-state construction forces the scalar schedule cost
`q_B = Omega(kappa_+(B))`. Tomography then selects a possibly different hard input `p_*`, but every
solution preparation on `p_*` invokes that same `q_B`-query circuit. Thus the tomography witness
itself pays both factors. Lean formalizes this quantifier transfer in
`clean_qls_worst_case_product` and its grid and corridor specializations.

This restores `tilde Omega(n^2/epsilon)` on the paper's sparse grid families and
`tilde Omega(n^3/epsilon)` on macroscopic corridor families, against the classical
`tilde O(n log(1/epsilon))` upper bound. No restriction beyond `p in span(1)^perp` is used. The
generator and load subspaces studied in the experiments are not premises of this theorem.

## Oracle model

### The two preparation unitaries

Pareek et al. use "state preparation" for loading the right hand side. Their `T_b` is the circuit
depth of one preparation of `|b>`. They give `T_b = O(N)` for an arbitrary preparation circuit and
`T_b = O(log N)` when a QRAM already contains the data. The QRAM assumption moves the initial data
load outside `T_b`; it does not make solution tomography polylogarithmic.

The tomography citation uses "state preparation unitary" for a different operation. In this
repository the two operations are:

```text
U_p : |0> -> |p>                  right hand side loading
W_p : |0> -> |B^+ p>/||B^+ p||   QLS solution preparation
```

Van Apeldoorn et al. prove that an `epsilon` accurate classical description of a `d` dimensional
pure state requires `tilde Theta(d/epsilon)` calls to `W_p` and `W_p^dagger` in their oracle model.
Pareek et al. state the same readout cost as `O(N/epsilon)` in Section IV.D and multiply it by the
cost of producing one solution copy. Their Figure 4 writes this composition as
`T_r * kappa * (T_b + T_s)` for HHL. Section IV.B also says that `|b>` must be prepared for each of
the `O(kappa)` repetitions.

The Lean cost ledger is therefore:

```text
qSolve    = U_p/U_p^dagger calls inside one W_p/W_p^dagger
calls(p)  = W_p/W_p^dagger calls made by tomography
total(p)  >= calls(p) * qSolve
```

`clean_qls_worst_case_product` proves the multiplication at this query level. Pareek's
polylogarithmic term is the circuit depth assigned to one QRAM backed `U_p` call, not the number of
`W_p` calls needed for readout. The paper sometimes writes `O(N/epsilon)` while calling it a
minimum complexity; the lower bound notation there should be `Omega` (and the cited result is
`tilde Theta`). That notation slip does not change the cost composition.

[Pareek et al., accepted manuscript](https://www.osti.gov/servlets/purl/3007530) and
[van Apeldoorn et al.](https://arxiv.org/abs/2207.08800) are the sources for these two distinct
costs.

`QLSOracleModel` records matrix oracle calls, right hand side preparation oracle calls, target state
error, observable error, and success probability separately. The primary construction uses
controlled access to `U_p` and `U_p^dagger`. For orthonormal fast and slow balanced eigenvectors,
define

```text
p_+ = (kappa u_fast + u_slow) / sqrt(kappa^2 + 1)
p_- = (kappa u_fast - u_slow) / sqrt(kappa^2 + 1).
```

Both are normalized elements of `span(1)^perp`. Their distance is
`2/sqrt(kappa^2+1)`, while the normalized solutions `(u_fast +/- u_slow)/sqrt(2)` are a constant
distance apart. `preparationOraclePlus` and `preparationOracleMinus` are explicit plane rotations:
they prepare the two states, are exact inverses, and their squared action difference on every vector
is `4/(kappa^2+1)` times its squared norm. The standard query hybrid therefore gives
`Omega(kappa_+)` right hand side oracle calls. The matrix oracle is the same in both cases.

`worst_case_corridor_qls_exceeds_classical` combines this hybrid lower bound, the quadratic corridor
condition, and the nearly linear classical upper bound in one theorem.

The tomography hard target is also a valid DCPF solution target. The formal tomography interface
is instantiated on `span(1)^perp`, and Lean proves that this subspace has dimension `n - 1`. Since
`n - 1 >= n / 2` for `n >= 2`, the cited dimension-linear lower bound retains its `Omega(n)`
factor. On `span(1)^perp`, a connected
Laplacian is invertible. For any nonzero target `theta`, the normalized injection

```text
p = B theta / ||B theta||
```

is balanced and normalized, and its normalized solution is `theta / ||theta||`. Lean proves the
abstract invertible-subspace statement in `normalized_rhs_reaches_every_target`.

The 2026 matrix oracle lower bound of Mori et al. uses non-Laplacian circuit clock matrices. No
known reduction found in this review simultaneously produces positive weighted grounded grid
Laplacians, retains `kappa = Theta(n)` or larger, fixes a freely prepared right hand side, and
simulates a grid oracle query with `O(1)` source queries. Symmetrization alone does not establish
the positive off-diagonal sign pattern, row sum structure, or grounded graph realization.

## Balanced worst case hard pair

For a connected Laplacian, write

```text
kappa_+(B) = lambda_max(B) / lambda_2(B).
```

This is the ordinary spectral condition number of `B` restricted to `span(1)^perp`; the plus sign
records that the zero eigenvalue on `span(1)` is omitted. It is also the condition number of the
Moore--Penrose inverse on the lossless injection space.

The coefficient calculations are

```text
||p_+ - p_-||^2 = 4/(kappa^2+1)
||theta_+ - theta_-||^2 = 2
B^+ p_+ proportional to theta_+
B^+ p_- proportional to theta_-.
```

Lean proves these identities in `prepared_sqDistance`, `solution_sqDistance`,
`inverseMap_preparedPlus`, and `inverseMap_preparedMinus`. It proves the concrete preparation oracle
identities in `preparationOraclePlus_prepares`, `preparationOracleMinus_prepares`, both composition
theorems, and `preparationOracle_gap_sq`. `hybrid_distance_le` and `rhs_query_lower_bound` formalize
the query hybrid arithmetic. The external quantum query fact is stated explicitly: one oracle call
can increase distinguishability by at most the operator distance of the two controlled oracles.

The coded star family and `joint_hard_family_readout_lower_bound` remain an independent direct-sum
construction. They are not needed for the recovered product theorem.

## Why “not already the solution” is insufficient

The condition `|p> != |theta>` excludes only exact pass through instances. It provides no lower
bound on their distance, no promise that low singular directions are activated, and no pair of
nearby inputs with separated outputs. States can differ by an arbitrarily small amount while
remaining easy, or differ substantially while lying in a well-conditioned invariant subspace.

The base operating point experiment therefore reports three diagnostics instead:

- phase invariant normalized distance between `|p>` and `|theta>`;
- truncation effective condition numbers at errors `0.001`, `0.01`, and `0.1`;
- the filtering factor `||A^-1 theta|| / (kappa ||theta||)` and low spectral solution mass.

The primary empirical condition is `kappa_eff(0.01) / kappa >= 1/2`. This says that the recorded
injection activates eigenvalues within a factor two of the smallest positive eigenvalue. It is not
a query lower bound. Dalzell, Li, and Su leave lower bounds below their effective condition number
open.

## Local observables

The intended observables are not arbitrary Hermitian matrices. They are

```text
M_i  = e_i e_i^T
M_ij = (e_i - e_j)(e_i - e_j)^T.
```

For hard normalized solution states `(u_min + u_max)/sqrt(2)` and
`(u_min - u_max)/sqrt(2)`, Lean proves the signed expectation differences

```text
2 u_min[i] u_max[i]
2 (u_min[i] - u_min[j]) (u_max[i] - u_max[j]).
```

Taking absolute values gives the paper's `gamma_i` and `gamma_ij`. Any listed local observable with
`gamma_M > 0` distinguishes the hard pair when additive estimation error is below `gamma_M/4`.
A constant precision corollary needs a uniform lower bound on `gamma_M / ||M||`; the experiment
reports the best normalized witness but does not assume such a lower bound.

The `M = I` theorem remains a regression test for the original unqualified statement. Its answer
is the known constant one for every normalized state. It does not refute the restricted local
observable theorem because `I` is outside the paper's intended class.

## Operational subspaces and corpus result

The spaces below are optional restrictions for a stronger claim about perturbations around one
fixed dispatch. They are not required for the general lossless DCPF lower bound, whose right hand
side domain is all of `span(1)^perp` and whose conditioning is exactly `kappa_+(B)`.

The experiment audits:

- `S_G`: balanced redispatch among generator buses with strictly positive upward and downward
  headroom;
- `S_G+L`: the same buses plus two-sided perturbations at buses with positive recorded load.

For every computed subspace it forms an orthonormal balanced support basis, applies the Laplacian
pseudoinverse, computes the extreme restricted singular values, reconstructs both singular
directions, constructs the hard pair, and checks solve, singular vector, balance, and support
residuals. The empirical condition is `kappa_S / kappa >= 1/2`.

The schema version 2 survey completed 78 primary systems with no case failure. It includes all 66
canonical PGLib cases, all 132 API/SAD operating variants, and 12 additional systems. Among the
primary systems:

- 56 satisfy the positive series susceptance model and 22 are unavailable under it;
- 45 receive spectral and operating point analysis, 11 exceed the 8,000-bus spectral limit, and
  22 fail the weight model;
- 44 of 45 recorded injections pass the effective conditioning condition;
- 3 generator subspaces pass `kappa_S / kappa >= 1/2` and 42 fail;
- 13 generator plus load subspaces pass, 9 fail, and 23 exceed the restricted SVD size limit;
- all 45 computed operating points have a nondegenerate bus or active branch witness.

Grounded slack sensitivity is reported separately and never substituted for the balanced primary
analysis. It is computed for the recorded reference bus in 27 primary cases and is indeterminate
under the 2,500-bus grounded size limit in 18. The grounded to balanced condition number ratio
ranges from `1.18` to `10.5` in the computed cases, confirming that slack choice can materially
change the numerical condition number.

The 132 PGLib variants receive separate injection and headroom analysis. Of these, 72 have computed
spectra through their canonical topology: 71 base injections pass, 6 generator subspaces pass, and
22 generator plus load subspaces pass. The other 60 are recorded as indeterminate because the
canonical topology fails the weight model or exceeds the spectral limit.

These counts reject the idea that the operational subspace condition is nonrestrictive across the
whole corpus. It selects a real subset, with `S_G+L` fitting substantially more cases than `S_G`.
The theorem is valid on that subset and scales with `kappa_S`, not automatically with the full
matrix condition number.

## Controlled corridors

Unit weight paths of lengths 8, 16, and 32 separate spectral conditioning from instance specific
conditioning:

| Right hand side | `kappa_eff(0.01) / kappa` behavior |
|---|---|
| largest-eigenvalue eigenvector | `0.0396`, `0.00970`, `0.00241`; fails |
| sparse endpoint transfer | `1`; passes |
| constructed hard pair | `1`; passes |

The easy family becomes arbitrarily ill conditioned as a matrix family while its selected right
hand side avoids the low spectrum. Sparse realistic transfer injections and the constructed hard
pair activate the full condition number on the same topology.

## Interpretation

The full balanced space is the lossless DCPF input domain. The recovered theorem has the stated
worst case order:

```text
for every fixed B and every clean QLS readout Q that succeeds for all p in span(1)^perp,
there exists p in span(1)^perp with T_Q(B,p) = tilde Omega(n kappa_+(B) / epsilon).
```

The product relies on the opaque oracle family and fixed coherent schedule required by the cited
tomography model. Reachability of target states alone would not suffice if a special unitary
extension leaked its classical amplitudes through other inputs, which is why correctness for every
valid extension is explicit. An architecture that gives the classical output direct side access to
`p`, rather than reading out a QLS solution state through this interface, is not the algorithm
described in the proof. The separate two-state theorem still gives
`Omega(kappa_+)` for any algorithm in the stated right hand side oracle model. The corpus subspaces
answer the separate fixed dispatch question and do not limit either worst case theorem.
