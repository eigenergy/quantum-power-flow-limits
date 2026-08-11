# Proposition 3 formalization

## Result

Fix a connected positive weighted Laplacian `B` on `n >= 2` buses. The
formalized lossless input space is

```text
zeroSumSubspace n = {x : Fin n -> R | sum_i x_i = 0}.
```

For the fixed coherent QLS schedule and tomography interface stated in the
paper, Lean derives one balanced input with total query cost

```text
tilde Omega(n * kappa_+(B) / epsilon).
```

The grid and corridor wrappers then substitute linear and quadratic condition
growth, respectively. The quantum query and tomography lower bounds and the
classical comparison bounds enter through explicit theorem premises.

## Balanced hard pair

Let `u_fast` and `u_slow` be normalized extreme modes of `B` restricted to the
zero sum subspace. With `kappa = kappa_+(B)`, define

```text
p_plus  = (kappa * u_fast + u_slow) / sqrt(kappa^2 + 1)
p_minus = (kappa * u_fast - u_slow) / sqrt(kappa^2 + 1).
```

Both inputs are normalized and balanced. Their distance is
`2 / sqrt(kappa^2 + 1)`, while their normalized solutions are
`(u_fast + u_slow) / sqrt(2)` and `(u_fast - u_slow) / sqrt(2)`, a constant
distance apart.

`QueryHardness.lean` defines controlled preparation rotations for the two
inputs and proves their preparation, inverse, and operator gap formulas. Given
the standard one query hybrid progress premise, Lean derives the
`Omega(kappa)` lower bound on right hand side preparation queries. The matrix
oracle is fixed across the two instances.

## Fixed schedule product

The proof distinguishes two preparation operations:

```text
U_p : |0> -> |p>                  right hand side loading
W_p : |0> -> |B^+ p>/||B^+ p||   QLS solution preparation
```

For fixed `B`, one coherent implementation of `W_p` and `W_p^dagger` has a
fixed internal schedule of calls to `U_p` and `U_p^dagger`. The hard pair lower
bounds the length of this input independent schedule. The cited tomography
bound then selects one balanced target whose readout invokes that same
schedule `tilde Omega((n - 1)/epsilon)` times. Lean checks the multiplication
on that single final input; it does not multiply costs selected on unrelated
inputs.

The public tomography interface is stated for a finite dimensional real
Hilbert space and uses its `finrank`. It is instantiated with
`zeroSumSubspace n`. Lean proves

```text
finrank R (zeroSumSubspace n) = n - 1
n - 1 >= n / 2  when n >= 2.
```

The constant factor is absorbed into the asymptotic constant, leaving the
paper's `tilde Omega(n * kappa / epsilon)` rate unchanged.

## Reachability

Every nonzero target direction in the balanced space is a valid normalized
DCPF solution direction. Since a connected Laplacian is invertible on that
space, take

```text
p = B theta / ||B theta||.
```

This input is normalized and balanced, and its normalized solution has the
direction of `theta`. `normalized_rhs_reaches_every_target` proves this step.
The fixed schedule, grid, and corridor wrappers take targets in
`zeroSumSubspace n`, so balance follows from the target type.

## Local observables

The manuscript uses squared bus and branch quantities:

```text
M_i  = e_i e_i^T
M_ij = (e_i - e_j)(e_i - e_j)^T.
```

For the two hard solution states, Lean proves the signed expectation
differences

```text
2 u_slow[i] u_fast[i]
2 (u_slow[i] - u_slow[j]) (u_fast[i] - u_fast[j]).
```

Their absolute values are the displayed gaps. The public observable wrapper
keeps the condition `gamma > 0` and takes:

- the controlled preparation hybrid premise;
- the right hand side query count for one solve;
- the estimator's total observable query count;
- a premise that the estimator performs at least one QLS solve;
- additive error at most `gamma / 4` on both hard inputs.

It returns both

```text
solverGap * condition / hybridConstant <= observableQueries
```

and separation of the two estimates by at least `gamma / 2`. Thus every
relevant bus or branch observable with a positive gap inherits the solve query
lower bound.

## External premises

Lean proves the graph spectrum, hard pair, controlled rotations, hybrid cost
arithmetic, zero sum dimension, target reachability, observable gaps, and all
grid and corridor substitutions. The following results remain explicit cited
premises at the public boundary:

- the one query controlled preparation hybrid progress bound;
- the pure state tomography lower bound in the stated preparation unitary
  model;
- the classical SDD solve upper bound used for comparison;
- the dense state loading lower bound used for the no QRAM comparison.

`paper_claims.toml` records these dependencies for each affected wrapper, and
Comparator checks that the wrapper statements match `Challenge.lean`.
