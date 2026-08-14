# Query lower bound counterexamples

The intended Proposition 3 is a worst case statement: every QLS algorithm has a hard power flow
input. The direct reduction must exhibit that input inside the lossless DCPF domain. It need not
show that every operating point is hard.

`DiagonalQLSAlgorithm.zero_query_solver_at_arbitrary_condition` gives a compiled counterexample.
For every real `kappa >= 1`, the matrix is `diag(1, 1/kappa)` and the right hand side is `e0`.
Its exact condition number is `kappa`, but its normalized solution is already `e0`. Passing the
prepared right hand side through uses zero matrix oracle queries. One uniform algorithm works for
the whole family. This does not dispute the cited worst case lower bound; it disproves the
instancewise reading of the claim.

A valid result must state a worst case or distributional lower bound over right hand sides. The
paper's readout levels follow Pareek et al.: `D >= 1` counts application outputs such as selected
bus angles or branch quantities. The local observable theorem therefore assumes a nonzero gap on
the hard pair and proves both the fixed solve query cost and distinguishability at quarter-gap
error. A condition number lower bound alone does not supply that reduction.

The recovered construction is now formalized in `PowerFlowLimits/QueryHardness.lean`. For every
fixed connected Laplacian, two lossless prepared right hand sides at squared distance
`4 / (kappa_+^2 + 1)` map to normalized solutions at squared distance `2`. Explicit plane rotation
oracles prepare the pair, are exact inverses, and have the required `O(1/kappa_+)` operator gap.
The exact bus and branch observable gaps are also proved for the paper's intended rank-one local
observables. A hybrid lower bound then counts right hand side preparation oracle calls. See
`docs/proposition-3-recovery.md` for the precise trust boundary and corpus results.

For full classical readout, the recovered proof does not require the two-state witness to be the
tomography witness. The two-state argument lower bounds the fixed query schedule of the controlled
QLS solution unitary and inverse. Tomography chooses the final hard balanced input, and every one of
its solution preparation calls pays that same schedule. Lean proves this single-input product in
`clean_qls_worst_case_product`.

The stronger matrix oracle route remains open. The circuit clock matrices in the current rigorous
QLS lower bound are not positive weighted grounded Laplacians, and no checked symmetrization or
Schur complement construction met the required sign pattern, row sum, conditioning, fixed input,
and constant query simulation criteria.
