# Query and readout extensions

These modules collect results that are independent of the manuscript claim surface:

- `PowerFlowLimits.Extensions.QueryReadout` contains the unit star spectrum, coded right hand side
  attenuation, coded solve identity, joint direct sum arithmetic, and separate readout diagnostics.
- `PowerFlowLimits.Extensions.QueryCounterexamples` contains a diagonal family with arbitrary
  condition number that one uniform zero-query pass-through algorithm solves exactly.

The unit star supplies a positive weighted Laplacian witness. Its radial balanced mode has
eigenvalue `r+1`, while every zero-sum leaf codeword has eigenvalue one. The coded construction
places a common component in the fast mode and an informative component in a slow mode. Lean proves
that the prepared signal is attenuated by the inverse gain ratio and that solving recovers the
normalized coded state up to a scalar.

The joint lower bound is conditional on a fractional phase direct sum premise. Given that premise,
the coded attenuation estimate, and a comparison between the gain ratio and condition number, Lean
derives the `Omega(n * kappa / epsilon)` product and its grid and corridor specializations. This does
not formalize the external quantum direct sum theorem. The separate state readout diagnostics use
different worst case inputs and therefore yield a maximum of their lower bounds, not their product.

The diagonal counterexample limits what condition number alone can establish. A worst case or
distributional theorem must identify hard right hand sides; it cannot infer an instancewise matrix
oracle lower bound from a large condition number.

## Open matrix oracle route

A stronger result would embed a rigorous quantum linear systems matrix oracle lower bound into a
positive weighted grounded Laplacian while preserving all of the following:

1. nonpositive off-diagonal entries and the Laplacian row sum structure;
2. the required condition number;
3. a fixed hard input state;
4. constant overhead oracle query simulation.

The circuit clock matrices used by current general quantum linear systems lower bounds do not have
this graph Laplacian structure. No checked symmetrization, graph gadget, or Schur complement
construction in this repository establishes all four properties. That reduction remains open and
is not used by the manuscript Comparator or `PaperClaims` interface.
