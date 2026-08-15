# Public claim ledger

This ledger maps the public preprint to its Lean declarations. It distinguishes a proved claim
from arithmetic proved after importing a cited quantum lower bound as a hypothesis. A row is
complete only when its source claim and Lean declaration have the same model, quantifiers,
constants, and dependencies.

| ID | Original letter claim | Lean declaration or target | Status |
|---|---|---|---|
| M0 | Positive weighted branch incidence defines the susceptance Laplacian | `WeightedGraph`, `WeightedGraph.laplacian` | Proved model |
| M1 | Connected grid means ordinary path connectivity | `WeightedGraph.CombinatoriallyConnected` | Defined |
| M2 | Positive weights and path connectivity imply `lambda₂ > 0` | `combinatoriallyConnected_implies_spectralConnected` | Proved |
| F1a | Every QLS algorithm has a worst case input requiring `Omega(kappa)` oracle queries | `RHSQueryHardness.preparationOracle_gap_sq`, `hybrid_distance_le`, `rhs_query_lower_bound` | Proved for the explicit balanced hard pair after importing the standard one-query hybrid progress bound; easy inputs are irrelevant to this worst case quantifier |
| F1b | A QLS algorithm attains the matching conditioning dependence | quantum algorithm upper bound target | Not formalized |
| F2a | Classical pure-state magnitude recovery needs `tilde Omega(d/epsilon)` controlled calls to the solution preparation unitary `W_p` and its inverse | `clean_qls_worst_case_product` tomography premise | Imported from van Apeldoorn et al.; the hard family is real and nonnegative |
| F2b | Each `W_p` or `W_p^dagger` call pays the fixed internal schedule of right hand side loading calls `U_p` and `U_p^dagger` | `clean_qls_worst_case_product` | Proved as explicit cost composition on one tomography hard input; Pareek's QRAM `O(log n)` term is the depth assigned to one `U_p` call |
| F2c | Dense classical loading without QRAM costs `Omega(n)` gates | input oracle and gate model target | Not formalized |
| F3a | The classical Laplacian is SDD | `WeightedGraph.unitLaplacian_isSDD` | Proved |
| F3b | Classical solve time is `tilde O(m log(1/epsilon))` | classical algorithm and cost model target | Not formalized |
| F3c | Combinatorial preconditioning makes conditioning dependence logarithmic | preconditioner model target | Not formalized |
| L1.1 | `lambda_max >= 2 b(E)/(n-1)` | `two_totalWeight_div_le_lambdaMax` | Proved |
| L1.2 | `lambda_max >= 2 max_e b_e` | `exists_maxWeight_lambdaMax_bound` | Proved |
| L1.3 | Cut Rayleigh bound for `lambda₂` | `lambda2_le_cut_div`, `lambda2_mul_le_cut` | Proved |
| L1.4 | Total-weight condition number consequence | `kappaPlus_ge_totalWeight` | Proved from ordinary connectivity |
| L1.5 | Maximum-edge condition number consequence | `exists_maxWeight_kappa_bound` | Proved |
| T1.1 | Every boundary edge of `A union X` meets `X` | `boundaryEdges_subset_incident` | Proved |
| T1.2 | `b(partial S) <= s Delta b_max` | internal theorem in `separator_kappa_bound`; extraction target | Proved internally |
| T1.3 | Separator condition number bound with exact constant | `separator_kappa_bound` | Proved from ordinary connectivity and an explicit partition |
| C1.1 | Width `tau` gives a bag of at most `tau+1` whose removal has components of size at most `n/2` | `FiniteRootedTree.exists_weighted_centroid_component_bound`, `RootedTreeDecomposition.exists_balanced_bag`, `WeightedGraph.exists_balanced_bag_of_tree_decomposition` | Proved from the standard vertex coverage, edge coverage, and connected bag occurrence axioms |
| C1.2 | Greedy component grouping gives a `(tau+1,1/4)` separation | `component_partition_has_quarter_separation` | Proved from the component partition left by the bag |
| C1.2a | Connectedness gives `m >= n-1` in the Corollary 1 proof | `WeightedGraph.card_sub_one_le_edges` | Proved using mathlib's spanning-tree theorem |
| C1.3 | Treewidth condition number bound with constant `3/8` | `WeightedGraph.treewidth_kappa_bound_of_tree_decomposition` | Proved end to end from a width-at-most-`tau` rooted tree decomposition when `tau+1 <= floor(n/4)` |
| C1.4 | Lipton–Tarjan gives the stated planar separation | planar embedding and separator theorem target | Not formalized |
| C1.5 | `n >= 288` turns the Lipton--Tarjan partition into a `1/6` balanced partition | `sqrt_eight_mul_card_le_sixth`, `planar_kappa_bound_of_lipton_partition` | Proved from the quantitative separator output |
| C1.6 | Planar condition number bound with constant `5/18` | `kappa_bound_of_sqrt_separator_partition` | Arithmetic proved; separator existence is a hypothesis |
| NP1 | Planarizing `c` crossings gives separator size `O(sqrt(n+c))` balanced on original buses | planarization and Lipton--Tarjan's vertex cost separator target | Not formalized |
| P1.1 | Corridor topology matches the induced path and endpoint restrictions | `CorridorTopology`, `corridor_kappa_bound_of_topology` | Proved with an exact indexed path, disjoint vertex cover, and nonpath endpoint restrictions |
| P1.2 | Corridor bound `2 beta² (ell-1)² b(E)/b(E_P)` | `corridor_kappa_bound` | Proved from ordinary connectivity |
| P1.3 | `b(E_P) <= (ell-1)b_max` | `corridorWeight_le_length_mul_bmax` | Proved from the defining cardinality `|E_P| = ell-1` |
| P1.4 | Macroscopic corridor in a sparse family gives `Omega(n²)` | `corridor_kappa_quadratic_bound`, `corridor_family_isBigOmega_quadratic` | Proved using mathlib's `IsBigO atTop`; connectedness gives the only edge-count lower bound needed |
| P1.5 | `ell=2` recovers the tie line case | `two_bus_corridor_kappa_bound` | Proved as a single interface branch; the corridor coefficient is `2 beta²`, so “recovers” means the mechanism and order, not equality with Theorem 1's `2 beta(1-beta)` coefficient |
| P2.1 | Independent bounded positive susceptances satisfy the Hoeffding lower tail | internal proof of `random_kappa_bound` | Proved |
| P2.2 | Separator condition bound holds with the stated probability and exponent | `random_kappa_bound` | Proved from ordinary connectivity per outcome |
| P2.3 | The same substitution transfers to Corollary 1 | `random_treewidth_kappa_bound`, `random_kappa_bound_of_sqrt_separator_partition` | Proved conditional on the separator partitions |
| P2.4 | The same substitution transfers to Proposition 1 | `random_corridor_kappa_bound` | Proved |
| P2.5 | Bounded susceptances are sub-Gaussian | mathlib `HasSubgaussianMGF` bridge | Used and proved in context |
| G1 | A grid family has the exact stated deterministic or high-probability bounds | `separator_family_isBigOmega_linear`, `corridor_family_isBigOmega_quadratic`, `random_kappa_bound_exponential` | Deterministic separator and corridor families are proved using mathlib `IsBigO atTop`; a positive mean-to-maximum ratio gives the explicit probability floor `1 - exp(-2 epsilon² rho² m)` |
| P3.1 | Every QLS algorithm has a hard lossless DCPF injection costing `Omega(kappa_+)` | `RHSQueryHardness.prepared_sqDistance`, `solution_sqDistance`, `preparationOracle_gap_sq`, `rhs_query_lower_bound` | Proved for every fixed connected Laplacian in the controlled right hand side preparation oracle model; both inputs lie in `span(1)^perp` and the matrix oracle is fixed |
| P3.2 | Corridor grid families give a quantum lower bound above the nearly linear classical upper bound | `worst_case_corridor_qls_exceeds_classical` | Proved: `kappa_+ = Omega(n²)` yields an `Omega(n²)` worst case right hand side query lower bound, which exceeds the classical `tilde O(n)` bound above the explicit threshold |
| P3.3 | One intended local observable costs `Omega(kappa)` on the hard pair when its gap is nonzero | `PaperClaims.proposition3_localObservable`, `RHSQueryHardness.bus_observable_gap`, `RHSQueryHardness.branch_observable_gap` | Proved for the paper's bus and branch rank-one observables by composing the fixed solve schedule lower bound with quarter-gap distinguishability |
| P3.4 | Clean QLS readout costs `tilde Omega(n kappa_+/epsilon)` on one worst case balanced injection | `finrank_zeroSumSubspace`, `clean_qls_worst_case_product`, `PaperClaims.proposition3_fixedScheduleReadout` | Proved on the `n-1` dimensional zero sum subspace; `n-1 >= n/2` for `n >= 2` preserves the stated asymptotic rate and the fixed coherent schedule supplies the condition factor |
| P3.4a | Grid and corridor families give `tilde Omega(n²/epsilon)` and `tilde Omega(n³/epsilon)` | `clean_qls_worst_case_grid_product`, `clean_qls_worst_case_corridor_product`, `clean_qls_grid_product_exceeds_nearly_linear` | Proved with explicit structural and sparse classical comparison premises |
| P3.5 | The hard injection conclusion applies to every QLS solver in the stated oracle model | `RHSQueryHardness.preparationOracle_gap_sq`, `hybrid_distance_le`, `rhs_query_lower_bound` | Proved from the standard query hybrid premise for arbitrary algorithms using the controlled right hand side preparation oracle and its inverse |
| P3.6 | The canonical hard pair is normalized, lossless, and has input distance `2/sqrt(kappa²+1)` | `RHSQueryHardness.preparedPlus_normalized`, `preparedMinus_normalized`, `prepared_sqDistance`, `BalancedModePair.embed_balanced` | Proved |
| P3.7 | Canonical preparation unitaries realize the hard pair and differ by `2/sqrt(kappa²+1)` in operator norm | `RHSQueryHardness.preparationOraclePlus_prepares`, `preparationOracleMinus_prepares`, both composition theorems, `preparationOracle_gap_sq` | Proved exactly as real orthogonal plane rotations |
| P3.8 | The normalized solutions remain a constant distance apart | `RHSQueryHardness.inverseMap_preparedPlus`, `inverseMap_preparedMinus`, `solution_sqDistance`, `solve_balancedPreparedPlus`, `solve_balancedPreparedMinus` | Proved |
| P3.9 | The quadratic corridor lower bound exceeds the nearly linear classical upper bound | `worst_case_corridor_qls_exceeds_classical` | Proved above the displayed constant and logarithmic threshold |
| P3.10 | The full readout product holds for every clean QLS readout with a fixed coherent schedule | `clean_qls_worst_case_product` and its grid and corridor specializations | Proved with one final hard input; the hard pair lower bounds the input-independent schedule and tomography selects the input |
| P3.11 | Bus and branch observables inherit the hard-pair distinction at error below one quarter of a nonzero gap | `PaperClaims.proposition3_localObservable`, `RHSQueryHardness.bus_observable_gap`, `branch_observable_gap` | Proved for the stated nonzero-gap application observables, including their inherited right hand side query lower bound |
| AC1 | The flat start AC Jacobian is governed by the same Laplacian blocks | `WeightedGraph.hasDerivAt_acActiveInjection_line`, `WeightedGraph.acAngleJacobian_eq_laplacian`, `WeightedGraph.acAngleJacobian_flat_eq_laplacian` | The lossless unit-voltage active-angle block and its calculus certificate are proved; other AC blocks remain |
| AC2 | Conditioning can degrade away from flat start | certified counterexample or monotonicity target | Not formalized |
| AC3 | Newton iterations pay tomography cost per classical iterate | iterative algorithm/composition target | Not formalized |
| OPF1 | Each DC-OPF IPM network block is a positive weighted Laplacian | `WeightedGraph.hasDerivAt_dcOpfBranchBarrierAlongLine`, `WeightedGraph.hasDerivAt_dcOpfBranchBarrierDerivativeAlongLine`, `WeightedGraph.dcOpfNetworkBlock_eq_laplacian` | Proved for the angle Hessian of the two-sided branch-flow log barrier at every strictly feasible iterate; a complete KKT system with the remaining DC-OPF terms is not yet modeled |
| OPF2 | The separator theorem applies at every positive weighted IPM network block | `WeightedGraph.dcOpfBarrierScale_pos`, `WeightedGraph.dcOpfNetworkBlock_separator_kappa_bound` | Proved for the modeled branch-flow barrier block with its exact iterate-dependent weights |
| OPF3 | Barrier weight spread only degrades conditioning near convergence | exact comparison theorem or Lean counterexample target | Not formalized |
| OPF4 | Quantum IPMs compound readout over `tilde O(sqrt n)` iterations | quantum IPM cost model target | Not formalized |
| NP2 | Polynomial quantum algorithms for the stated NP-hard layers imply `NP subset BQP` | reduction and complexity-class model target | Not formalized |
| NP3 | Oracle search speedups are at most quadratic | BBBV oracle theorem target | Not formalized |
| HY1 | Variational and decomposition hybrids retain the stated barriers | explicit hybrid models and lower-bound targets | Not formalized |
| GR1a | Grounding removes the slack weighted degree from the trace | `groundedLaplacian_trace_eq`, `groundedLaplacian_trace_correction` | Proved |
| GR1b | Poincare separation gives `lambda_min(B_r) <= lambda₂(B)` | `groundedEigenvalueMin_le_lambda2` | Proved |
| GR1c | The corrected grounded trace and interlacing transfer each condition bound | `corrected_trace_over_lambda2_le_groundedConditionNumber` | Proved when the corrected trace is nonnegative |
| E1 | The empirical table supports the claimed exponents | certified data, parser, and regression certificates | Python evidence only; not a Lean theorem |
| E2 | Large interconnections exhibit the asserted weak ties and oscillations | cited observational data certificates | External empirical claim |

## Current trust boundary

The proof modules contain no `sorry` or `proof_wanted`. Their axiom closure is limited to
`propext`, `Quot.sound`, and `Classical.choice`. Comparator checks the declarations listed in
`comparator.json` against the independent `Challenge.lean` statements. The current Comparator
surface proves exact statement identity for the completed structural declarations; it does not
turn the rows marked incomplete into proved claims.

The next structural dependency is planar separator existence. The balanced hard pair, canonical preparation
oracles, query hybrid arithmetic, target reachability, fixed schedule product, corridor comparison,
and coded hard family are proved in `PowerFlowLimits/QueryHardness.lean` and
`PowerFlowLimits/EndToEnd.lean`. All hard injections lie in the full lossless space
`span(1)^perp`; no generator redispatch subspace is part of the theorem.
See `docs/proposition-3-recovery.md`.
