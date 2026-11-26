# Public claim ledger

This ledger maps the first revision of the letter to its Lean declarations. It distinguishes a
proved claim from arithmetic proved after importing a cited result as a hypothesis. A row is
complete only when its source claim and Lean declaration have the same model, quantifiers,
constants, and dependencies.

The numbering is that of the revised letter. Proposition 2 is the query lower bound result
(Proposition 3 of the submitted version), and Proposition 3 is the DC-OPF Newton system bound.
Rows labeled R belong to the probabilistic Proposition 2 of the submitted version, which the
revision removed.

| ID | Letter claim | Lean declaration or target | Status |
|---|---|---|---|
| M0 | Positive weighted branch incidence defines the susceptance Laplacian | `WeightedGraph`, `WeightedGraph.laplacian` | Proved model |
| M1 | Connected grid means ordinary path connectivity | `WeightedGraph.CombinatoriallyConnected` | Defined |
| M2 | Positive weights and path connectivity imply `lambda₂ > 0` | `combinatoriallyConnected_implies_spectralConnected` | Proved |
| S1 | `kappa_+ = ‖B‖₂ ‖B⁺‖₂` is the ordinary condition number of `B` on balanced injections | `lambda2_sq_mul_sq_le_sum_sq_laplacian_mulVec`, `sum_sq_laplacian_mulVec_le`, `balanced_solve_norm_bounds` | Proved: every balanced `theta` satisfies `lambda₂ ‖theta‖ <= ‖B theta‖ <= lambda_max ‖theta‖`; attainment is given by the extreme modes of `SpectralHardPair.lean` |
| GR1a | Interlacing gives `lambda_min(B_r) <= lambda₂(B)` | `groundedEigenvalueMin_le_lambda2` | Proved |
| GR1b | `tr(B_r) >= b(E)` | `groundedLaplacian_trace_eq`, `totalWeight_le_grounded_trace` | Proved |
| GR1c | `(B_r)_ii >= b_max` at a retained end of a heaviest branch | `edgeWeight_le_groundedEigenvalueMax` | Proved for every branch |
| GR1d | `lambda_max(B_r) >= max{b(E)/(n-1), b_max}`, half of Lemma 1(i) | `totalWeight_div_le_groundedEigenvalueMax`, `half_lemma1_le_groundedEigenvalueMax` | Proved |
| GR2 | Each bound on `kappa_+` holds for `kappa_2(B_r)` with its constant halved | `groundedConditionNumber_ge_of_lambda2_mul_le` | Proved as a transfer principle: a Rayleigh bound `lambda₂ c <= d` and `q <= lambda_max(B_r)` give `kappa_2(B_r) >= c q / d` |
| GR2a | Grounded Lemma 1 | `cut_totalWeight_bound_le_groundedConditionNumber`, `cut_edge_bound_le_groundedConditionNumber` | Proved |
| GR2b | Grounded Theorem 1 | `grounded_separator_kappa_bound_combined` | Proved |
| GR2c | Grounded Corollary 1 | `WeightedGraph.grounded_treewidth_kappa_bound_of_tree_decomposition`, `grounded_planar_kappa_bound_of_lipton_partition` | Part (i) proved; part (ii) relative to the cited planar separator theorem |
| GR2d | Grounded Proposition 1 | `grounded_corridor_kappa_bound_combined` | Proved |
| GR3 | The corrected trace transfer of the submitted version | `corrected_trace_over_lambda2_le_groundedConditionNumber` | Proved; no longer a public claim |
| F1a | A QLS solver needs `Omega(kappa)` queries on some input | `RHSQueryHardness.preparationOracle_gap_sq`, `hybrid_distance_le`, `rhs_query_lower_bound` | Proved for the explicit balanced hard pair after importing the standard one-query hybrid progress bound |
| F1b | A QLS algorithm attains the matching conditioning dependence | quantum algorithm upper bound target | Not formalized |
| F2a | Tomography of an `n` dimensional state needs `tilde Theta(n/epsilon)` uses of its preparation circuit and inverse | `clean_qls_worst_case_product` tomography premise | Lower bound imported from van Apeldoorn et al.; the hard family is real and nonnegative |
| F2b | Each solver call pays the fixed internal schedule of right hand side loading calls | `clean_qls_worst_case_product` | Proved as explicit cost composition on one tomography hard input |
| F2c | Dense classical loading without QRAM costs `Omega(n)` gates per query | input oracle and gate model target | Not formalized |
| F3a | The classical Laplacian is SDD | `WeightedGraph.unitLaplacian_isSDD` | Proved |
| F3b | Classical solve time is `tilde O(m log(1/delta))` in the energy norm | classical algorithm and cost model target | Not formalized |
| F3c | Euclidean and energy norm relative errors differ by at most `sqrt(kappa_+)` | `euclidean_error_le_energy_error`, `energy_error_le_euclidean_error` | Proved in squared, cross multiplied form |
| F3d | `delta = epsilon / sqrt(kappa_+)` gives `‖thetahat - theta‖₂ <= epsilon ‖theta‖₂` | `euclidean_accuracy_of_energy_accuracy`, `euclidean_accuracy_of_scaled_energy_accuracy` | Proved for a balanced error |
| L1.1 | `lambda_max >= 2 b(E)/(n-1)` | `two_totalWeight_div_le_lambdaMax` | Proved |
| L1.2 | `lambda_max >= 2 max_e b_e` | `exists_maxWeight_lambdaMax_bound` | Proved |
| L1.3 | Cut Rayleigh bound for `lambda₂` | `lambda2_le_cut_div`, `lambda2_mul_le_cut` | Proved |
| L1.4 | Total weight condition number consequence | `kappaPlus_ge_totalWeight` | Proved from ordinary connectivity |
| L1.5 | Maximum edge condition number consequence | `exists_maxWeight_kappa_bound` | Proved |
| T1.1 | Every boundary edge of `A union X` meets `X` | `boundaryEdges_subset_incident` | Proved |
| T1.2 | `b(partial S) <= s Delta b_max` | `separator_lambda2_mul_le` | Proved in the form `lambda₂ beta (1 - beta) n <= s Delta b_max` |
| T1.3 | Separator bound, total weight term | `separator_kappa_bound` | Proved from ordinary connectivity and an explicit partition |
| T1.4 | Separator bound, topology only term `2 beta (1 - beta) n / (s Delta)` | `separator_kappa_bound_topological`, `separator_kappa_bound_combined` | Proved for every positive weighting |
| C1.1 | Width `tau` gives a bag of at most `tau+1` whose removal has components of size at most `n/2` | `FiniteRootedTree.exists_weighted_centroid_component_bound`, `RootedTreeDecomposition.exists_balanced_bag`, `WeightedGraph.exists_balanced_bag_of_tree_decomposition` | Proved from the standard vertex coverage, edge coverage, and connected bag occurrence axioms |
| C1.2 | `G` admits a `(tau+1,1/4)` separation | `component_partition_has_quarter_separation`, `WeightedGraph.exists_quarter_separation_of_tree_decomposition` | Proved |
| C1.2a | Connectedness gives `m >= n-1` in the Corollary 1 proof | `WeightedGraph.card_sub_one_le_edges` | Proved using mathlib's spanning-tree theorem |
| C1.3 | Treewidth bound `3 max{b(E)/b_max, n} / (8 (tau+1) Delta)` | `WeightedGraph.treewidth_kappa_bound_of_tree_decomposition_combined` | Proved end to end from a rooted tree decomposition of width at most `tau` with `tau+1 <= floor(n/4)` |
| C1.4 | Lipton--Tarjan gives the stated planar separation | `LiptonTarjanVertexCostTheorem` | Cited premise, stated for an abstract planarity predicate |
| C1.5 | `n >= 288` turns the Lipton--Tarjan partition into a `1/6` balanced partition | `sqrt_eight_mul_card_le_sixth`, `exists_originalPlanarPartition` | Proved from the quantitative separator output |
| C1.6 | Planar bound `5 max{b(E)/b_max, n} / (18 sqrt(8n) Delta)` | `planar_kappa_bound_from_lipton_tarjan_combined` | Proved relative to C1.4 |
| NP1 | Placing a dummy vertex at each of `c` crossings and applying the vertex cost theorem yields `s <= 2 sqrt(8(n+c))` | `CrossingSchedule.planarizedGraph`, `CrossingSchedule.exists_projectedNearPlanarPartition` | Proved relative to C1.4, with the planarity of the planarized graph as a hypothesis |
| NP2 | Part (ii) persists up to constants when `c = O(n)` | `CrossingSchedule.nearPlanar_kappa_bound_combined`, `nearPlanar_kappa_bound_of_linear_crossings_topological` | Proved relative to C1.4 above the explicit threshold `1152 (n + c) <= n²` |
| P1.1 | Corridor topology matches the induced path and endpoint restrictions | `CorridorTopology`, `corridor_kappa_bound_of_topology` | Proved with an exact indexed path, disjoint vertex cover, and nonpath endpoint restrictions |
| P1.2 | Corridor bound `2 beta² (ell-1)² max{b(E), n b_max} / b(E_P)` | `corridor_kappa_bound_combined_exact` | Proved from ordinary connectivity |
| P1.3 | `b(E_P) <= (ell-1) b_max`, hence the bound is at least `2 beta² n (ell-1)` | `corridorWeight_le_length_mul_bmax`, `corridor_topological_le_combined_exact` | Proved |
| P1.4 | A corridor of length `Theta(n)` gives `Omega(n²)` for all positive susceptances | `corridor_kappa_quadratic_bound_topological`, `corridor_family_isBigOmega_quadratic_topological` | Proved using mathlib's `IsBigO atTop` |
| P1.5 | `ell=2` recovers the tie line scaling | `two_bus_corridor_kappa_bound` | Proved as a single interface branch; the corridor coefficient is `2 beta²`, so the statement concerns the mechanism and the order |
| A1 | None of the bounds needs line data; they hold for every positive choice of susceptances | universal quantification over `WeightedGraph.weights` in T1.4, C1.3, C1.6, P1.3 | Proved |
| A2 | This covers random line data under any joint distribution | `separator_topological_bound_surely`, `corridor_topological_bound_surely` | Proved: the events have probability one for every probability measure on positive weights |
| G1 | A grid family has `kappa = Omega(n)`, and `Omega(n²)` with corridors | `separator_family_isBigOmega_linear_topological`, `corridor_family_isBigOmega_quadratic_topological` | Proved using mathlib `IsBigO atTop` |
| P2.1 | The hard pair `p_± = (kappa u ± v)/sqrt(kappa²+1)` is normalized and balanced | `RHSQueryHardness.preparedPlus_normalized`, `preparedMinus_normalized`, `BalancedModePair.embed_balanced` | Proved |
| P2.2 | `theta_±` is proportional to `u ± v`, so `‖theta_+ - theta_-‖ = sqrt(2) ‖theta_±‖` | `RHSQueryHardness.inverseMap_preparedPlus`, `solution_sqDistance`, `solve_balancedPreparedPlus`, `SpectralHardPair.exists_balancedModePair_laplacian_inverse` | Proved for every connected Laplacian with distinct extreme eigenvalues |
| P2.3 | An output of accuracy `epsilon < 1/sqrt(2)` tells `p_+` from `p_-` | `RHSQueryHardness.accurate_output_separates`, `hardPair_accurate_output_separates` | Proved for classical outputs and, at unit scale, for states |
| P2.4 | Preparation circuits with `‖U_{p_+} - U_{p_-}‖ = 2/sqrt(kappa²+1)` exist | `RHSQueryHardness.preparationOraclePlus_prepares`, `preparationOracleMinus_prepares`, `preparationOracle_gap_sq` | Proved exactly as real orthogonal plane rotations |
| P2.5 | By the hybrid argument, `T` queries tell them apart with advantage `O(T/kappa)`; part (i) | `RHSQueryHardness.hybrid_distance_le`, `rhs_query_lower_bound`, `PaperClaims.ControlledPreparationHybridBound` | Proved from the standard query hybrid premise |
| P2.6 | Every unit vector in `1⊥` is the normalized solution of some balanced injection | `finrank_zeroSumSubspace`, `normalized_rhs_reaches_every_target` | Proved on the `n-1` dimensional zero sum subspace |
| P2.7 | Part (ii): a QLS pipeline makes `tilde Omega(n kappa / epsilon)` queries | `clean_qls_worst_case_product`, `PaperClaims.proposition2_fixedScheduleReadout` | Proved relative to the hybrid and tomography premises; `n-1 >= n/2` preserves the rate |
| P2.8 | Grid and corridor families give `tilde Omega(n²/epsilon)` and `tilde Omega(n³/epsilon)` | `clean_qls_worst_case_grid_product`, `clean_qls_worst_case_corridor_product`, `clean_qls_grid_product_exceeds_nearly_linear` | Proved with explicit structural and sparse classical comparison premises |
| P2.9 | Part (iii): bus and branch observables with gaps `2 abs(u_i v_i)` and `2 abs((u_i-u_j)(v_i-v_j))` | `RHSQueryHardness.bus_observable_gap`, `branch_observable_gap`, `estimates_separated_of_quarter_gap`, `PaperClaims.proposition2_localObservable` | Proved for estimates within a quarter of a nonzero gap, relative to the hybrid premise |
| P2.10 | The quadratic corridor lower bound exceeds the nearly linear classical upper bound | `worst_case_corridor_qls_exceeds_classical` | Proved above the displayed constant and logarithmic threshold |
| P2.11 | Easy inputs exist, so the bound is a worst case statement | `DiagonalQLSAlgorithm.zero_query_solver_at_arbitrary_condition` | Proved counterexample to instancewise readings |
| H1 | Substituting `kappa = Omega(n)` into `D kappa^{3/2} << n/d` forces `D << n^{-1/2} < 1` | `hhl_criterion_readout_bound`, `hhl_criterion_no_readout_level` | Proved |
| ID1 | `kappa_eff(epsilon) <= kappa` | `slowMass_lambda2`, `inputDependentConditionNumber_le` | Proved for the definition stated in the README |
| ID2 | On `p_±`, half the mass of the solution sits on the slowest mode, so `kappa_eff = kappa` for all `epsilon < 1/sqrt(2)` | `RHSQueryHardness.slow_mass_balancedSolution`, `inputDependentConditionNumber_hardPair` | Proved |
| ID3 | At the recorded operating points of 36 PGLib systems, `kappa_eff(0.01) >= kappa/2` in 35 | numerical survey | Python evidence only; not a Lean theorem |
| AC1 | At a lossless flat start the active power and angle block equals the Laplacian | `WeightedGraph.hasDerivAt_acActiveInjection_line`, `WeightedGraph.acAngleJacobian_flat_eq_laplacian` | Proved with its calculus certificate |
| AC2 | The off diagonal blocks vanish | `WeightedGraph.hasDerivAt_acActivePower_voltage_flat`, `WeightedGraph.hasDerivAt_acReactivePower_angle_flat` | Proved for the lossless model with voltage magnitudes and bus shunts |
| AC3 | `J = diag(B_r, J_QV)` gives `kappa_2(J) >= kappa_2(B_r)` | `blockDiagonal_singular_bounds`, `rayleigh_lower_of_singular_lower`, `groundedConditionNumber_le_of_singular_bounds`, `flatStart_blockDiagonal_condition_bound` | Proved in singular value form for an arbitrary reactive block |
| AC4 | A quantum inner solver pays (F2) at every Newton iteration | iterative algorithm and composition target | Not formalized |
| OPF1 | The barrier Hessian block `L_w` is a Laplacian with positive iteration dependent weights | `WeightedGraph.hasDerivAt_dcOpfBranchBarrierAlongLine`, `WeightedGraph.hasDerivAt_dcOpfBranchBarrierDerivativeAlongLine`, `WeightedGraph.dcOpfBarrierScale_pos`, `WeightedGraph.dcOpfNetworkBlock_eq_laplacian` | Proved for the two-sided branch flow log barrier at every strictly feasible iterate |
| OPF2 | `kappa_2(L_w) >= beta (1 - beta) n / (s Delta)` at every iterate | `WeightedGraph.dcOpfNewtonMatrix_angle_block`, `WeightedGraph.dcOpfGroundedBlock_condition_bound` | Proved for every positive choice of the weights |
| OPF3 | Proposition 3: `kappa_2(K) >= sqrt(beta n / s) / (2 Delta)` | `WeightedGraph.sum_sq_laplacian_mulVec_busIndicator_le`, `abs_entry_le_of_singular_upper`, `WeightedGraph.dcOpfNewton_condition_bound` | Proved in singular value form for every generation block, generator map, and positive weights |
| OPF4 | Quantum IPMs pay (F1) and (F2) at every iteration | quantum IPM cost model target | Not formalized |
| NP3 | Polynomial quantum algorithms for the stated NP-hard problems imply `NP subset BQP` | reduction and complexity-class model target | Not formalized |
| NP4 | Oracle search speedups are at most quadratic | BBBV oracle theorem target | Not formalized |
| HY1 | Variational schemes retain the stated barriers | explicit hybrid models and lower-bound targets | Not formalized |
| R1 | Submitted version: independent bounded positive susceptances satisfy the Hoeffding lower tail | internal proof of `random_kappa_bound` | Proved; not in the revised letter |
| R2 | Submitted version: separator, treewidth, planar, and corridor bounds with the stated probability | `random_kappa_bound`, `random_treewidth_kappa_bound`, `random_kappa_bound_of_sqrt_separator_partition`, `random_corridor_kappa_bound` | Proved; not in the revised letter |
| E1 | Table I documents the topological conditions on large test systems | certified data, parser, and certificates | Python evidence and the `qpf-check` certificates; not a universal Lean theorem |

## Current trust boundary

The proof modules contain no `sorry` or `proof_wanted`. Their axiom closure is limited to
`propext`, `Quot.sound`, and `Classical.choice`. Comparator checks the declarations listed in
`comparator.json` against the independent `Challenge.lean` statements. The Comparator surface
proves exact statement identity for the public declarations; it does not turn the rows marked
not formalized into proved claims.

The external premises are the vertex cost form of the Lipton--Tarjan planar separator theorem,
the one-query hybrid progress bound, the pure state tomography lower bound, the classical SDD
solve time, and the dense loading gate count. Each enters as an explicit hypothesis of the
theorems that use it. All hard injections lie in the full lossless space `span(1)^perp`; no
generator redispatch subspace is part of the theorem. See `docs/query-lower-bound-recovery.md`.
