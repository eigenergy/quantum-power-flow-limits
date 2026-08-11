/-
Copyright (c) 2026 Power Flow Limits contributors. All rights reserved.
Released under the MIT license. See LICENSE for details.
-/

import PowerFlowLimits.ACPowerFlow
import PowerFlowLimits.Corridors
import PowerFlowLimits.EndToEnd
import PowerFlowLimits.Grounded
import PowerFlowLimits.OptimalPowerFlow
import PowerFlowLimits.PlanarSeparator
import PowerFlowLimits.Random
import PowerFlowLimits.SpectralHardPair
import PowerFlowLimits.TreeDecomposition

/-!
# Public claim surface

This module collects the statements checked by Comparator. It separates results proved in this
repository from theorem-valued premises imported from the graph theory and quantum algorithms
literature.
-/

open Finset BigOperators
open Matrix
open scoped Matrix

noncomputable section

set_option autoImplicit false

variable {n m : ℕ}

namespace PaperClaims

/-- The external hybrid argument for a controlled right hand side preparation oracle and its
inverse. `qSolve` is one fixed coherent solve schedule for the fixed matrix. -/
structure ControlledPreparationHybridBound {d : ℕ}
    (pair : RHSQueryHardness.BalancedModePair d) (qSolve : ℕ)
    (condition distance gap constant : ℝ)
    (preparePlus prepareMinus preparePlusInv prepareMinusInv :
      (Fin 2 → ℝ) → Fin 2 → ℝ) : Prop where
  plus_prepares : pair.embed (preparePlus RHSQueryHardness.preparationBasis) =
    RHSQueryHardness.balancedPreparedPlus pair condition
  minus_prepares : pair.embed (prepareMinus RHSQueryHardness.preparationBasis) =
    RHSQueryHardness.balancedPreparedMinus pair condition
  plus_left_inverse : Function.LeftInverse preparePlusInv preparePlus
  plus_right_inverse : Function.RightInverse preparePlusInv preparePlus
  minus_left_inverse : Function.LeftInverse prepareMinusInv prepareMinus
  minus_right_inverse : Function.RightInverse prepareMinusInv prepareMinus
  plus_norm : ∀ x, RHSQueryHardness.sqNorm (preparePlus x) = RHSQueryHardness.sqNorm x
  minus_norm : ∀ x, RHSQueryHardness.sqNorm (prepareMinus x) = RHSQueryHardness.sqNorm x
  plus_inv_norm :
    ∀ x, RHSQueryHardness.sqNorm (preparePlusInv x) = RHSQueryHardness.sqNorm x
  minus_inv_norm :
    ∀ x, RHSQueryHardness.sqNorm (prepareMinusInv x) = RHSQueryHardness.sqNorm x
  condition_pos : 0 < condition
  gap_pos : 0 < gap
  constant_pos : 0 < constant
  output_distance_sq : distance ^ 2 = RHSQueryHardness.sqDistance
    (RHSQueryHardness.balancedSolutionPlus pair)
    (RHSQueryHardness.balancedSolutionMinus pair)
  separated : gap ≤ distance
  progress : condition * distance ≤ constant * qSolve

/-- The external pure state tomography lower bound on a finite dimensional real Hilbert space,
with its norm, error, success probability, and query count made explicit. -/
structure PureStateTomographyBound {index state : Type*}
    [NormedAddCommGroup state] [InnerProductSpace ℝ state] [FiniteDimensional ℝ state]
    (target : index → state) (calls : index → ℝ) (basis : state)
    (prepare prepareInv : index → state → state)
    (error successProbability constant : ℝ) : Prop where
  dimension_pos : 0 < Module.finrank ℝ state
  basis_normalized : ‖basis‖ = 1
  normalized : ∀ p, ‖target p‖ = 1
  prepares : ∀ p, prepare p basis = target p
  left_inverse : ∀ p, Function.LeftInverse (prepareInv p) (prepare p)
  right_inverse : ∀ p, Function.RightInverse (prepareInv p) (prepare p)
  prepare_norm : ∀ p x, ‖prepare p x‖ = ‖x‖
  inverse_norm : ∀ p x, ‖prepareInv p x‖ = ‖x‖
  error_pos : 0 < error
  error_lt_one : error < 1
  success_gt_half : 1 / 2 < successProbability
  constant_pos : 0 < constant
  lowerBound : ∃ p, constant * ((Module.finrank ℝ state : ℝ) / error) ≤ calls p

/-- The external solve-time upper bound for a classical SDD solver instantiated on the fixed
graph. The logarithmic factor records the accuracy and failure-probability dependence of the
cited algorithm. -/
structure ClassicalSDDSolveBound {index : Type*} (G : WeightedGraph n m)
    (solveTime : index → ℝ) (constant logFactor : ℝ) : Prop where
  constant_nonnegative : 0 ≤ constant
  logFactor_nonnegative : 0 ≤ logFactor
  upperBound : ∀ p, solveTime p ≤ constant * m * logFactor

/-- The external gate lower bound for loading a generic dense classical vector without QRAM in
the cited one-qubit rotation and CNOT circuit model. -/
structure DenseLoadingBound {index : Type*} (d : ℕ) (isDense : index → Prop)
    (loadTime : index → ℝ) (constant : ℝ) : Prop where
  constant_pos : 0 < constant
  lowerBound : ∀ p, isDense p → constant * d ≤ loadTime p

/-- A graph-derived certificate for the canonical two-mode hard instance. -/
structure GraphHardPairCertificate (G : WeightedGraph n m) where
  /-- The orthonormal extreme modes constructed from the graph Laplacian. -/
  pair : RHSQueryHardness.BalancedModePair n
  condition_pos : 0 < effectiveConditionNumber G (fun _ ↦ 1)
  fastEigen : ∀ i, ∑ j, G.laplacian (fun _ ↦ 1) i j * pair.fast j =
    laplacianEigenvalueMax G (fun _ ↦ 1) * pair.fast i
  slowEigen : ∀ i, ∑ j, G.laplacian (fun _ ↦ 1) i j * pair.slow j =
    laplacian_eigenvalue₂ G (fun _ ↦ 1) * pair.slow i
  preparedPlus_normalized : RHSQueryHardness.sqNorm
    (RHSQueryHardness.balancedPreparedPlus pair
      (effectiveConditionNumber G (fun _ ↦ 1))) = 1
  preparedMinus_normalized : RHSQueryHardness.sqNorm
    (RHSQueryHardness.balancedPreparedMinus pair
      (effectiveConditionNumber G (fun _ ↦ 1))) = 1
  inputGap : RHSQueryHardness.sqDistance
      (RHSQueryHardness.balancedPreparedPlus pair
        (effectiveConditionNumber G (fun _ ↦ 1)))
      (RHSQueryHardness.balancedPreparedMinus pair
        (effectiveConditionNumber G (fun _ ↦ 1))) =
    4 / (effectiveConditionNumber G (fun _ ↦ 1) ^ 2 + 1)
  solutionPlus_normalized :
    RHSQueryHardness.sqNorm (RHSQueryHardness.balancedSolutionPlus pair) = 1
  solutionMinus_normalized :
    RHSQueryHardness.sqNorm (RHSQueryHardness.balancedSolutionMinus pair) = 1
  outputGap : RHSQueryHardness.sqDistance
      (RHSQueryHardness.balancedSolutionPlus pair)
      (RHSQueryHardness.balancedSolutionMinus pair) = 2
  oraclePlus_prepares : RHSQueryHardness.preparationOraclePlus
      (effectiveConditionNumber G (fun _ ↦ 1)) RHSQueryHardness.preparationBasis =
    RHSQueryHardness.preparedPlus (effectiveConditionNumber G (fun _ ↦ 1))
  oracleMinus_prepares : RHSQueryHardness.preparationOracleMinus
      (effectiveConditionNumber G (fun _ ↦ 1)) RHSQueryHardness.preparationBasis =
    RHSQueryHardness.preparedMinus (effectiveConditionNumber G (fun _ ↦ 1))
  oraclePlus_inverse : ∀ x, RHSQueryHardness.preparationOraclePlus
      (effectiveConditionNumber G (fun _ ↦ 1))
      (RHSQueryHardness.preparationOracleMinus
        (effectiveConditionNumber G (fun _ ↦ 1)) x) = x
  oracleMinus_inverse : ∀ x, RHSQueryHardness.preparationOracleMinus
      (effectiveConditionNumber G (fun _ ↦ 1))
      (RHSQueryHardness.preparationOraclePlus
        (effectiveConditionNumber G (fun _ ↦ 1)) x) = x
  inversePlus : RHSQueryHardness.inverseMap
      (effectiveConditionNumber G (fun _ ↦ 1))
      (RHSQueryHardness.preparedPlus (effectiveConditionNumber G (fun _ ↦ 1))) =
    fun i ↦ (effectiveConditionNumber G (fun _ ↦ 1) * Real.sqrt 2 /
      Real.sqrt (effectiveConditionNumber G (fun _ ↦ 1) ^ 2 + 1)) *
        RHSQueryHardness.solutionPlus i
  inverseMinus : RHSQueryHardness.inverseMap
      (effectiveConditionNumber G (fun _ ↦ 1))
      (RHSQueryHardness.preparedMinus (effectiveConditionNumber G (fun _ ↦ 1))) =
    fun i ↦ (effectiveConditionNumber G (fun _ ↦ 1) * Real.sqrt 2 /
      Real.sqrt (effectiveConditionNumber G (fun _ ↦ 1) ^ 2 + 1)) *
        RHSQueryHardness.solutionMinus i
  inverseGainRatio :
    (1 / laplacian_eigenvalue₂ G (fun _ ↦ 1)) /
        (1 / laplacianEigenvalueMax G (fun _ ↦ 1)) =
      effectiveConditionNumber G (fun _ ↦ 1)
  solvePlus : G.laplacian (fun _ ↦ 1) *ᵥ
      ((effectiveConditionNumber G (fun _ ↦ 1) * Real.sqrt 2 /
          Real.sqrt (effectiveConditionNumber G (fun _ ↦ 1) ^ 2 + 1)) •
        RHSQueryHardness.balancedSolutionPlus pair) =
    laplacianEigenvalueMax G (fun _ ↦ 1) •
      RHSQueryHardness.balancedPreparedPlus pair
        (effectiveConditionNumber G (fun _ ↦ 1))
  solveMinus : G.laplacian (fun _ ↦ 1) *ᵥ
      ((effectiveConditionNumber G (fun _ ↦ 1) * Real.sqrt 2 /
          Real.sqrt (effectiveConditionNumber G (fun _ ↦ 1) ^ 2 + 1)) •
        RHSQueryHardness.balancedSolutionMinus pair) =
    laplacianEigenvalueMax G (fun _ ↦ 1) •
      RHSQueryHardness.balancedPreparedMinus pair
        (effectiveConditionNumber G (fun _ ↦ 1))

/-- Lemma 1: the trace, edge, cut, and resulting condition number inequalities. -/
theorem lemma1_weightedCuts (G : WeightedGraph n m) (S : Finset (Fin n))
    (e : Fin m) (hn : 1 < n) (hne : S.Nonempty) (hproper : S ≠ Finset.univ)
    (hconn : G.CombinatoriallyConnected) :
    2 * G.totalWeight / ((n : ℝ) - 1) ≤
        laplacianEigenvalueMax G (fun _ ↦ 1) ∧
      2 * G.weights e ≤ laplacianEigenvalueMax G (fun _ ↦ 1) ∧
      laplacian_eigenvalue₂ G (fun _ ↦ 1) *
          ((S.card : ℝ) * ((n : ℝ) - S.card)) ≤
        (n : ℝ) * G.cutWeight S ∧
      2 * ((S.card : ℝ) / n) * (1 - (S.card : ℝ) / n) * G.totalWeight /
          G.cutWeight S ≤ effectiveConditionNumber G (fun _ ↦ 1) ∧
      2 * ((S.card : ℝ) / n) * (1 - (S.card : ℝ) / n) *
          ((n : ℝ) * G.weights e) / G.cutWeight S ≤
        effectiveConditionNumber G (fun _ ↦ 1) := by
  exact ⟨two_totalWeight_div_le_lambdaMax G hn, two_mul_weight_le_lambdaMax G e,
    lambda2_mul_le_cut G S hne hproper, kappaPlus_ge_totalWeight G S hne hproper hconn,
    kappaPlus_ge_edge G S hne hproper hconn e⟩

/-- The separator condition number bound. -/
theorem theorem1_separator (G : WeightedGraph n m)
    (A X B : Finset (Fin n)) (s Δ bmax β : ℝ)
    (hcover : A ∪ X ∪ B = Finset.univ)
    (hdisjoint : Disjoint (A ∪ X) B)
    (hnoCrossing : ∀ e, ¬(G.posEndpoint e ∈ A ∧ G.negEndpoint e ∈ B) ∧
      ¬(G.posEndpoint e ∈ B ∧ G.negEndpoint e ∈ A))
    (hX : (X.card : ℝ) ≤ s)
    (hdegree : ∀ i, ((G.incidentEdges i).card : ℝ) ≤ Δ)
    (hweight : ∀ e, G.weights e ≤ bmax)
    (hβ : 0 < β) (hβhalf : β ≤ 1 / 2)
    (hA : β * n ≤ ((A ∪ X).card : ℝ)) (hB : β * n ≤ (B.card : ℝ))
    (hconn : G.CombinatoriallyConnected) :
    2 * β * (1 - β) * G.totalWeight / (s * Δ * bmax) ≤
      effectiveConditionNumber G (fun _ ↦ 1) := by
  exact separator_kappa_bound G A X B s Δ bmax β hcover hdisjoint hnoCrossing hX
    hdegree hweight hβ hβhalf hA hB hconn

/-- The tree decomposition form of the treewidth corollary. -/
theorem corollary1_treewidth {k τ : ℕ} (G : WeightedGraph n m)
    (D : RootedTreeDecomposition G.toSimpleGraph k)
    (hn : 0 < n) (hwidth : D.HasWidthAtMost τ) (hτ : τ + 1 ≤ n / 4)
    (Δ bmax : ℝ)
    (hdegree : ∀ i, ((G.incidentEdges i).card : ℝ) ≤ Δ)
    (hweight : ∀ e, G.weights e ≤ bmax)
    (hconn : G.CombinatoriallyConnected) :
    3 / 8 * G.totalWeight / (((τ : ℝ) + 1) * Δ * bmax) ≤
      effectiveConditionNumber G (fun _ ↦ 1) := by
  exact G.treewidth_kappa_bound_of_tree_decomposition D hn hwidth hτ Δ bmax hdegree
    hweight hconn

/-- The planar corollary from a planarity certificate and the theorem-valued external
Lipton--Tarjan premise. -/
theorem corollary1_planarFromLiptonTarjan (Planar : PlanarityPredicate)
    (hLT : LiptonTarjanVertexCostTheorem Planar) (G : WeightedGraph n m)
    (hplanar : Planar _ G.toSimpleGraph) (hn : 288 ≤ n) (Δ bmax : ℝ)
    (hdegree : ∀ i, ((G.incidentEdges i).card : ℝ) ≤ Δ)
    (hweight : ∀ e, G.weights e ≤ bmax)
    (hconn : G.CombinatoriallyConnected) :
    5 / 18 * G.totalWeight / (Real.sqrt (8 * n) * Δ * bmax) ≤
      effectiveConditionNumber G (fun _ ↦ 1) := by
  exact planar_kappa_bound_from_lipton_tarjan Planar hLT G hplanar hn Δ bmax hdegree
    hweight hconn

/-- The macroscopic corridor condition number bound. -/
theorem proposition1_corridor (G : WeightedGraph n m)
    (left right : Finset (Fin n)) (ℓ : ℕ) (hℓ : 2 ≤ ℓ)
    (path : Fin ℓ → Fin n) (pathEdges : Finset (Fin m)) (β : ℝ)
    (hpathInjective : Function.Injective path)
    (hleft : ∀ i, path i ∉ left) (hright : ∀ i, path i ∉ right)
    (hdisjoint : Disjoint left right)
    (hpath : ∀ e ∈ pathEdges, ∃ i : Fin ℓ, ∃ h : i.val + 1 < ℓ,
      (G.posEndpoint e = path i ∧ G.negEndpoint e = path ⟨i.val + 1, h⟩) ∨
      (G.posEndpoint e = path ⟨i.val + 1, h⟩ ∧ G.negEndpoint e = path i))
    (hnonpath : ∀ e ∉ pathEdges,
      ((G.posEndpoint e ∈ left ∨ G.posEndpoint e = path ⟨0, by omega⟩) ∧
       (G.negEndpoint e ∈ left ∨ G.negEndpoint e = path ⟨0, by omega⟩)) ∨
      ((G.posEndpoint e ∈ right ∨ G.posEndpoint e = path ⟨ℓ - 1, by omega⟩) ∧
       (G.negEndpoint e ∈ right ∨ G.negEndpoint e = path ⟨ℓ - 1, by omega⟩)))
    (hβ : 0 < β)
    (hleftSize : β * n ≤ (left.card : ℝ))
    (hrightSize : β * n ≤ (right.card : ℝ))
    (hconn : G.CombinatoriallyConnected) :
    2 * β ^ 2 * ((ℓ : ℝ) - 1) ^ 2 * G.totalWeight /
        (∑ e ∈ pathEdges, G.weights e) ≤
      effectiveConditionNumber G (fun _ ↦ 1) := by
  exact corridor_kappa_bound G left right ℓ hℓ path pathEdges β hpathInjective hleft
    hright hdisjoint hpath hnonpath hβ hleftSize hrightSize hconn

/-- The exponential probability form of the random separator bound. -/
theorem proposition2_randomSeparator {sample : Type*} [MeasurableSpace sample]
    (measure : MeasureTheory.Measure sample) [MeasureTheory.IsProbabilityMeasure measure]
    (G : WeightedGraph n m) (hm : 0 < m) (weight : Fin m → sample → ℝ)
    (hmeasurable : ∀ e, Measurable (weight e))
    (hindependent : ProbabilityTheory.iIndepFun weight measure)
    (bmax : ℝ) (hbounded : ∀ ω, ∀ e, weight e ω ∈ Set.Ioc 0 bmax)
    (A X B : Finset (Fin n)) (s Δ β ε ρ : ℝ)
    (hcover : A ∪ X ∪ B = Finset.univ)
    (hdisjoint : Disjoint (A ∪ X) B)
    (hnoCrossing : ∀ e, ¬(G.posEndpoint e ∈ A ∧ G.negEndpoint e ∈ B) ∧
      ¬(G.posEndpoint e ∈ B ∧ G.negEndpoint e ∈ A))
    (hX : (X.card : ℝ) ≤ s)
    (hdegree : ∀ i, ((G.incidentEdges i).card : ℝ) ≤ Δ)
    (hβ : 0 < β) (hβhalf : β ≤ 1 / 2)
    (hA : β * n ≤ ((A ∪ X).card : ℝ)) (hB : β * n ≤ (B.card : ℝ))
    (hdenominator : 0 < s * Δ * bmax) (hε : 0 < ε) (hρ : 0 < ρ)
    (hmean : ρ * (m : ℝ) * bmax ≤ ∑ e, ∫ ω, weight e ω ∂measure)
    (hconn : G.CombinatoriallyConnected) :
    1 - Real.exp (-2 * ε ^ 2 * ρ ^ 2 * m) ≤
      measure.real {ω | 2 * β * (1 - β) *
          ((1 - ε) * (∑ e, ∫ ω', weight e ω' ∂measure)) / (s * Δ * bmax) ≤
        effectiveConditionNumber
          (G.withWeights (fun e ↦ weight e ω) (fun e ↦ (hbounded ω e).1))
          (fun _ ↦ 1)} := by
  exact random_kappa_bound_exponential measure G hm weight hmeasurable hindependent bmax
    hbounded A X B s Δ β ε ρ hcover hdisjoint hnoCrossing hX hdegree hβ hβhalf hA
    hB hdenominator hε hρ hmean hconn

/-- The random treewidth transfer from an actual rooted tree decomposition. -/
theorem proposition2_randomTreewidth {sample : Type*} [MeasurableSpace sample]
    {k τ : ℕ}
    (measure : MeasureTheory.Measure sample) [MeasureTheory.IsProbabilityMeasure measure]
    (G : WeightedGraph n m) (hm : 0 < m) (weight : Fin m → sample → ℝ)
    (hmeasurable : ∀ e, Measurable (weight e))
    (hindependent : ProbabilityTheory.iIndepFun weight measure)
    (bmax : ℝ) (hbounded : ∀ ω, ∀ e, weight e ω ∈ Set.Ioc 0 bmax)
    (D : RootedTreeDecomposition G.toSimpleGraph k)
    (hn : 0 < n) (hwidth : D.HasWidthAtMost τ) (hτ : τ + 1 ≤ n / 4)
    (Δ ε ρ : ℝ)
    (hdegree : ∀ i, ((G.incidentEdges i).card : ℝ) ≤ Δ)
    (hdenominator : 0 < (((τ : ℝ) + 1) * Δ * bmax))
    (hε : 0 < ε) (hρ : 0 < ρ)
    (hmean : ρ * (m : ℝ) * bmax ≤ ∑ e, ∫ ω, weight e ω ∂measure)
    (hconn : G.CombinatoriallyConnected) :
    1 - Real.exp (-2 * ε ^ 2 * ρ ^ 2 * m) ≤
      measure.real {ω | 3 / 8 * ((1 - ε) * (∑ e, ∫ ω', weight e ω' ∂measure)) /
          (((τ : ℝ) + 1) * Δ * bmax) ≤
        effectiveConditionNumber
          (G.withWeights (fun e ↦ weight e ω) (fun e ↦ (hbounded ω e).1))
          (fun _ ↦ 1)} := by
  classical
  obtain ⟨X, hXwidth, hcomponentHalf⟩ :=
    G.exists_balanced_bag_of_tree_decomposition D hn hwidth
  have hXτ : (X.card : ℝ) ≤ (τ : ℝ) + 1 := by
    exact_mod_cast hXwidth
  have hXquarterNat : X.card ≤ n / 4 := hXwidth.trans hτ
  have hXquarter : (X.card : ℝ) ≤ (n : ℝ) / 4 := by
    have hcast : (X.card : ℝ) ≤ ((n / 4 : ℕ) : ℝ) := by
      exact_mod_cast hXquarterNat
    exact hcast.trans Nat.cast_div_le
  let H := G.graphOff X
  let componentEquiv : H.ConnectedComponent ≃ Fin (Fintype.card H.ConnectedComponent) :=
    Fintype.equivFin H.ConnectedComponent
  let component : Fin (Fintype.card H.ConnectedComponent) → Finset (Fin n) :=
    fun i ↦ G.componentVerticesOff X (componentEquiv.symm i)
  have hparts : ∀ ⦃i j⦄, i ≠ j → Disjoint (component i) (component j) := by
    intro i j hij
    rw [Finset.disjoint_left]
    intro v hvi hvj
    simp only [component, WeightedGraph.componentVerticesOff, Finset.mem_filter,
      Finset.mem_univ, true_and] at hvi hvj
    obtain ⟨hviX, hi⟩ := hvi
    obtain ⟨_, hj⟩ := hvj
    have hc : componentEquiv.symm i = componentEquiv.symm j := hi.symm.trans hj
    exact hij (componentEquiv.symm.injective hc)
  have hXparts : ∀ i, Disjoint X (component i) := by
    intro i
    rw [Finset.disjoint_left]
    intro v hvX hvi
    simp only [component, WeightedGraph.componentVerticesOff, Finset.mem_filter,
      Finset.mem_univ, true_and] at hvi
    exact hvi.1 hvX
  have hcover : X ∪ Finset.univ.biUnion component = Finset.univ :=
    Finset.eq_univ_of_forall fun v ↦ by
      by_cases hvX : v ∈ X
      · exact Finset.mem_union_left _ hvX
      · apply Finset.mem_union_right
        rw [Finset.mem_biUnion]
        let c : H.ConnectedComponent := H.connectedComponentMk ⟨v, hvX⟩
        let i : Fin (Fintype.card H.ConnectedComponent) := componentEquiv c
        refine ⟨i, Finset.mem_univ i, ?_⟩
        change v ∈ G.componentVerticesOff X (componentEquiv.symm i)
        unfold WeightedGraph.componentVerticesOff
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨hvX, ?_⟩
        simp [H, i, c]
  have hcomponentHalf' : ∀ i, (component i).card ≤ n / 2 :=
    fun i ↦ hcomponentHalf (componentEquiv.symm i)
  have hedgeComponent : ∀ e, G.posEndpoint e ∉ X → G.negEndpoint e ∉ X →
      ∃ i, G.posEndpoint e ∈ component i ∧ G.negEndpoint e ∈ component i := by
    intro e hposX hnegX
    let u : {v : Fin n // v ∉ X} := ⟨G.posEndpoint e, hposX⟩
    let v : {v : Fin n // v ∉ X} := ⟨G.negEndpoint e, hnegX⟩
    have huv : H.Adj u v := ⟨e, Or.inl ⟨rfl, rfl⟩⟩
    let c : H.ConnectedComponent := H.connectedComponentMk u
    let i : Fin (Fintype.card H.ConnectedComponent) := componentEquiv c
    refine ⟨i, ?_, ?_⟩
    · change G.posEndpoint e ∈ G.componentVerticesOff X (componentEquiv.symm i)
      unfold WeightedGraph.componentVerticesOff
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨hposX, ?_⟩
      simp [H, i, c, u]
    · have hcomp : H.connectedComponentMk v = H.connectedComponentMk u :=
        (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj huv).symm
      change G.negEndpoint e ∈ G.componentVerticesOff X (componentEquiv.symm i)
      unfold WeightedGraph.componentVerticesOff
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨hnegX, ?_⟩
      simpa [H, i, c, v, u] using hcomp
  obtain ⟨A, B, hcover', hdisjoint, hnoCrossing, hA, hB⟩ :=
    component_partition_has_quarter_separation G X
      (Fintype.card H.ConnectedComponent) component hn hparts hXparts hcover
      hXquarter hcomponentHalf' hedgeComponent
  exact random_treewidth_kappa_bound_exponential measure G hm weight hmeasurable
    hindependent bmax hbounded A X B (τ : ℝ) Δ ε ρ hcover' hdisjoint hnoCrossing
    hXτ hdegree hA hB hdenominator hε hρ hmean hconn

/-- The random planar transfer from a planarity certificate and the theorem-valued external
Lipton--Tarjan premise. -/
theorem proposition2_randomPlanar {sample : Type*} [MeasurableSpace sample]
    (Planar : PlanarityPredicate) (hLT : LiptonTarjanVertexCostTheorem Planar)
    (measure : MeasureTheory.Measure sample) [MeasureTheory.IsProbabilityMeasure measure]
    (G : WeightedGraph n m) (hm : 0 < m) (weight : Fin m → sample → ℝ)
    (hmeasurable : ∀ e, Measurable (weight e))
    (hindependent : ProbabilityTheory.iIndepFun weight measure)
    (bmax : ℝ) (hbounded : ∀ ω, ∀ e, weight e ω ∈ Set.Ioc 0 bmax)
    (hplanar : Planar _ G.toSimpleGraph) (hn : 288 ≤ n) (Δ ε ρ : ℝ)
    (hdegree : ∀ i, ((G.incidentEdges i).card : ℝ) ≤ Δ)
    (hdenominator : 0 < Real.sqrt (8 * n) * Δ * bmax)
    (hε : 0 < ε) (hρ : 0 < ρ)
    (hmean : ρ * (m : ℝ) * bmax ≤ ∑ e, ∫ ω, weight e ω ∂measure)
    (hconn : G.CombinatoriallyConnected) :
    1 - Real.exp (-2 * ε ^ 2 * ρ ^ 2 * m) ≤
      measure.real {ω | 5 / 18 * ((1 - ε) * (∑ e, ∫ ω', weight e ω' ∂measure)) /
          (Real.sqrt (8 * n) * Δ * bmax) ≤
        effectiveConditionNumber
          (G.withWeights (fun e ↦ weight e ω) (fun e ↦ (hbounded ω e).1))
          (fun _ ↦ 1)} := by
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  rcases exists_originalPlanarPartition Planar hLT G hnpos hplanar with ⟨partition⟩
  have hcardNat : (partition.left ∪ partition.separator).card +
      partition.right.card = n := by
    rw [← Finset.card_union_of_disjoint partition.disjoint_union_right, partition.cover,
      Finset.card_univ, Fintype.card_fin]
  have hcard : ((partition.left ∪ partition.separator).card : ℝ) +
      (partition.right.card : ℝ) = n := by
    exact_mod_cast hcardNat
  have hA : (n : ℝ) / 6 ≤ ((partition.left ∪ partition.separator).card : ℝ) := by
    linarith [partition.right_card_le]
  have hseparatorSixth : (partition.separator.card : ℝ) ≤ (n : ℝ) / 6 :=
    partition.separator_card_le.trans (sqrt_eight_mul_card_le_sixth n hn)
  have hunionNat : (partition.left ∪ partition.separator).card ≤
      partition.left.card + partition.separator.card :=
    Finset.card_union_le partition.left partition.separator
  have hunion : ((partition.left ∪ partition.separator).card : ℝ) ≤
      (partition.left.card : ℝ) + partition.separator.card := by
    exact_mod_cast hunionNat
  have hB : (n : ℝ) / 6 ≤ (partition.right.card : ℝ) := by
    linarith [partition.left_card_le, hseparatorSixth, hunion]
  exact random_kappa_bound_of_sqrt_separator_partition_exponential measure G hm weight
    hmeasurable hindependent bmax hbounded partition.left partition.separator partition.right
    Δ ε ρ partition.cover partition.disjoint_union_right partition.no_left_right_branch
    partition.separator_card_le hdegree hA hB hdenominator hε hρ hmean hconn

/-- The random corridor transfer with its explicit Hoeffding probability. -/
theorem proposition2_randomCorridor {sample : Type*} [MeasurableSpace sample]
    (measure : MeasureTheory.Measure sample) [MeasureTheory.IsProbabilityMeasure measure]
    (G : WeightedGraph n m) (hm : 0 < m) (weight : Fin m → sample → ℝ)
    (hmeasurable : ∀ e, Measurable (weight e))
    (hindependent : ProbabilityTheory.iIndepFun weight measure)
    (bmax : ℝ) (hbounded : ∀ ω, ∀ e, weight e ω ∈ Set.Ioc 0 bmax)
    (left right : Finset (Fin n)) (ℓ : ℕ) (hℓ : 2 ≤ ℓ)
    (path : Fin ℓ → Fin n) (pathEdges : Finset (Fin m)) (hpathEdges : pathEdges.Nonempty)
    (β ε ρ : ℝ) (hpathInjective : Function.Injective path)
    (hleft : ∀ i, path i ∉ left) (hright : ∀ i, path i ∉ right)
    (hdisjoint : Disjoint left right)
    (hpath : ∀ e ∈ pathEdges, ∃ i : Fin ℓ, ∃ h : i.val + 1 < ℓ,
      (G.posEndpoint e = path i ∧ G.negEndpoint e = path ⟨i.val + 1, h⟩) ∨
      (G.posEndpoint e = path ⟨i.val + 1, h⟩ ∧ G.negEndpoint e = path i))
    (hnonpath : ∀ e ∉ pathEdges,
      ((G.posEndpoint e ∈ left ∨ G.posEndpoint e = path ⟨0, by omega⟩) ∧
       (G.negEndpoint e ∈ left ∨ G.negEndpoint e = path ⟨0, by omega⟩)) ∨
      ((G.posEndpoint e ∈ right ∨ G.posEndpoint e = path ⟨ℓ - 1, by omega⟩) ∧
       (G.negEndpoint e ∈ right ∨ G.negEndpoint e = path ⟨ℓ - 1, by omega⟩)))
    (hβ : 0 < β) (hleftSize : β * n ≤ (left.card : ℝ))
    (hrightSize : β * n ≤ (right.card : ℝ))
    (hε : 0 < ε) (hρ : 0 < ρ)
    (hmean : ρ * (m : ℝ) * bmax ≤ ∑ e, ∫ ω, weight e ω ∂measure)
    (hconn : G.CombinatoriallyConnected) :
    1 - Real.exp (-2 * ε ^ 2 * ρ ^ 2 * m) ≤
      measure.real {ω | 2 * β ^ 2 * ((ℓ : ℝ) - 1) ^ 2 *
          ((1 - ε) * (∑ e, ∫ ω', weight e ω' ∂measure)) /
            (∑ e ∈ pathEdges, weight e ω) ≤
        effectiveConditionNumber
          (G.withWeights (fun e ↦ weight e ω) (fun e ↦ (hbounded ω e).1))
          (fun _ ↦ 1)} := by
  exact random_corridor_kappa_bound_exponential measure G hm weight hmeasurable hindependent
    bmax hbounded left right ℓ hℓ path pathEdges hpathEdges β ε ρ hpathInjective hleft
    hright hdisjoint hpath hnonpath hβ hleftSize hrightSize hε hρ hmean hconn

/-- A connected weighted Laplacian with distinct extreme eigenvalues supplies the complete
canonical hard pair certificate. -/
theorem proposition3_balancedHardPair (G : WeightedGraph n m)
    (hconn : G.CombinatoriallyConnected) (hn : 1 < n)
    (hextreme : laplacian_eigenvalue₂ G (fun _ ↦ 1) <
      laplacianEigenvalueMax G (fun _ ↦ 1)) :
    Nonempty (GraphHardPairCertificate G) := by
  obtain ⟨pair, hfast, hslow, hsolvePlus, hsolveMinus⟩ :=
    SpectralHardPair.exists_balancedModePair_laplacian_inverse G hconn hn hextreme
  have htwo : 0 < laplacian_eigenvalue₂ G (fun _ ↦ 1) :=
    combinatoriallyConnected_implies_spectralConnected G hconn hn
  have hmax : 0 < laplacianEigenvalueMax G (fun _ ↦ 1) :=
    SpectralHardPair.lambdaMax_pos_of_combinatoriallyConnected G hconn hn
  have hcondition : 0 < effectiveConditionNumber G (fun _ ↦ 1) := by
    exact div_pos hmax htwo
  refine ⟨
    { pair := pair
      condition_pos := hcondition
      fastEigen := hfast
      slowEigen := hslow
      preparedPlus_normalized :=
        RHSQueryHardness.balancedPreparedPlus_normalized pair _
      preparedMinus_normalized :=
        RHSQueryHardness.balancedPreparedMinus_normalized pair _
      inputGap := RHSQueryHardness.balancedPrepared_sqDistance pair _ hcondition
      solutionPlus_normalized := RHSQueryHardness.balancedSolutionPlus_normalized pair
      solutionMinus_normalized := RHSQueryHardness.balancedSolutionMinus_normalized pair
      outputGap := RHSQueryHardness.balancedSolution_sqDistance pair
      oraclePlus_prepares := RHSQueryHardness.preparationOraclePlus_prepares _
      oracleMinus_prepares := RHSQueryHardness.preparationOracleMinus_prepares _
      oraclePlus_inverse := RHSQueryHardness.preparationOraclePlus_comp_minus _ hcondition
      oracleMinus_inverse := RHSQueryHardness.preparationOracleMinus_comp_plus _ hcondition
      inversePlus := RHSQueryHardness.inverseMap_preparedPlus _
      inverseMinus := RHSQueryHardness.inverseMap_preparedMinus _
      inverseGainRatio :=
        RHSQueryHardness.laplacian_inverse_gain_ratio_eq_kappaPlus G htwo hmax
      solvePlus := hsolvePlus
      solveMinus := hsolveMinus }
  ⟩

private theorem normalized_balanced_target_reachable
    (G : WeightedGraph n m) (hconn : G.CombinatoriallyConnected) (hn : 0 < n)
    (target : Fin n → ℝ) (hbalanced : RHSQueryHardness.IsBalanced target)
    (hnormalized : dotProduct target target = 1) :
    ∃ (rhs : Fin n → ℝ) (scale : ℝ),
      RHSQueryHardness.IsBalanced rhs ∧
        RHSQueryHardness.sqNorm rhs = 1 ∧
        0 < scale ∧
        G.laplacian (fun _ ↦ 1) *ᵥ (scale • target) = rhs := by
  let theta := SpectralHardPair.asZeroSumVector target hbalanced
  have htarget : target ≠ 0 := by
    intro hzero
    rw [hzero] at hnormalized
    simp at hnormalized
  have htheta : theta ≠ 0 := by
    intro hzero
    apply htarget
    funext i
    have hi := congrArg
      (fun z : zeroSumSubspace n ↦ (z : EuclideanSpace ℝ (Fin n)) i) hzero
    simpa [theta, SpectralHardPair.asZeroSumVector] using hi
  obtain ⟨rhsZero, scale, hrhsNorm, hscale, hsolve⟩ :=
    normalized_rhs_reaches_every_target
      (SpectralHardPair.restrictedLaplacianEquiv G hconn hn) theta htheta
  let rhs : Fin n → ℝ := fun i ↦ (rhsZero : EuclideanSpace ℝ (Fin n)) i
  have hrhsBalanced : RHSQueryHardness.IsBalanced rhs := by
    change ∑ i, (rhsZero : EuclideanSpace ℝ (Fin n)) i = 0
    exact rhsZero.2
  have hrhsSqNorm : RHSQueryHardness.sqNorm rhs = 1 := by
    have hsquares := SpectralHardPair.zeroSum_norm_sq rhsZero
    rw [hrhsNorm] at hsquares
    simpa [rhs, RHSQueryHardness.sqNorm, dotProduct, pow_two] using hsquares.symm
  have happly := congrArg
    (SpectralHardPair.restrictedLaplacianEquiv G hconn hn) hsolve
  have hrestricted : SpectralHardPair.restrictedLaplacian G (scale • theta) = rhsZero := by
    change (SpectralHardPair.restrictedLaplacianEquiv G hconn hn) (scale • theta) = rhsZero
    simpa using happly.symm
  have hcoe := congrArg
    (fun z : zeroSumSubspace n ↦ (z : EuclideanSpace ℝ (Fin n))) hrestricted
  have hscaledAction :
      scale • (G.laplacian (fun _ ↦ 1) *ᵥ target) = rhs := by
    apply WithLp.toLp_injective 2
    simpa [rhs, theta, SpectralHardPair.restrictedLaplacian_coe,
      SpectralHardPair.laplacianOperator_apply, SpectralHardPair.asZeroSumVector] using hcoe
  have hcoordinate :
      G.laplacian (fun _ ↦ 1) *ᵥ (scale • target) = rhs := by
    calc
      G.laplacian (fun _ ↦ 1) *ᵥ (scale • target) =
          scale • (G.laplacian (fun _ ↦ 1) *ᵥ target) := by
        funext i
        simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = rhs := hscaledAction
  exact ⟨rhs, scale, hrhsBalanced, hrhsSqNorm, hscale, hcoordinate⟩

private theorem normalized_zeroSum_target_reachable
    (G : WeightedGraph n m) (hconn : G.CombinatoriallyConnected) (hn : 0 < n)
    (target : zeroSumSubspace n) (hnormalized : ‖target‖ = 1) :
    ∃ (rhs : Fin n → ℝ) (scale : ℝ),
      RHSQueryHardness.IsBalanced rhs ∧
        RHSQueryHardness.sqNorm rhs = 1 ∧
        0 < scale ∧
        G.laplacian (fun _ ↦ 1) *ᵥ (scale • fun i ↦ target.1 i) = rhs := by
  let coordinates : Fin n → ℝ := fun i ↦ target.1 i
  have hbalanced : RHSQueryHardness.IsBalanced coordinates := by
    change ∑ i, target.1 i = 0
    exact target.2
  have hnormalized' : dotProduct coordinates coordinates = 1 := by
    have hnorm := SpectralHardPair.zeroSum_norm_sq target
    rw [hnormalized] at hnorm
    simpa [coordinates, dotProduct, pow_two] using hnorm.symm
  simpa [coordinates] using
    normalized_balanced_target_reachable G hconn hn coordinates hbalanced hnormalized'

private theorem balanced_tomography_lowerBound {index : Type*}
    (hn : 1 < n) (target : index → zeroSumSubspace n) (calls : index → ℝ)
    (basis : zeroSumSubspace n)
    (prepare prepareInv : index → zeroSumSubspace n → zeroSumSubspace n)
    (error successProbability constant : ℝ)
    (tomography : PureStateTomographyBound target calls basis prepare prepareInv error
      successProbability constant) :
    ∃ p, (constant / 2) * ((n : ℝ) / error) ≤ calls p := by
  obtain ⟨p, hp⟩ := tomography.lowerBound
  have hdim := finrank_zeroSumSubspace (Nat.zero_lt_of_lt hn)
  have hnat : n ≤ (n - 1) * 2 := by omega
  have hhalf : (n : ℝ) / 2 ≤ (Module.finrank ℝ (zeroSumSubspace n) : ℝ) := by
    rw [hdim]
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
    exact_mod_cast hnat
  refine ⟨p, ?_⟩
  calc
    (constant / 2) * ((n : ℝ) / error) =
        constant * (((n : ℝ) / 2) / error) := by ring
    _ ≤ constant * ((Module.finrank ℝ (zeroSumSubspace n) : ℝ) / error) := by
      exact mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right hhalf tomography.error_pos.le)
        tomography.constant_pos.le
    _ ≤ calls p := hp

private theorem sparse_classical_lt_total
    (nn mm classicalTime total classicalConstant sparseConstant logFactor
      quantumPerVertex : ℝ)
    (hn : 0 < nn) (hconstant : 0 ≤ classicalConstant) (hlog : 0 ≤ logFactor)
    (hsparse : mm ≤ sparseConstant * nn)
    (hclassical : classicalTime ≤ classicalConstant * mm * logFactor)
    (hthreshold : classicalConstant * sparseConstant * logFactor < quantumPerVertex)
    (hquantum : nn * quantumPerVertex ≤ total) :
    classicalTime < total := by
  have hsparseTime :
      classicalConstant * mm * logFactor ≤
        classicalConstant * (sparseConstant * nn) * logFactor :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsparse hconstant) hlog
  have hstrict :
      classicalConstant * (sparseConstant * nn) * logFactor <
        nn * quantumPerVertex := by
    calc
      classicalConstant * (sparseConstant * nn) * logFactor =
          nn * (classicalConstant * sparseConstant * logFactor) := by ring
      _ < nn * quantumPerVertex := mul_lt_mul_of_pos_left hthreshold hn
  exact lt_of_le_of_lt hclassical
    (lt_of_le_of_lt hsparseTime (lt_of_lt_of_le hstrict hquantum))

/-- Fixed schedule full readout lower bound for one graph, relative to the explicit hybrid and
tomography premises. -/
theorem proposition3_fixedScheduleReadout {index : Type*}
    (G : WeightedGraph n m) (hconn : G.CombinatoriallyConnected) (hn : 1 < n)
    (hardPair : GraphHardPairCertificate G)
    (qSolve : ℕ) (calls total classicalTime loadTime : index → ℝ)
    (target : index → zeroSumSubspace n) (isDense : index → Prop)
    (preparePlus prepareMinus preparePlusInv prepareMinusInv :
      (Fin 2 → ℝ) → Fin 2 → ℝ)
    (tomographyBasis : zeroSumSubspace n)
    (tomographyPrepare tomographyPrepareInv :
      index → zeroSumSubspace n → zeroSumSubspace n)
    (distance gap hybridConstant error successProbability tomographyConstant
      classicalConstant sparseConstant classicalLogFactor loadingConstant : ℝ)
    (hybrid : ControlledPreparationHybridBound hardPair.pair qSolve
      (effectiveConditionNumber G (fun _ ↦ 1)) distance gap hybridConstant preparePlus
      prepareMinus preparePlusInv prepareMinusInv)
    (tomography : PureStateTomographyBound target calls tomographyBasis
      tomographyPrepare tomographyPrepareInv error successProbability tomographyConstant)
    (classicalSolve : ClassicalSDDSolveBound G classicalTime classicalConstant
      classicalLogFactor)
    (denseLoading : DenseLoadingBound n isDense loadTime loadingConstant)
    (htotal : ∀ p, calls p * qSolve ≤ total p)
    (hsparse : (m : ℝ) ≤ sparseConstant * n)
    (hthreshold : classicalConstant * sparseConstant * classicalLogFactor <
      (tomographyConstant / 2) * gap * effectiveConditionNumber G (fun _ ↦ 1) /
        (hybridConstant * error)) :
    ∃ (p : index) (rhs : Fin n → ℝ) (scale : ℝ),
      (tomographyConstant / 2) * gap *
          ((n : ℝ) * effectiveConditionNumber G (fun _ ↦ 1)) /
          (hybridConstant * error) ≤ total p ∧
        RHSQueryHardness.IsBalanced rhs ∧
        RHSQueryHardness.sqNorm rhs = 1 ∧
        0 < scale ∧
        G.laplacian (fun _ ↦ 1) *ᵥ (scale • fun i ↦ (target p).1 i) = rhs ∧
        classicalTime p < total p ∧
        (isDense p → loadingConstant * n ≤ loadTime p) := by
  have htomography := balanced_tomography_lowerBound hn target calls tomographyBasis
    tomographyPrepare tomographyPrepareInv error successProbability tomographyConstant tomography
  obtain ⟨p, hquantum⟩ := clean_qls_worst_case_product qSolve calls total n error
    (effectiveConditionNumber G (fun _ ↦ 1)) distance gap hybridConstant
    (tomographyConstant / 2) (by exact_mod_cast Nat.zero_lt_of_lt hn) tomography.error_pos
    hardPair.condition_pos hybrid.gap_pos hybrid.constant_pos
    (div_pos tomography.constant_pos (by norm_num)) hybrid.separated hybrid.progress
    htomography htotal
  obtain ⟨rhs, scale, hrhsBalanced, hrhsNormalized, hscale, hreach⟩ :=
    normalized_zeroSum_target_reachable G hconn (Nat.zero_lt_of_lt hn) (target p)
      (tomography.normalized p)
  have hquantumPerVertex :
      (n : ℝ) * ((tomographyConstant / 2) * gap *
          effectiveConditionNumber G (fun _ ↦ 1) / (hybridConstant * error)) ≤ total p := by
    calc
      (n : ℝ) * ((tomographyConstant / 2) * gap *
          effectiveConditionNumber G (fun _ ↦ 1) / (hybridConstant * error)) =
          (tomographyConstant / 2) * gap *
            ((n : ℝ) * effectiveConditionNumber G (fun _ ↦ 1)) /
              (hybridConstant * error) := by ring
      _ ≤ total p := hquantum
  have hclassical := sparse_classical_lt_total n m (classicalTime p) (total p)
    classicalConstant sparseConstant classicalLogFactor
    ((tomographyConstant / 2) * gap * effectiveConditionNumber G (fun _ ↦ 1) /
      (hybridConstant * error))
    (by exact_mod_cast Nat.zero_lt_of_lt hn) classicalSolve.constant_nonnegative
    classicalSolve.logFactor_nonnegative hsparse (classicalSolve.upperBound p)
    hthreshold hquantumPerVertex
  exact ⟨p, rhs, scale, hquantum, hrhsBalanced, hrhsNormalized, hscale, hreach,
    hclassical, denseLoading.lowerBound p⟩

/-- Fixed schedule full readout lower bound when the fixed graph condition number grows
linearly. -/
theorem proposition3_gridReadout {index : Type*}
    (G : WeightedGraph n m) (hconn : G.CombinatoriallyConnected) (hn : 1 < n)
    (hardPair : GraphHardPairCertificate G)
    (qSolve : ℕ) (calls total classicalTime loadTime : index → ℝ)
    (target : index → zeroSumSubspace n) (isDense : index → Prop)
    (preparePlus prepareMinus preparePlusInv prepareMinusInv :
      (Fin 2 → ℝ) → Fin 2 → ℝ)
    (tomographyBasis : zeroSumSubspace n)
    (tomographyPrepare tomographyPrepareInv :
      index → zeroSumSubspace n → zeroSumSubspace n)
    (distance gap hybridConstant error successProbability tomographyConstant cK
      classicalConstant sparseConstant classicalLogFactor loadingConstant : ℝ)
    (hybrid : ControlledPreparationHybridBound hardPair.pair qSolve
      (effectiveConditionNumber G (fun _ ↦ 1)) distance gap hybridConstant preparePlus
      prepareMinus preparePlusInv prepareMinusInv)
    (tomography : PureStateTomographyBound target calls tomographyBasis
      tomographyPrepare tomographyPrepareInv error successProbability tomographyConstant)
    (classicalSolve : ClassicalSDDSolveBound G classicalTime classicalConstant
      classicalLogFactor)
    (denseLoading : DenseLoadingBound n isDense loadTime loadingConstant)
    (htotal : ∀ p, calls p * qSolve ≤ total p)
    (hconditionLinear : cK * (n : ℝ) ≤ effectiveConditionNumber G (fun _ ↦ 1))
    (hsparse : (m : ℝ) ≤ sparseConstant * n)
    (hthreshold : classicalConstant * sparseConstant * classicalLogFactor <
      (tomographyConstant / 2) * gap * cK * n / (hybridConstant * error)) :
    ∃ (p : index) (rhs : Fin n → ℝ) (scale : ℝ),
      (tomographyConstant / 2) * gap * cK * (n : ℝ) ^ 2 /
          (hybridConstant * error) ≤ total p ∧
        RHSQueryHardness.IsBalanced rhs ∧
        RHSQueryHardness.sqNorm rhs = 1 ∧
        0 < scale ∧
        G.laplacian (fun _ ↦ 1) *ᵥ (scale • fun i ↦ (target p).1 i) = rhs ∧
        classicalTime p < total p ∧
        (isDense p → loadingConstant * n ≤ loadTime p) := by
  have htomography := balanced_tomography_lowerBound hn target calls tomographyBasis
    tomographyPrepare tomographyPrepareInv error successProbability tomographyConstant tomography
  obtain ⟨p, hquantum⟩ := clean_qls_worst_case_grid_product qSolve calls total n error
    (effectiveConditionNumber G (fun _ ↦ 1)) distance gap hybridConstant
    (tomographyConstant / 2) cK (by exact_mod_cast Nat.zero_lt_of_lt hn)
    tomography.error_pos hardPair.condition_pos hybrid.gap_pos hybrid.constant_pos
    (div_pos tomography.constant_pos (by norm_num)) hybrid.separated hybrid.progress htomography
    htotal hconditionLinear
  obtain ⟨rhs, scale, hrhsBalanced, hrhsNormalized, hscale, hreach⟩ :=
    normalized_zeroSum_target_reachable G hconn (Nat.zero_lt_of_lt hn) (target p)
      (tomography.normalized p)
  have hquantumPerVertex :
      (n : ℝ) * ((tomographyConstant / 2) * gap * cK * n /
        (hybridConstant * error)) ≤ total p := by
    calc
      (n : ℝ) * ((tomographyConstant / 2) * gap * cK * n /
          (hybridConstant * error)) =
          (tomographyConstant / 2) * gap * cK * (n : ℝ) ^ 2 /
            (hybridConstant * error) := by ring
      _ ≤ total p := hquantum
  have hclassical := sparse_classical_lt_total n m (classicalTime p) (total p)
    classicalConstant sparseConstant classicalLogFactor
    ((tomographyConstant / 2) * gap * cK * n / (hybridConstant * error))
    (by exact_mod_cast Nat.zero_lt_of_lt hn) classicalSolve.constant_nonnegative
    classicalSolve.logFactor_nonnegative hsparse (classicalSolve.upperBound p)
    hthreshold hquantumPerVertex
  exact ⟨p, rhs, scale, hquantum, hrhsBalanced, hrhsNormalized, hscale, hreach,
    hclassical, denseLoading.lowerBound p⟩

/-- Fixed schedule full readout lower bound when the fixed graph condition number grows
quadratically. -/
theorem proposition3_corridorReadout {index : Type*}
    (G : WeightedGraph n m) (hconn : G.CombinatoriallyConnected) (hn : 1 < n)
    (hardPair : GraphHardPairCertificate G)
    (qSolve : ℕ) (calls total classicalTime loadTime : index → ℝ)
    (target : index → zeroSumSubspace n) (isDense : index → Prop)
    (preparePlus prepareMinus preparePlusInv prepareMinusInv :
      (Fin 2 → ℝ) → Fin 2 → ℝ)
    (tomographyBasis : zeroSumSubspace n)
    (tomographyPrepare tomographyPrepareInv :
      index → zeroSumSubspace n → zeroSumSubspace n)
    (distance gap hybridConstant error successProbability tomographyConstant cK
      classicalConstant sparseConstant classicalLogFactor loadingConstant : ℝ)
    (hybrid : ControlledPreparationHybridBound hardPair.pair qSolve
      (effectiveConditionNumber G (fun _ ↦ 1)) distance gap hybridConstant preparePlus
      prepareMinus preparePlusInv prepareMinusInv)
    (tomography : PureStateTomographyBound target calls tomographyBasis
      tomographyPrepare tomographyPrepareInv error successProbability tomographyConstant)
    (classicalSolve : ClassicalSDDSolveBound G classicalTime classicalConstant
      classicalLogFactor)
    (denseLoading : DenseLoadingBound n isDense loadTime loadingConstant)
    (htotal : ∀ p, calls p * qSolve ≤ total p)
    (hconditionQuadratic :
      cK * (n : ℝ) ^ 2 ≤ effectiveConditionNumber G (fun _ ↦ 1))
    (hsparse : (m : ℝ) ≤ sparseConstant * n)
    (hthreshold : classicalConstant * sparseConstant * classicalLogFactor <
      (tomographyConstant / 2) * gap * cK * n ^ 2 / (hybridConstant * error)) :
    ∃ (p : index) (rhs : Fin n → ℝ) (scale : ℝ),
      (tomographyConstant / 2) * gap * cK * (n : ℝ) ^ 3 /
          (hybridConstant * error) ≤ total p ∧
        RHSQueryHardness.IsBalanced rhs ∧
        RHSQueryHardness.sqNorm rhs = 1 ∧
        0 < scale ∧
        G.laplacian (fun _ ↦ 1) *ᵥ (scale • fun i ↦ (target p).1 i) = rhs ∧
        classicalTime p < total p ∧
        (isDense p → loadingConstant * n ≤ loadTime p) := by
  have htomography := balanced_tomography_lowerBound hn target calls tomographyBasis
    tomographyPrepare tomographyPrepareInv error successProbability tomographyConstant tomography
  obtain ⟨p, hquantum⟩ := clean_qls_worst_case_corridor_product qSolve calls total n error
    (effectiveConditionNumber G (fun _ ↦ 1)) distance gap hybridConstant
    (tomographyConstant / 2) cK (by exact_mod_cast Nat.zero_lt_of_lt hn)
    tomography.error_pos hardPair.condition_pos hybrid.gap_pos hybrid.constant_pos
    (div_pos tomography.constant_pos (by norm_num)) hybrid.separated hybrid.progress htomography
    htotal hconditionQuadratic
  obtain ⟨rhs, scale, hrhsBalanced, hrhsNormalized, hscale, hreach⟩ :=
    normalized_zeroSum_target_reachable G hconn (Nat.zero_lt_of_lt hn) (target p)
      (tomography.normalized p)
  have hquantumPerVertex :
      (n : ℝ) * ((tomographyConstant / 2) * gap * cK * n ^ 2 /
        (hybridConstant * error)) ≤ total p := by
    calc
      (n : ℝ) * ((tomographyConstant / 2) * gap * cK * n ^ 2 /
          (hybridConstant * error)) =
          (tomographyConstant / 2) * gap * cK * (n : ℝ) ^ 3 /
            (hybridConstant * error) := by ring
      _ ≤ total p := hquantum
  have hclassical := sparse_classical_lt_total n m (classicalTime p) (total p)
    classicalConstant sparseConstant classicalLogFactor
    ((tomographyConstant / 2) * gap * cK * n ^ 2 / (hybridConstant * error))
    (by exact_mod_cast Nat.zero_lt_of_lt hn) classicalSolve.constant_nonnegative
    classicalSolve.logFactor_nonnegative hsparse (classicalSolve.upperBound p)
    hthreshold hquantumPerVertex
  exact ⟨p, rhs, scale, hquantum, hrhsBalanced, hrhsNormalized, hscale, hreach,
    hclassical, denseLoading.lowerBound p⟩

/-- A bus or branch observable with nonzero gap inherits the fixed solve schedule's right hand
side query lower bound and remains distinguishable under quarter-gap errors. -/
theorem proposition3_localObservable
    (pair : RHSQueryHardness.BalancedModePair n) (qSolve : ℕ)
    (condition solverDistance solverGap hybridConstant observableQueries : ℝ)
    (preparePlus prepareMinus preparePlusInv prepareMinusInv :
      (Fin 2 → ℝ) → Fin 2 → ℝ)
    (hybrid : ControlledPreparationHybridBound pair qSolve condition solverDistance solverGap
      hybridConstant preparePlus prepareMinus preparePlusInv prepareMinusInv)
    (husesSolve : (qSolve : ℝ) ≤ observableQueries)
    (isBranch : Bool) (i j : Fin n)
    (estimatePlus estimateMinus gamma : ℝ) (_hgamma : 0 < gamma)
    (hexact :
      |(if isBranch then
          (RHSQueryHardness.balancedSolutionPlus pair i -
            RHSQueryHardness.balancedSolutionPlus pair j) ^ 2
        else (RHSQueryHardness.balancedSolutionPlus pair i) ^ 2) -
        (if isBranch then
          (RHSQueryHardness.balancedSolutionMinus pair i -
            RHSQueryHardness.balancedSolutionMinus pair j) ^ 2
        else (RHSQueryHardness.balancedSolutionMinus pair i) ^ 2)| = gamma)
    (hplus :
      |estimatePlus -
        (if isBranch then
          (RHSQueryHardness.balancedSolutionPlus pair i -
            RHSQueryHardness.balancedSolutionPlus pair j) ^ 2
        else (RHSQueryHardness.balancedSolutionPlus pair i) ^ 2)| ≤ gamma / 4)
    (hminus :
      |estimateMinus -
        (if isBranch then
          (RHSQueryHardness.balancedSolutionMinus pair i -
            RHSQueryHardness.balancedSolutionMinus pair j) ^ 2
        else (RHSQueryHardness.balancedSolutionMinus pair i) ^ 2)| ≤ gamma / 4) :
    solverGap * condition / hybridConstant ≤ observableQueries ∧
      gamma / 2 ≤ |estimatePlus - estimateMinus| := by
  have hquery : solverGap * condition / hybridConstant ≤ (qSolve : ℝ) :=
    RHSQueryHardness.rhs_query_lower_bound qSolve solverDistance solverGap hybridConstant
      condition hybrid.condition_pos hybrid.constant_pos hybrid.separated hybrid.progress
  refine ⟨hquery.trans husesSolve, ?_⟩
  by_cases hgamma : 0 < gamma
  · exact RHSQueryHardness.estimates_separated_of_quarter_gap
      (if isBranch then
        (RHSQueryHardness.balancedSolutionPlus pair i -
          RHSQueryHardness.balancedSolutionPlus pair j) ^ 2
      else (RHSQueryHardness.balancedSolutionPlus pair i) ^ 2)
      (if isBranch then
        (RHSQueryHardness.balancedSolutionMinus pair i -
          RHSQueryHardness.balancedSolutionMinus pair j) ^ 2
      else (RHSQueryHardness.balancedSolutionMinus pair i) ^ 2)
      estimatePlus estimateMinus gamma hexact hplus hminus
  · exact (hgamma _hgamma).elim

/-- The corrected trace condition bound transfers to the grounded matrix. -/
theorem groundedConditioningTransfer (G : WeightedGraph n m) (slack : Fin n)
    (Δ bmax : ℝ) (hconn : G.CombinatoriallyConnected) (hn : 1 < n)
    (hdegree : ((G.incidentEdges slack).card : ℝ) ≤ Δ)
    (hbmaxNonnegative : 0 ≤ bmax) (hweight : ∀ e, G.weights e ≤ bmax)
    (hcorrected : 0 ≤ 2 * G.totalWeight - Δ * bmax) :
    ((2 * G.totalWeight - Δ * bmax) / ((n : ℝ) - 1)) /
        laplacian_eigenvalue₂ G (fun _ ↦ 1) ≤
      groundedConditionNumber G slack := by
  exact corrected_trace_over_lambda2_le_groundedConditionNumber G slack Δ bmax hconn hn
    hdegree hbmaxNonnegative hweight hcorrected

/-- At flat start, the lossless active-angle block is the DC susceptance Laplacian. -/
theorem flatStartACBlock (G : WeightedGraph n m) :
    G.acAngleJacobian (fun _ ↦ 0) = G.laplacian (fun _ ↦ 1) := by
  exact G.acAngleJacobian_flat_eq_laplacian

/-- At a strictly feasible iterate, the DC optimal power flow barrier scales are positive and
the angle block is the corresponding rescaled Laplacian. -/
theorem dcOpfBarrierBlock (G : WeightedGraph n m)
    (limit : Fin m → ℝ) (barrier : ℝ) (angle : Fin n → ℝ)
    (hbarrier : 0 < barrier)
    (hminus : ∀ e, 0 < limit e - G.dcBranchFlow angle e)
    (hplus : ∀ e, 0 < limit e + G.dcBranchFlow angle e) :
    (∀ e, 0 < G.dcOpfBarrierScale limit barrier angle e) ∧
      G.dcOpfNetworkBlock limit barrier angle =
        G.laplacian (G.dcOpfBarrierScale limit barrier angle) := by
  exact ⟨G.dcOpfBarrierScale_pos limit barrier angle hbarrier hminus hplus,
    G.dcOpfNetworkBlock_eq_laplacian limit barrier angle⟩

/-- The near planar extension from a crossing schedule, a planarity certificate for the
constructed planarization, and the theorem-valued external Lipton--Tarjan premise. -/
theorem nearPlanarFromCrossingDrawing {c : ℕ} (Planar : PlanarityPredicate)
    (hLT : LiptonTarjanVertexCostTheorem Planar) (G : WeightedGraph n m)
    (schedule : CrossingSchedule G c)
    (hplanar : Planar _ schedule.planarizedGraph)
    (hsmall : 1152 * (n + c) ≤ n ^ 2) (Δ bmax : ℝ)
    (hdegree : ∀ i, ((G.incidentEdges i).card : ℝ) ≤ Δ)
    (hweight : ∀ e, G.weights e ≤ bmax)
    (hconn : G.CombinatoriallyConnected) :
    5 / 36 * G.totalWeight / (Real.sqrt (8 * ((n : ℝ) + c)) * Δ * bmax) ≤
      effectiveConditionNumber G (fun _ ↦ 1) := by
  exact schedule.nearPlanar_kappa_bound Planar hLT hplanar hsmall Δ bmax hdegree hweight
    hconn

end PaperClaims

end
