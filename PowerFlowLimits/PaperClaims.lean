/-
Copyright (c) 2026 Power Flow Limits contributors. All rights reserved.
Released under the MIT license. See LICENSE for details.
-/

import PowerFlowLimits.ACFlatStart
import PowerFlowLimits.ACPowerFlow
import PowerFlowLimits.AnyDistribution
import PowerFlowLimits.Corridors
import PowerFlowLimits.DcOpfNewton
import PowerFlowLimits.EndToEnd
import PowerFlowLimits.EnergyNorm
import PowerFlowLimits.Grounded
import PowerFlowLimits.GroundedTransfer
import PowerFlowLimits.InputDependent
import PowerFlowLimits.OptimalPowerFlow
import PowerFlowLimits.PlanarSeparator
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

/-- The weighted and topology only separator condition number bounds. -/
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
    max (2 * β * (1 - β) * G.totalWeight / (s * Δ * bmax))
        (2 * β * (1 - β) * n / (s * Δ)) ≤
      effectiveConditionNumber G (fun _ ↦ 1) := by
  exact separator_kappa_bound_combined G A X B s Δ bmax β hcover hdisjoint
    hnoCrossing hX
    hdegree hweight hβ hβhalf hA hB hconn

/-- Corollary 1(i), first claim. A tree decomposition of width at most `τ ≤ n / 4 - 1` yields a
`(τ + 1, 1 / 4)` separation of the grid. -/
theorem corollary1_treewidthSeparation {k τ : ℕ} (G : WeightedGraph n m)
    (D : RootedTreeDecomposition G.toSimpleGraph k)
    (hn : 0 < n) (hwidth : D.HasWidthAtMost τ) (hτ : τ + 1 ≤ n / 4) :
    ∃ A X B : Finset (Fin n),
      A ∪ X ∪ B = Finset.univ ∧
      Disjoint (A ∪ X) B ∧
      (∀ e, ¬(G.posEndpoint e ∈ A ∧ G.negEndpoint e ∈ B) ∧
        ¬(G.posEndpoint e ∈ B ∧ G.negEndpoint e ∈ A)) ∧
      (X.card : ℝ) ≤ (τ : ℝ) + 1 ∧
      (n : ℝ) / 4 ≤ ((A ∪ X).card : ℝ) ∧
      (n : ℝ) / 4 ≤ (B.card : ℝ) := by
  exact G.exists_quarter_separation_of_tree_decomposition D hn hwidth hτ

/-- The weighted and topology only tree decomposition forms of the treewidth corollary. -/
theorem corollary1_treewidth {k τ : ℕ} (G : WeightedGraph n m)
    (D : RootedTreeDecomposition G.toSimpleGraph k)
    (hn : 0 < n) (hwidth : D.HasWidthAtMost τ) (hτ : τ + 1 ≤ n / 4)
    (Δ bmax : ℝ)
    (hdegree : ∀ i, ((G.incidentEdges i).card : ℝ) ≤ Δ)
    (hweight : ∀ e, G.weights e ≤ bmax)
    (hconn : G.CombinatoriallyConnected) :
    max (3 / 8 * G.totalWeight / (((τ : ℝ) + 1) * Δ * bmax))
        (3 / 8 * n / (((τ : ℝ) + 1) * Δ)) ≤
      effectiveConditionNumber G (fun _ ↦ 1) := by
  exact G.treewidth_kappa_bound_of_tree_decomposition_combined D hn hwidth hτ Δ bmax
    hdegree hweight hconn

/-- The planar corollary from a planarity certificate and the theorem-valued external
Lipton--Tarjan premise. -/
theorem corollary1_planarFromLiptonTarjan (Planar : PlanarityPredicate)
    (hLT : LiptonTarjanVertexCostTheorem Planar) (G : WeightedGraph n m)
    (hplanar : Planar _ G.toSimpleGraph) (hn : 288 ≤ n) (Δ bmax : ℝ)
    (hdegree : ∀ i, ((G.incidentEdges i).card : ℝ) ≤ Δ)
    (hweight : ∀ e, G.weights e ≤ bmax)
    (hconn : G.CombinatoriallyConnected) :
    max (5 / 18 * G.totalWeight / (Real.sqrt (8 * n) * Δ * bmax))
        (5 / 18 * n / (Real.sqrt (8 * n) * Δ)) ≤
      effectiveConditionNumber G (fun _ ↦ 1) := by
  exact planar_kappa_bound_from_lipton_tarjan_combined Planar hLT G hplanar hn Δ bmax
    hdegree hweight hconn

/-- The near planar separator. Placing a dummy vertex at each of `c` branch crossings and
applying the vertex cost form of Lipton--Tarjan gives a separator of at most `2 √(8 (n + c))`
buses whose two sides each hold at most `2 n / 3` buses. -/
theorem nearPlanarSeparatorFromCrossingDrawing {c : ℕ} (Planar : PlanarityPredicate)
    (hLT : LiptonTarjanVertexCostTheorem Planar) (G : WeightedGraph n m)
    (schedule : CrossingSchedule G c) (hn : 0 < n)
    (hplanar : Planar _ schedule.planarizedGraph) :
    ∃ A X B : Finset (Fin n),
      A ∪ X ∪ B = Finset.univ ∧
      Disjoint (A ∪ X) B ∧
      (∀ e, ¬(G.posEndpoint e ∈ A ∧ G.negEndpoint e ∈ B) ∧
        ¬(G.posEndpoint e ∈ B ∧ G.negEndpoint e ∈ A)) ∧
      (X.card : ℝ) ≤ 2 * Real.sqrt (8 * ((n : ℝ) + c)) ∧
      (A.card : ℝ) ≤ 2 * n / 3 ∧
      (B.card : ℝ) ≤ 2 * n / 3 := by
  obtain ⟨P⟩ := schedule.exists_projectedNearPlanarPartition Planar hLT hn hplanar
  exact ⟨P.left, P.separator, P.right, P.cover, P.disjoint_union_right,
    P.no_left_right_branch, P.separator_card_le, P.left_card_le, P.right_card_le⟩

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
    max (5 / 36 * G.totalWeight /
          (Real.sqrt (8 * ((n : ℝ) + c)) * Δ * bmax))
        (5 / 36 * n / (Real.sqrt (8 * ((n : ℝ) + c)) * Δ)) ≤
      effectiveConditionNumber G (fun _ ↦ 1) := by
  exact schedule.nearPlanar_kappa_bound_combined Planar hLT hplanar hsmall Δ bmax
    hdegree hweight hconn

/-- The macroscopic corridor condition number bound. -/
theorem proposition1_corridor (G : WeightedGraph n m)
    (left right : Finset (Fin n)) (ℓ : ℕ) (path : Fin ℓ → Fin n)
    (pathEdges : Finset (Fin m))
    (corridor : CorridorTopology G left right ℓ path pathEdges)
    (β : ℝ) (hβ : 0 < β)
    (hleftSize : β * n ≤ (left.card : ℝ))
    (hrightSize : β * n ≤ (right.card : ℝ))
    (emax : Fin m) (hmax : ∀ e, G.weights e ≤ G.weights emax)
    (hconn : G.CombinatoriallyConnected) :
    2 * β ^ 2 * ((ℓ : ℝ) - 1) ^ 2 *
        max G.totalWeight ((n : ℝ) * G.weights emax) /
          (∑ e ∈ pathEdges, G.weights e) ≤
      effectiveConditionNumber G (fun _ ↦ 1) ∧
      2 * β ^ 2 * n * ((ℓ : ℝ) - 1) ≤
        2 * β ^ 2 * ((ℓ : ℝ) - 1) ^ 2 *
          max G.totalWeight ((n : ℝ) * G.weights emax) /
            (∑ e ∈ pathEdges, G.weights e) ∧
      2 * β ^ 2 * n * ((ℓ : ℝ) - 1) ≤
        effectiveConditionNumber G (fun _ ↦ 1) := by
  have hexact := corridor_kappa_bound_combined_exact G left right ℓ path pathEdges
    corridor β hβ hleftSize hrightSize emax hmax hconn
  have hchain := corridor_topological_le_combined_exact G left right ℓ path pathEdges
    corridor β hβ emax hmax
  exact ⟨hexact, hchain, hchain.trans hexact⟩

/-- The topology only term of Theorem 1 holds with probability one for random positive
susceptances under any joint distribution. -/
theorem anyDistribution_separator {sample : Type*} [MeasurableSpace sample]
    (measure : MeasureTheory.Measure sample) [MeasureTheory.IsProbabilityMeasure measure]
    (G : WeightedGraph n m) (weight : sample → Fin m → ℝ)
    (hpositive : ∀ ω e, 0 < weight ω e)
    (A X B : Finset (Fin n)) (s Δ β : ℝ)
    (hcover : A ∪ X ∪ B = Finset.univ)
    (hdisjoint : Disjoint (A ∪ X) B)
    (hnoCrossing : ∀ e, ¬(G.posEndpoint e ∈ A ∧ G.negEndpoint e ∈ B) ∧
      ¬(G.posEndpoint e ∈ B ∧ G.negEndpoint e ∈ A))
    (hX : (X.card : ℝ) ≤ s)
    (hdegree : ∀ i, ((G.incidentEdges i).card : ℝ) ≤ Δ)
    (hβ : 0 < β) (hβhalf : β ≤ 1 / 2)
    (hA : β * n ≤ ((A ∪ X).card : ℝ)) (hB : β * n ≤ (B.card : ℝ))
    (hconn : G.CombinatoriallyConnected) :
    measure.real {ω | 2 * β * (1 - β) * n / (s * Δ) ≤
      effectiveConditionNumber (G.withWeights (weight ω) (hpositive ω)) (fun _ ↦ 1)} = 1 := by
  exact separator_topological_bound_surely measure G weight hpositive A X B s Δ β hcover
    hdisjoint hnoCrossing hX hdegree hβ hβhalf hA hB hconn

/-- The topology only bound of Proposition 1 holds with probability one for random positive
susceptances under any joint distribution. -/
theorem anyDistribution_corridor {sample : Type*} [MeasurableSpace sample]
    (measure : MeasureTheory.Measure sample) [MeasureTheory.IsProbabilityMeasure measure]
    (G : WeightedGraph n m) (weight : sample → Fin m → ℝ)
    (hpositive : ∀ ω e, 0 < weight ω e)
    (left right : Finset (Fin n)) (ℓ : ℕ) (path : Fin ℓ → Fin n)
    (pathEdges : Finset (Fin m))
    (corridor : CorridorTopology G left right ℓ path pathEdges)
    (β : ℝ) (hβ : 0 < β)
    (hleftSize : β * n ≤ (left.card : ℝ))
    (hrightSize : β * n ≤ (right.card : ℝ))
    (hconn : G.CombinatoriallyConnected) :
    measure.real {ω | 2 * β ^ 2 * n * ((ℓ : ℝ) - 1) ≤
      effectiveConditionNumber (G.withWeights (weight ω) (hpositive ω)) (fun _ ↦ 1)} = 1 := by
  exact corridor_topological_bound_surely measure G weight hpositive left right ℓ path
    pathEdges corridor β hβ hleftSize hrightSize hconn

/-- The pseudo condition number is the condition number of `B` on balanced injections. If
`B θ = p` with `θ` balanced, then `λ₂ ‖θ‖ ≤ ‖p‖ ≤ λ_max ‖θ‖`, so `κ₊ = ‖B‖₂ ‖B⁺‖₂`. -/
theorem pseudoConditionNumber_balancedSolve (G : WeightedGraph n m) (hn : 1 < n)
    (θ p : Fin n → ℝ) (hθ : ∑ i, θ i = 0)
    (hsolve : ∀ i, ∑ j, G.laplacian (fun _ ↦ 1) i j * θ j = p i) :
    laplacian_eigenvalue₂ G (fun _ ↦ 1) ^ 2 * ∑ i, θ i ^ 2 ≤ ∑ i, p i ^ 2 ∧
      ∑ i, p i ^ 2 ≤ laplacianEigenvalueMax G (fun _ ↦ 1) ^ 2 * ∑ i, θ i ^ 2 := by
  exact balanced_solve_norm_bounds G hn θ p hθ hsolve

/-- Fact (F3), accuracy conversion. A classical output with energy norm relative error
`ε / √κ₊` and balanced error has Euclidean relative error at most `ε`. -/
theorem energyNormAccuracy (G : WeightedGraph n m)
    (hconn : G.CombinatoriallyConnected) (hn : 1 < n)
    (θ θhat : Fin n → ℝ) (ε : ℝ)
    (hbalanced : ∑ i, (θhat i - θ i) = 0)
    (henergy : laplacianEnergy G (fun i ↦ θhat i - θ i) ≤
      (ε / Real.sqrt (effectiveConditionNumber G (fun _ ↦ 1))) ^ 2 * laplacianEnergy G θ) :
    ∑ i, (θhat i - θ i) ^ 2 ≤ ε ^ 2 * ∑ i, θ i ^ 2 := by
  exact euclidean_accuracy_of_scaled_energy_accuracy G hconn hn θ θhat ε hbalanced henergy

/-- The grounded matrix `B_r`. Interlacing gives `λ_min(B_r) ≤ λ₂(B)`, the grounded trace keeps
`b(E)`, and `λ_max(B_r) ≥ max {b(E) / (n - 1), b_e}`, half of Lemma 1(i). -/
theorem groundedHalfLemma1 (G : WeightedGraph n m) (slack : Fin n) (e : Fin m)
    (hn : 1 < n) :
    groundedLaplacianEigenvalueMin G slack ≤ laplacian_eigenvalue₂ G (fun _ ↦ 1) ∧
      G.totalWeight ≤ ∑ i, groundedLaplacian G slack i i ∧
      max (G.totalWeight / ((n : ℝ) - 1)) (G.weights e) ≤
        groundedLaplacianEigenvalueMax G slack := by
  exact ⟨groundedEigenvalueMin_le_lambda2 G slack hn, totalWeight_le_grounded_trace G slack,
    half_lemma1_le_groundedEigenvalueMax G slack e hn⟩

/-- Lemma 1, equation (1), for the grounded matrix with half the constant. -/
theorem groundedLemma1 (G : WeightedGraph n m) (slack : Fin n) (S : Finset (Fin n))
    (e : Fin m) (hne : S.Nonempty) (hproper : S ≠ Finset.univ)
    (hconn : G.CombinatoriallyConnected) :
    max (((S.card : ℝ) / n) * (1 - (S.card : ℝ) / n) * G.totalWeight / G.cutWeight S)
        (((S.card : ℝ) / n) * (1 - (S.card : ℝ) / n) * ((n : ℝ) * G.weights e) /
          G.cutWeight S) ≤
      groundedConditionNumber G slack := by
  exact max_le (cut_totalWeight_bound_le_groundedConditionNumber G slack S hne hproper hconn)
    (cut_edge_bound_le_groundedConditionNumber G slack S e hne hproper hconn)

/-- Theorem 1 for the grounded matrix with half the constant. -/
theorem groundedTheorem1 (G : WeightedGraph n m) (slack : Fin n)
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
    max (β * (1 - β) * G.totalWeight / (s * Δ * bmax))
        (β * (1 - β) * n / (s * Δ)) ≤
      groundedConditionNumber G slack := by
  exact grounded_separator_kappa_bound_combined G slack A X B s Δ bmax β hcover hdisjoint
    hnoCrossing hX hdegree hweight hβ hβhalf hA hB hconn

/-- Corollary 1(i) for the grounded matrix with half the constant. -/
theorem groundedCorollary1_treewidth {k τ : ℕ} (G : WeightedGraph n m) (slack : Fin n)
    (D : RootedTreeDecomposition G.toSimpleGraph k)
    (hwidth : D.HasWidthAtMost τ) (hτ : τ + 1 ≤ n / 4)
    (Δ bmax : ℝ)
    (hdegree : ∀ i, ((G.incidentEdges i).card : ℝ) ≤ Δ)
    (hweight : ∀ e, G.weights e ≤ bmax)
    (hconn : G.CombinatoriallyConnected) :
    max (3 / 16 * G.totalWeight / (((τ : ℝ) + 1) * Δ * bmax))
        (3 / 16 * n / (((τ : ℝ) + 1) * Δ)) ≤
      groundedConditionNumber G slack := by
  exact G.grounded_treewidth_kappa_bound_of_tree_decomposition slack D hwidth hτ Δ bmax
    hdegree hweight hconn

/-- Corollary 1(ii) for the grounded matrix with half the constant, relative to the cited
planar separator theorem. -/
theorem groundedCorollary1_planarFromLiptonTarjan (Planar : PlanarityPredicate)
    (hLT : LiptonTarjanVertexCostTheorem Planar) (G : WeightedGraph n m) (slack : Fin n)
    (hplanar : Planar _ G.toSimpleGraph) (hn : 288 ≤ n) (Δ bmax : ℝ)
    (hdegree : ∀ i, ((G.incidentEdges i).card : ℝ) ≤ Δ)
    (hweight : ∀ e, G.weights e ≤ bmax)
    (hconn : G.CombinatoriallyConnected) :
    max (5 / 36 * G.totalWeight / (Real.sqrt (8 * n) * Δ * bmax))
        (5 / 36 * n / (Real.sqrt (8 * n) * Δ)) ≤
      groundedConditionNumber G slack := by
  obtain ⟨P⟩ := exists_originalPlanarPartition Planar hLT G (by omega) hplanar
  exact grounded_planar_kappa_bound_of_lipton_partition G slack P.left P.separator P.right
    Δ bmax hn P.cover P.disjoint_union_right P.no_left_right_branch P.separator_card_le
    P.left_card_le P.right_card_le hdegree hweight hconn

/-- Proposition 1 for the grounded matrix with half the constant. -/
theorem groundedProposition1 (G : WeightedGraph n m) (slack : Fin n)
    (left right : Finset (Fin n)) (ℓ : ℕ) (path : Fin ℓ → Fin n)
    (pathEdges : Finset (Fin m))
    (corridor : CorridorTopology G left right ℓ path pathEdges)
    (β : ℝ) (hβ : 0 < β)
    (hleftSize : β * n ≤ (left.card : ℝ))
    (hrightSize : β * n ≤ (right.card : ℝ))
    (branch : Fin m)
    (hconn : G.CombinatoriallyConnected) :
    max (β ^ 2 * ((ℓ : ℝ) - 1) ^ 2 * G.totalWeight / (∑ e ∈ pathEdges, G.weights e))
        (max (β ^ 2 * ((ℓ : ℝ) - 1) ^ 2 * ((n : ℝ) * G.weights branch) /
            (∑ e ∈ pathEdges, G.weights e))
          (β ^ 2 * n * ((ℓ : ℝ) - 1))) ≤
      groundedConditionNumber G slack := by
  exact grounded_corridor_kappa_bound_combined G slack left right ℓ path pathEdges corridor
    β hβ hleftSize hrightSize branch hconn

/-- A connected weighted Laplacian with distinct extreme eigenvalues supplies the complete
canonical hard pair certificate. -/
theorem proposition2_balancedHardPair (G : WeightedGraph n m)
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

/-- The decision rule of Proposition 2. The two hard solutions are `scale • ψ₊` and
`scale • ψ₋`. A classical output, or a state when `scale = 1`, within relative accuracy
`ε < 1 / √2` of one of them is not within that accuracy of the other. -/
theorem proposition2_accurateOutputSeparates (pair : RHSQueryHardness.BalancedModePair n)
    (scale ε : ℝ) (hscale : scale ≠ 0) (hε : ε ^ 2 < 1 / 2) (output : Fin n → ℝ) :
    (RHSQueryHardness.sqDistance output
          (scale • RHSQueryHardness.balancedSolutionPlus pair) ≤
        ε ^ 2 * RHSQueryHardness.sqNorm (scale • RHSQueryHardness.balancedSolutionPlus pair) →
      ε ^ 2 * RHSQueryHardness.sqNorm (scale • RHSQueryHardness.balancedSolutionMinus pair) <
        RHSQueryHardness.sqDistance output
          (scale • RHSQueryHardness.balancedSolutionMinus pair)) ∧
      (RHSQueryHardness.sqDistance output
            (scale • RHSQueryHardness.balancedSolutionMinus pair) ≤
          ε ^ 2 *
            RHSQueryHardness.sqNorm (scale • RHSQueryHardness.balancedSolutionMinus pair) →
        ε ^ 2 * RHSQueryHardness.sqNorm (scale • RHSQueryHardness.balancedSolutionPlus pair) <
          RHSQueryHardness.sqDistance output
            (scale • RHSQueryHardness.balancedSolutionPlus pair)) := by
  exact ⟨RHSQueryHardness.hardPair_accurate_output_separates pair scale ε hscale hε output,
    RHSQueryHardness.hardPair_accurate_output_separates' pair scale ε hscale hε output⟩

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
theorem proposition2_fixedScheduleReadout {index : Type*}
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
theorem proposition2_gridReadout {index : Type*}
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
theorem proposition2_corridorReadout {index : Type*}
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
theorem proposition2_localObservable
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

/-- Input dependent solvers on the hard pair. The effective condition number never exceeds
`κ₊`, and it equals `κ₊` on both hard solutions for every `ε < 1 / √2`. -/
theorem inputDependentSolvers_hardPair (G : WeightedGraph n m)
    (hconn : G.CombinatoriallyConnected) (hn : 1 < n)
    (hardPair : GraphHardPairCertificate G) (ε : ℝ) (hε : ε ^ 2 < 1 / 2) :
    (∀ ψ : Fin n → ℝ, inputDependentConditionNumber G ε ψ ≤
        effectiveConditionNumber G (fun _ ↦ 1)) ∧
      inputDependentConditionNumber G ε
          (RHSQueryHardness.balancedSolutionPlus hardPair.pair) =
        effectiveConditionNumber G (fun _ ↦ 1) ∧
      inputDependentConditionNumber G ε
          (RHSQueryHardness.balancedSolutionMinus hardPair.pair) =
        effectiveConditionNumber G (fun _ ↦ 1) := by
  have hordered :=
    SpectralHardPair.lambda2_le_lambdaMax_of_combinatoriallyConnected G hconn hn
  have hpositive := combinatoriallyConnected_implies_spectralConnected G hconn hn
  unfold WeightedGraph.Connected at hpositive
  obtain ⟨hplus, hminus⟩ := inputDependentConditionNumber_hardPair G hardPair.pair
    hardPair.slowEigen hordered ε hε
  exact ⟨fun ψ ↦ inputDependentConditionNumber_le G ε ψ hpositive hordered, hplus, hminus⟩

/-- Substituting `κ ≥ c n` into the criterion `D κ^{3/2} ≤ n / d` of Pareek et al. gives
`D c^{3/2} √n ≤ 1`, so no readout level `D ≥ 1` passes once `c^{3/2} √n > 1`. -/
theorem hhlCriterion_readoutLevel (nodes sparsity readout condition growth : ℝ)
    (hnodes : 0 < nodes) (hsparsity : 1 ≤ sparsity) (hreadout : 0 ≤ readout)
    (hgrowth : 0 < growth) (hcondition : growth * nodes ≤ condition)
    (hcriterion : readout * condition ^ (3 / 2 : ℝ) ≤ nodes / sparsity) :
    readout * (growth ^ (3 / 2 : ℝ) * Real.sqrt nodes) ≤ 1 ∧
      (1 < growth ^ (3 / 2 : ℝ) * Real.sqrt nodes → readout < 1) := by
  exact ⟨hhl_criterion_readout_bound nodes sparsity readout condition growth hnodes
      hsparsity hreadout hgrowth hcondition hcriterion,
    fun hlarge ↦ hhl_criterion_no_readout_level nodes sparsity readout condition growth
      hnodes hsparsity hreadout hgrowth hcondition hcriterion hlarge⟩

/-- At flat start, the lossless active-angle block is the DC susceptance Laplacian. -/
theorem flatStartACBlock (G : WeightedGraph n m) :
    G.acAngleJacobian (fun _ ↦ 0) = G.laplacian (fun _ ↦ 1) := by
  exact G.acAngleJacobian_flat_eq_laplacian

/-- The off diagonal blocks of the lossless Newton Jacobian vanish at flat angles. The model
with voltage magnitudes reduces to the unit voltage model, its active injections vanish at flat
angles, and the derivatives of active power in voltage magnitude and of reactive power in angle
are zero there. -/
theorem flatStartACOffDiagonalBlocks (G : WeightedGraph n m)
    (shunt voltage direction : Fin n → ℝ) (i : Fin n) :
    (∀ θ : Fin n → ℝ, G.acActivePower θ (fun _ ↦ 1) = G.acActiveInjection θ) ∧
      G.acActivePower (fun _ ↦ 0) voltage i = 0 ∧
      HasDerivAt
        (fun t ↦ G.acActivePower (fun _ ↦ 0) (fun v ↦ voltage v + t * direction v) i)
        0 0 ∧
      HasDerivAt
        (fun t ↦ G.acReactivePower shunt (fun v ↦ t * direction v) voltage i) 0 0 := by
  exact ⟨G.acActivePower_unit_voltage, G.acActivePower_flat_angle voltage i,
    G.hasDerivAt_acActivePower_voltage_flat voltage direction i 0,
    G.hasDerivAt_acReactivePower_angle_flat shunt voltage direction i⟩

/-- The first Newton system of lossless AC power flow. For `J = diag(B_r, J_QV)`, every pair
of singular value bounds of `J` satisfies `σmax / σmin ≥ κ₂(B_r)`. -/
theorem flatStartACConditioning (G : WeightedGraph n m) (slack : Fin n) (hn : 1 < n)
    {reactiveIndex : Type*} [Fintype reactiveIndex]
    (reactiveBlock : Matrix reactiveIndex reactiveIndex ℝ)
    (σmin σmax : ℝ) (hσmin : 0 < σmin) (hσmax : 0 ≤ σmax)
    (hlower : ∀ z : GroundedIndex slack ⊕ reactiveIndex → ℝ,
      σmin ^ 2 * ∑ y, z y ^ 2 ≤
        ∑ y, ((Matrix.fromBlocks (groundedLaplacian G slack) 0 0 reactiveBlock *ᵥ z) y) ^ 2)
    (hupper : ∀ z : GroundedIndex slack ⊕ reactiveIndex → ℝ,
      ∑ y, ((Matrix.fromBlocks (groundedLaplacian G slack) 0 0 reactiveBlock *ᵥ z) y) ^ 2 ≤
        σmax ^ 2 * ∑ y, z y ^ 2) :
    groundedConditionNumber G slack ≤ σmax / σmin := by
  exact flatStart_blockDiagonal_condition_bound G slack hn reactiveBlock σmin σmax hσmin
    hσmax hlower hupper

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

/-- The barrier Hessian block `L_w` of the DC-OPF Newton system is a grounded Laplacian with
positive weights, so `κ₂(L_w) ≥ β (1 - β) n / (s Δ)` at every iterate. -/
theorem dcOpfGroundedBarrierBlock (G : WeightedGraph n m) (slack : Fin n)
    (scale : Fin m → ℝ) (hscale : ∀ e, 0 < scale e)
    (A X B : Finset (Fin n)) (s Δ β : ℝ)
    (hcover : A ∪ X ∪ B = Finset.univ)
    (hdisjoint : Disjoint (A ∪ X) B)
    (hnoCrossing : ∀ e, ¬(G.posEndpoint e ∈ A ∧ G.negEndpoint e ∈ B) ∧
      ¬(G.posEndpoint e ∈ B ∧ G.negEndpoint e ∈ A))
    (hX : (X.card : ℝ) ≤ s)
    (hdegree : ∀ i, ((G.incidentEdges i).card : ℝ) ≤ Δ)
    (hβ : 0 < β) (hβhalf : β ≤ 1 / 2)
    (hA : β * n ≤ ((A ∪ X).card : ℝ)) (hB : β * n ≤ (B.card : ℝ))
    (hconn : G.CombinatoriallyConnected) :
    β * (1 - β) * n / (s * Δ) ≤
      groundedConditionNumber
        (G.withWeights (fun e ↦ scale e * G.weights e)
          (fun e ↦ mul_pos (hscale e) (G.weights_pos e))) slack := by
  exact G.dcOpfGroundedBlock_condition_bound slack scale hscale A X B s Δ β hcover
    hdisjoint hnoCrossing hX hdegree hβ hβhalf hA hB hconn

/-- Proposition 3. If the grid has maximum degree `Δ` and an `(s, β)` separation, then every
pair of singular value bounds of the DC-OPF Newton matrix `K` satisfies
`σmax / σmin ≥ √(β n / s) / (2 Δ)`, for every generation block, every generator map, and every
positive choice of the iteration dependent branch weights. -/
theorem proposition3_dcOpfNewtonSystem {g : ℕ} (G : WeightedGraph n m) (slack : Fin n)
    (generationBlock : Matrix (Fin g) (Fin g) ℝ) (generatorMap : Matrix (Fin n) (Fin g) ℝ)
    (scale : Fin m → ℝ) (hscale : ∀ e, 0 < scale e)
    (A X B : Finset (Fin n)) (s Δ β : ℝ)
    (hcover : A ∪ X ∪ B = Finset.univ)
    (hdisjoint : Disjoint (A ∪ X) B)
    (hnoCrossing : ∀ e, ¬(G.posEndpoint e ∈ A ∧ G.negEndpoint e ∈ B) ∧
      ¬(G.posEndpoint e ∈ B ∧ G.negEndpoint e ∈ A))
    (hX : (X.card : ℝ) ≤ s)
    (hdegree : ∀ i, ((G.incidentEdges i).card : ℝ) ≤ Δ)
    (hβ : 0 < β)
    (hA : β * n ≤ ((A ∪ X).card : ℝ)) (hB : β * n ≤ (B.card : ℝ))
    (σmin σmax : ℝ) (hσmin : 0 < σmin) (hσmax : 0 ≤ σmax)
    (hlower : ∀ z : DcOpfNewtonIndex g slack → ℝ,
      σmin ^ 2 * ∑ y, z y ^ 2 ≤
        ∑ y, ((G.dcOpfNewtonMatrix slack generationBlock generatorMap scale *ᵥ z) y) ^ 2)
    (hupper : ∀ z : DcOpfNewtonIndex g slack → ℝ,
      ∑ y, ((G.dcOpfNewtonMatrix slack generationBlock generatorMap scale *ᵥ z) y) ^ 2 ≤
        σmax ^ 2 * ∑ y, z y ^ 2) :
    Real.sqrt (β * n / s) / (2 * Δ) ≤ σmax / σmin := by
  exact G.dcOpfNewton_condition_bound slack generationBlock generatorMap scale hscale A X B
    s Δ β hcover hdisjoint hnoCrossing hX hdegree hβ hA hB σmin σmax hσmin hσmax hlower
    hupper

end PaperClaims

end
