/-
Copyright (c) 2026 Power Flow Limits contributors. All rights reserved.
Released under the MIT license. See LICENSE for details.
-/

import Challenge.Definitions

/-!
# Trusted public theorem statements

This file contains exactly the theorem statements checked by Comparator. It imports only the
independent definitions and Mathlib dependencies in `Challenge.Definitions`.
-/

open Finset BigOperators
open Matrix
open scoped Matrix

noncomputable section

set_option autoImplicit false

variable {n m : ℕ}

namespace PaperClaims

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
  sorry

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
  sorry

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
  sorry

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
  sorry

theorem corollary1_planarFromLiptonTarjan (Planar : PlanarityPredicate)
    (hLT : LiptonTarjanVertexCostTheorem Planar) (G : WeightedGraph n m)
    (hplanar : Planar _ G.toSimpleGraph) (hn : 288 ≤ n) (Δ bmax : ℝ)
    (hdegree : ∀ i, ((G.incidentEdges i).card : ℝ) ≤ Δ)
    (hweight : ∀ e, G.weights e ≤ bmax)
    (hconn : G.CombinatoriallyConnected) :
    max (5 / 18 * G.totalWeight / (Real.sqrt (8 * n) * Δ * bmax))
        (5 / 18 * n / (Real.sqrt (8 * n) * Δ)) ≤
      effectiveConditionNumber G (fun _ ↦ 1) := by
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

theorem pseudoConditionNumber_balancedSolve (G : WeightedGraph n m) (hn : 1 < n)
    (θ p : Fin n → ℝ) (hθ : ∑ i, θ i = 0)
    (hsolve : ∀ i, ∑ j, G.laplacian (fun _ ↦ 1) i j * θ j = p i) :
    laplacian_eigenvalue₂ G (fun _ ↦ 1) ^ 2 * ∑ i, θ i ^ 2 ≤ ∑ i, p i ^ 2 ∧
      ∑ i, p i ^ 2 ≤ laplacianEigenvalueMax G (fun _ ↦ 1) ^ 2 * ∑ i, θ i ^ 2 := by
  sorry

theorem energyNormAccuracy (G : WeightedGraph n m)
    (hconn : G.CombinatoriallyConnected) (hn : 1 < n)
    (θ θhat : Fin n → ℝ) (ε : ℝ)
    (hbalanced : ∑ i, (θhat i - θ i) = 0)
    (henergy : laplacianEnergy G (fun i ↦ θhat i - θ i) ≤
      (ε / Real.sqrt (effectiveConditionNumber G (fun _ ↦ 1))) ^ 2 * laplacianEnergy G θ) :
    ∑ i, (θhat i - θ i) ^ 2 ≤ ε ^ 2 * ∑ i, θ i ^ 2 := by
  sorry

theorem groundedHalfLemma1 (G : WeightedGraph n m) (slack : Fin n) (e : Fin m)
    (hn : 1 < n) :
    groundedLaplacianEigenvalueMin G slack ≤ laplacian_eigenvalue₂ G (fun _ ↦ 1) ∧
      G.totalWeight ≤ ∑ i, groundedLaplacian G slack i i ∧
      max (G.totalWeight / ((n : ℝ) - 1)) (G.weights e) ≤
        groundedLaplacianEigenvalueMax G slack := by
  sorry

theorem groundedLemma1 (G : WeightedGraph n m) (slack : Fin n) (S : Finset (Fin n))
    (e : Fin m) (hne : S.Nonempty) (hproper : S ≠ Finset.univ)
    (hconn : G.CombinatoriallyConnected) :
    max (((S.card : ℝ) / n) * (1 - (S.card : ℝ) / n) * G.totalWeight / G.cutWeight S)
        (((S.card : ℝ) / n) * (1 - (S.card : ℝ) / n) * ((n : ℝ) * G.weights e) /
          G.cutWeight S) ≤
      groundedConditionNumber G slack := by
  sorry

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
  sorry

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
  sorry

theorem groundedCorollary1_planarFromLiptonTarjan (Planar : PlanarityPredicate)
    (hLT : LiptonTarjanVertexCostTheorem Planar) (G : WeightedGraph n m) (slack : Fin n)
    (hplanar : Planar _ G.toSimpleGraph) (hn : 288 ≤ n) (Δ bmax : ℝ)
    (hdegree : ∀ i, ((G.incidentEdges i).card : ℝ) ≤ Δ)
    (hweight : ∀ e, G.weights e ≤ bmax)
    (hconn : G.CombinatoriallyConnected) :
    max (5 / 36 * G.totalWeight / (Real.sqrt (8 * n) * Δ * bmax))
        (5 / 36 * n / (Real.sqrt (8 * n) * Δ)) ≤
      groundedConditionNumber G slack := by
  sorry

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
  sorry

theorem proposition2_balancedHardPair (G : WeightedGraph n m)
    (hconn : G.CombinatoriallyConnected) (hn : 1 < n)
    (hextreme : laplacian_eigenvalue₂ G (fun _ ↦ 1) <
      laplacianEigenvalueMax G (fun _ ↦ 1)) :
    Nonempty (GraphHardPairCertificate G) := by
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

theorem hhlCriterion_readoutLevel (nodes sparsity readout condition growth : ℝ)
    (hnodes : 0 < nodes) (hsparsity : 1 ≤ sparsity) (hreadout : 0 ≤ readout)
    (hgrowth : 0 < growth) (hcondition : growth * nodes ≤ condition)
    (hcriterion : readout * condition ^ (3 / 2 : ℝ) ≤ nodes / sparsity) :
    readout * (growth ^ (3 / 2 : ℝ) * Real.sqrt nodes) ≤ 1 ∧
      (1 < growth ^ (3 / 2 : ℝ) * Real.sqrt nodes → readout < 1) := by
  sorry

theorem flatStartACBlock (G : WeightedGraph n m) :
    G.acAngleJacobian (fun _ ↦ 0) = G.laplacian (fun _ ↦ 1) := by
  sorry

theorem flatStartACOffDiagonalBlocks (G : WeightedGraph n m)
    (shunt voltage direction : Fin n → ℝ) (i : Fin n) :
    (∀ θ : Fin n → ℝ, G.acActivePower θ (fun _ ↦ 1) = G.acActiveInjection θ) ∧
      G.acActivePower (fun _ ↦ 0) voltage i = 0 ∧
      HasDerivAt
        (fun t ↦ G.acActivePower (fun _ ↦ 0) (fun v ↦ voltage v + t * direction v) i)
        0 0 ∧
      HasDerivAt
        (fun t ↦ G.acReactivePower shunt (fun v ↦ t * direction v) voltage i) 0 0 := by
  sorry

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
  sorry

theorem dcOpfBarrierBlock (G : WeightedGraph n m)
    (limit : Fin m → ℝ) (barrier : ℝ) (angle : Fin n → ℝ)
    (hbarrier : 0 < barrier)
    (hminus : ∀ e, 0 < limit e - G.dcBranchFlow angle e)
    (hplus : ∀ e, 0 < limit e + G.dcBranchFlow angle e) :
    (∀ e, 0 < G.dcOpfBarrierScale limit barrier angle e) ∧
      G.dcOpfNetworkBlock limit barrier angle =
        G.laplacian (G.dcOpfBarrierScale limit barrier angle) := by
  sorry

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
  sorry

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
  sorry

end PaperClaims

end
