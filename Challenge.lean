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
    2 * β * (1 - β) * G.totalWeight / (s * Δ * bmax) ≤
      effectiveConditionNumber G (fun _ ↦ 1) := by
  sorry

theorem corollary1_treewidth {k τ : ℕ} (G : WeightedGraph n m)
    (D : RootedTreeDecomposition G.toSimpleGraph k)
    (hn : 0 < n) (hwidth : D.HasWidthAtMost τ) (hτ : τ + 1 ≤ n / 4)
    (Δ bmax : ℝ)
    (hdegree : ∀ i, ((G.incidentEdges i).card : ℝ) ≤ Δ)
    (hweight : ∀ e, G.weights e ≤ bmax)
    (hconn : G.CombinatoriallyConnected) :
    3 / 8 * G.totalWeight / (((τ : ℝ) + 1) * Δ * bmax) ≤
      effectiveConditionNumber G (fun _ ↦ 1) := by
  sorry

theorem corollary1_planarFromLiptonTarjan (Planar : PlanarityPredicate)
    (hLT : LiptonTarjanVertexCostTheorem Planar) (G : WeightedGraph n m)
    (hplanar : Planar _ G.toSimpleGraph) (hn : 288 ≤ n) (Δ bmax : ℝ)
    (hdegree : ∀ i, ((G.incidentEdges i).card : ℝ) ≤ Δ)
    (hweight : ∀ e, G.weights e ≤ bmax)
    (hconn : G.CombinatoriallyConnected) :
    5 / 18 * G.totalWeight / (Real.sqrt (8 * n) * Δ * bmax) ≤
      effectiveConditionNumber G (fun _ ↦ 1) := by
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

theorem proposition3_balancedHardPair (G : WeightedGraph n m)
    (hconn : G.CombinatoriallyConnected) (hn : 1 < n)
    (hextreme : laplacian_eigenvalue₂ G (fun _ ↦ 1) <
      laplacianEigenvalueMax G (fun _ ↦ 1)) :
    Nonempty (GraphHardPairCertificate G) := by
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

theorem groundedConditioningTransfer (G : WeightedGraph n m) (slack : Fin n)
    (Δ bmax : ℝ) (hconn : G.CombinatoriallyConnected) (hn : 1 < n)
    (hdegree : ((G.incidentEdges slack).card : ℝ) ≤ Δ)
    (hbmaxNonnegative : 0 ≤ bmax) (hweight : ∀ e, G.weights e ≤ bmax)
    (hcorrected : 0 ≤ 2 * G.totalWeight - Δ * bmax) :
    ((2 * G.totalWeight - Δ * bmax) / ((n : ℝ) - 1)) /
        laplacian_eigenvalue₂ G (fun _ ↦ 1) ≤
      groundedConditionNumber G slack := by
  sorry

theorem flatStartACBlock (G : WeightedGraph n m) :
    G.acAngleJacobian (fun _ ↦ 0) = G.laplacian (fun _ ↦ 1) := by
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
  sorry

end PaperClaims

end
