/-
Copyright (c) 2026 Cameron Khanpour and Samuel Talkington. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Cameron Khanpour, Samuel Talkington
-/
import PowerFlowLimits.Corridors
import PowerFlowLimits.Separators
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# The topology only bounds under random line data

The term `n` in Theorem 1 and the last bound of Proposition 1 contain no susceptances. They hold
for every positive choice of the branch weights, so they hold with probability one for random
line data under any joint distribution. No independence, boundedness, or moment assumption is
needed, which is why the revised letter no longer states a separate probabilistic proposition.
-/

open Finset BigOperators

noncomputable section

variable {n m : ℕ}

/-- A corridor is a property of the incidence structure, so it survives a change of weights. -/
def CorridorTopology.withWeights {G : WeightedGraph n m}
    {VS VT : Finset (Fin n)} {ℓ : ℕ} {p : Fin ℓ → Fin n} {EP : Finset (Fin m)}
    (C : CorridorTopology G VS VT ℓ p EP) (w : Fin m → ℝ) (hw : ∀ e, 0 < w e) :
    CorridorTopology (G.withWeights w hw) VS VT ℓ p EP where
  length_two := C.length_two
  path_injective := C.path_injective
  pathEdge := C.pathEdge
  pathEdge_injective := C.pathEdge_injective
  pathEdge_range := C.pathEdge_range
  pathEdge_endpoints := C.pathEdge_endpoints
  path_disjoint_left := C.path_disjoint_left
  path_disjoint_right := C.path_disjoint_right
  bulks_disjoint := C.bulks_disjoint
  vertex_cover := C.vertex_cover
  nonpath_internal := C.nonpath_internal

/-- The topology only separator bound holds surely for random positive susceptances with an
arbitrary joint distribution. -/
theorem separator_topological_bound_surely {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (G : WeightedGraph n m) (weight : Ω → Fin m → ℝ) (hpos : ∀ ω e, 0 < weight ω e)
    (A X Bv : Finset (Fin n)) (s Δ β : ℝ)
    (hcover : A ∪ X ∪ Bv = Finset.univ)
    (hdisj : Disjoint (A ∪ X) Bv)
    (hnoAB : ∀ e, ¬(G.posEndpoint e ∈ A ∧ G.negEndpoint e ∈ Bv) ∧
      ¬(G.posEndpoint e ∈ Bv ∧ G.negEndpoint e ∈ A))
    (hX : (X.card : ℝ) ≤ s)
    (hdeg : ∀ i, ((G.incidentEdges i).card : ℝ) ≤ Δ)
    (hβ : 0 < β) (hβ' : β ≤ 1 / 2)
    (hA_size : β * n ≤ ((A ∪ X).card : ℝ)) (hB_size : β * n ≤ (Bv.card : ℝ))
    (hconn : G.CombinatoriallyConnected) :
    μ.real {ω | 2 * β * (1 - β) * n / (s * Δ) ≤
      effectiveConditionNumber (G.withWeights (weight ω) (hpos ω)) (fun _ ↦ 1)} = 1 := by
  have hall : {ω | 2 * β * (1 - β) * n / (s * Δ) ≤
      effectiveConditionNumber (G.withWeights (weight ω) (hpos ω)) (fun _ ↦ 1)} =
        Set.univ := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact separator_kappa_bound_topological (G.withWeights (weight ω) (hpos ω)) A X Bv s Δ β
      hcover hdisj hnoAB hX hdeg hβ hβ' hA_size hB_size
      ((G.withWeights_combinatoriallyConnected_iff _ _).mpr hconn)
  rw [hall]
  exact MeasureTheory.probReal_univ

/-- The topology only corridor bound holds surely for random positive susceptances with an
arbitrary joint distribution. -/
theorem corridor_topological_bound_surely {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (G : WeightedGraph n m) (weight : Ω → Fin m → ℝ) (hpos : ∀ ω e, 0 < weight ω e)
    (VS VT : Finset (Fin n)) (ℓ : ℕ) (p : Fin ℓ → Fin n)
    (EP : Finset (Fin m)) (C : CorridorTopology G VS VT ℓ p EP)
    (β : ℝ) (hβ : 0 < β)
    (hVS_size : β * n ≤ (VS.card : ℝ))
    (hVT_size : β * n ≤ (VT.card : ℝ))
    (hconn : G.CombinatoriallyConnected) :
    μ.real {ω | 2 * β ^ 2 * n * ((ℓ : ℝ) - 1) ≤
      effectiveConditionNumber (G.withWeights (weight ω) (hpos ω)) (fun _ ↦ 1)} = 1 := by
  have hall : {ω | 2 * β ^ 2 * n * ((ℓ : ℝ) - 1) ≤
      effectiveConditionNumber (G.withWeights (weight ω) (hpos ω)) (fun _ ↦ 1)} =
        Set.univ := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact corridor_kappa_bound_topological (G.withWeights (weight ω) (hpos ω)) VS VT ℓ p EP
      (C.withWeights (weight ω) (hpos ω)) β hβ hVS_size hVT_size
      ((G.withWeights_combinatoriallyConnected_iff _ _).mpr hconn)
  rw [hall]
  exact MeasureTheory.probReal_univ

end
