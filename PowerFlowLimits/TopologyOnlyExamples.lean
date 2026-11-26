/-
Copyright (c) 2026 Cameron Khanpour and Samuel Talkington. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Cameron Khanpour, Samuel Talkington
-/
import PowerFlowLimits.Corridors
import PowerFlowLimits.Grounded
import PowerFlowLimits.PlanarSeparator

/-!
# Compiling examples for topology only conditioning bounds

These examples exercise arbitrarily nonuniform weights, maximum edges on and off a cut,
macroscopic corridors, both choices of grounded endpoint, and the finite threshold implied by a
linear crossing count.
-/

open Finset BigOperators

noncomputable section

variable {n m c : ℕ}

/-- Reweighting one branch to `1` and every other branch to an arbitrary `η > 0` leaves the
topology bound unchanged. In particular, the theorem has no weight spread or mean ratio premise. -/
example (G : WeightedGraph n m) (A X Bv : Finset (Fin n)) (s Δ β η : ℝ)
    (eHeavy : Fin m) (hη : 0 < η)
    (hcover : A ∪ X ∪ Bv = Finset.univ)
    (hdisj : Disjoint (A ∪ X) Bv)
    (hnoAB : ∀ e, ¬(G.posEndpoint e ∈ A ∧ G.negEndpoint e ∈ Bv) ∧
      ¬(G.posEndpoint e ∈ Bv ∧ G.negEndpoint e ∈ A))
    (hX : (X.card : ℝ) ≤ s)
    (hdeg : ∀ i, ((G.incidentEdges i).card : ℝ) ≤ Δ)
    (hβ : 0 < β) (hβ' : β ≤ 1 / 2)
    (hA_size : β * n ≤ ((A ∪ X).card : ℝ))
    (hB_size : β * n ≤ (Bv.card : ℝ))
    (hconn : G.CombinatoriallyConnected) :
    2 * β * (1 - β) * n / (s * Δ) ≤
      effectiveConditionNumber
        (G.withWeights (fun e ↦ if e = eHeavy then 1 else η) (by
          intro e
          by_cases he : e = eHeavy <;> simp [he, hη]))
        (fun _ ↦ 1) := by
  let hw : ∀ e, 0 < if e = eHeavy then (1 : ℝ) else η := by
    intro e
    by_cases he : e = eHeavy <;> simp [he, hη]
  let H := G.withWeights (fun e ↦ if e = eHeavy then 1 else η) hw
  apply separator_kappa_bound_topological H A X Bv s Δ β
  · exact hcover
  · exact hdisj
  · simpa [H, WeightedGraph.withWeights] using hnoAB
  · exact hX
  · simpa [H, WeightedGraph.withWeights] using hdeg
  · exact hβ
  · exact hβ'
  · exact hA_size
  · exact hB_size
  · simpa [H] using hconn

example (G : WeightedGraph n m) (A X Bv : Finset (Fin n)) (s Δ β : ℝ)
    (hcover : A ∪ X ∪ Bv = Finset.univ)
    (hdisj : Disjoint (A ∪ X) Bv)
    (hnoAB : ∀ e, ¬(G.posEndpoint e ∈ A ∧ G.negEndpoint e ∈ Bv) ∧
      ¬(G.posEndpoint e ∈ Bv ∧ G.negEndpoint e ∈ A))
    (hX : (X.card : ℝ) ≤ s)
    (hdeg : ∀ i, ((G.incidentEdges i).card : ℝ) ≤ Δ)
    (hβ : 0 < β) (hβ' : β ≤ 1 / 2)
    (hA_size : β * n ≤ ((A ∪ X).card : ℝ))
    (hB_size : β * n ≤ (Bv.card : ℝ))
    (hconn : G.CombinatoriallyConnected) :
    2 * β * (1 - β) * n / (s * Δ) ≤
      effectiveConditionNumber G (fun _ ↦ 1) :=
  separator_kappa_bound_topological G A X Bv s Δ β hcover hdisj hnoAB hX hdeg
    hβ hβ' hA_size hB_size hconn

/-- The topology bound does not depend on whether the maximum branch is in the tested cut. -/
example (G : WeightedGraph n m) (A X Bv : Finset (Fin n)) (s Δ β : ℝ)
    (emax : Fin m) (_hmax : ∀ e, G.weights e ≤ G.weights emax)
    (hcover : A ∪ X ∪ Bv = Finset.univ)
    (hdisj : Disjoint (A ∪ X) Bv)
    (hnoAB : ∀ e, ¬(G.posEndpoint e ∈ A ∧ G.negEndpoint e ∈ Bv) ∧
      ¬(G.posEndpoint e ∈ Bv ∧ G.negEndpoint e ∈ A))
    (hX : (X.card : ℝ) ≤ s)
    (hdeg : ∀ i, ((G.incidentEdges i).card : ℝ) ≤ Δ)
    (hβ : 0 < β) (hβ' : β ≤ 1 / 2)
    (hA_size : β * n ≤ ((A ∪ X).card : ℝ))
    (hB_size : β * n ≤ (Bv.card : ℝ))
    (hconn : G.CombinatoriallyConnected) :
    (((G.posEndpoint emax ∈ A ∪ X ∧ G.negEndpoint emax ∈ Bv) ∨
        (G.posEndpoint emax ∈ Bv ∧ G.negEndpoint emax ∈ A ∪ X)) →
      2 * β * (1 - β) * n / (s * Δ) ≤
        effectiveConditionNumber G (fun _ ↦ 1)) ∧
    (¬((G.posEndpoint emax ∈ A ∪ X ∧ G.negEndpoint emax ∈ Bv) ∨
        (G.posEndpoint emax ∈ Bv ∧ G.negEndpoint emax ∈ A ∪ X)) →
      2 * β * (1 - β) * n / (s * Δ) ≤
        effectiveConditionNumber G (fun _ ↦ 1)) := by
  have htop := separator_kappa_bound_topological G A X Bv s Δ β hcover hdisj hnoAB
    hX hdeg hβ hβ' hA_size hB_size hconn
  exact ⟨fun _ ↦ htop, fun _ ↦ htop⟩

example (G : WeightedGraph n m) (VS VT : Finset (Fin n)) (ell : ℕ)
    (p : Fin ell → Fin n) (EP : Finset (Fin m))
    (C : CorridorTopology G VS VT ell p EP) (β : ℝ) (hβ : 0 < β)
    (hVS_size : β * n ≤ (VS.card : ℝ))
    (hVT_size : β * n ≤ (VT.card : ℝ))
    (hconn : G.CombinatoriallyConnected) :
    2 * β ^ 2 * n * ((ell : ℝ) - 1) ≤
      effectiveConditionNumber G (fun _ ↦ 1) :=
  corridor_kappa_bound_topological G VS VT ell p EP C β hβ hVS_size hVT_size hconn

/-- The public corridor formula retains the exact path-weight denominator before its topology
only simplification. -/
example (G : WeightedGraph n m) (VS VT : Finset (Fin n)) (ell : ℕ)
    (p : Fin ell → Fin n) (EP : Finset (Fin m))
    (C : CorridorTopology G VS VT ell p EP) (β : ℝ) (hβ : 0 < β)
    (hVS_size : β * n ≤ (VS.card : ℝ))
    (hVT_size : β * n ≤ (VT.card : ℝ))
    (emax : Fin m) (hmax : ∀ e, G.weights e ≤ G.weights emax)
    (hconn : G.CombinatoriallyConnected) :
    2 * β ^ 2 * ((ell : ℝ) - 1) ^ 2 *
        max G.totalWeight ((n : ℝ) * G.weights emax) /
          (∑ e ∈ EP, G.weights e) ≤
      effectiveConditionNumber G (fun _ ↦ 1) :=
  corridor_kappa_bound_combined_exact G VS VT ell p EP C β hβ hVS_size hVT_size
    emax hmax hconn

/-- The macroscopic corridor conclusion survives an arbitrarily nonuniform positive reweighting. -/
example (G : WeightedGraph n m) (VS VT : Finset (Fin n)) (ell : ℕ)
    (p : Fin ell → Fin n) (EP : Finset (Fin m))
    (C : CorridorTopology G VS VT ell p EP) (β α η : ℝ) (eHeavy : Fin m)
    (hη : 0 < η) (hβ : 0 < β)
    (hVS_size : β * n ≤ (VS.card : ℝ))
    (hVT_size : β * n ≤ (VT.card : ℝ))
    (hmacro : α * n ≤ (ell : ℝ) - 1)
    (hconn : G.CombinatoriallyConnected) :
    2 * β ^ 2 * α * (n : ℝ) ^ 2 ≤
      effectiveConditionNumber
        (G.withWeights (fun e ↦ if e = eHeavy then 1 else η) (by
          intro e
          by_cases he : e = eHeavy <;> simp [he, hη]))
        (fun _ ↦ 1) := by
  let hw : ∀ e, 0 < if e = eHeavy then (1 : ℝ) else η := by
    intro e
    by_cases he : e = eHeavy <;> simp [he, hη]
  let H := G.withWeights (fun e ↦ if e = eHeavy then 1 else η) hw
  have CH : CorridorTopology H VS VT ell p EP := by
    refine {
      length_two := C.length_two
      path_injective := C.path_injective
      pathEdge := C.pathEdge
      pathEdge_injective := C.pathEdge_injective
      pathEdge_range := C.pathEdge_range
      pathEdge_endpoints := ?_
      path_disjoint_left := C.path_disjoint_left
      path_disjoint_right := C.path_disjoint_right
      bulks_disjoint := C.bulks_disjoint
      vertex_cover := C.vertex_cover
      nonpath_internal := ?_
    }
    · simpa [H, WeightedGraph.withWeights, WeightedGraph.posEndpoint,
        WeightedGraph.negEndpoint] using C.pathEdge_endpoints
    · simpa [H, WeightedGraph.withWeights, WeightedGraph.posEndpoint,
        WeightedGraph.negEndpoint] using C.nonpath_internal
  exact corridor_kappa_quadratic_bound_topological H VS VT ell p EP CH β α hβ hVS_size
    hVT_size hmacro (by simpa [H] using hconn)

/-- The separator topology bound transfers to any choice of grounded bus with half the
ungrounded coefficient. -/
example (G : WeightedGraph n m) (r : Fin n) (A X Bv : Finset (Fin n)) (s Δ β : ℝ)
    (hcover : A ∪ X ∪ Bv = Finset.univ)
    (hdisj : Disjoint (A ∪ X) Bv)
    (hnoAB : ∀ e, ¬(G.posEndpoint e ∈ A ∧ G.negEndpoint e ∈ Bv) ∧
      ¬(G.posEndpoint e ∈ Bv ∧ G.negEndpoint e ∈ A))
    (hX : (X.card : ℝ) ≤ s)
    (hdeg : ∀ i, ((G.incidentEdges i).card : ℝ) ≤ Δ)
    (hβ : 0 < β) (hβ' : β ≤ 1 / 2)
    (hA_size : β * n ≤ ((A ∪ X).card : ℝ))
    (hB_size : β * n ≤ (Bv.card : ℝ))
    (hconn : G.CombinatoriallyConnected) :
    β * (1 - β) * n / (s * Δ) ≤ groundedConditionNumber G r :=
  grounded_separator_kappa_bound_topological G r A X Bv s Δ β hcover hdisj hnoAB hX hdeg
    hβ hβ' hA_size hB_size hconn

/-- The corridor topology bound also transfers directly to any grounded bus. -/
example (G : WeightedGraph n m) (r : Fin n) (VS VT : Finset (Fin n)) (ell : ℕ)
    (p : Fin ell → Fin n) (EP : Finset (Fin m))
    (C : CorridorTopology G VS VT ell p EP) (β : ℝ) (hβ : 0 < β)
    (hVS_size : β * n ≤ (VS.card : ℝ))
    (hVT_size : β * n ≤ (VT.card : ℝ))
    (hconn : G.CombinatoriallyConnected) :
    β ^ 2 * n * ((ell : ℝ) - 1) ≤ groundedConditionNumber G r :=
  grounded_corridor_kappa_bound_topological G r VS VT ell p EP C β hβ
    hVS_size hVT_size hconn

example (G : WeightedGraph n m) (r : Fin n) (e : Fin m)
    (hconn : G.CombinatoriallyConnected) (hn : 1 < n) :
    G.weights e / laplacian_eigenvalue₂ G (fun _ ↦ 1) ≤
      groundedConditionNumber G r :=
  edgeWeight_div_lambda2_le_groundedConditionNumber G r e hconn hn

/-- Grounding either endpoint of a maximum branch retains the same constant transfer. -/
example (G : WeightedGraph n m) (e : Fin m)
    (_hmax : ∀ f, G.weights f ≤ G.weights e)
    (hconn : G.CombinatoriallyConnected) (hn : 1 < n) :
    G.weights e / laplacian_eigenvalue₂ G (fun _ ↦ 1) ≤
        groundedConditionNumber G (G.posEndpoint e) ∧
      G.weights e / laplacian_eigenvalue₂ G (fun _ ↦ 1) ≤
        groundedConditionNumber G (G.negEndpoint e) := by
  constructor
  · exact edgeWeight_div_lambda2_le_groundedConditionNumber G (G.posEndpoint e) e hconn hn
  · exact edgeWeight_div_lambda2_le_groundedConditionNumber G (G.negEndpoint e) e hconn hn

example (n c C : ℕ) (hc : c ≤ C * n) (hn : 1152 * (C + 1) ≤ n) :
    1152 * (n + c) ≤ n ^ 2 :=
  nearPlanar_balance_of_crossings_le_linear n c C hc hn

end
