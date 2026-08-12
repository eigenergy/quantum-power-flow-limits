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

These examples exercise the maximum edge separator and corridor bounds, their grounded transfer,
and the finite threshold implied by a linear crossing count.
-/

open Finset BigOperators

noncomputable section

variable {n m c : ℕ}

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

example (G : WeightedGraph n m) (VS VT : Finset (Fin n)) (ell : ℕ)
    (p : Fin ell → Fin n) (EP : Finset (Fin m))
    (C : CorridorTopology G VS VT ell p EP) (β : ℝ) (hβ : 0 < β)
    (hVS_size : β * n ≤ (VS.card : ℝ))
    (hVT_size : β * n ≤ (VT.card : ℝ))
    (hconn : G.CombinatoriallyConnected) :
    2 * β ^ 2 * n * ((ell : ℝ) - 1) ≤
      effectiveConditionNumber G (fun _ ↦ 1) :=
  corridor_kappa_bound_topological G VS VT ell p EP C β hβ hVS_size hVT_size hconn

example (G : WeightedGraph n m) (r : Fin n) (e : Fin m)
    (hconn : G.CombinatoriallyConnected) (hn : 1 < n) :
    G.weights e / laplacian_eigenvalue₂ G (fun _ ↦ 1) ≤
      groundedConditionNumber G r :=
  edgeWeight_div_lambda2_le_groundedConditionNumber G r e hconn hn

example (n c C : ℕ) (hc : c ≤ C * n) (hn : 1152 * (C + 1) ≤ n) :
    1152 * (n + c) ≤ n ^ 2 :=
  nearPlanar_balance_of_crossings_le_linear n c C hc hn

end
