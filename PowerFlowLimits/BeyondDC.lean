/-
Copyright (c) 2026 Cameron Khanpour and Samuel Talkington. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Cameron Khanpour, Samuel Talkington
-/
import PowerFlowLimits.Separators

/-!
# Structural transfer beyond a fixed DC power flow matrix

Positive branch rescaling preserves the network topology. Therefore the separator theorem applies
to every positive weighted Laplacian on the same incidence matrix, including the network blocks
claimed for DC optimal power flow interior point iterations in the original letter.
-/

open Finset BigOperators

noncomputable section

variable {n m : ℕ}

/-- Moving a positive branch scale from the switching vector into the stored weights leaves the
Laplacian and its effective condition number unchanged. -/
theorem effectiveConditionNumber_withWeights_eq (G : WeightedGraph n m)
    (scale : Fin m → ℝ) (hscale : ∀ e, 0 < scale e) :
    effectiveConditionNumber
        (G.withWeights (fun e ↦ scale e * G.weights e)
          (fun e ↦ mul_pos (hscale e) (G.weights_pos e)))
        (fun _ ↦ 1) =
      effectiveConditionNumber G scale := by
  let H := G.withWeights (fun e ↦ scale e * G.weights e)
    (fun e ↦ mul_pos (hscale e) (G.weights_pos e))
  have hL : H.laplacian (fun _ ↦ 1) = G.laplacian scale := by
    funext i j
    apply Finset.sum_congr rfl
    intro e _
    simp only [H, WeightedGraph.withWeights]
    ring
  unfold effectiveConditionNumber laplacianEigenvalueMax laplacian_eigenvalue₂
  rw [hL]

/-- The separator bound is uniform over every positive rescaling of the branch weights. -/
theorem positiveRescaling_separator_kappa_bound (G : WeightedGraph n m)
    (scale : Fin m → ℝ) (hscale : ∀ e, 0 < scale e)
    (A X Bv : Finset (Fin n)) (s Δ bmax β : ℝ)
    (hcover : A ∪ X ∪ Bv = Finset.univ)
    (hdisj : Disjoint (A ∪ X) Bv)
    (hnoAB : ∀ e, ¬(G.posEndpoint e ∈ A ∧ G.negEndpoint e ∈ Bv) ∧
      ¬(G.posEndpoint e ∈ Bv ∧ G.negEndpoint e ∈ A))
    (hX : (X.card : ℝ) ≤ s)
    (hdeg : ∀ i, ((G.incidentEdges i).card : ℝ) ≤ Δ)
    (hbmax : ∀ e, scale e * G.weights e ≤ bmax)
    (hβ : 0 < β) (hβ' : β ≤ 1 / 2)
    (hA_size : β * n ≤ ((A ∪ X).card : ℝ))
    (hB_size : β * n ≤ (Bv.card : ℝ))
    (hconn : G.CombinatoriallyConnected) :
    2 * β * (1 - β) * (∑ e, scale e * G.weights e) / (s * Δ * bmax) ≤
      effectiveConditionNumber
        (G.withWeights (fun e ↦ scale e * G.weights e)
          (fun e ↦ mul_pos (hscale e) (G.weights_pos e)))
        (fun _ ↦ 1) := by
  let H := G.withWeights (fun e ↦ scale e * G.weights e)
    (fun e ↦ mul_pos (hscale e) (G.weights_pos e))
  have hH := separator_kappa_bound H A X Bv s Δ bmax β
    hcover hdisj hnoAB hX hdeg hbmax hβ hβ' hA_size hB_size
    ((G.withWeights_combinatoriallyConnected_iff _ _).mpr hconn)
  simpa [H, WeightedGraph.totalWeight] using hH

end
