/-
Copyright (c) 2026 Cameron Khanpour and Samuel Talkington. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Cameron Khanpour, Samuel Talkington
-/
import PowerFlowLimits.BeyondDC
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# DC optimal power flow barrier network block

The logarithmic barriers for two-sided branch-flow limits have a positive weighted-Laplacian
Hessian on every strictly feasible iterate.
-/

open Finset BigOperators

noncomputable section

variable {n m : ℕ}

/-- DC branch flow `bₑ(Aᵀθ)ₑ`. -/
def WeightedGraph.dcBranchFlow (G : WeightedGraph n m)
    (θ : Fin n → ℝ) (e : Fin m) : ℝ :=
  G.weights e * voltageDrop G θ e

/-- One two-sided logarithmic line-flow barrier, restricted to an angle-space line. -/
def WeightedGraph.dcOpfBranchBarrierAlongLine (G : WeightedGraph n m)
    (limit : Fin m → ℝ) (μ : ℝ) (θ h : Fin n → ℝ) (e : Fin m) (t : ℝ) : ℝ :=
  -μ * (Real.log (limit e - G.dcBranchFlow (fun v ↦ θ v + t * h v) e) +
    Real.log (limit e + G.dcBranchFlow (fun v ↦ θ v + t * h v) e))

/-- The first directional derivative of one line-flow barrier. -/
def WeightedGraph.dcOpfBranchBarrierDerivativeAlongLine (G : WeightedGraph n m)
    (limit : Fin m → ℝ) (μ : ℝ) (θ h : Fin n → ℝ) (e : Fin m) (t : ℝ) : ℝ :=
  μ * G.weights e * voltageDrop G h e *
    ((limit e - G.dcBranchFlow (fun v ↦ θ v + t * h v) e)⁻¹ -
      (limit e + G.dcBranchFlow (fun v ↦ θ v + t * h v) e)⁻¹)

/-- The positive scale multiplying the original branch susceptance in the barrier Hessian. -/
def WeightedGraph.dcOpfBarrierScale (G : WeightedGraph n m)
    (limit : Fin m → ℝ) (μ : ℝ) (θ : Fin n → ℝ) (e : Fin m) : ℝ :=
  μ * G.weights e *
    (((limit e - G.dcBranchFlow θ e) ^ 2)⁻¹ +
      ((limit e + G.dcBranchFlow θ e) ^ 2)⁻¹)

/-- Strict feasibility and a positive barrier parameter make every Hessian scale positive. -/
theorem WeightedGraph.dcOpfBarrierScale_pos (G : WeightedGraph n m)
    (limit : Fin m → ℝ) (μ : ℝ) (θ : Fin n → ℝ)
    (hμ : 0 < μ)
    (hminus : ∀ e, 0 < limit e - G.dcBranchFlow θ e)
    (hplus : ∀ e, 0 < limit e + G.dcBranchFlow θ e) :
    ∀ e, 0 < G.dcOpfBarrierScale limit μ θ e := by
  intro e
  unfold WeightedGraph.dcOpfBarrierScale
  have hm : 0 < ((limit e - G.dcBranchFlow θ e) ^ 2)⁻¹ :=
    inv_pos.mpr (sq_pos_of_pos (hminus e))
  have hp : 0 < ((limit e + G.dcBranchFlow θ e) ^ 2)⁻¹ :=
    inv_pos.mpr (sq_pos_of_pos (hplus e))
  exact mul_pos (mul_pos hμ (G.weights_pos e)) (add_pos hm hp)

/-- Calculus certificate for the first directional derivative of a branch barrier. -/
theorem WeightedGraph.hasDerivAt_dcOpfBranchBarrierAlongLine
    (G : WeightedGraph n m) (limit : Fin m → ℝ) (μ : ℝ)
    (θ h : Fin n → ℝ) (e : Fin m) (t : ℝ)
    (hminus : limit e - G.dcBranchFlow (fun v ↦ θ v + t * h v) e ≠ 0)
    (hplus : limit e + G.dcBranchFlow (fun v ↦ θ v + t * h v) e ≠ 0) :
    HasDerivAt (G.dcOpfBranchBarrierAlongLine limit μ θ h e)
      (G.dcOpfBranchBarrierDerivativeAlongLine limit μ θ h e t) t := by
  have hdrop : ∀ u : ℝ,
      G.dcBranchFlow (fun v ↦ θ v + u * h v) e =
        G.dcBranchFlow θ e + u * (G.weights e * voltageDrop G h e) := by
    intro u
    unfold WeightedGraph.dcBranchFlow
    rw [voltageDrop_eq_endpoint_diff, voltageDrop_eq_endpoint_diff,
      voltageDrop_eq_endpoint_diff]
    ring
  have hflow : HasDerivAt
      (fun u ↦ G.dcBranchFlow (fun v ↦ θ v + u * h v) e)
      (G.weights e * voltageDrop G h e) t := by
    convert (hasDerivAt_const t (G.dcBranchFlow θ e)).add
      ((hasDerivAt_id (𝕜 := ℝ) t).mul_const
        (G.weights e * voltageDrop G h e)) using 1
    · funext u
      simp [hdrop]
    · ring
  have hm := (hasDerivAt_const t (limit e)).sub hflow
  have hp := (hasDerivAt_const t (limit e)).add hflow
  have hlogs := (hm.log hminus).add (hp.log hplus)
  have hscaled := hlogs.const_mul (-μ)
  convert hscaled using 1
  · unfold WeightedGraph.dcOpfBranchBarrierDerivativeAlongLine
    simp only [Pi.sub_apply, Pi.add_apply, zero_sub, zero_add, div_eq_mul_inv]
    field_simp [hminus, hplus]
    ring

/-- Differentiating the first derivative yields the positive quadratic Hessian coefficient. -/
theorem WeightedGraph.hasDerivAt_dcOpfBranchBarrierDerivativeAlongLine
    (G : WeightedGraph n m) (limit : Fin m → ℝ) (μ : ℝ)
    (θ h : Fin n → ℝ) (e : Fin m) (t : ℝ)
    (hminus : limit e - G.dcBranchFlow (fun v ↦ θ v + t * h v) e ≠ 0)
    (hplus : limit e + G.dcBranchFlow (fun v ↦ θ v + t * h v) e ≠ 0) :
    HasDerivAt (G.dcOpfBranchBarrierDerivativeAlongLine limit μ θ h e)
      (G.dcOpfBarrierScale limit μ (fun v ↦ θ v + t * h v) e *
        G.weights e * voltageDrop G h e ^ 2) t := by
  have hdrop : ∀ u : ℝ,
      G.dcBranchFlow (fun v ↦ θ v + u * h v) e =
        G.dcBranchFlow θ e + u * (G.weights e * voltageDrop G h e) := by
    intro u
    unfold WeightedGraph.dcBranchFlow
    rw [voltageDrop_eq_endpoint_diff, voltageDrop_eq_endpoint_diff,
      voltageDrop_eq_endpoint_diff]
    ring
  have hflow : HasDerivAt
      (fun u ↦ G.dcBranchFlow (fun v ↦ θ v + u * h v) e)
      (G.weights e * voltageDrop G h e) t := by
    convert (hasDerivAt_const t (G.dcBranchFlow θ e)).add
      ((hasDerivAt_id (𝕜 := ℝ) t).mul_const
        (G.weights e * voltageDrop G h e)) using 1
    · funext u
      simp [hdrop]
    · ring
  have hm := (hasDerivAt_const t (limit e)).sub hflow
  have hp := (hasDerivAt_const t (limit e)).add hflow
  have hinvs := (hm.inv hminus).sub (hp.inv hplus)
  have hscaled := hinvs.const_mul (μ * G.weights e * voltageDrop G h e)
  convert hscaled using 1
  · unfold WeightedGraph.dcOpfBarrierScale
    simp only [Pi.sub_apply, Pi.add_apply, zero_sub, zero_add]
    field_simp [hminus, hplus]
    ring

/-- The DC OPF barrier Hessian's angle network block. -/
def WeightedGraph.dcOpfNetworkBlock (G : WeightedGraph n m)
    (limit : Fin m → ℝ) (μ : ℝ) (θ : Fin n → ℝ) (i j : Fin n) : ℝ :=
  ∑ e, G.incidence i e *
    (G.dcOpfBarrierScale limit μ θ e * G.weights e) * G.incidence j e

/-- The DC OPF network block is exactly a branch-rescaled susceptance Laplacian. -/
theorem WeightedGraph.dcOpfNetworkBlock_eq_laplacian (G : WeightedGraph n m)
    (limit : Fin m → ℝ) (μ : ℝ) (θ : Fin n → ℝ) :
    G.dcOpfNetworkBlock limit μ θ = G.laplacian (G.dcOpfBarrierScale limit μ θ) := by
  funext i j
  apply Finset.sum_congr rfl
  intro e _
  ring

/-- Every strictly feasible DC OPF line-flow barrier iterate inherits the separator bound. -/
theorem WeightedGraph.dcOpfNetworkBlock_separator_kappa_bound (G : WeightedGraph n m)
    (limit : Fin m → ℝ) (μ : ℝ) (θ : Fin n → ℝ)
    (A X Bv : Finset (Fin n)) (s Δ bmax β : ℝ)
    (hμ : 0 < μ)
    (hminus : ∀ e, 0 < limit e - G.dcBranchFlow θ e)
    (hplus : ∀ e, 0 < limit e + G.dcBranchFlow θ e)
    (hcover : A ∪ X ∪ Bv = Finset.univ)
    (hdisj : Disjoint (A ∪ X) Bv)
    (hnoAB : ∀ e, ¬(G.posEndpoint e ∈ A ∧ G.negEndpoint e ∈ Bv) ∧
      ¬(G.posEndpoint e ∈ Bv ∧ G.negEndpoint e ∈ A))
    (hX : (X.card : ℝ) ≤ s)
    (hdeg : ∀ i, ((G.incidentEdges i).card : ℝ) ≤ Δ)
    (hbmax : ∀ e, G.dcOpfBarrierScale limit μ θ e * G.weights e ≤ bmax)
    (hβ : 0 < β) (hβ' : β ≤ 1 / 2)
    (hA_size : β * n ≤ ((A ∪ X).card : ℝ))
    (hB_size : β * n ≤ (Bv.card : ℝ))
    (hconn : G.CombinatoriallyConnected) :
    2 * β * (1 - β) *
        (∑ e, G.dcOpfBarrierScale limit μ θ e * G.weights e) /
        (s * Δ * bmax) ≤
      effectiveConditionNumber G (G.dcOpfBarrierScale limit μ θ) := by
  have hscale := G.dcOpfBarrierScale_pos limit μ θ hμ hminus hplus
  have hbound := positiveRescaling_separator_kappa_bound G
    (G.dcOpfBarrierScale limit μ θ) hscale A X Bv s Δ bmax β
    hcover hdisj hnoAB hX hdeg hbmax hβ hβ' hA_size hB_size hconn
  rw [effectiveConditionNumber_withWeights_eq G _ hscale] at hbound
  exact hbound

end
