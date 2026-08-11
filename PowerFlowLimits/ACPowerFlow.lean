/-
Copyright (c) 2026 Cameron Khanpour and Samuel Talkington. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Cameron Khanpour, Samuel Talkington
-/
import PowerFlowLimits.BeyondDC
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Lossless AC power flow at flat start

The active-power angle Jacobian of the lossless, unit-voltage AC model is the same weighted
Laplacian as DC power flow at flat start.
-/

open Finset BigOperators

noncomputable section

variable {n m : ℕ}

/-- Lossless unit-voltage active injection at bus `i`. Each oriented branch contributes
`Aᵢₑ bₑ sin((Aᵀθ)ₑ)`. -/
def WeightedGraph.acActiveInjection (G : WeightedGraph n m)
    (θ : Fin n → ℝ) (i : Fin n) : ℝ :=
  ∑ e, G.incidence i e * G.weights e * Real.sin (voltageDrop G θ e)

/-- The active-injection Jacobian with respect to voltage angles. -/
def WeightedGraph.acAngleJacobian (G : WeightedGraph n m)
    (θ : Fin n → ℝ) (i j : Fin n) : ℝ :=
  ∑ e, G.incidence i e * G.weights e * Real.cos (voltageDrop G θ e) *
    G.incidence j e

/-- At every angle profile, the lossless active-angle block is a branch-rescaled Laplacian. -/
theorem WeightedGraph.acAngleJacobian_eq_laplacian (G : WeightedGraph n m)
    (θ : Fin n → ℝ) :
    G.acAngleJacobian θ =
      G.laplacian (fun e ↦ Real.cos (voltageDrop G θ e)) := by
  funext i j
  apply Finset.sum_congr rfl
  intro e _
  ring

/-- The displayed matrix is the actual directional derivative of the nonlinear active-injection
map. This avoids treating the Jacobian formula as a definition without a calculus certificate. -/
theorem WeightedGraph.hasDerivAt_acActiveInjection_line
    (G : WeightedGraph n m) (θ h : Fin n → ℝ) (i : Fin n) :
    HasDerivAt
      (fun t ↦ G.acActiveInjection (fun v ↦ θ v + t * h v) i)
      (∑ j, G.acAngleJacobian θ i j * h j) 0 := by
  have hdrop : ∀ e : Fin m, ∀ t : ℝ,
      voltageDrop G (fun v ↦ θ v + t * h v) e =
        voltageDrop G θ e + t * voltageDrop G h e := by
    intro e t
    rw [voltageDrop_eq_endpoint_diff, voltageDrop_eq_endpoint_diff,
      voltageDrop_eq_endpoint_diff]
    ring
  have hedge : ∀ e : Fin m,
      HasDerivAt
        (fun t ↦ G.incidence i e * G.weights e *
          Real.sin (voltageDrop G (fun v ↦ θ v + t * h v) e))
        (G.incidence i e * G.weights e *
          (Real.cos (voltageDrop G θ e) * voltageDrop G h e)) 0 := by
    intro e
    have hlinear : HasDerivAt
        (fun t ↦ voltageDrop G θ e + t * voltageDrop G h e)
        (voltageDrop G h e) 0 := by
      convert (hasDerivAt_const (0 : ℝ) (voltageDrop G θ e)).add
        ((hasDerivAt_id (𝕜 := ℝ) 0).mul_const (voltageDrop G h e)) using 1
      all_goals ring
    have hsin := hlinear.sin
    have hscaled := hsin.const_mul (G.incidence i e * G.weights e)
    simpa only [hdrop, zero_mul, add_zero] using hscaled
  have hsum := HasDerivAt.fun_sum fun e (_he : e ∈ Finset.univ) ↦ hedge e
  have hderiv :
      ∑ e, G.incidence i e * G.weights e *
          (Real.cos (voltageDrop G θ e) * voltageDrop G h e) =
        ∑ j, G.acAngleJacobian θ i j * h j := by
    simp only [WeightedGraph.acAngleJacobian, voltageDrop]
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro e _
    ring
  simpa only [WeightedGraph.acActiveInjection, hderiv] using hsum

/-- At flat start, every cosine factor is one, so the lossless AC active-angle Jacobian is exactly
the DC susceptance Laplacian. -/
theorem WeightedGraph.acAngleJacobian_flat_eq_laplacian (G : WeightedGraph n m) :
    G.acAngleJacobian (fun _ ↦ 0) = G.laplacian (fun _ ↦ 1) := by
  rw [G.acAngleJacobian_eq_laplacian]
  congr 1
  funext e
  simp [voltageDrop]

/-- On the stable-angle region where every branch cosine is positive, Theorem 1 applies directly
to the AC active-angle Jacobian at that iterate. -/
theorem WeightedGraph.acAngleJacobian_separator_kappa_bound
    (G : WeightedGraph n m) (θ : Fin n → ℝ)
    (hstable : ∀ e, 0 < Real.cos (voltageDrop G θ e))
    (A X Bv : Finset (Fin n)) (s Δ bmax β : ℝ)
    (hcover : A ∪ X ∪ Bv = Finset.univ)
    (hdisj : Disjoint (A ∪ X) Bv)
    (hnoAB : ∀ e, ¬(G.posEndpoint e ∈ A ∧ G.negEndpoint e ∈ Bv) ∧
      ¬(G.posEndpoint e ∈ Bv ∧ G.negEndpoint e ∈ A))
    (hX : (X.card : ℝ) ≤ s)
    (hdeg : ∀ i, ((G.incidentEdges i).card : ℝ) ≤ Δ)
    (hbmax : ∀ e, Real.cos (voltageDrop G θ e) * G.weights e ≤ bmax)
    (hβ : 0 < β) (hβ' : β ≤ 1 / 2)
    (hA_size : β * n ≤ ((A ∪ X).card : ℝ))
    (hB_size : β * n ≤ (Bv.card : ℝ))
    (hconn : G.CombinatoriallyConnected) :
    2 * β * (1 - β) *
        (∑ e, Real.cos (voltageDrop G θ e) * G.weights e) /
          (s * Δ * bmax) ≤
      effectiveConditionNumber G (fun e ↦ Real.cos (voltageDrop G θ e)) := by
  have h := positiveRescaling_separator_kappa_bound G
    (fun e ↦ Real.cos (voltageDrop G θ e)) hstable A X Bv s Δ bmax β
    hcover hdisj hnoAB hX hdeg hbmax hβ hβ' hA_size hB_size hconn
  rw [effectiveConditionNumber_withWeights_eq G
    (fun e ↦ Real.cos (voltageDrop G θ e)) hstable] at h
  exact h

end
