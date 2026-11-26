/-
Copyright (c) 2026 Cameron Khanpour and Samuel Talkington. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Cameron Khanpour, Samuel Talkington
-/
import PowerFlowLimits.Eigenvalues

/-!
# The pseudo condition number on balanced injections and the energy norm

This file proves two statements of the letter's setup.

* `κ₊(B) = ‖B‖₂ ‖B⁺‖₂` is the ordinary condition number of `B` on balanced injections. Every
  balanced angle vector `θ` satisfies `λ₂ ‖θ‖ ≤ ‖B θ‖ ≤ λ_max ‖θ‖`.
* Fact (F3). Relative errors in the Euclidean norm and in the energy norm `‖x‖_B² = xᵀ B x`
  differ by at most `√κ₊`. An energy norm accuracy `δ = ε / √κ₊` therefore gives the Euclidean
  accuracy `ε` of quantum solvers.
-/

open Finset BigOperators
open scoped Matrix

noncomputable section

variable {n m : ℕ}

/-- The quadratic form `xᵀ B x` of the susceptance Laplacian. -/
def laplacianEnergy (G : WeightedGraph n m) (x : Fin n → ℝ) : ℝ :=
  ∑ i, (∑ j, G.laplacian (fun _ ↦ 1) i j * x j) * x i

theorem laplacianEnergy_eq_sum_drops (G : WeightedGraph n m) (x : Fin n → ℝ) :
    laplacianEnergy G x = ∑ e, G.weights e * voltageDrop G x e ^ 2 := by
  unfold laplacianEnergy
  have hcomm : ∑ i, (∑ j, G.laplacian (fun _ ↦ 1) i j * x j) * x i =
      ∑ i, x i * ∑ j, G.laplacian (fun _ ↦ 1) i j * x j := by
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    ring
  rw [hcomm, laplacian_quadratic]
  refine Finset.sum_congr rfl fun e _ ↦ ?_
  ring

theorem laplacianEnergy_nonneg (G : WeightedGraph n m) (x : Fin n → ℝ) :
    0 ≤ laplacianEnergy G x := by
  rw [laplacianEnergy_eq_sum_drops]
  exact Finset.sum_nonneg fun e _ ↦ mul_nonneg (G.weights_pos e).le (sq_nonneg _)

/-- The Rayleigh lower bound is attained by the supremum: `λ₂ ‖x‖² ≤ xᵀ B x` on `1⊥`. -/
theorem lambda2_mul_sq_le_energy (G : WeightedGraph n m) (x : Fin n → ℝ)
    (hx : ∑ i, x i = 0) :
    laplacian_eigenvalue₂ G (fun _ ↦ 1) * ∑ i, x i ^ 2 ≤ laplacianEnergy G x := by
  by_cases hzero : ∑ i, x i ^ 2 = 0
  · rw [hzero, mul_zero]
    exact laplacianEnergy_nonneg G x
  · have hpos : 0 < ∑ i, x i ^ 2 :=
      lt_of_le_of_ne (Finset.sum_nonneg fun i _ ↦ sq_nonneg _) (Ne.symm hzero)
    have hle : laplacian_eigenvalue₂ G (fun _ ↦ 1) ≤
        laplacianEnergy G x / ∑ i, x i ^ 2 := by
      unfold laplacian_eigenvalue₂
      refine csSup_le (lambda2_set_nonempty G) fun r hr ↦ ?_
      exact (le_div_iff₀ hpos).mpr (hr x hx)
    exact (le_div_iff₀ hpos).mp hle

/-- The Rayleigh upper bound is attained by the infimum: `xᵀ B x ≤ λ_max ‖x‖²`. -/
theorem energy_le_lambdaMax_mul_sq (G : WeightedGraph n m) (x : Fin n → ℝ) :
    laplacianEnergy G x ≤ laplacianEigenvalueMax G (fun _ ↦ 1) * ∑ i, x i ^ 2 := by
  by_cases hzero : ∑ i, x i ^ 2 = 0
  · have hall : ∀ i, x i = 0 := by
      intro i
      have hsq := (Finset.sum_eq_zero_iff_of_nonneg fun j _ ↦ sq_nonneg (x j)).mp hzero i
        (Finset.mem_univ i)
      exact pow_eq_zero_iff (by norm_num) |>.mp hsq
    have henergy : laplacianEnergy G x = 0 := by
      unfold laplacianEnergy
      refine Finset.sum_eq_zero fun i _ ↦ ?_
      rw [hall i, mul_zero]
    rw [henergy, hzero, mul_zero]
  · have hpos : 0 < ∑ i, x i ^ 2 :=
      lt_of_le_of_ne (Finset.sum_nonneg fun i _ ↦ sq_nonneg _) (Ne.symm hzero)
    have hle := rayleigh_div_le_lambdaMax G (fun _ ↦ 1) x hzero
    exact (div_le_iff₀ hpos).mp hle

/-- The bilinear form of the Laplacian as a sum over branches. -/
theorem laplacian_bilinear (G : WeightedGraph n m) (x y : Fin n → ℝ) :
    ∑ i, y i * ∑ j, G.laplacian (fun _ ↦ 1) i j * x j =
      ∑ e, G.weights e * voltageDrop G x e * voltageDrop G y e := by
  have hrow : ∀ i, ∑ j, G.laplacian (fun _ ↦ 1) i j * x j =
      ∑ e, G.incidence i e * (G.weights e * 1) * voltageDrop G x e :=
    fun i ↦ laplacian_mulVec_apply G (fun _ ↦ 1) x i
  simp_rw [hrow, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ ↦ ?_
  have hy : voltageDrop G y e = ∑ i, G.incidence i e * y i := by rw [voltageDrop]
  rw [hy, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  ring

/-- Cauchy--Schwarz for the positive semidefinite Laplacian form. -/
theorem laplacian_bilinear_sq_le (G : WeightedGraph n m) (x y : Fin n → ℝ) :
    (∑ i, y i * ∑ j, G.laplacian (fun _ ↦ 1) i j * x j) ^ 2 ≤
      laplacianEnergy G x * laplacianEnergy G y := by
  rw [laplacian_bilinear, laplacianEnergy_eq_sum_drops, laplacianEnergy_eq_sum_drops]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin m))
    (fun e ↦ Real.sqrt (G.weights e) * voltageDrop G x e)
    (fun e ↦ Real.sqrt (G.weights e) * voltageDrop G y e)
  have hleft : ∑ e, Real.sqrt (G.weights e) * voltageDrop G x e *
      (Real.sqrt (G.weights e) * voltageDrop G y e) =
        ∑ e, G.weights e * voltageDrop G x e * voltageDrop G y e := by
    refine Finset.sum_congr rfl fun e _ ↦ ?_
    have hsqrt := Real.mul_self_sqrt (G.weights_pos e).le
    calc
      Real.sqrt (G.weights e) * voltageDrop G x e *
          (Real.sqrt (G.weights e) * voltageDrop G y e) =
          (Real.sqrt (G.weights e) * Real.sqrt (G.weights e)) *
            voltageDrop G x e * voltageDrop G y e := by ring
      _ = G.weights e * voltageDrop G x e * voltageDrop G y e := by rw [hsqrt]
  have hsq : ∀ z : Fin n → ℝ,
      ∑ e, (Real.sqrt (G.weights e) * voltageDrop G z e) ^ 2 =
        ∑ e, G.weights e * voltageDrop G z e ^ 2 := by
    intro z
    refine Finset.sum_congr rfl fun e _ ↦ ?_
    rw [mul_pow, Real.sq_sqrt (G.weights_pos e).le]
  rw [hleft, hsq x, hsq y] at hcs
  exact hcs

/-- `‖B x‖ ≤ λ_max ‖x‖` in squared form. The largest eigenvalue is the spectral norm of `B`. -/
theorem sum_sq_laplacian_mulVec_le (G : WeightedGraph n m) (x : Fin n → ℝ) :
    ∑ i, (∑ j, G.laplacian (fun _ ↦ 1) i j * x j) ^ 2 ≤
      laplacianEigenvalueMax G (fun _ ↦ 1) ^ 2 * ∑ i, x i ^ 2 := by
  set y : Fin n → ℝ := fun i ↦ ∑ j, G.laplacian (fun _ ↦ 1) i j * x j with hy
  set N : ℝ := ∑ i, y i ^ 2 with hN
  have hN_nonneg : 0 ≤ N := Finset.sum_nonneg fun i _ ↦ sq_nonneg _
  have hN_eq : N = ∑ i, y i * ∑ j, G.laplacian (fun _ ↦ 1) i j * x j := by
    rw [hN]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [sq]
  have hcs := laplacian_bilinear_sq_le G x y
  rw [← hN_eq] at hcs
  have hx := energy_le_lambdaMax_mul_sq G x
  have hyE := energy_le_lambdaMax_mul_sq G y
  rw [← hN] at hyE
  have hprod : laplacianEnergy G x * laplacianEnergy G y ≤
      (laplacianEigenvalueMax G (fun _ ↦ 1) * ∑ i, x i ^ 2) *
        (laplacianEigenvalueMax G (fun _ ↦ 1) * N) :=
    mul_le_mul hx hyE (laplacianEnergy_nonneg G y)
      ((laplacianEnergy_nonneg G x).trans hx)
  by_cases hzero : N = 0
  · change N ≤ _
    rw [hzero]
    exact mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun i _ ↦ sq_nonneg _)
  · have hN_pos : 0 < N := lt_of_le_of_ne hN_nonneg (Ne.symm hzero)
    have hchain : N * N ≤
        (laplacianEigenvalueMax G (fun _ ↦ 1) ^ 2 * ∑ i, x i ^ 2) * N := by
      calc
        N * N = N ^ 2 := (sq N).symm
        _ ≤ laplacianEnergy G x * laplacianEnergy G y := hcs
        _ ≤ (laplacianEigenvalueMax G (fun _ ↦ 1) * ∑ i, x i ^ 2) *
            (laplacianEigenvalueMax G (fun _ ↦ 1) * N) := hprod
        _ = (laplacianEigenvalueMax G (fun _ ↦ 1) ^ 2 * ∑ i, x i ^ 2) * N := by ring
    exact le_of_mul_le_mul_right hchain hN_pos

/-- `λ₂ ‖x‖ ≤ ‖B x‖` on balanced vectors, in squared form. The reciprocal of `λ₂` is the
spectral norm of the pseudoinverse `B⁺`. -/
theorem lambda2_sq_mul_sq_le_sum_sq_laplacian_mulVec (G : WeightedGraph n m)
    (hn : 1 < n) (x : Fin n → ℝ) (hx : ∑ i, x i = 0) :
    laplacian_eigenvalue₂ G (fun _ ↦ 1) ^ 2 * ∑ i, x i ^ 2 ≤
      ∑ i, (∑ j, G.laplacian (fun _ ↦ 1) i j * x j) ^ 2 := by
  set M : ℝ := ∑ i, x i ^ 2 with hM
  have hM_nonneg : 0 ≤ M := Finset.sum_nonneg fun i _ ↦ sq_nonneg _
  have hlambda_nonneg := lambda2_nonneg G hn
  have hray := lambda2_mul_sq_le_energy G x hx
  rw [← hM] at hray
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n))
    (fun i ↦ ∑ j, G.laplacian (fun _ ↦ 1) i j * x j) x
  have henergy : laplacianEnergy G x =
      ∑ i, (∑ j, G.laplacian (fun _ ↦ 1) i j * x j) * x i := rfl
  rw [← henergy, ← hM] at hcs
  by_cases hzero : M = 0
  · rw [hzero, mul_zero]
    exact Finset.sum_nonneg fun i _ ↦ sq_nonneg _
  · have hM_pos : 0 < M := lt_of_le_of_ne hM_nonneg (Ne.symm hzero)
    have hsq : (laplacian_eigenvalue₂ G (fun _ ↦ 1) * M) ^ 2 ≤ laplacianEnergy G x ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg hlambda_nonneg hM_nonneg) hray 2
    have hchain : (laplacian_eigenvalue₂ G (fun _ ↦ 1) ^ 2 * M) * M ≤
        (∑ i, (∑ j, G.laplacian (fun _ ↦ 1) i j * x j) ^ 2) * M := by
      calc
        (laplacian_eigenvalue₂ G (fun _ ↦ 1) ^ 2 * M) * M =
            (laplacian_eigenvalue₂ G (fun _ ↦ 1) * M) ^ 2 := by ring
        _ ≤ laplacianEnergy G x ^ 2 := hsq
        _ ≤ (∑ i, (∑ j, G.laplacian (fun _ ↦ 1) i j * x j) ^ 2) * M := hcs
    exact le_of_mul_le_mul_right hchain hM_pos

/-- The pseudo condition number is the condition number of `B` on balanced injections. If
`B θ = p` with `θ` balanced, then `λ₂ ‖θ‖ ≤ ‖p‖ ≤ λ_max ‖θ‖`. Hence `‖B‖₂ = λ_max`,
`‖B⁺‖₂ = 1 / λ₂` on `1⊥`, and `κ₊ = ‖B‖₂ ‖B⁺‖₂`. Both bounds are attained by the extreme
eigenvectors constructed in `SpectralHardPair.lean`. -/
theorem balanced_solve_norm_bounds (G : WeightedGraph n m) (hn : 1 < n)
    (θ p : Fin n → ℝ) (hθ : ∑ i, θ i = 0)
    (hsolve : ∀ i, ∑ j, G.laplacian (fun _ ↦ 1) i j * θ j = p i) :
    laplacian_eigenvalue₂ G (fun _ ↦ 1) ^ 2 * ∑ i, θ i ^ 2 ≤ ∑ i, p i ^ 2 ∧
      ∑ i, p i ^ 2 ≤ laplacianEigenvalueMax G (fun _ ↦ 1) ^ 2 * ∑ i, θ i ^ 2 := by
  have hlow := lambda2_sq_mul_sq_le_sum_sq_laplacian_mulVec G hn θ hθ
  have hhigh := sum_sq_laplacian_mulVec_le G θ
  simp_rw [hsolve] at hlow hhigh
  exact ⟨hlow, hhigh⟩

/-- Euclidean relative error is at most `√κ₊` times energy norm relative error, in squared and
cross multiplied form. The error `x` is balanced. -/
theorem euclidean_error_le_energy_error (G : WeightedGraph n m)
    (x θ : Fin n → ℝ) (hx : ∑ i, x i = 0) :
    laplacian_eigenvalue₂ G (fun _ ↦ 1) * (∑ i, x i ^ 2) * laplacianEnergy G θ ≤
      laplacianEigenvalueMax G (fun _ ↦ 1) * (∑ i, θ i ^ 2) * laplacianEnergy G x := by
  have hlow := lambda2_mul_sq_le_energy G x hx
  have hhigh := energy_le_lambdaMax_mul_sq G θ
  have hθ_nonneg := laplacianEnergy_nonneg G θ
  have hx_nonneg := laplacianEnergy_nonneg G x
  calc
    laplacian_eigenvalue₂ G (fun _ ↦ 1) * (∑ i, x i ^ 2) * laplacianEnergy G θ ≤
        laplacianEnergy G x * laplacianEnergy G θ :=
      mul_le_mul_of_nonneg_right hlow hθ_nonneg
    _ ≤ laplacianEnergy G x * (laplacianEigenvalueMax G (fun _ ↦ 1) * ∑ i, θ i ^ 2) :=
      mul_le_mul_of_nonneg_left hhigh hx_nonneg
    _ = laplacianEigenvalueMax G (fun _ ↦ 1) * (∑ i, θ i ^ 2) * laplacianEnergy G x := by
      ring

/-- Energy norm relative error is at most `√κ₊` times Euclidean relative error, in squared and
cross multiplied form. The reference `θ` is balanced. -/
theorem energy_error_le_euclidean_error (G : WeightedGraph n m)
    (x θ : Fin n → ℝ) (hθ : ∑ i, θ i = 0) :
    laplacian_eigenvalue₂ G (fun _ ↦ 1) * (∑ i, θ i ^ 2) * laplacianEnergy G x ≤
      laplacianEigenvalueMax G (fun _ ↦ 1) * (∑ i, x i ^ 2) * laplacianEnergy G θ :=
  euclidean_error_le_energy_error G θ x hθ

/-- Fact (F3), accuracy conversion. If the classical output `θhat` has energy norm relative error
`δ` and the error is balanced, then its squared Euclidean relative error is at most `δ² κ₊`. -/
theorem euclidean_accuracy_of_energy_accuracy (G : WeightedGraph n m)
    (hconn : G.CombinatoriallyConnected) (hn : 1 < n)
    (θ θhat : Fin n → ℝ) (δ : ℝ)
    (hbalanced : ∑ i, (θhat i - θ i) = 0)
    (henergy : laplacianEnergy G (fun i ↦ θhat i - θ i) ≤ δ ^ 2 * laplacianEnergy G θ) :
    ∑ i, (θhat i - θ i) ^ 2 ≤
      δ ^ 2 * effectiveConditionNumber G (fun _ ↦ 1) * ∑ i, θ i ^ 2 := by
  have hlambda_pos := combinatoriallyConnected_implies_spectralConnected G hconn hn
  unfold WeightedGraph.Connected at hlambda_pos
  have hlow := lambda2_mul_sq_le_energy G (fun i ↦ θhat i - θ i) hbalanced
  have hhigh := energy_le_lambdaMax_mul_sq G θ
  have hchain : laplacian_eigenvalue₂ G (fun _ ↦ 1) * ∑ i, (θhat i - θ i) ^ 2 ≤
      δ ^ 2 * (laplacianEigenvalueMax G (fun _ ↦ 1) * ∑ i, θ i ^ 2) :=
    hlow.trans (henergy.trans (mul_le_mul_of_nonneg_left hhigh (sq_nonneg δ)))
  unfold effectiveConditionNumber
  rw [mul_div_assoc', div_mul_eq_mul_div, le_div_iff₀ hlambda_pos]
  calc
    (∑ i, (θhat i - θ i) ^ 2) * laplacian_eigenvalue₂ G (fun _ ↦ 1) =
        laplacian_eigenvalue₂ G (fun _ ↦ 1) * ∑ i, (θhat i - θ i) ^ 2 := by ring
    _ ≤ δ ^ 2 * (laplacianEigenvalueMax G (fun _ ↦ 1) * ∑ i, θ i ^ 2) := hchain
    _ = δ ^ 2 * laplacianEigenvalueMax G (fun _ ↦ 1) * ∑ i, θ i ^ 2 := by ring

/-- Fact (F3) with the letter's choice `δ = ε / √κ₊`: the classical output then meets the
Euclidean accuracy `‖θhat - θ‖₂ ≤ ε ‖θ‖₂` of quantum solvers. -/
theorem euclidean_accuracy_of_scaled_energy_accuracy (G : WeightedGraph n m)
    (hconn : G.CombinatoriallyConnected) (hn : 1 < n)
    (θ θhat : Fin n → ℝ) (ε : ℝ)
    (hbalanced : ∑ i, (θhat i - θ i) = 0)
    (henergy : laplacianEnergy G (fun i ↦ θhat i - θ i) ≤
      (ε / Real.sqrt (effectiveConditionNumber G (fun _ ↦ 1))) ^ 2 * laplacianEnergy G θ) :
    ∑ i, (θhat i - θ i) ^ 2 ≤ ε ^ 2 * ∑ i, θ i ^ 2 := by
  have hlambda_pos := combinatoriallyConnected_implies_spectralConnected G hconn hn
  unfold WeightedGraph.Connected at hlambda_pos
  have hmax_nonneg : 0 ≤ laplacianEigenvalueMax G (fun _ ↦ 1) :=
    lambdaMax_nonneg G (fun _ ↦ 1) (fun _ ↦ zero_le_one) (by omega)
  have hkappa_nonneg : 0 ≤ effectiveConditionNumber G (fun _ ↦ 1) :=
    div_nonneg hmax_nonneg hlambda_pos.le
  have hbase := euclidean_accuracy_of_energy_accuracy G hconn hn θ θhat
    (ε / Real.sqrt (effectiveConditionNumber G (fun _ ↦ 1))) hbalanced henergy
  have hsum_nonneg : 0 ≤ ∑ i, θ i ^ 2 := Finset.sum_nonneg fun i _ ↦ sq_nonneg _
  have hfactor : (ε / Real.sqrt (effectiveConditionNumber G (fun _ ↦ 1))) ^ 2 *
      effectiveConditionNumber G (fun _ ↦ 1) ≤ ε ^ 2 := by
    by_cases hzero : effectiveConditionNumber G (fun _ ↦ 1) = 0
    · rw [hzero, mul_zero]
      exact sq_nonneg ε
    · have hkappa_pos : 0 < effectiveConditionNumber G (fun _ ↦ 1) :=
        lt_of_le_of_ne hkappa_nonneg (Ne.symm hzero)
      rw [div_pow, Real.sq_sqrt hkappa_nonneg, div_mul_cancel₀ _ hkappa_pos.ne']
  exact hbase.trans (mul_le_mul_of_nonneg_right hfactor hsum_nonneg)

end
