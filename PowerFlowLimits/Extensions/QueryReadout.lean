/-
Copyright (c) 2026 Cameron Khanpour and Samuel Talkington. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Cameron Khanpour, Samuel Talkington
-/
import PowerFlowLimits.QueryHardness

/-!
# Query and readout extensions

This module contains coded and unit-star constructions that strengthen, but are not needed by, the
manuscript claim surface.
-/

open Finset BigOperators Matrix

noncomputable section

namespace PowerFlowLimits.Extensions.QueryReadout

open RHSQueryHardness

/-- Unit-weight star Laplacian on one center and `r` leaves. -/
def starLaplacianAction (r : ℕ) (x : Fin (r + 1) → ℝ) : Fin (r + 1) → ℝ :=
  Fin.cases ((r : ℝ) * x 0 - ∑ j : Fin r, x j.succ)
    (fun j ↦ x j.succ - x 0)

/-- The radial fast mode of the unit star. -/
def starFast (r : ℕ) : Fin (r + 1) → ℝ :=
  Fin.cases (-(r : ℝ)) (fun _ ↦ 1)

/-- A leaf codeword, extended by zero at the star center. -/
def starSlow {r : ℕ} (z : Fin r → ℝ) : Fin (r + 1) → ℝ :=
  Fin.cases 0 z

theorem starFast_balanced (r : ℕ) : IsBalanced (starFast r) := by
  simp [IsBalanced, starFast, Fin.sum_univ_succ]

theorem starSlow_balanced {r : ℕ} (z : Fin r → ℝ) (hz : ∑ j, z j = 0) :
    IsBalanced (starSlow z) := by
  simpa [IsBalanced, starSlow, Fin.sum_univ_succ] using hz

/-- The radial star mode has eigenvalue `r+1`. -/
theorem starLaplacianAction_fast (r : ℕ) :
    starLaplacianAction r (starFast r) = (r + 1 : ℝ) • starFast r := by
  funext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simp [starLaplacianAction, starFast]
    ring
  · simp [starLaplacianAction, starFast]
    ring

/-- Every zero-sum leaf codeword is a slow star eigenmode with eigenvalue one. -/
theorem starLaplacianAction_slow {r : ℕ} (z : Fin r → ℝ) (hz : ∑ j, z j = 0) :
    starLaplacianAction r (starSlow z) = starSlow z := by
  funext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simp [starLaplacianAction, starSlow, hz]
  · simp [starLaplacianAction, starSlow]

theorem starSlow_sqNorm {r : ℕ} (z : Fin r → ℝ) :
    sqNorm (starSlow z) = sqNorm z := by
  simp [sqNorm, dotProduct, starSlow, Fin.sum_univ_succ]

theorem starFast_dot_starSlow {r : ℕ} (z : Fin r → ℝ) (hz : ∑ j, z j = 0) :
    dotProduct (starFast r) (starSlow z) = 0 := by
  simpa [dotProduct, starFast, starSlow, Fin.sum_univ_succ] using hz

theorem starFast_sqNorm (r : ℕ) :
    sqNorm (starFast r) = (r : ℝ) * (r + 1) := by
  simp [sqNorm, dotProduct, starFast, Fin.sum_univ_succ]
  ring

/-- Exact Rayleigh numerator on the balanced subspace of the unit star. -/
theorem starLaplacian_energy_of_balanced (r : ℕ) (x : Fin (r + 1) → ℝ)
    (hx : IsBalanced x) :
    dotProduct x (starLaplacianAction r x) =
      sqNorm x + (r + 1 : ℝ) * (x 0) ^ 2 := by
  have hx' : x 0 + ∑ j : Fin r, x j.succ = 0 := by
    simpa [IsBalanced, Fin.sum_univ_succ] using hx
  simp only [dotProduct, sqNorm, starLaplacianAction, Fin.sum_univ_succ,
    Fin.cases_zero, Fin.cases_succ]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  rw [← Finset.sum_mul]
  have hmul := congrArg (fun y : ℝ ↦ 2 * x 0 * y) hx'
  ring_nf at hmul
  ring_nf
  linarith

theorem starLaplacian_rayleigh_lower (r : ℕ) (x : Fin (r + 1) → ℝ)
    (hx : IsBalanced x) :
    sqNorm x ≤ dotProduct x (starLaplacianAction r x) := by
  rw [starLaplacian_energy_of_balanced r x hx]
  have hnonneg : 0 ≤ (r + 1 : ℝ) * (x 0) ^ 2 := by positivity
  linarith

theorem starLaplacian_rayleigh_upper (r : ℕ) (x : Fin (r + 1) → ℝ)
    (hx : IsBalanced x) :
    dotProduct x (starLaplacianAction r x) ≤ (r + 1 : ℝ) * sqNorm x := by
  have hx' : x 0 + ∑ j : Fin r, x j.succ = 0 := by
    simpa [IsBalanced, Fin.sum_univ_succ] using hx
  have hsqeq : (x 0) ^ 2 = (∑ j : Fin r, x j.succ) ^ 2 := by
    have h := congrArg (fun y : ℝ ↦ y ^ 2) hx'
    nlinarith
  have hcs : (∑ j : Fin r, x j.succ) ^ 2 ≤
      (r : ℝ) * ∑ j : Fin r, (x j.succ) ^ 2 := by
    simpa using (sq_sum_le_card_mul_sum_sq
      (s := (Finset.univ : Finset (Fin r))) (f := fun j ↦ x j.succ))
  have hcenter : (x 0) ^ 2 ≤ (r : ℝ) * ∑ j : Fin r, (x j.succ) ^ 2 :=
    hsqeq.le.trans hcs
  rw [starLaplacian_energy_of_balanced r x hx]
  have hnorm : sqNorm x = (x 0) ^ 2 + ∑ j : Fin r, (x j.succ) ^ 2 := by
    simp [sqNorm, dotProduct, Fin.sum_univ_succ, sq]
  rw [hnorm]
  nlinarith

/-- Coefficients of a coded right hand side. The first coordinate is a common fast mode and the
second is a codeword in a slow eigenspace. -/
def codedPrepared (κ α : ℝ) : Fin 2 → ℝ := fun i ↦
  if i = 0 then κ / Real.sqrt (κ ^ 2 + α ^ 2)
  else α / Real.sqrt (κ ^ 2 + α ^ 2)

/-- Coefficients of the normalized solution corresponding to `codedPrepared`. -/
def codedSolution (α : ℝ) : Fin 2 → ℝ := fun i ↦
  if i = 0 then 1 / Real.sqrt (1 + α ^ 2)
  else α / Real.sqrt (1 + α ^ 2)

theorem codedPrepared_normalized (κ α : ℝ) (hκ : 0 < κ) :
    sqNorm (codedPrepared κ α) = 1 := by
  have hpos : 0 < κ ^ 2 + α ^ 2 := by positivity
  have hsqrt : Real.sqrt (κ ^ 2 + α ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hpos)
  simp [sqNorm, dotProduct, codedPrepared, Fin.sum_univ_two]
  field_simp [hsqrt]
  nlinarith [Real.sq_sqrt hpos.le]

theorem codedSolution_normalized (α : ℝ) :
    sqNorm (codedSolution α) = 1 := by
  have hpos : 0 < 1 + α ^ 2 := by positivity
  have hsqrt : Real.sqrt (1 + α ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hpos)
  simp [sqNorm, dotProduct, codedSolution, Fin.sum_univ_two]
  field_simp [hsqrt]
  nlinarith [Real.sq_sqrt hpos.le]

/-- Applying inverse gains `1` and `κ` to a coded prepared state yields its coded solution,
up to the displayed positive normalization scalar. -/
theorem inverseMap_codedPrepared (κ α : ℝ) :
    inverseMap κ (codedPrepared κ α) =
      fun i ↦ (κ * Real.sqrt (1 + α ^ 2) / Real.sqrt (κ ^ 2 + α ^ 2)) *
        codedSolution α i := by
  have hsqrt : Real.sqrt (1 + α ^ 2) ≠ 0 := by positivity
  funext i
  fin_cases i <;> simp [inverseMap, codedPrepared, codedSolution]
  <;> field_simp [hsqrt]

/-- The informative amplitude of the prepared right hand side is at most the solution signal
amplitude divided by the inverse gain ratio. -/
theorem codedPrepared_signal_le (κ α : ℝ) (hκ : 0 < κ) (hα : 0 ≤ α) :
    α / Real.sqrt (κ ^ 2 + α ^ 2) ≤ α / κ := by
  have hsq : κ ^ 2 ≤ κ ^ 2 + α ^ 2 := by nlinarith [sq_nonneg α]
  have hsqrt : κ ≤ Real.sqrt (κ ^ 2 + α ^ 2) := by
    have h := Real.sqrt_le_sqrt hsq
    simpa [Real.sqrt_sq_eq_abs, abs_of_pos hκ] using h
  exact div_le_div_of_nonneg_left hα hκ hsqrt

/-- The coded version of the two-mode solve identity. The slow vector can be any normalized
codeword in a common slow eigenspace. -/
theorem solve_codedPrepared {d : ℕ} (P : BalancedModePair d) (κ α : ℝ)
    (solve : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ))
    (hfast : solve P.fast = P.fast) (hslow : solve P.slow = κ • P.slow) :
    solve (P.embed (codedPrepared κ α)) =
      (κ * Real.sqrt (1 + α ^ 2) / Real.sqrt (κ ^ 2 + α ^ 2)) •
        P.embed (codedSolution α) := by
  have hsqrt : Real.sqrt (1 + α ^ 2) ≠ 0 := by positivity
  simp only [BalancedModePair.embed, LinearMap.map_add, LinearMap.map_smul, hfast, hslow]
  ext i
  simp [codedPrepared, codedSolution]
  field_simp [hsqrt]

end PowerFlowLimits.Extensions.QueryReadout

end
