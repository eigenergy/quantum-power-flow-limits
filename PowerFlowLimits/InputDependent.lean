/-
Copyright (c) 2026 Cameron Khanpour and Samuel Talkington. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Cameron Khanpour, Samuel Talkington
-/
import PowerFlowLimits.EnergyNorm
import PowerFlowLimits.QueryHardness
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Readout thresholds and input dependent solvers on the hard pair

This file proves three statements that accompany the query lower bounds of the letter.

* An output of relative accuracy `ε < 1 / √2` for one solution of the hard pair is not accurate
  for the other, so it tells the two injections apart.
* The effective condition number of input dependent solvers equals `κ₊` on the hard pair for
  every `ε < 1 / √2`, because half the mass of the solution sits on the slowest mode.
* Substituting `κ = Ω(n)` into the criterion `D κ^{3/2} ≤ n / d` forces `D = O(n^{-1/2})`.

The effective condition number follows the letter's description. A cutoff `μ` is admissible for
a solution direction `ψ` at tolerance `ε` when the squared mass of `ψ` on the eigenvectors with
eigenvalue below `μ` is at most `ε²`, and `κ_eff(ε)` is `λ_max` divided by the largest
admissible cutoff.
-/

open Finset BigOperators Matrix
open scoped Matrix

noncomputable section

variable {n m : ℕ}

namespace RHSQueryHardness

/-- A squared triangle inequality: `‖x - y‖² ≤ 2 ‖out - x‖² + 2 ‖out - y‖²`. -/
theorem sqDistance_le_two_mul_add {d : ℕ} (x y out : Fin d → ℝ) :
    sqDistance x y ≤ 2 * sqDistance out x + 2 * sqDistance out y := by
  simp only [sqDistance, sqNorm, dotProduct, Pi.sub_apply]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  nlinarith [sq_nonneg (out i - x i + (out i - y i))]

/-- If two vectors of equal norm are `√2` norms apart, then an output within relative accuracy
`ε < 1 / √2` of the first is farther than that from the second. -/
theorem accurate_output_separates {d : ℕ} (xp xm out : Fin d → ℝ) (ε : ℝ)
    (hnorm : sqNorm xp = sqNorm xm) (hdist : sqDistance xp xm = 2 * sqNorm xp)
    (hpos : 0 < sqNorm xp) (hε : ε ^ 2 < 1 / 2)
    (hplus : sqDistance out xp ≤ ε ^ 2 * sqNorm xp) :
    ε ^ 2 * sqNorm xm < sqDistance out xm := by
  have htriangle := sqDistance_le_two_mul_add xp xm out
  rw [hdist] at htriangle
  rw [← hnorm]
  have hmargin : 0 < (1 / 2 - ε ^ 2) * sqNorm xp := mul_pos (sub_pos.mpr hε) hpos
  nlinarith

theorem sqNorm_smul {d : ℕ} (c : ℝ) (x : Fin d → ℝ) :
    sqNorm (c • x) = c ^ 2 * sqNorm x := by
  simp only [sqNorm, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

theorem sqDistance_smul {d : ℕ} (c : ℝ) (x y : Fin d → ℝ) :
    sqDistance (c • x) (c • y) = c ^ 2 * sqDistance x y := by
  rw [sqDistance, ← smul_sub, sqNorm_smul, sqDistance]

/-- The decision rule in the proof of the query lower bounds. The two solutions of the hard pair
are `c • ψ₊` and `c • ψ₋` for a common scale `c ≠ 0`. A classical output or a state within
relative accuracy `ε < 1 / √2` of one is not within that accuracy of the other. -/
theorem hardPair_accurate_output_separates {d : ℕ} (P : BalancedModePair d) (c ε : ℝ)
    (hc : c ≠ 0) (hε : ε ^ 2 < 1 / 2) (out : Fin d → ℝ)
    (hplus : sqDistance out (c • balancedSolutionPlus P) ≤
      ε ^ 2 * sqNorm (c • balancedSolutionPlus P)) :
    ε ^ 2 * sqNorm (c • balancedSolutionMinus P) <
      sqDistance out (c • balancedSolutionMinus P) := by
  have hcsq : 0 < c ^ 2 := by positivity
  refine accurate_output_separates (c • balancedSolutionPlus P) (c • balancedSolutionMinus P)
    out ε ?_ ?_ ?_ hε hplus
  · rw [sqNorm_smul, sqNorm_smul, balancedSolutionPlus_normalized,
      balancedSolutionMinus_normalized]
  · rw [sqDistance_smul, sqNorm_smul, balancedSolution_sqDistance,
      balancedSolutionPlus_normalized]
    ring
  · rw [sqNorm_smul, balancedSolutionPlus_normalized]
    linarith

/-- The same decision rule with the roles of the two solutions exchanged. -/
theorem hardPair_accurate_output_separates' {d : ℕ} (P : BalancedModePair d) (c ε : ℝ)
    (hc : c ≠ 0) (hε : ε ^ 2 < 1 / 2) (out : Fin d → ℝ)
    (hminus : sqDistance out (c • balancedSolutionMinus P) ≤
      ε ^ 2 * sqNorm (c • balancedSolutionMinus P)) :
    ε ^ 2 * sqNorm (c • balancedSolutionPlus P) <
      sqDistance out (c • balancedSolutionPlus P) := by
  have hcsq : 0 < c ^ 2 := by positivity
  have hsymm : sqDistance (balancedSolutionMinus P) (balancedSolutionPlus P) = 2 := by
    have h := balancedSolution_sqDistance P
    simp only [sqDistance, sqNorm, dotProduct, Pi.sub_apply] at h ⊢
    rw [← h]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    ring
  refine accurate_output_separates (c • balancedSolutionMinus P) (c • balancedSolutionPlus P)
    out ε ?_ ?_ ?_ hε hminus
  · rw [sqNorm_smul, sqNorm_smul, balancedSolutionPlus_normalized,
      balancedSolutionMinus_normalized]
  · rw [sqDistance_smul, sqNorm_smul, hsymm, balancedSolutionMinus_normalized]
    ring
  · rw [sqNorm_smul, balancedSolutionMinus_normalized]
    linarith

theorem BalancedModePair.slow_dot_embed {d : ℕ} (P : BalancedModePair d) (z : Fin 2 → ℝ) :
    dotProduct P.slow (P.embed z) = z 1 := by
  have hslow : dotProduct P.slow P.slow = 1 := P.slow_normalized
  simp [BalancedModePair.embed, dotProduct_add, dotProduct_smul, hslow, P.slow_dot_fast]

/-- Half the mass of each hard solution state sits on the slow mode. -/
theorem slow_mass_balancedSolution {d : ℕ} (P : BalancedModePair d) :
    dotProduct P.slow (balancedSolutionPlus P) ^ 2 = 1 / 2 ∧
      dotProduct P.slow (balancedSolutionMinus P) ^ 2 = 1 / 2 := by
  have hsqrt : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  constructor
  · rw [balancedSolutionPlus, P.slow_dot_embed]
    simp only [solutionPlus]
    norm_num [div_pow, hsqrt]
  · rw [balancedSolutionMinus, P.slow_dot_embed]
    simp only [solutionMinus]
    norm_num [div_pow, hsqrt]

end RHSQueryHardness

/-- Balanced eigenvectors of the susceptance Laplacian with eigenvalue below the cutoff `μ`. -/
def slowModes (G : WeightedGraph n m) (μ : ℝ) : Set (Fin n → ℝ) :=
  {w | ∑ i, w i = 0 ∧ ∃ lam : ℝ, lam < μ ∧
    ∀ i, ∑ j, G.laplacian (fun _ ↦ 1) i j * w j = lam * w i}

/-- Squared mass of the direction `ψ` on the span of the modes slower than `μ`. This is the
squared norm of the projection of `ψ` onto that span, written as a supremum over unit vectors. -/
def slowMass (G : WeightedGraph n m) (μ : ℝ) (ψ : Fin n → ℝ) : ℝ :=
  sSup {a : ℝ | ∃ w ∈ Submodule.span ℝ (slowModes G μ),
    dotProduct w w = 1 ∧ a = dotProduct w ψ ^ 2}

/-- The effective condition number of input dependent solvers for the solution direction `ψ` at
tolerance `ε`: the largest eigenvalue divided by the largest cutoff below which `ψ` carries
squared mass at most `ε²`. -/
def inputDependentConditionNumber (G : WeightedGraph n m) (ε : ℝ) (ψ : Fin n → ℝ) : ℝ :=
  laplacianEigenvalueMax G (fun _ ↦ 1) /
    sSup {μ : ℝ | μ ≤ laplacianEigenvalueMax G (fun _ ↦ 1) ∧ slowMass G μ ψ ≤ ε ^ 2}

/-- No nonzero balanced eigenvector has an eigenvalue below `λ₂`. -/
theorem eq_zero_of_mem_slowModes_lambda2 (G : WeightedGraph n m) (w : Fin n → ℝ)
    (hw : w ∈ slowModes G (laplacian_eigenvalue₂ G (fun _ ↦ 1))) : w = 0 := by
  obtain ⟨hbalanced, lam, hlam, heigen⟩ := hw
  have hray := lambda2_mul_sq_le_energy G w hbalanced
  have henergy : laplacianEnergy G w = lam * ∑ i, w i ^ 2 := by
    unfold laplacianEnergy
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [heigen i]
    ring
  rw [henergy] at hray
  have hsum_nonneg : 0 ≤ ∑ i, w i ^ 2 := Finset.sum_nonneg fun i _ ↦ sq_nonneg _
  have hsum_zero : ∑ i, w i ^ 2 = 0 := by
    by_contra hne
    have hpos : 0 < ∑ i, w i ^ 2 := lt_of_le_of_ne hsum_nonneg (Ne.symm hne)
    nlinarith [mul_pos (sub_pos.mpr hlam) hpos]
  funext i
  have hsq := (Finset.sum_eq_zero_iff_of_nonneg fun j _ ↦ sq_nonneg (w j)).mp hsum_zero i
    (Finset.mem_univ i)
  exact pow_eq_zero_iff (by norm_num) |>.mp hsq

/-- At the cutoff `λ₂` there are no slower modes, so the slow mass vanishes. -/
theorem slowMass_lambda2 (G : WeightedGraph n m) (ψ : Fin n → ℝ) :
    slowMass G (laplacian_eigenvalue₂ G (fun _ ↦ 1)) ψ = 0 := by
  have hspan : Submodule.span ℝ (slowModes G (laplacian_eigenvalue₂ G (fun _ ↦ 1))) ≤ ⊥ := by
    rw [Submodule.span_le]
    intro w hw
    rw [eq_zero_of_mem_slowModes_lambda2 G w hw]
    exact Submodule.zero_mem _
  have hempty : {a : ℝ | ∃ w ∈ Submodule.span ℝ
      (slowModes G (laplacian_eigenvalue₂ G (fun _ ↦ 1))),
        dotProduct w w = 1 ∧ a = dotProduct w ψ ^ 2} = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro a ⟨w, hw, hnorm, _⟩
    have hzero : w = 0 := (Submodule.mem_bot ℝ).mp (hspan hw)
    rw [hzero] at hnorm
    simp at hnorm
  unfold slowMass
  rw [hempty, Real.sSup_empty]

/-- A unit mode slower than the cutoff contributes its squared overlap to the slow mass. -/
theorem sq_dotProduct_le_slowMass (G : WeightedGraph n m) (μ : ℝ) (v ψ : Fin n → ℝ)
    (hv : v ∈ slowModes G μ) (hnorm : dotProduct v v = 1) :
    dotProduct v ψ ^ 2 ≤ slowMass G μ ψ := by
  unfold slowMass
  refine le_csSup ?_ ⟨v, Submodule.subset_span hv, hnorm, rfl⟩
  refine ⟨dotProduct ψ ψ, ?_⟩
  rintro a ⟨w, _, hw, rfl⟩
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n)) w ψ
  have hw' : ∑ i, w i ^ 2 = 1 := by
    simpa [dotProduct, sq] using hw
  have hψ : dotProduct ψ ψ = ∑ i, ψ i ^ 2 := by
    simp [dotProduct, sq]
  rw [hw', one_mul] at hcs
  rw [hψ]
  exact hcs

/-- The cutoff `λ₂` is always admissible, so the effective condition number never exceeds the
pseudo condition number. -/
theorem inputDependentConditionNumber_le (G : WeightedGraph n m) (ε : ℝ) (ψ : Fin n → ℝ)
    (hlambda : 0 < laplacian_eigenvalue₂ G (fun _ ↦ 1))
    (hle : laplacian_eigenvalue₂ G (fun _ ↦ 1) ≤ laplacianEigenvalueMax G (fun _ ↦ 1)) :
    inputDependentConditionNumber G ε ψ ≤ effectiveConditionNumber G (fun _ ↦ 1) := by
  have hmem : laplacian_eigenvalue₂ G (fun _ ↦ 1) ∈
      {μ : ℝ | μ ≤ laplacianEigenvalueMax G (fun _ ↦ 1) ∧ slowMass G μ ψ ≤ ε ^ 2} := by
    refine ⟨hle, ?_⟩
    rw [slowMass_lambda2]
    exact sq_nonneg ε
  have hbdd : BddAbove
      {μ : ℝ | μ ≤ laplacianEigenvalueMax G (fun _ ↦ 1) ∧ slowMass G μ ψ ≤ ε ^ 2} :=
    ⟨laplacianEigenvalueMax G (fun _ ↦ 1), fun μ hμ ↦ hμ.1⟩
  have hcut := le_csSup hbdd hmem
  unfold inputDependentConditionNumber effectiveConditionNumber
  exact div_le_div_of_nonneg_left (hlambda.le.trans hle) hlambda hcut

/-- If the solution direction carries more than `ε²` squared mass on a mode of eigenvalue `λ₂`,
then no cutoff above `λ₂` is admissible and the effective condition number equals `κ₊`. -/
theorem inputDependentConditionNumber_eq_of_slow_mass (G : WeightedGraph n m)
    (v ψ : Fin n → ℝ) (hbalanced : ∑ i, v i = 0) (hnorm : dotProduct v v = 1)
    (heigen : ∀ i, ∑ j, G.laplacian (fun _ ↦ 1) i j * v j =
      laplacian_eigenvalue₂ G (fun _ ↦ 1) * v i)
    (hle : laplacian_eigenvalue₂ G (fun _ ↦ 1) ≤ laplacianEigenvalueMax G (fun _ ↦ 1))
    (ε : ℝ) (hmass : ε ^ 2 < dotProduct v ψ ^ 2) :
    inputDependentConditionNumber G ε ψ = effectiveConditionNumber G (fun _ ↦ 1) := by
  have hmem : laplacian_eigenvalue₂ G (fun _ ↦ 1) ∈
      {μ : ℝ | μ ≤ laplacianEigenvalueMax G (fun _ ↦ 1) ∧ slowMass G μ ψ ≤ ε ^ 2} := by
    refine ⟨hle, ?_⟩
    rw [slowMass_lambda2]
    exact sq_nonneg ε
  have hupper : ∀ μ ∈
      {μ : ℝ | μ ≤ laplacianEigenvalueMax G (fun _ ↦ 1) ∧ slowMass G μ ψ ≤ ε ^ 2},
        μ ≤ laplacian_eigenvalue₂ G (fun _ ↦ 1) := by
    intro μ hμ
    by_contra hlt
    push_neg at hlt
    have hslow : v ∈ slowModes G μ := ⟨hbalanced, _, hlt, heigen⟩
    have hmass_le := sq_dotProduct_le_slowMass G μ v ψ hslow hnorm
    linarith [hμ.2]
  have hcut : sSup
      {μ : ℝ | μ ≤ laplacianEigenvalueMax G (fun _ ↦ 1) ∧ slowMass G μ ψ ≤ ε ^ 2} =
        laplacian_eigenvalue₂ G (fun _ ↦ 1) :=
    le_antisymm (csSup_le ⟨_, hmem⟩ hupper) (le_csSup ⟨_, hupper⟩ hmem)
  unfold inputDependentConditionNumber effectiveConditionNumber
  rw [hcut]

/-- On the hard pair the effective condition number equals `κ₊` for every `ε < 1 / √2`. Input
dependent solvers therefore gain nothing on these injections. -/
theorem inputDependentConditionNumber_hardPair (G : WeightedGraph n m)
    (P : RHSQueryHardness.BalancedModePair n)
    (hslow : ∀ i, ∑ j, G.laplacian (fun _ ↦ 1) i j * P.slow j =
      laplacian_eigenvalue₂ G (fun _ ↦ 1) * P.slow i)
    (hle : laplacian_eigenvalue₂ G (fun _ ↦ 1) ≤ laplacianEigenvalueMax G (fun _ ↦ 1))
    (ε : ℝ) (hε : ε ^ 2 < 1 / 2) :
    inputDependentConditionNumber G ε (RHSQueryHardness.balancedSolutionPlus P) =
        effectiveConditionNumber G (fun _ ↦ 1) ∧
      inputDependentConditionNumber G ε (RHSQueryHardness.balancedSolutionMinus P) =
        effectiveConditionNumber G (fun _ ↦ 1) := by
  obtain ⟨hplus, hminus⟩ := RHSQueryHardness.slow_mass_balancedSolution P
  have hbalanced : ∑ i, P.slow i = 0 := P.slow_balanced
  have hnorm : dotProduct P.slow P.slow = 1 := P.slow_normalized
  exact ⟨inputDependentConditionNumber_eq_of_slow_mass G P.slow _ hbalanced hnorm hslow hle ε
      (by rw [hplus]; exact hε),
    inputDependentConditionNumber_eq_of_slow_mass G P.slow _ hbalanced hnorm hslow hle ε
      (by rw [hminus]; exact hε)⟩

/-- Substituting linear growth `κ ≥ c n` into the criterion `D κ^{3/2} ≤ n / d` of Pareek et al.
gives `D c^{3/2} √n ≤ 1`, so the admissible readout level decays like `n^{-1/2}`. -/
theorem hhl_criterion_readout_bound (nn d D κ c : ℝ) (hn : 0 < nn) (hd : 1 ≤ d)
    (hD : 0 ≤ D) (hc : 0 < c) (hκ : c * nn ≤ κ)
    (hcriterion : D * κ ^ (3 / 2 : ℝ) ≤ nn / d) :
    D * (c ^ (3 / 2 : ℝ) * Real.sqrt nn) ≤ 1 := by
  have hcn_nonneg : 0 ≤ c * nn := (mul_pos hc hn).le
  have hpow_le : (c * nn) ^ (3 / 2 : ℝ) ≤ κ ^ (3 / 2 : ℝ) :=
    Real.rpow_le_rpow hcn_nonneg hκ (by norm_num)
  have hsplit : (c * nn) ^ (3 / 2 : ℝ) = c ^ (3 / 2 : ℝ) * (nn * Real.sqrt nn) := by
    rw [Real.mul_rpow hc.le hn.le]
    have hnn : nn ^ (3 / 2 : ℝ) = nn * Real.sqrt nn := by
      rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hn, Real.rpow_one,
        Real.sqrt_eq_rpow]
    rw [hnn]
  have hdiv : nn / d ≤ nn := div_le_self hn.le hd
  have hchain : D * (c ^ (3 / 2 : ℝ) * Real.sqrt nn) * nn ≤ 1 * nn := by
    calc
      D * (c ^ (3 / 2 : ℝ) * Real.sqrt nn) * nn =
          D * (c ^ (3 / 2 : ℝ) * (nn * Real.sqrt nn)) := by ring
      _ = D * (c * nn) ^ (3 / 2 : ℝ) := by rw [hsplit]
      _ ≤ D * κ ^ (3 / 2 : ℝ) := mul_le_mul_of_nonneg_left hpow_le hD
      _ ≤ nn / d := hcriterion
      _ ≤ nn := hdiv
      _ = 1 * nn := (one_mul nn).symm
  exact le_of_mul_le_mul_right hchain hn

/-- Once `c^{3/2} √n > 1`, the criterion forces a readout level below one entry. -/
theorem hhl_criterion_no_readout_level (nn d D κ c : ℝ) (hn : 0 < nn) (hd : 1 ≤ d)
    (hD : 0 ≤ D) (hc : 0 < c) (hκ : c * nn ≤ κ)
    (hcriterion : D * κ ^ (3 / 2 : ℝ) ≤ nn / d)
    (hlarge : 1 < c ^ (3 / 2 : ℝ) * Real.sqrt nn) :
    D < 1 := by
  have hbound := hhl_criterion_readout_bound nn d D κ c hn hd hD hc hκ hcriterion
  by_contra hD_ge
  push_neg at hD_ge
  have hprod : 1 < D * (c ^ (3 / 2 : ℝ) * Real.sqrt nn) := by
    nlinarith
  linarith

end
