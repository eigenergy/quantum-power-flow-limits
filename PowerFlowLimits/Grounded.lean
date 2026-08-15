/-
Copyright (c) 2026 Cameron Khanpour and Samuel Talkington. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Cameron Khanpour, Samuel Talkington
-/
import PowerFlowLimits.Eigenvalues

/-!
# Grounded susceptance matrices

Deleting a slack bus removes its weighted degree from the Laplacian trace. This file proves the
exact trace correction used in the original letter. Principal-submatrix interlacing is kept as a
separate variational theorem.
-/

open Finset BigOperators
open scoped Matrix

noncomputable section

variable {n m : ℕ}

/-- Bus indices after deleting the slack bus `r`. -/
abbrev GroundedIndex (r : Fin n) := {i : Fin n // i ≠ r}

/-- The principal Laplacian matrix obtained by deleting the slack bus row and column. -/
def groundedLaplacian (G : WeightedGraph n m) (r : Fin n) :
    Matrix (GroundedIndex r) (GroundedIndex r) ℝ :=
  fun i j ↦ G.laplacian (fun _ ↦ 1) i j

@[simp]
theorem groundedLaplacian_apply (G : WeightedGraph n m) (r : Fin n)
    (i j : GroundedIndex r) :
    groundedLaplacian G r i j = G.laplacian (fun _ ↦ 1) i j :=
  rfl

/-- Smallest eigenvalue of the grounded Laplacian, in Rayleigh lower-bound form. Test vectors are
functions on all buses constrained to vanish at the deleted slack bus. -/
@[irreducible] def groundedLaplacianEigenvalueMin (G : WeightedGraph n m) (r : Fin n) : ℝ :=
  sSup {a : ℝ | ∀ (x : Fin n → ℝ), x r = 0 →
    a * (∑ i, x i ^ 2) ≤
      ∑ i, (∑ j, G.laplacian (fun _ ↦ 1) i j * x j) * x i}

/-- Largest eigenvalue of the grounded Laplacian, in Rayleigh upper-bound form. -/
def groundedLaplacianEigenvalueMax (G : WeightedGraph n m) (r : Fin n) : ℝ :=
  sInf {a : ℝ | ∀ (x : Fin n → ℝ), x r = 0 →
    ∑ i, (∑ j, G.laplacian (fun _ ↦ 1) i j * x j) * x i ≤
      a * ∑ i, x i ^ 2}

/-- Spectral condition number of the grounded Laplacian. -/
def groundedConditionNumber (G : WeightedGraph n m) (r : Fin n) : ℝ :=
  groundedLaplacianEigenvalueMax G r / groundedLaplacianEigenvalueMin G r

private theorem unitLaplacianQuadratic_nonneg (G : WeightedGraph n m)
    (x : Fin n → ℝ) :
    0 ≤ ∑ i, (∑ j, G.laplacian (fun _ ↦ 1) i j * x j) * x i := by
  have hcomm : ∑ i, (∑ j, G.laplacian (fun _ ↦ 1) i j * x j) * x i =
      ∑ i, x i * ∑ j, G.laplacian (fun _ ↦ 1) i j * x j := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hcomm, laplacian_quadratic]
  exact Finset.sum_nonneg fun e _ ↦
    mul_nonneg (mul_nonneg zero_le_one (G.weights_pos e).le) (sq_nonneg _)

/-- Zero is an admissible Rayleigh lower bound for the grounded Laplacian. -/
theorem groundedEigenvalueMin_set_nonempty (G : WeightedGraph n m) (r : Fin n) :
    {a : ℝ | ∀ (x : Fin n → ℝ), x r = 0 →
      a * (∑ i, x i ^ 2) ≤
        ∑ i, (∑ j, G.laplacian (fun _ ↦ 1) i j * x j) * x i}.Nonempty :=
  ⟨0, fun x _ ↦ by simpa using unitLaplacianQuadratic_nonneg G x⟩

/-- With another bus besides the slack bus, the grounded Rayleigh set is bounded above. -/
theorem groundedEigenvalueMin_set_bddAbove (G : WeightedGraph n m) (r : Fin n)
    (hn : 1 < n) :
    BddAbove {a : ℝ | ∀ (x : Fin n → ℝ), x r = 0 →
      a * (∑ i, x i ^ 2) ≤
        ∑ i, (∑ j, G.laplacian (fun _ ↦ 1) i j * x j) * x i} := by
  letI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  obtain ⟨i, hi⟩ := exists_ne r
  let x : Fin n → ℝ := stdBasis i
  have hx_r : x r = 0 := by
    simp [x, stdBasis, Ne.symm hi]
  have hx_sq : ∑ j, x j ^ 2 = 1 := by
    simp [x, stdBasis, sq, Finset.sum_ite_eq', Finset.mem_univ]
  refine ⟨∑ j, (∑ k, G.laplacian (fun _ ↦ 1) j k * x k) * x j, ?_⟩
  intro a ha
  have h := ha x hx_r
  rw [hx_sq, mul_one] at h
  exact h

/-- Euclidean bus vectors constrained to vanish at the slack bus. -/
def groundedSubspace (r : Fin n) : Submodule ℝ (EuclideanSpace ℝ (Fin n)) where
  carrier := {x | x r = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    simpa using congrArg₂ (· + ·) hx hy
  smul_mem' := by
    intro c x hx
    change c * x r = 0
    rw [hx, mul_zero]

/-- Weighted voltage drops of a vector grounded at `r`. -/
def WeightedGraph.groundedWeightedDropLinearMap (G : WeightedGraph n m) (r : Fin n) :
    groundedSubspace r →ₗ[ℝ] EuclideanSpace ℝ (Fin m) where
  toFun x := WithLp.toLp 2 fun e ↦
    Real.sqrt (G.weights e) * voltageDrop G (fun i ↦ x.1 i) e
  map_add' := by
    intro x y
    ext e
    simp only [voltageDrop_eq_endpoint_diff, Submodule.coe_add, PiLp.add_apply]
    ring
  map_smul' := by
    intro c x
    ext e
    simp only [RingHom.id_apply, voltageDrop_eq_endpoint_diff, SetLike.val_smul,
      PiLp.smul_apply, smul_eq_mul]
    ring

@[simp]
theorem WeightedGraph.groundedWeightedDropLinearMap_apply (G : WeightedGraph n m)
    (r : Fin n) (x : groundedSubspace r) (e : Fin m) :
    G.groundedWeightedDropLinearMap r x e =
      Real.sqrt (G.weights e) * voltageDrop G (fun i ↦ x.1 i) e :=
  rfl

theorem WeightedGraph.groundedWeightedDropLinearMap_norm_sq (G : WeightedGraph n m)
    (r : Fin n) (x : groundedSubspace r) :
    ‖G.groundedWeightedDropLinearMap r x‖ ^ 2 =
      ∑ e, G.weights e * (voltageDrop G (fun i ↦ x.1 i) e) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  refine Finset.sum_congr rfl fun e _ ↦ ?_
  rw [G.groundedWeightedDropLinearMap_apply, Real.norm_eq_abs, sq_abs, mul_pow,
    Real.sq_sqrt (G.weights_pos e).le]

/-- Grounding removes the constant-vector kernel on an ordinarily connected graph. -/
theorem WeightedGraph.groundedWeightedDropLinearMap_injective (G : WeightedGraph n m)
    (r : Fin n) (hconn : G.CombinatoriallyConnected) :
    Function.Injective (G.groundedWeightedDropLinearMap r) := by
  intro x y hxy
  apply Subtype.ext
  ext i
  let z : Fin n → ℝ := fun j ↦ x.1 j - y.1 j
  have hdrop : ∀ e, voltageDrop G z e = 0 := by
    intro e
    have he := congrArg (fun v : EuclideanSpace ℝ (Fin m) ↦ v e) hxy
    simp only [G.groundedWeightedDropLinearMap_apply] at he
    have hsqrt : 0 < Real.sqrt (G.weights e) := Real.sqrt_pos.2 (G.weights_pos e)
    simp only [z, voltageDrop_eq_endpoint_diff] at he ⊢
    nlinarith
  have hadj : ∀ u v, G.toSimpleGraph.Adj u v → z u = z v := by
    intro u v huv
    rcases huv with ⟨e, h | h⟩
    · have he := hdrop e
      rw [voltageDrop_eq_endpoint_diff] at he
      rcases h with ⟨rfl, rfl⟩
      exact sub_eq_zero.mp he
    · have he := hdrop e
      rw [voltageDrop_eq_endpoint_diff] at he
      rcases h with ⟨rfl, rfl⟩
      exact (sub_eq_zero.mp he).symm
  have hmul : G.laplacian (fun _ ↦ 1) *ᵥ z = 0 :=
    (laplacian_mulVec_eq_zero_iff_forall_adj G z).mpr hadj
  obtain ⟨c, hc⟩ := (laplacian_mulVec_eq_zero_iff_constant G hconn z).mp hmul
  have hzr : z r = 0 := by
    change x.1 r - y.1 r = 0
    rw [x.2, y.2, sub_self]
  have hc0 : c = 0 := by
    have := congrFun hc r
    simpa [hzr] using this.symm
  have hzi : z i = 0 := by simp [hc, hc0]
  exact sub_eq_zero.mp hzi

/-- Ordinary connectivity makes the grounded Laplacian positive definite. -/
theorem groundedEigenvalueMin_pos (G : WeightedGraph n m) (r : Fin n)
    (hconn : G.CombinatoriallyConnected) (hn : 1 < n) :
    0 < groundedLaplacianEigenvalueMin G r := by
  obtain ⟨K, hK_pos, hanti⟩ :=
    (LinearMap.injective_iff_antilipschitz (G.groundedWeightedDropLinearMap r)).mp
      (G.groundedWeightedDropLinearMap_injective r hconn)
  let a : ℝ := ((K : ℝ) ^ 2)⁻¹
  have hK_real : 0 < (K : ℝ) := by exact_mod_cast hK_pos
  have hK_sq : 0 < (K : ℝ) ^ 2 := sq_pos_of_pos hK_real
  have ha_pos : 0 < a := by simp only [a]; positivity
  have ha_mem : a ∈ {b : ℝ | ∀ (x : Fin n → ℝ), x r = 0 →
      b * (∑ i, x i ^ 2) ≤
        ∑ i, (∑ j, G.laplacian (fun _ ↦ 1) i j * x j) * x i} := by
    intro x hx
    let xE : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 x
    let z : groundedSubspace r := ⟨xE, by simpa [xE] using hx⟩
    have hbound : ‖z‖ ≤ (K : ℝ) * ‖G.groundedWeightedDropLinearMap r z‖ :=
      ZeroHomClass.bound_of_antilipschitz (G.groundedWeightedDropLinearMap r) hanti z
    have hsq : ‖z‖ ^ 2 ≤ ((K : ℝ) * ‖G.groundedWeightedDropLinearMap r z‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg z)
        (mul_nonneg hK_real.le
          (norm_nonneg (G.groundedWeightedDropLinearMap r z)))).mpr hbound
    have hscaled : ((K : ℝ) ^ 2)⁻¹ * ‖z‖ ^ 2 ≤
        ‖G.groundedWeightedDropLinearMap r z‖ ^ 2 := by
      calc
        ((K : ℝ) ^ 2)⁻¹ * ‖z‖ ^ 2 = ‖z‖ ^ 2 / (K : ℝ) ^ 2 := by
          field_simp
        _ ≤ ‖G.groundedWeightedDropLinearMap r z‖ ^ 2 := by
          rw [div_le_iff₀ hK_sq]
          simpa [mul_pow, mul_comm] using hsq
    have hz_norm : ‖z‖ ^ 2 = ∑ i, x i ^ 2 := by
      change ‖xE‖ ^ 2 = ∑ i, x i ^ 2
      rw [EuclideanSpace.norm_sq_eq]
      simp [xE, Real.norm_eq_abs, sq_abs]
    have hdrop_norm : ‖G.groundedWeightedDropLinearMap r z‖ ^ 2 =
        ∑ e, G.weights e * (voltageDrop G x e) ^ 2 := by
      simpa [z, xE] using G.groundedWeightedDropLinearMap_norm_sq r z
    have henergy : a * (∑ i, x i ^ 2) ≤
        ∑ e, G.weights e * (voltageDrop G x e) ^ 2 := by
      rw [hz_norm, hdrop_norm] at hscaled
      exact hscaled
    calc
      a * (∑ i, x i ^ 2) ≤
          ∑ e, G.weights e * (voltageDrop G x e) ^ 2 := henergy
      _ = ∑ e, 1 * G.weights e * (voltageDrop G x e) ^ 2 := by simp
      _ = ∑ i, x i * ∑ j, G.laplacian (fun _ ↦ 1) i j * x j :=
        (laplacian_quadratic G (fun _ ↦ 1) x).symm
      _ = ∑ i, (∑ j, G.laplacian (fun _ ↦ 1) i j * x j) * x i := by
        apply Finset.sum_congr rfl
        intro i _
        ring
  have ha_le : a ≤ groundedLaplacianEigenvalueMin G r := by
    unfold groundedLaplacianEigenvalueMin
    exact le_csSup (groundedEigenvalueMin_set_bddAbove G r hn) ha_mem
  exact lt_of_lt_of_le ha_pos ha_le

/-- The upper Rayleigh set for the grounded Laplacian is nonempty. -/
theorem groundedEigenvalueMax_set_nonempty (G : WeightedGraph n m) (r : Fin n) :
    {a : ℝ | ∀ (x : Fin n → ℝ), x r = 0 →
      ∑ i, (∑ j, G.laplacian (fun _ ↦ 1) i j * x j) * x i ≤
        a * ∑ i, x i ^ 2}.Nonempty := by
  obtain ⟨a, ha⟩ := lambdaMax_set_nonempty G (fun _ ↦ 1)
  exact ⟨a, fun x _ ↦ ha x⟩

/-- Every retained diagonal entry bounds the largest grounded eigenvalue. -/
theorem grounded_diag_le_eigenvalueMax (G : WeightedGraph n m) (r : Fin n)
    (i : GroundedIndex r) :
    groundedLaplacian G r i i ≤ groundedLaplacianEigenvalueMax G r := by
  refine le_csInf (groundedEigenvalueMax_set_nonempty G r) (fun a ha ↦ ?_)
  let x : Fin n → ℝ := stdBasis i.1
  have hx_r : x r = 0 := by
    simp [x, stdBasis, Ne.symm i.2]
  have h := ha x hx_r
  have hquad : ∑ j, (∑ k, G.laplacian (fun _ ↦ 1) j k * x k) * x j =
      groundedLaplacian G r i i := by
    simp [x, stdBasis, groundedLaplacian, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ]
  have hsq : ∑ j, x j ^ 2 = 1 := by
    simp [x, stdBasis, sq, Finset.sum_ite_eq', Finset.mem_univ]
  rw [hquad, hsq, mul_one] at h
  exact h

private theorem card_groundedIndex (r : Fin n) :
    Fintype.card (GroundedIndex r) = n - 1 := by
  simp [GroundedIndex, Fintype.card_subtype_compl]

/-- The largest grounded eigenvalue is at least the average grounded diagonal. -/
theorem grounded_trace_average_le_eigenvalueMax (G : WeightedGraph n m) (r : Fin n)
    (hn : 1 < n) :
    (∑ i, groundedLaplacian G r i i) / ((n : ℝ) - 1) ≤
      groundedLaplacianEigenvalueMax G r := by
  let avg := (∑ i, groundedLaplacian G r i i) / ((n : ℝ) - 1)
  have hden : 0 < (n : ℝ) - 1 := by
    rw [← Nat.cast_one, ← Nat.cast_sub (by omega : 1 ≤ n)]
    exact_mod_cast Nat.sub_pos_of_lt hn
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  have hsum : ∑ _i : GroundedIndex r, avg ≤
      ∑ i, groundedLaplacian G r i i := by
    rw [Finset.sum_const, Finset.card_univ, card_groundedIndex r, nsmul_eq_mul, hcast]
    change ((n : ℝ) - 1) *
      ((∑ i, groundedLaplacian G r i i) / ((n : ℝ) - 1)) ≤ _
    rw [mul_div_cancel₀ _ hden.ne']
  letI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  obtain ⟨i, hi⟩ := exists_ne r
  let iGround : GroundedIndex r := ⟨i, hi⟩
  obtain ⟨j, _, hj⟩ := Finset.exists_le_of_sum_le
    ⟨iGround, Finset.mem_univ _⟩ hsum
  exact hj.trans (grounded_diag_le_eigenvalueMax G r j)

private theorem sum_shift_sq (x : Fin n → ℝ) (r : Fin n)
    (hx : ∑ i, x i = 0) :
    ∑ i, (x i - x r) ^ 2 = ∑ i, x i ^ 2 + (n : ℝ) * (x r) ^ 2 := by
  calc
    ∑ i, (x i - x r) ^ 2 =
        ∑ i, (x i ^ 2 - 2 * x i * x r + (x r) ^ 2) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = ∑ i, x i ^ 2 - 2 * x r * ∑ i, x i + ∑ _i : Fin n, (x r) ^ 2 := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      have hcross : ∑ i, 2 * x i * x r = 2 * x r * ∑ i, x i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [hcross]
    _ = ∑ i, x i ^ 2 + (n : ℝ) * (x r) ^ 2 := by
      rw [hx, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
      ring

private theorem unitLaplacianQuadratic_shift (G : WeightedGraph n m)
    (x : Fin n → ℝ) (c : ℝ) :
    ∑ i, (∑ j, G.laplacian (fun _ ↦ 1) i j * (x j - c)) * (x i - c) =
      ∑ i, (∑ j, G.laplacian (fun _ ↦ 1) i j * x j) * x i := by
  have hleft : ∑ i, (∑ j, G.laplacian (fun _ ↦ 1) i j * (x j - c)) *
      (x i - c) = ∑ i, (x i - c) *
        ∑ j, G.laplacian (fun _ ↦ 1) i j * (x j - c) := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hright : ∑ i, (∑ j, G.laplacian (fun _ ↦ 1) i j * x j) * x i =
      ∑ i, x i * ∑ j, G.laplacian (fun _ ↦ 1) i j * x j := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hleft, hright, laplacian_quadratic, laplacian_quadratic]
  apply Finset.sum_congr rfl
  intro e _
  rw [voltageDrop_eq_endpoint_diff, voltageDrop_eq_endpoint_diff]
  ring

/-- Poincare separation for grounding: the smallest eigenvalue after deleting one bus is no larger
than the full Laplacian's second eigenvalue. -/
theorem groundedEigenvalueMin_le_lambda2 (G : WeightedGraph n m) (r : Fin n)
    (hn : 1 < n) :
    groundedLaplacianEigenvalueMin G r ≤ laplacian_eigenvalue₂ G (fun _ ↦ 1) := by
  unfold groundedLaplacianEigenvalueMin
  refine csSup_le (groundedEigenvalueMin_set_nonempty G r) ?_
  intro a ha
  by_cases ha_nonneg : 0 ≤ a
  · have ha_lambda : a ∈ {b : ℝ | ∀ (x : Fin n → ℝ), ∑ i, x i = 0 →
        b * (∑ i, x i ^ 2) ≤
          ∑ i, (∑ j, G.laplacian (fun _ ↦ 1) i j * x j) * x i} := by
      intro x hx
      let y : Fin n → ℝ := fun i ↦ x i - x r
      have hy_r : y r = 0 := by simp [y]
      have hy_bound := ha y hy_r
      have hnorm : ∑ i, x i ^ 2 ≤ ∑ i, y i ^ 2 := by
        rw [sum_shift_sq x r hx]
        exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg n) (sq_nonneg _))
      have hscaled : a * ∑ i, x i ^ 2 ≤ a * ∑ i, y i ^ 2 :=
        mul_le_mul_of_nonneg_left hnorm ha_nonneg
      calc
        a * ∑ i, x i ^ 2 ≤ a * ∑ i, y i ^ 2 := hscaled
        _ ≤ ∑ i, (∑ j, G.laplacian (fun _ ↦ 1) i j * y j) * y i := hy_bound
        _ = ∑ i, (∑ j, G.laplacian (fun _ ↦ 1) i j * x j) * x i :=
          unitLaplacianQuadratic_shift G x (x r)
    unfold laplacian_eigenvalue₂
    exact le_csSup (lambda2_set_bddAbove G hn) ha_lambda
  · exact le_trans (le_of_not_ge ha_nonneg) (lambda2_nonneg G hn)

/-- Grounding removes exactly the slack bus weighted degree from the trace. -/
theorem groundedLaplacian_trace_eq (G : WeightedGraph n m) (r : Fin n) :
    ∑ i, groundedLaplacian G r i i = 2 * G.totalWeight - G.weightedDegree r := by
  have hsplit := Fintype.sum_eq_add_sum_subtype_ne
    (fun i ↦ G.laplacian (fun _ ↦ 1) i i) r
  have htrace := laplacian_diag_sum G
  have hdiag := weightedDegree_eq_diag G r
  change (∑ i : GroundedIndex r, G.laplacian (fun _ ↦ 1) i i) = _
  linarith

/-- A uniform branch bound controls the slack bus trace correction. -/
theorem weightedDegree_le_card_mul_bmax (G : WeightedGraph n m) (r : Fin n)
    (bmax : ℝ) (hbmax : ∀ e, G.weights e ≤ bmax) :
    G.weightedDegree r ≤ ((G.incidentEdges r).card : ℝ) * bmax := by
  unfold WeightedGraph.weightedDegree
  calc
    ∑ e ∈ G.incidentEdges r, G.weights e ≤
        ∑ _e ∈ G.incidentEdges r, bmax :=
      Finset.sum_le_sum fun e _ ↦ hbmax e
    _ = ((G.incidentEdges r).card : ℝ) * bmax := by
      rw [Finset.sum_const, nsmul_eq_mul]

/-- The grounded trace is at least `2 b(E) - Delta b_max`. -/
theorem groundedLaplacian_trace_correction (G : WeightedGraph n m) (r : Fin n)
    (Δ bmax : ℝ) (hdegree : ((G.incidentEdges r).card : ℝ) ≤ Δ)
    (hbmax_nonneg : 0 ≤ bmax) (hbmax : ∀ e, G.weights e ≤ bmax) :
    2 * G.totalWeight - Δ * bmax ≤ ∑ i, groundedLaplacian G r i i := by
  rw [groundedLaplacian_trace_eq]
  have hcard := weightedDegree_le_card_mul_bmax G r bmax hbmax
  have hmul : ((G.incidentEdges r).card : ℝ) * bmax ≤ Δ * bmax :=
    mul_le_mul_of_nonneg_right hdegree hbmax_nonneg
  linarith

/-- Exact grounded trace lower bound for the largest grounded eigenvalue. -/
theorem grounded_trace_div_le_eigenvalueMax (G : WeightedGraph n m) (r : Fin n)
    (hn : 1 < n) :
    (2 * G.totalWeight - G.weightedDegree r) / ((n : ℝ) - 1) ≤
      groundedLaplacianEigenvalueMax G r := by
  rw [← groundedLaplacian_trace_eq G r]
  exact grounded_trace_average_le_eigenvalueMax G r hn

/-- The letter's uniform trace correction lower bound for the grounded maximum eigenvalue. -/
theorem grounded_corrected_trace_div_le_eigenvalueMax (G : WeightedGraph n m)
    (r : Fin n) (Δ bmax : ℝ) (hn : 1 < n)
    (hdegree : ((G.incidentEdges r).card : ℝ) ≤ Δ)
    (hbmax_nonneg : 0 ≤ bmax) (hbmax : ∀ e, G.weights e ≤ bmax) :
    (2 * G.totalWeight - Δ * bmax) / ((n : ℝ) - 1) ≤
      groundedLaplacianEigenvalueMax G r := by
  have hden_pos : 0 < (n : ℝ) - 1 := by
    rw [← Nat.cast_one, ← Nat.cast_sub (by omega : 1 ≤ n)]
    exact_mod_cast Nat.sub_pos_of_lt hn
  have htrace := groundedLaplacian_trace_correction
    G r Δ bmax hdegree hbmax_nonneg hbmax
  exact (div_le_div_of_nonneg_right htrace hden_pos.le).trans
    (grounded_trace_average_le_eigenvalueMax G r hn)

/-- Every corrected trace condition bound transfers to the grounded matrix. -/
theorem corrected_trace_over_lambda2_le_groundedConditionNumber
    (G : WeightedGraph n m) (r : Fin n) (Δ bmax : ℝ)
    (hconn : G.CombinatoriallyConnected) (hn : 1 < n)
    (hdegree : ((G.incidentEdges r).card : ℝ) ≤ Δ)
    (hbmax_nonneg : 0 ≤ bmax) (hbmax : ∀ e, G.weights e ≤ bmax)
    (hcorrected : 0 ≤ 2 * G.totalWeight - Δ * bmax) :
    ((2 * G.totalWeight - Δ * bmax) / ((n : ℝ) - 1)) /
        laplacian_eigenvalue₂ G (fun _ ↦ 1) ≤ groundedConditionNumber G r := by
  have hden : 0 < (n : ℝ) - 1 := by
    rw [← Nat.cast_one, ← Nat.cast_sub (by omega : 1 ≤ n)]
    exact_mod_cast Nat.sub_pos_of_lt hn
  have hnum_nonneg :
      0 ≤ (2 * G.totalWeight - Δ * bmax) / ((n : ℝ) - 1) :=
    div_nonneg hcorrected hden.le
  have hmin_pos := groundedEigenvalueMin_pos G r hconn hn
  have hlambda_pos := combinatoriallyConnected_implies_spectralConnected G hconn hn
  have hinterlace := groundedEigenvalueMin_le_lambda2 G r hn
  have hmax := grounded_corrected_trace_div_le_eigenvalueMax
    G r Δ bmax hn hdegree hbmax_nonneg hbmax
  unfold WeightedGraph.Connected at hlambda_pos
  unfold groundedConditionNumber
  exact (div_le_div_of_nonneg_left hnum_nonneg hmin_pos hinterlace).trans
    (div_le_div_of_nonneg_right hmax hmin_pos.le)

end
