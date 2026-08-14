/-
Copyright (c) 2026 Cameron Khanpour and Samuel Talkington. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Cameron Khanpour, Samuel Talkington
-/
import PowerFlowLimits.Connectivity
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Variational eigenvalues

This file defines lambda_2, lambda_max, and the effective condition number. It also proves the
trace bound through the spectral theorem.

Part of the Lean 4 formalization of
"Proving the Limits of Quantum Power Flow" (Khanpour and Talkington).
-/

open Finset BigOperators
open scoped Matrix

noncomputable section

variable {n m : ℕ}

/-- Second-smallest eigenvalue of the switched Laplacian λ₂(L_s),
    defined via the Rayleigh quotient: supremum of all r such that
    r·‖x‖² ≤ xᵀLx for every x ⊥ 1. -/
@[irreducible] def laplacian_eigenvalue₂ (G : WeightedGraph n m) (s : Fin m → ℝ) : ℝ :=
  sSup {r : ℝ | ∀ (x : Fin n → ℝ), ∑ i, x i = 0 →
    r * (∑ i, x i ^ 2) ≤ ∑ i, (∑ j, G.laplacian s i j * x j) * x i}

/-- Spectral connectivity predicate: the switched graph is connected iff λ₂(L_s) > 0. -/
def WeightedGraph.Connected (G : WeightedGraph n m) (s : Fin m → ℝ) : Prop :=
  0 < laplacian_eigenvalue₂ G s

/-- The λ₂ Rayleigh set at unit switching is nonempty: 0 belongs to it, since
    the Laplacian quadratic form is positive semidefinite. -/
theorem lambda2_set_nonempty (G : WeightedGraph n m) :
    {r : ℝ | ∀ (x : Fin n → ℝ), ∑ i, x i = 0 →
      r * (∑ i, x i ^ 2) ≤
        ∑ i, (∑ j, G.laplacian (fun _ => 1) i j * x j) * x i}.Nonempty := by
  refine ⟨0, fun x _ => ?_⟩
  rw [zero_mul]
  have h_comm : ∑ i, (∑ j, G.laplacian (fun _ => 1) i j * x j) * x i =
      ∑ i, x i * ∑ j, G.laplacian (fun _ => 1) i j * x j := by
    apply Finset.sum_congr rfl; intro i _; ring
  rw [h_comm, laplacian_quadratic]
  exact Finset.sum_nonneg fun e _ =>
    mul_nonneg (mul_nonneg zero_le_one (G.weights_pos e).le) (sq_nonneg _)

/-- With at least two buses, the variational set defining `lambda₂` is bounded above. -/
theorem lambda2_set_bddAbove (G : WeightedGraph n m) (hn : 1 < n) :
    BddAbove {r : ℝ | ∀ (x : Fin n → ℝ), ∑ i, x i = 0 →
      r * (∑ i, x i ^ 2) ≤
        ∑ i, (∑ j, G.laplacian (fun _ ↦ 1) i j * x j) * x i} := by
  let i₀ : Fin n := ⟨0, by omega⟩
  let i₁ : Fin n := ⟨1, by omega⟩
  have hi : i₀ ≠ i₁ := by
    intro h
    have := congrArg Fin.val h
    simp only [i₀, i₁] at this
    omega
  let x : Fin n → ℝ := fun i ↦ stdBasis i₀ i - stdBasis i₁ i
  have hx_sum : ∑ i, x i = 0 := by
    simp [x, stdBasis, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ]
  have hx_pointwise : ∀ i, x i ^ 2 =
      (if i = i₀ then 1 else 0) + (if i = i₁ then 1 else 0) := by
    intro i
    by_cases h0 : i = i₀
    · subst i
      simp [x, stdBasis, hi]
    · by_cases h1 : i = i₁
      · subst i
        simp [x, stdBasis, h0]
      · simp [x, stdBasis, h0, h1]
  have hx_sq : ∑ i, x i ^ 2 = 2 := by
    simp_rw [hx_pointwise, Finset.sum_add_distrib]
    simp [Finset.sum_ite_eq', Finset.mem_univ]
    norm_num
  refine ⟨(∑ i, (∑ j, G.laplacian (fun _ ↦ 1) i j * x j) * x i) / 2, ?_⟩
  intro r hr
  have h := hr x hx_sum
  rw [hx_sq] at h
  linarith

/-- The variational second eigenvalue is nonnegative at unit switching. -/
theorem lambda2_nonneg (G : WeightedGraph n m) (hn : 1 < n) :
    0 ≤ laplacian_eigenvalue₂ G (fun _ ↦ 1) := by
  have hzero : 0 ∈ {r : ℝ | ∀ (x : Fin n → ℝ), ∑ i, x i = 0 →
      r * (∑ i, x i ^ 2) ≤
        ∑ i, (∑ j, G.laplacian (fun _ ↦ 1) i j * x j) * x i} := by
    intro x _
    rw [zero_mul]
    have hcomm : ∑ i, (∑ j, G.laplacian (fun _ ↦ 1) i j * x j) * x i =
        ∑ i, x i * ∑ j, G.laplacian (fun _ ↦ 1) i j * x j := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hcomm, laplacian_quadratic]
    exact Finset.sum_nonneg fun e _ ↦
      mul_nonneg (mul_nonneg zero_le_one (G.weights_pos e).le) (sq_nonneg _)
  unfold laplacian_eigenvalue₂
  exact le_csSup (lambda2_set_bddAbove G hn) hzero

/-- Ordinary graph connectivity with positive branch weights implies positive `lambda₂`. -/
theorem combinatoriallyConnected_implies_spectralConnected (G : WeightedGraph n m)
    (hconn : G.CombinatoriallyConnected) (hn : 1 < n) :
    G.Connected (fun _ ↦ 1) := by
  obtain ⟨K, hK_pos, hanti⟩ :=
    (LinearMap.injective_iff_antilipschitz G.weightedDropLinearMap).mp
      (G.weightedDropLinearMap_injective hconn (by omega))
  let r : ℝ := ((K : ℝ) ^ 2)⁻¹
  have hK_real : 0 < (K : ℝ) := by exact_mod_cast hK_pos
  have hK_sq : 0 < (K : ℝ) ^ 2 := sq_pos_of_pos hK_real
  have hr_pos : 0 < r := by simp only [r]; positivity
  have hr_mem : r ∈ {a : ℝ | ∀ (x : Fin n → ℝ), ∑ i, x i = 0 →
      a * (∑ i, x i ^ 2) ≤
        ∑ i, (∑ j, G.laplacian (fun _ ↦ 1) i j * x j) * x i} := by
    intro x hx
    let xE : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 x
    let z : zeroSumSubspace n := ⟨xE, by simpa [xE] using hx⟩
    have hbound : ‖z‖ ≤ (K : ℝ) * ‖G.weightedDropLinearMap z‖ :=
      ZeroHomClass.bound_of_antilipschitz G.weightedDropLinearMap hanti z
    have hsq : ‖z‖ ^ 2 ≤ ((K : ℝ) * ‖G.weightedDropLinearMap z‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg z)
        (mul_nonneg hK_real.le (norm_nonneg (G.weightedDropLinearMap z)))).mpr hbound
    have hscaled : ((K : ℝ) ^ 2)⁻¹ * ‖z‖ ^ 2 ≤
        ‖G.weightedDropLinearMap z‖ ^ 2 := by
      calc
        ((K : ℝ) ^ 2)⁻¹ * ‖z‖ ^ 2 = ‖z‖ ^ 2 / (K : ℝ) ^ 2 := by
          field_simp
        _ ≤ ‖G.weightedDropLinearMap z‖ ^ 2 := by
          rw [div_le_iff₀ hK_sq]
          simpa [mul_pow, mul_comm] using hsq
    have hz_norm : ‖z‖ ^ 2 = ∑ i, x i ^ 2 := by
      change ‖xE‖ ^ 2 = ∑ i, x i ^ 2
      rw [EuclideanSpace.norm_sq_eq]
      simp [xE, Real.norm_eq_abs, sq_abs]
    have hdrop_norm : ‖G.weightedDropLinearMap z‖ ^ 2 =
        ∑ e, G.weights e * (voltageDrop G x e) ^ 2 := by
      simpa [z, xE] using G.weightedDropLinearMap_norm_sq z
    have henergy : r * (∑ i, x i ^ 2) ≤
        ∑ e, G.weights e * (voltageDrop G x e) ^ 2 := by
      rw [hz_norm, hdrop_norm] at hscaled
      exact hscaled
    calc
      r * (∑ i, x i ^ 2) ≤
          ∑ e, G.weights e * (voltageDrop G x e) ^ 2 := henergy
      _ = ∑ e, 1 * G.weights e * (voltageDrop G x e) ^ 2 := by simp
      _ = ∑ i, x i * ∑ j, G.laplacian (fun _ ↦ 1) i j * x j :=
        (laplacian_quadratic G (fun _ ↦ 1) x).symm
      _ = ∑ i, (∑ j, G.laplacian (fun _ ↦ 1) i j * x j) * x i := by
        apply Finset.sum_congr rfl
        intro i _
        ring
  have hr_le : r ≤ sSup {a : ℝ | ∀ (x : Fin n → ℝ), ∑ i, x i = 0 →
      a * (∑ i, x i ^ 2) ≤
        ∑ i, (∑ j, G.laplacian (fun _ ↦ 1) i j * x j) * x i} :=
    le_csSup (lambda2_set_bddAbove G hn) hr_mem
  unfold WeightedGraph.Connected laplacian_eigenvalue₂
  exact lt_of_lt_of_le hr_pos hr_le

/-- A spectrally connected graph has at least two nodes. -/
theorem WeightedGraph.Connected.one_lt {G : WeightedGraph n m} {s : Fin m → ℝ}
    (hconn : G.Connected s) : 1 < n := by
  by_contra hle
  push_neg at hle
  have h_all_zero : ∀ (x : Fin n → ℝ), ∑ i, x i = 0 → ∀ i, x i = 0 := by
    intro x hx i
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with rfl | rfl
    · exact Fin.elim0 i
    · have hi : i = ⟨0, by omega⟩ := Fin.ext (by omega)
      rw [hi]; simpa [hi] using hx
  have h_eq : laplacian_eigenvalue₂ G s =
      sSup {r : ℝ | ∀ (x : Fin n → ℝ), ∑ i, x i = 0 →
        r * (∑ i, x i ^ 2) ≤ ∑ i, (∑ j, G.laplacian s i j * x j) * x i} := by
    unfold laplacian_eigenvalue₂; rfl
  have h_set_univ : {r : ℝ | ∀ (x : Fin n → ℝ), ∑ i, x i = 0 →
      r * (∑ i, x i ^ 2) ≤ ∑ i, (∑ j, G.laplacian s i j * x j) * x i} =
      Set.univ := by
    ext r
    simp only [Set.mem_univ, iff_true, Set.mem_setOf_eq]
    intro x hx
    have hz := h_all_zero x hx
    have h_sq : ∑ i, x i ^ 2 = 0 :=
      Finset.sum_eq_zero fun i _ => by rw [hz i]; ring
    have h_quad : ∑ i, (∑ j, G.laplacian s i j * x j) * x i = 0 :=
      Finset.sum_eq_zero fun i _ => by rw [hz i]; ring
    rw [h_sq, h_quad]
    simp
  have hpos : (0 : ℝ) < 0 := by
    have h := hconn
    unfold WeightedGraph.Connected at h
    rw [h_eq, h_set_univ, Real.sSup_univ] at h
    exact h
  exact lt_irrefl 0 hpos

/-- Largest eigenvalue λ_max(L_s), defined variationally as the least upper
    Rayleigh bound: the infimum of all r with xᵀLx ≤ r‖x‖² for every x.
    Dual to `laplacian_eigenvalue₂`'s sSup characterization. -/
def laplacianEigenvalueMax (G : WeightedGraph n m) (s : Fin m → ℝ) : ℝ :=
  sInf {r : ℝ | ∀ x : Fin n → ℝ,
    ∑ i, (∑ j, G.laplacian s i j * x j) * x i ≤ r * ∑ i, x i ^ 2}

/-- Effective condition number κ₊(L_s) = λ_max(L_s)/λ₂(L_s). -/
def effectiveConditionNumber (G : WeightedGraph n m) (s : Fin m → ℝ) : ℝ :=
  laplacianEigenvalueMax G s / laplacian_eigenvalue₂ G s

/-- The upper Rayleigh set is nonempty: 2·Σ_e |s_e| w_e is an upper bound,
    since (Δx_e)² ≤ 2‖x‖². -/
theorem lambdaMax_set_nonempty (G : WeightedGraph n m) (s : Fin m → ℝ) :
    {r : ℝ | ∀ x : Fin n → ℝ,
      ∑ i, (∑ j, G.laplacian s i j * x j) * x i ≤ r * ∑ i, x i ^ 2}.Nonempty := by
  refine ⟨2 * ∑ e, |s e| * G.weights e, fun x => ?_⟩
  have h_comm : ∑ i, (∑ j, G.laplacian s i j * x j) * x i =
      ∑ i, x i * ∑ j, G.laplacian s i j * x j := by
    apply Finset.sum_congr rfl; intro i _; ring
  rw [h_comm, laplacian_quadratic]
  have h_pair : ∀ e : Fin m,
      x (G.posEndpoint e) ^ 2 + x (G.negEndpoint e) ^ 2 ≤ ∑ i, x i ^ 2 := by
    intro e
    calc x (G.posEndpoint e) ^ 2 + x (G.negEndpoint e) ^ 2
        = ∑ i ∈ ({G.posEndpoint e, G.negEndpoint e} : Finset (Fin n)), x i ^ 2 := by
          rw [Finset.sum_pair (G.endpoints_ne e)]
      _ ≤ ∑ i, x i ^ 2 := Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.subset_univ _) (fun i _ _ => sq_nonneg _)
  have h_edge : ∀ e : Fin m, s e * G.weights e * (voltageDrop G x e) ^ 2 ≤
      |s e| * G.weights e * (2 * ∑ i, x i ^ 2) := by
    intro e
    have hw := (G.weights_pos e).le
    have hvd : (voltageDrop G x e) ^ 2 ≤ 2 * ∑ i, x i ^ 2 :=
      le_trans (voltageDrop_sq_le_endpoint_sq G x e) (by linarith [h_pair e])
    calc s e * G.weights e * (voltageDrop G x e) ^ 2
        ≤ |s e| * G.weights e * (voltageDrop G x e) ^ 2 :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_abs_self (s e)) hw) (sq_nonneg _)
      _ ≤ |s e| * G.weights e * (2 * ∑ i, x i ^ 2) :=
          mul_le_mul_of_nonneg_left hvd (mul_nonneg (abs_nonneg _) hw)
  calc ∑ e, s e * G.weights e * (voltageDrop G x e) ^ 2
      ≤ ∑ e, |s e| * G.weights e * (2 * ∑ i, x i ^ 2) :=
        Finset.sum_le_sum fun e _ => h_edge e
    _ = (∑ e, |s e| * G.weights e) * (2 * ∑ i, x i ^ 2) := by
        rw [← Finset.sum_mul]
    _ = 2 * (∑ e, |s e| * G.weights e) * ∑ i, x i ^ 2 := by ring

/-- Variational lower bound: every Rayleigh quotient bounds λ_max from below. -/
theorem rayleigh_div_le_lambdaMax (G : WeightedGraph n m) (s : Fin m → ℝ)
    (x : Fin n → ℝ) (hx : ∑ i, x i ^ 2 ≠ 0) :
    (∑ i, (∑ j, G.laplacian s i j * x j) * x i) / (∑ i, x i ^ 2) ≤
      laplacianEigenvalueMax G s := by
  have hx_pos : 0 < ∑ i, x i ^ 2 :=
    lt_of_le_of_ne (Finset.sum_nonneg fun i _ => sq_nonneg _) (Ne.symm hx)
  refine le_csInf (lambdaMax_set_nonempty G s) (fun r hr => ?_)
  exact (div_le_iff₀ hx_pos).mpr (hr x)

/-- Diagonal entries bound λ_max from below (test vector: standard basis). -/
theorem diag_le_lambdaMax (G : WeightedGraph n m) (s : Fin m → ℝ) (i₀ : Fin n) :
    G.laplacian s i₀ i₀ ≤ laplacianEigenvalueMax G s := by
  refine le_csInf (lambdaMax_set_nonempty G s) (fun r hr => ?_)
  have h := hr (stdBasis i₀)
  have hL : ∑ i, (∑ j, G.laplacian s i j * stdBasis i₀ j) * stdBasis i₀ i =
      G.laplacian s i₀ i₀ := by
    simp [stdBasis, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ]
  have hsq : ∑ i, stdBasis i₀ i ^ 2 = 1 := by
    simp [stdBasis, sq, Finset.sum_ite_eq', Finset.mem_univ]
  rw [hL, hsq, mul_one] at h
  exact h

/-- λ_max ≥ 0 for nonnegative switching (the Laplacian is PSD). -/
theorem lambdaMax_nonneg (G : WeightedGraph n m) (s : Fin m → ℝ)
    (hs : ∀ e, 0 ≤ s e) (hn : 0 < n) :
    0 ≤ laplacianEigenvalueMax G s := by
  refine le_trans ?_ (diag_le_lambdaMax G s ⟨0, hn⟩)
  unfold WeightedGraph.laplacian
  refine Finset.sum_nonneg fun e _ => ?_
  have hterm : G.incidence ⟨0, hn⟩ e * (G.weights e * s e) * G.incidence ⟨0, hn⟩ e =
      (G.weights e * s e) * G.incidence ⟨0, hn⟩ e ^ 2 := by ring
  rw [hterm]
  exact mul_nonneg (mul_nonneg (G.weights_pos e).le (hs e)) (sq_nonneg _)

/-- Averaged trace bound: λ_max(B) ≥ 2 b(E)/n. Elementary version of
    Lemma 1(i)'s trace bound (no kernel dimension count needed), and exactly
    what the κ₊ consequence uses after the paper's n/(n-1) ≥ 1 step. -/
theorem two_totalWeight_div_card_le_lambdaMax (G : WeightedGraph n m) (hn : 0 < n) :
    2 * G.totalWeight / (n : ℝ) ≤ laplacianEigenvalueMax G (fun _ => 1) := by
  have h_trace := laplacian_diag_sum G
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have h_sum_le : ∑ _i : Fin n, 2 * G.totalWeight / (n : ℝ) ≤
      ∑ i, G.laplacian (fun _ => 1) i i := by
    rw [h_trace, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    rw [mul_div_cancel₀ _ hn_pos.ne']
  obtain ⟨i, _, hi⟩ := Finset.exists_le_of_sum_le
    ⟨⟨0, hn⟩, Finset.mem_univ _⟩ h_sum_le
  exact le_trans hi (diag_le_lambdaMax G _ i)

/-- Lemma 1(i), edge form: λ_max(B) ≥ 2 b_e for every branch e.
    Test vector: eᵢ - eⱼ at the endpoints of e. -/
theorem two_mul_weight_le_lambdaMax (G : WeightedGraph n m) (e : Fin m) :
    2 * G.weights e ≤ laplacianEigenvalueMax G (fun _ => 1) := by
  set x : Fin n → ℝ := fun i =>
    if i = G.posEndpoint e then 1 else if i = G.negEndpoint e then -1 else 0
    with hx_def
  have hne := G.endpoints_ne e
  have hx_sq : ∑ i, x i ^ 2 = 2 := by
    have hpt : ∀ i, x i ^ 2 =
        (if i = G.posEndpoint e then (1 : ℝ) else 0) +
        (if i = G.negEndpoint e then (1 : ℝ) else 0) := by
      intro i
      by_cases h1 : i = G.posEndpoint e
      · subst h1; simp [hx_def, hne]
      · by_cases h2 : i = G.negEndpoint e
        · subst h2; simp [hx_def, h1]
        · simp [hx_def, h1, h2]
    simp_rw [hpt, Finset.sum_add_distrib]
    simp [Finset.sum_ite_eq', Finset.mem_univ]
    norm_num
  have h_comm : ∑ i, (∑ j, G.laplacian (fun _ => 1) i j * x j) * x i =
      ∑ i, x i * ∑ j, G.laplacian (fun _ => 1) i j * x j := by
    apply Finset.sum_congr rfl; intro i _; ring
  have h_vd : voltageDrop G x e = 2 := by
    rw [voltageDrop_eq_endpoint_diff]
    have h1 : x (G.posEndpoint e) = 1 := by simp [hx_def]
    have h2 : x (G.negEndpoint e) = -1 := by simp [hx_def, hne.symm]
    rw [h1, h2]; norm_num
  have h_lower : 4 * G.weights e ≤
      ∑ i, (∑ j, G.laplacian (fun _ => 1) i j * x j) * x i := by
    rw [h_comm, laplacian_quadratic]
    have h_single : (1 : ℝ) * G.weights e * (voltageDrop G x e) ^ 2 ≤
        ∑ f, (1 : ℝ) * G.weights f * (voltageDrop G x f) ^ 2 :=
      Finset.single_le_sum
        (fun f _ => mul_nonneg (mul_nonneg zero_le_one (G.weights_pos f).le)
          (sq_nonneg _))
        (Finset.mem_univ e)
    rw [h_vd] at h_single
    linarith
  have h2 := rayleigh_div_le_lambdaMax G (fun _ => 1) x
    (by rw [hx_sq]; norm_num)
  rw [hx_sq] at h2
  linarith

/-- Lemma 1(i), maximum-edge form. A nonempty finite edge set has a branch attaining the maximum
weight, and twice that weight bounds `lambda_max` from below. -/
theorem exists_maxWeight_lambdaMax_bound (G : WeightedGraph n m) (hm : 0 < m) :
    ∃ e : Fin m, (∀ f, G.weights f ≤ G.weights e) ∧
      2 * G.weights e ≤ laplacianEigenvalueMax G (fun _ ↦ 1) := by
  have huniv : (Finset.univ : Finset (Fin m)).Nonempty :=
    ⟨⟨0, hm⟩, Finset.mem_univ _⟩
  obtain ⟨e, _, he⟩ := Finset.exists_max_image Finset.univ G.weights huniv
  exact ⟨e, fun f ↦ he f (Finset.mem_univ f), two_mul_weight_le_lambdaMax G e⟩

/-- Lemma 1(i), trace form: λ_max(B) ≥ 2 b(E)/(n-1).
    tr(B) = 2b(E) spreads over at most n-1 nonzero eigenvalues, since the
    all-ones vector is in the kernel. -/
theorem two_totalWeight_div_le_lambdaMax (G : WeightedGraph n m) (hn : 1 < n) :
    2 * G.totalWeight / ((n : ℝ) - 1) ≤ laplacianEigenvalueMax G (fun _ => 1) := by
  classical
  set B : Matrix (Fin n) (Fin n) ℝ := Matrix.of (G.laplacian (fun _ => 1)) with hB_def
  have hB_herm : B.IsHermitian :=
    Matrix.ext fun i j => by
      simp only [Matrix.conjTranspose_apply, star_trivial, hB_def, Matrix.of_apply]
      exact G.laplacian_symmetric (fun _ => 1) j i
  -- every eigenvalue is at most λ_max
  have h_eig_le : ∀ i₁ : Fin n,
      hB_herm.eigenvalues i₁ ≤ laplacianEigenvalueMax G (fun _ => 1) := by
    intro i₁
    refine le_csInf (lambdaMax_set_nonempty G _) (fun r hr => ?_)
    set v : Fin n → ℝ := ⇑(hB_herm.eigenvectorBasis i₁) with hv_def
    have hmv : B *ᵥ v = hB_herm.eigenvalues i₁ • v :=
      hB_herm.mulVec_eigenvectorBasis i₁
    have hv_sq : ∑ j, v j ^ 2 = 1 := by
      have h1 := hB_herm.eigenvectorBasis.orthonormal.1 i₁
      rw [EuclideanSpace.norm_eq] at h1
      have h2 : ∑ j, ‖v j‖ ^ 2 = 1 := Real.sqrt_eq_one.mp h1
      simpa [Real.norm_eq_abs, sq_abs] using h2
    have hquad : ∑ k, (∑ j, G.laplacian (fun _ => 1) k j * v j) * v k =
        hB_herm.eigenvalues i₁ := by
      have hcol : ∀ k, ∑ j, G.laplacian (fun _ => 1) k j * v j = (B *ᵥ v) k := by
        intro k
        simp [Matrix.mulVec, dotProduct, hB_def]
      calc ∑ k, (∑ j, G.laplacian (fun _ => 1) k j * v j) * v k
          = ∑ k, (B *ᵥ v) k * v k :=
            Finset.sum_congr rfl fun k _ => by rw [hcol k]
        _ = ∑ k, (hB_herm.eigenvalues i₁ • v) k * v k := by rw [hmv]
        _ = hB_herm.eigenvalues i₁ * ∑ k, v k ^ 2 := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun k _ => by
              simp only [Pi.smul_apply, smul_eq_mul]; ring
        _ = hB_herm.eigenvalues i₁ := by rw [hv_sq, mul_one]
    have h := hr v
    rw [hquad, hv_sq, mul_one] at h
    exact h
  -- some eigenvalue vanishes: the all-ones vector is in the kernel
  have h_ones_ne : (fun _ : Fin n => (1 : ℝ)) ≠ 0 := by
    intro h
    have := congrFun h ⟨0, by omega⟩
    simp at this
  have h_mv_ones : B *ᵥ (fun _ => (1 : ℝ)) = 0 := by
    funext i
    simp only [Matrix.mulVec, dotProduct, mul_one, hB_def, Matrix.of_apply,
      Pi.zero_apply]
    exact G.laplacian_kernel (fun _ => 1) i
  have h_det : B.det = 0 :=
    Matrix.exists_mulVec_eq_zero_iff.mp ⟨_, h_ones_ne, h_mv_ones⟩
  have h_prod : ∏ i₁, hB_herm.eigenvalues i₁ = 0 := by
    have h := hB_herm.det_eq_prod_eigenvalues
    rw [h_det] at h
    simpa using h.symm
  obtain ⟨i₀, _, h_i₀⟩ := Finset.prod_eq_zero_iff.mp h_prod
  -- trace = sum of eigenvalues = 2 b(E)
  have h_tr_eig : ∑ i₁, hB_herm.eigenvalues i₁ = 2 * G.totalWeight := by
    have h := hB_herm.trace_eq_sum_eigenvalues
    have h_tr : B.trace = 2 * G.totalWeight := by
      have hdiag : B.trace = ∑ i, G.laplacian (fun _ => 1) i i := by
        simp [Matrix.trace, Matrix.diag, hB_def]
      rw [hdiag, laplacian_diag_sum]
    rw [h_tr] at h
    simpa using h.symm
  -- assemble: 2 b(E) spreads over the n-1 eigenvalues away from i₀
  have hn1_pos : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (1 : ℝ) < n := by exact_mod_cast hn
    linarith
  have h_bound : ∑ i₁ ∈ Finset.univ.erase i₀, hB_herm.eigenvalues i₁ ≤
      ((n : ℝ) - 1) * laplacianEigenvalueMax G (fun _ => 1) := by
    calc ∑ i₁ ∈ Finset.univ.erase i₀, hB_herm.eigenvalues i₁
        ≤ ∑ _i₁ ∈ Finset.univ.erase i₀, laplacianEigenvalueMax G (fun _ => 1) :=
          Finset.sum_le_sum fun i₁ _ => h_eig_le i₁
      _ = ((Finset.univ.erase i₀).card : ℝ) *
            laplacianEigenvalueMax G (fun _ => 1) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = ((n : ℝ) - 1) * laplacianEigenvalueMax G (fun _ => 1) := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
            Fintype.card_fin, Nat.cast_sub hn.le, Nat.cast_one]
  have h2W : 2 * G.totalWeight ≤
      ((n : ℝ) - 1) * laplacianEigenvalueMax G (fun _ => 1) := by
    calc 2 * G.totalWeight = ∑ i₁, hB_herm.eigenvalues i₁ := h_tr_eig.symm
      _ = hB_herm.eigenvalues i₀ +
            ∑ i₁ ∈ Finset.univ.erase i₀, hB_herm.eigenvalues i₁ :=
          (Finset.add_sum_erase _ _ (Finset.mem_univ i₀)).symm
      _ = ∑ i₁ ∈ Finset.univ.erase i₀, hB_herm.eigenvalues i₁ := by
          rw [h_i₀, zero_add]
      _ ≤ ((n : ℝ) - 1) * laplacianEigenvalueMax G (fun _ => 1) := h_bound
  rw [div_le_iff₀ hn1_pos]
  linarith

end
