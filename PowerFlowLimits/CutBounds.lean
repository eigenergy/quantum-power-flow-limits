/-
Copyright (c) 2026 Cameron Khanpour and Samuel Talkington. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Cameron Khanpour, Samuel Talkington
-/
import PowerFlowLimits.Eigenvalues

/-!
# Lemma 1 (lem:cut): weighted cuts control conditioning, with the kappa_+ consequences

Part of the Lean 4 formalization of
"The Limits of Quantum Computers for Power Flow" (Khanpour and Talkington).
-/

open Finset BigOperators

noncomputable section

variable {n m : ℕ}

/-- Lemma 1(ii), product form: λ₂(B) · |S|(n-|S|) ≤ n · b(∂S).
    Test vector: x = 1_S - (|S|/n)·1 ⊥ 1, with xᵀBx = b(∂S) and
    ‖x‖² = |S|(n-|S|)/n. -/
theorem lambda2_mul_le_cut (G : WeightedGraph n m) (S : Finset (Fin n))
    (hne : S.Nonempty) (hproper : S ≠ Finset.univ) :
    laplacian_eigenvalue₂ G (fun _ => 1) * ((S.card : ℝ) * ((n : ℝ) - S.card)) ≤
      (n : ℝ) * G.cutWeight S := by
  have hn : 0 < n := hne.choose.pos
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hcard_lt : S.card < n := by
    have h := Finset.card_lt_card (Finset.ssubset_univ_iff.mpr hproper)
    simpa using h
  have hA_pos : (0 : ℝ) < (S.card : ℝ) * ((n : ℝ) - S.card) := by
    have h1 : (0 : ℝ) < S.card := Nat.cast_pos.mpr (Finset.card_pos.mpr hne)
    have h2 : (S.card : ℝ) < n := Nat.cast_lt.mpr hcard_lt
    exact mul_pos h1 (by linarith)
  set x : Fin n → ℝ := proj (fun i => if i ∈ S then 1 else 0) with hx_def
  have h_ind_sum : ∑ i, (if i ∈ S then (1 : ℝ) else 0) = S.card := by
    simp [Finset.sum_ite_mem]
  have hx_sum : ∑ i, x i = 0 := proj_sum_zero _ hn
  have hx_i : ∀ i, x i = (if i ∈ S then (1 : ℝ) else 0) - (S.card : ℝ) / n := by
    intro i; rw [hx_def]; simp [proj, h_ind_sum]
  have hx_sq : ∑ i, x i ^ 2 = (S.card : ℝ) * ((n : ℝ) - S.card) / n := by
    have hexp : ∀ i, x i ^ 2 =
        (if i ∈ S then (1 : ℝ) else 0) * (1 - 2 * ((S.card : ℝ) / n)) +
          ((S.card : ℝ) / n) ^ 2 := by
      intro i; rw [hx_i i]; by_cases hi : i ∈ S
      · simp only [if_pos hi]; ring
      · simp only [if_neg hi]; ring
    simp_rw [hexp]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, h_ind_sum, Finset.sum_const,
      Finset.card_fin, nsmul_eq_mul]
    field_simp
    ring
  have h_comm : ∑ i, (∑ j, G.laplacian (fun _ => 1) i j * x j) * x i =
      ∑ i, x i * ∑ j, G.laplacian (fun _ => 1) i j * x j := by
    apply Finset.sum_congr rfl; intro i _; ring
  have hq : ∑ i, (∑ j, G.laplacian (fun _ => 1) i j * x j) * x i =
      G.cutWeight S := by
    rw [h_comm, laplacian_quadratic]
    unfold WeightedGraph.cutWeight
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [voltageDrop_eq_endpoint_diff, hx_i (G.posEndpoint e),
      hx_i (G.negEndpoint e)]
    ring
  have h_sup_le : laplacian_eigenvalue₂ G (fun _ => 1) ≤
      (n : ℝ) * G.cutWeight S / ((S.card : ℝ) * ((n : ℝ) - S.card)) := by
    have h_eq : laplacian_eigenvalue₂ G (fun _ => 1) =
        sSup {r : ℝ | ∀ (y : Fin n → ℝ), ∑ i, y i = 0 →
          r * (∑ i, y i ^ 2) ≤
            ∑ i, (∑ j, G.laplacian (fun _ => 1) i j * y j) * y i} := by
      unfold laplacian_eigenvalue₂; rfl
    rw [h_eq]
    refine csSup_le (lambda2_set_nonempty G) (fun r hr => ?_)
    have h := hr x hx_sum
    rw [hx_sq, hq] at h
    rw [le_div_iff₀ hA_pos]
    calc r * ((S.card : ℝ) * ((n : ℝ) - S.card))
        = r * ((S.card : ℝ) * ((n : ℝ) - S.card) / n) * n := by field_simp
      _ ≤ G.cutWeight S * n := mul_le_mul_of_nonneg_right h hn_pos.le
      _ = (n : ℝ) * G.cutWeight S := by ring
  calc laplacian_eigenvalue₂ G (fun _ => 1) * ((S.card : ℝ) * ((n : ℝ) - S.card))
      ≤ ((n : ℝ) * G.cutWeight S / ((S.card : ℝ) * ((n : ℝ) - S.card))) *
        ((S.card : ℝ) * ((n : ℝ) - S.card)) :=
        mul_le_mul_of_nonneg_right h_sup_le hA_pos.le
    _ = (n : ℝ) * G.cutWeight S := div_mul_cancel₀ _ hA_pos.ne'

/-- Lemma 1(ii), paper form: λ₂(B) ≤ b(∂S)/(γ(1-γ)n) with γ = |S|/n. -/
theorem lambda2_le_cut_div (G : WeightedGraph n m) (S : Finset (Fin n))
    (hne : S.Nonempty) (hproper : S ≠ Finset.univ) :
    laplacian_eigenvalue₂ G (fun _ => 1) ≤
      G.cutWeight S /
        (((S.card : ℝ) / n) * (1 - (S.card : ℝ) / n) * n) := by
  have hn : 0 < n := hne.choose.pos
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hcard_lt : S.card < n := by
    have h := Finset.card_lt_card (Finset.ssubset_univ_iff.mpr hproper)
    simpa using h
  have hc_pos : (0 : ℝ) < S.card := Nat.cast_pos.mpr (Finset.card_pos.mpr hne)
  have hc_lt : (S.card : ℝ) < n := Nat.cast_lt.mpr hcard_lt
  have hA_pos : (0 : ℝ) < (S.card : ℝ) * ((n : ℝ) - S.card) :=
    mul_pos hc_pos (by linarith)
  have h := lambda2_mul_le_cut G S hne hproper
  have hden : ((S.card : ℝ) / n) * (1 - (S.card : ℝ) / n) * n =
      (S.card : ℝ) * ((n : ℝ) - S.card) / n := by
    field_simp
  rw [hden, le_div_iff₀ (by positivity)]
  calc laplacian_eigenvalue₂ G (fun _ => 1) *
        ((S.card : ℝ) * ((n : ℝ) - S.card) / n)
      = laplacian_eigenvalue₂ G (fun _ => 1) *
        ((S.card : ℝ) * ((n : ℝ) - S.card)) / n := by ring
    _ ≤ (n : ℝ) * G.cutWeight S / n := by gcongr
    _ = G.cutWeight S := by field_simp

/-- Lemma 1 consequence, eq. (2), total weight part:
    κ₊(B) ≥ 2γ(1-γ)·b(E)/b(∂S), using n/(n-1) ≥ 1. -/
theorem kappaPlus_ge_totalWeight (G : WeightedGraph n m) (S : Finset (Fin n))
    (hne : S.Nonempty) (hproper : S ≠ Finset.univ)
    (hconn : G.CombinatoriallyConnected) :
    2 * ((S.card : ℝ) / n) * (1 - (S.card : ℝ) / n) * G.totalWeight /
        G.cutWeight S ≤
      effectiveConditionNumber G (fun _ => 1) := by
  have hn : 0 < n := hne.choose.pos
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hcard_lt : S.card < n := by
    have h := Finset.card_lt_card (Finset.ssubset_univ_iff.mpr hproper)
    simpa using h
  have hn2 : 1 < n := lt_of_le_of_lt (Finset.one_le_card.mpr hne) hcard_lt
  have hspec := combinatoriallyConnected_implies_spectralConnected G hconn hn2
  have hc_pos : (0 : ℝ) < S.card := Nat.cast_pos.mpr (Finset.card_pos.mpr hne)
  have hc_lt : (S.card : ℝ) < n := Nat.cast_lt.mpr hcard_lt
  have hA_pos : (0 : ℝ) < (S.card : ℝ) * ((n : ℝ) - S.card) :=
    mul_pos hc_pos (by linarith)
  unfold WeightedGraph.Connected at hspec
  have hT3 := lambda2_mul_le_cut G S hne hproper
  have hcw_pos : 0 < G.cutWeight S := by
    have hpos := mul_pos hspec hA_pos
    nlinarith
  have hW_nn : 0 ≤ G.totalWeight :=
    Finset.sum_nonneg fun e _ => (G.weights_pos e).le
  have hlmax := two_totalWeight_div_card_le_lambdaMax G hn
  unfold effectiveConditionNumber
  rw [div_le_div_iff₀ hcw_pos hspec]
  calc 2 * ((S.card : ℝ) / n) * (1 - (S.card : ℝ) / n) * G.totalWeight *
        laplacian_eigenvalue₂ G (fun _ => 1)
      = (2 * G.totalWeight / (n : ℝ) ^ 2) *
        (laplacian_eigenvalue₂ G (fun _ => 1) *
          ((S.card : ℝ) * ((n : ℝ) - S.card))) := by
        field_simp
    _ ≤ (2 * G.totalWeight / (n : ℝ) ^ 2) * ((n : ℝ) * G.cutWeight S) :=
        mul_le_mul_of_nonneg_left hT3
          (div_nonneg (by linarith) (sq_nonneg _))
    _ = (2 * G.totalWeight / (n : ℝ)) * G.cutWeight S := by
        field_simp
    _ ≤ laplacianEigenvalueMax G (fun _ => 1) * G.cutWeight S :=
        mul_le_mul_of_nonneg_right hlmax hcw_pos.le

/-- Lemma 1 consequence, eq. (2), per-edge part:
    κ₊(B) ≥ 2γ(1-γ)·n·b_e/b(∂S) for every branch e; maximizing over e gives
    the paper's n·max_e b_e term. -/
theorem kappaPlus_ge_edge (G : WeightedGraph n m) (S : Finset (Fin n))
    (hne : S.Nonempty) (hproper : S ≠ Finset.univ)
    (hconn : G.CombinatoriallyConnected) (e : Fin m) :
    2 * ((S.card : ℝ) / n) * (1 - (S.card : ℝ) / n) * ((n : ℝ) * G.weights e) /
        G.cutWeight S ≤
      effectiveConditionNumber G (fun _ => 1) := by
  have hn : 0 < n := hne.choose.pos
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hcard_lt : S.card < n := by
    have h := Finset.card_lt_card (Finset.ssubset_univ_iff.mpr hproper)
    simpa using h
  have hn2 : 1 < n := lt_of_le_of_lt (Finset.one_le_card.mpr hne) hcard_lt
  have hspec := combinatoriallyConnected_implies_spectralConnected G hconn hn2
  have hc_pos : (0 : ℝ) < S.card := Nat.cast_pos.mpr (Finset.card_pos.mpr hne)
  have hc_lt : (S.card : ℝ) < n := Nat.cast_lt.mpr hcard_lt
  have hA_pos : (0 : ℝ) < (S.card : ℝ) * ((n : ℝ) - S.card) :=
    mul_pos hc_pos (by linarith)
  unfold WeightedGraph.Connected at hspec
  have hT3 := lambda2_mul_le_cut G S hne hproper
  have hcw_pos : 0 < G.cutWeight S := by
    have hpos := mul_pos hspec hA_pos
    nlinarith
  have hw_pos := G.weights_pos e
  have hlmax := two_mul_weight_le_lambdaMax G e
  unfold effectiveConditionNumber
  rw [div_le_div_iff₀ hcw_pos hspec]
  calc 2 * ((S.card : ℝ) / n) * (1 - (S.card : ℝ) / n) *
        ((n : ℝ) * G.weights e) * laplacian_eigenvalue₂ G (fun _ => 1)
      = (2 * G.weights e / (n : ℝ)) *
        (laplacian_eigenvalue₂ G (fun _ => 1) *
          ((S.card : ℝ) * ((n : ℝ) - S.card))) := by
        field_simp
    _ ≤ (2 * G.weights e / (n : ℝ)) * ((n : ℝ) * G.cutWeight S) :=
        mul_le_mul_of_nonneg_left hT3
          (div_nonneg (by linarith) hn_pos.le)
    _ = (2 * G.weights e) * G.cutWeight S := by
        field_simp
    _ ≤ laplacianEigenvalueMax G (fun _ => 1) * G.cutWeight S :=
        mul_le_mul_of_nonneg_right hlmax hcw_pos.le

/-- Lemma 1, equation (2), maximum-edge form. -/
theorem exists_maxWeight_kappa_bound (G : WeightedGraph n m) (S : Finset (Fin n))
    (hne : S.Nonempty) (hproper : S ≠ Finset.univ)
    (hconn : G.CombinatoriallyConnected) (hm : 0 < m) :
    ∃ e : Fin m, (∀ f, G.weights f ≤ G.weights e) ∧
      2 * ((S.card : ℝ) / n) * (1 - (S.card : ℝ) / n) *
          ((n : ℝ) * G.weights e) / G.cutWeight S ≤
        effectiveConditionNumber G (fun _ ↦ 1) := by
  obtain ⟨e, he, _⟩ := exists_maxWeight_lambdaMax_bound G hm
  exact ⟨e, he, kappaPlus_ge_edge G S hne hproper hconn e⟩

/-- Hub bound, beyond the paper's eq. (2): κ₊(B) ≥ γ(1-γ)·n·d_i/b(∂S) for
    every node i, since λ_max(B) ≥ d_i (diagonal Rayleigh quotient). For a
    node of weighted degree d_i > 2·max_e b_e — any hub with three or more
    comparably stiff branches — this beats the paper's per-edge term. -/
theorem kappaPlus_ge_weightedDegree (G : WeightedGraph n m)
    (S : Finset (Fin n)) (hne : S.Nonempty) (hproper : S ≠ Finset.univ)
    (hconn : G.CombinatoriallyConnected) (i : Fin n) :
    ((S.card : ℝ) / n) * (1 - (S.card : ℝ) / n) *
        ((n : ℝ) * G.weightedDegree i) / G.cutWeight S ≤
      effectiveConditionNumber G (fun _ => 1) := by
  have hn : 0 < n := hne.choose.pos
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hcard_lt : S.card < n := by
    have h := Finset.card_lt_card (Finset.ssubset_univ_iff.mpr hproper)
    simpa using h
  have hn2 : 1 < n := lt_of_le_of_lt (Finset.one_le_card.mpr hne) hcard_lt
  have hspec := combinatoriallyConnected_implies_spectralConnected G hconn hn2
  have hc_pos : (0 : ℝ) < S.card := Nat.cast_pos.mpr (Finset.card_pos.mpr hne)
  have hc_lt : (S.card : ℝ) < n := Nat.cast_lt.mpr hcard_lt
  have hA_pos : (0 : ℝ) < (S.card : ℝ) * ((n : ℝ) - S.card) :=
    mul_pos hc_pos (by linarith)
  unfold WeightedGraph.Connected at hspec
  have hT3 := lambda2_mul_le_cut G S hne hproper
  have hcw_pos : 0 < G.cutWeight S := by
    have hpos := mul_pos hspec hA_pos
    nlinarith
  have hd_nn : 0 ≤ G.weightedDegree i :=
    Finset.sum_nonneg fun e _ => (G.weights_pos e).le
  have hlmax : G.weightedDegree i ≤ laplacianEigenvalueMax G (fun _ => 1) := by
    rw [weightedDegree_eq_diag]
    exact diag_le_lambdaMax G _ i
  unfold effectiveConditionNumber
  rw [div_le_div_iff₀ hcw_pos hspec]
  calc ((S.card : ℝ) / n) * (1 - (S.card : ℝ) / n) *
        ((n : ℝ) * G.weightedDegree i) * laplacian_eigenvalue₂ G (fun _ => 1)
      = (G.weightedDegree i / n) *
        (laplacian_eigenvalue₂ G (fun _ => 1) *
          ((S.card : ℝ) * ((n : ℝ) - S.card))) := by
        field_simp
    _ ≤ (G.weightedDegree i / n) * ((n : ℝ) * G.cutWeight S) :=
        mul_le_mul_of_nonneg_left hT3 (div_nonneg hd_nn hn_pos.le)
    _ = G.weightedDegree i * G.cutWeight S := by
        field_simp
    _ ≤ laplacianEigenvalueMax G (fun _ => 1) * G.cutWeight S :=
        mul_le_mul_of_nonneg_right hlmax hcw_pos.le

end
