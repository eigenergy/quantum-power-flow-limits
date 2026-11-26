/-
Copyright (c) 2026 Cameron Khanpour and Samuel Talkington. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Cameron Khanpour, Samuel Talkington
-/
import PowerFlowLimits.Grounded
import PowerFlowLimits.TreeDecomposition

/-!
# Every bound transfers to the grounded matrix with its constant halved

Solvers often invert the grounded matrix `B_r`, the susceptance Laplacian with the slack bus
deleted. The letter states that each lower bound on `κ₊(B)` holds for `κ₂(B_r)` with its constant
halved. The argument has three parts, all proved here or in `Grounded.lean`.

* Interlacing gives `λ_min(B_r) ≤ λ₂(B)`.
* `tr(B_r) ≥ b(E)` gives `λ_max(B_r) ≥ b(E) / (n - 1)`.
* A retained endpoint of a heaviest branch gives `λ_max(B_r) ≥ b_max`.

Together these are half of Lemma 1(i), so every bound obtained by dividing Lemma 1(i) by an upper
bound on `λ₂` transfers. The transfers for Lemma 1, Theorem 1, Corollary 1, and Proposition 1 are
stated explicitly.
-/

open Finset BigOperators

noncomputable section

variable {n m : ℕ}

/-- A weighted degree is at most the total branch weight. -/
theorem weightedDegree_le_totalWeight (G : WeightedGraph n m) (r : Fin n) :
    G.weightedDegree r ≤ G.totalWeight := by
  unfold WeightedGraph.weightedDegree WeightedGraph.totalWeight
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun e _ _ ↦ (G.weights_pos e).le)

/-- The grounded trace keeps at least the total branch weight: `tr(B_r) ≥ b(E)`. -/
theorem totalWeight_le_grounded_trace (G : WeightedGraph n m) (r : Fin n) :
    G.totalWeight ≤ ∑ i, groundedLaplacian G r i i := by
  rw [groundedLaplacian_trace_eq]
  linarith [weightedDegree_le_totalWeight G r]

/-- `λ_max(B_r) ≥ b(E) / (n - 1)`, half of the trace bound in Lemma 1(i). -/
theorem totalWeight_div_le_groundedEigenvalueMax (G : WeightedGraph n m) (r : Fin n)
    (hn : 1 < n) :
    G.totalWeight / ((n : ℝ) - 1) ≤ groundedLaplacianEigenvalueMax G r := by
  have hden : 0 < (n : ℝ) - 1 := by
    have hcast : (1 : ℝ) < n := by exact_mod_cast hn
    linarith
  exact (div_le_div_of_nonneg_right (totalWeight_le_grounded_trace G r) hden.le).trans
    (grounded_trace_average_le_eigenvalueMax G r hn)

/-- The weaker averaged form `λ_max(B_r) ≥ b(E) / n`. -/
theorem totalWeight_div_card_le_groundedEigenvalueMax (G : WeightedGraph n m) (r : Fin n)
    (hn : 1 < n) :
    G.totalWeight / (n : ℝ) ≤ groundedLaplacianEigenvalueMax G r := by
  have hcast : (1 : ℝ) < n := by exact_mod_cast hn
  have hden : 0 < (n : ℝ) - 1 := by linarith
  have htotal_nonneg : 0 ≤ G.totalWeight :=
    Finset.sum_nonneg fun e _ ↦ (G.weights_pos e).le
  exact (div_le_div_of_nonneg_left htotal_nonneg hden (by linarith)).trans
    (totalWeight_div_le_groundedEigenvalueMax G r hn)

/-- Half of Lemma 1(i) holds for the grounded matrix:
`λ_max(B_r) ≥ max {b(E) / (n - 1), b_e}` for every branch `e`. -/
theorem half_lemma1_le_groundedEigenvalueMax (G : WeightedGraph n m) (r : Fin n)
    (e : Fin m) (hn : 1 < n) :
    max (G.totalWeight / ((n : ℝ) - 1)) (G.weights e) ≤
      groundedLaplacianEigenvalueMax G r :=
  max_le (totalWeight_div_le_groundedEigenvalueMax G r hn)
    (edgeWeight_le_groundedEigenvalueMax G r e)

/-- The transfer principle. If `λ₂(B) c ≤ d` and `q ≤ λ_max(B_r)`, then `κ₂(B_r) ≥ c q / d`.
Every bound of the letter has this form with `q` taken from half of Lemma 1(i). -/
theorem groundedConditionNumber_ge_of_lambda2_mul_le (G : WeightedGraph n m) (r : Fin n)
    (hconn : G.CombinatoriallyConnected) (hn : 1 < n) (c d q : ℝ)
    (hc : 0 < c) (hq_nonneg : 0 ≤ q) (hq : q ≤ groundedLaplacianEigenvalueMax G r)
    (hbound : laplacian_eigenvalue₂ G (fun _ ↦ 1) * c ≤ d) :
    c * q / d ≤ groundedConditionNumber G r := by
  have hmin_pos := groundedEigenvalueMin_pos G r hconn hn
  have hinterlace := groundedEigenvalueMin_le_lambda2 G r hn
  have hmin_bound : groundedLaplacianEigenvalueMin G r * c ≤ d :=
    (mul_le_mul_of_nonneg_right hinterlace hc.le).trans hbound
  have hd_pos : 0 < d := lt_of_lt_of_le (mul_pos hmin_pos hc) hmin_bound
  unfold groundedConditionNumber
  rw [div_le_div_iff₀ hd_pos hmin_pos]
  calc
    c * q * groundedLaplacianEigenvalueMin G r =
        q * (groundedLaplacianEigenvalueMin G r * c) := by ring
    _ ≤ q * d := mul_le_mul_of_nonneg_left hmin_bound hq_nonneg
    _ ≤ groundedLaplacianEigenvalueMax G r * d := mul_le_mul_of_nonneg_right hq hd_pos.le

/-- Lemma 1, equation (1), total weight term, for the grounded matrix with half the constant. -/
theorem cut_totalWeight_bound_le_groundedConditionNumber
    (G : WeightedGraph n m) (r : Fin n) (S : Finset (Fin n))
    (hne : S.Nonempty) (hproper : S ≠ Finset.univ)
    (hconn : G.CombinatoriallyConnected) :
    ((S.card : ℝ) / n) * (1 - (S.card : ℝ) / n) * G.totalWeight / G.cutWeight S ≤
      groundedConditionNumber G r := by
  have hn : 0 < n := hne.choose.pos
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hcard_lt : S.card < n := by
    simpa using Finset.card_lt_card (Finset.ssubset_univ_iff.mpr hproper)
  have hn2 : 1 < n := lt_of_le_of_lt (Finset.one_le_card.mpr hne) hcard_lt
  have hlambda_pos := combinatoriallyConnected_implies_spectralConnected G hconn hn2
  unfold WeightedGraph.Connected at hlambda_pos
  have hcard_pos : (0 : ℝ) < S.card := Nat.cast_pos.mpr (Finset.card_pos.mpr hne)
  have hcard_lt_real : (S.card : ℝ) < n := Nat.cast_lt.mpr hcard_lt
  have hproduct_pos : (0 : ℝ) < (S.card : ℝ) * ((n : ℝ) - S.card) :=
    mul_pos hcard_pos (sub_pos.mpr hcard_lt_real)
  have hcut := lambda2_mul_le_cut G S hne hproper
  have hcut_pos : 0 < G.cutWeight S := by
    have hpositive := mul_pos hlambda_pos hproduct_pos
    nlinarith
  have htotal_nonneg : 0 ≤ G.totalWeight :=
    Finset.sum_nonneg fun e _ ↦ (G.weights_pos e).le
  have htransfer := groundedConditionNumber_ge_of_lambda2_mul_le G r hconn hn2
    ((S.card : ℝ) * ((n : ℝ) - S.card)) ((n : ℝ) * G.cutWeight S)
    (G.totalWeight / n) hproduct_pos (div_nonneg htotal_nonneg hn_pos.le)
    (totalWeight_div_card_le_groundedEigenvalueMax G r hn2) hcut
  convert htransfer using 1
  field_simp

/-- The Rayleigh estimate behind Theorem 1: `λ₂(B) β (1 - β) n ≤ s Δ b_max`. -/
theorem separator_lambda2_mul_le (G : WeightedGraph n m)
    (A X Bv : Finset (Fin n)) (s Δ bmax β : ℝ)
    (hcover : A ∪ X ∪ Bv = Finset.univ)
    (hdisj : Disjoint (A ∪ X) Bv)
    (hnoAB : ∀ e, ¬(G.posEndpoint e ∈ A ∧ G.negEndpoint e ∈ Bv) ∧
      ¬(G.posEndpoint e ∈ Bv ∧ G.negEndpoint e ∈ A))
    (hX : (X.card : ℝ) ≤ s)
    (hdeg : ∀ i, ((G.incidentEdges i).card : ℝ) ≤ Δ)
    (hbmax : ∀ e, G.weights e ≤ bmax)
    (hβ : 0 < β)
    (hA_size : β * n ≤ ((A ∪ X).card : ℝ)) (hB_size : β * n ≤ (Bv.card : ℝ))
    (hconn : G.CombinatoriallyConnected) :
    laplacian_eigenvalue₂ G (fun _ ↦ 1) * (β * (1 - β) * n) ≤ s * Δ * bmax := by
  have hn : 0 < n := Fin.pos_iff_nonempty.mpr hconn.nonempty
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
  set S : Finset (Fin n) := A ∪ X with hS_def
  have hβn_pos : (0 : ℝ) < β * n := mul_pos hβ hn_pos
  have hS_ne : S.Nonempty := by
    rw [← Finset.card_pos]
    have hcard_pos : (0 : ℝ) < (S.card : ℝ) := lt_of_lt_of_le hβn_pos hA_size
    exact_mod_cast hcard_pos
  have hS_proper : S ≠ Finset.univ := by
    intro hS_univ
    have hBv_empty : Bv = ∅ := by
      rw [← Finset.subset_empty]
      intro b hb
      exact absurd (hS_univ ▸ Finset.mem_univ b : b ∈ S)
        (Finset.disjoint_right.mp hdisj hb)
    rw [hBv_empty] at hB_size
    simp only [Finset.card_empty, Nat.cast_zero] at hB_size
    linarith
  have hcard_lt : S.card < n := by
    simpa using Finset.card_lt_card (Finset.ssubset_univ_iff.mpr hS_proper)
  have hn2 : 1 < n := lt_of_le_of_lt (Finset.one_le_card.mpr hS_ne) hcard_lt
  have hm_pos : 0 < m := by
    have hm := G.card_sub_one_le_edges hconn
    omega
  have hbmax_pos : 0 < bmax := lt_of_lt_of_le (G.weights_pos ⟨0, hm_pos⟩) (hbmax ⟨0, hm_pos⟩)
  have hΔ_nonneg : 0 ≤ Δ := le_trans (Nat.cast_nonneg _) (hdeg ⟨0, hn⟩)
  have hcut_le : G.cutWeight S ≤ s * Δ * bmax := by
    rw [cutWeight_eq_sum_boundary]
    have hcard_le : ((G.boundaryEdges S).card : ℝ) ≤ s * Δ := by
      have hboundary : (G.boundaryEdges S).card ≤
          ∑ x ∈ X, (G.incidentEdges x).card :=
        le_trans
          (Finset.card_le_card
            (boundaryEdges_subset_incident G A X Bv hcover hnoAB))
          Finset.card_biUnion_le
      calc
        ((G.boundaryEdges S).card : ℝ) ≤
            ((∑ x ∈ X, (G.incidentEdges x).card : ℕ) : ℝ) := by
          exact_mod_cast hboundary
        _ = ∑ x ∈ X, ((G.incidentEdges x).card : ℝ) := by push_cast; rfl
        _ ≤ ∑ _x ∈ X, Δ := Finset.sum_le_sum fun x _ ↦ hdeg x
        _ = (X.card : ℝ) * Δ := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ s * Δ := mul_le_mul_of_nonneg_right hX hΔ_nonneg
    calc
      ∑ e ∈ G.boundaryEdges S, G.weights e ≤
          ∑ _e ∈ G.boundaryEdges S, bmax :=
        Finset.sum_le_sum fun e _ ↦ hbmax e
      _ = ((G.boundaryEdges S).card : ℝ) * bmax := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ s * Δ * bmax := mul_le_mul_of_nonneg_right hcard_le hbmax_pos.le
  have hcard_sum : (S.card : ℝ) + Bv.card ≤ n := by
    have hunion := Finset.card_union_of_disjoint hdisj
    have hle : (S ∪ Bv).card ≤ n := by
      simpa using Finset.card_le_card (Finset.subset_univ (S ∪ Bv))
    rw [hunion] at hle
    exact_mod_cast hle
  have hlambda_nonneg := lambda2_nonneg G hn2
  have hcut := lambda2_mul_le_cut G S hS_ne hS_proper
  -- `x (n - x) ≥ β (1 - β) n²` on `[β n, (1 - β) n]`
  have hproduct : β * (1 - β) * (n : ℝ) ^ 2 ≤ (S.card : ℝ) * ((n : ℝ) - S.card) := by
    have hlow : 0 ≤ (S.card : ℝ) - β * n := by linarith
    have hhigh : 0 ≤ (1 - β) * n - (S.card : ℝ) := by linarith
    nlinarith [mul_nonneg hlow hhigh]
  have hscaled : laplacian_eigenvalue₂ G (fun _ ↦ 1) * (β * (1 - β) * (n : ℝ) ^ 2) ≤
      (n : ℝ) * (s * Δ * bmax) :=
    (mul_le_mul_of_nonneg_left hproduct hlambda_nonneg).trans
      (hcut.trans (mul_le_mul_of_nonneg_left hcut_le hn_pos.le))
  have hfactor : laplacian_eigenvalue₂ G (fun _ ↦ 1) * (β * (1 - β) * (n : ℝ) ^ 2) =
      (n : ℝ) * (laplacian_eigenvalue₂ G (fun _ ↦ 1) * (β * (1 - β) * n)) := by ring
  rw [hfactor] at hscaled
  exact le_of_mul_le_mul_left hscaled hn_pos

/-- Theorem 1, total weight term, for the grounded matrix with half the constant. -/
theorem grounded_separator_kappa_bound (G : WeightedGraph n m) (r : Fin n)
    (A X Bv : Finset (Fin n)) (s Δ bmax β : ℝ)
    (hcover : A ∪ X ∪ Bv = Finset.univ)
    (hdisj : Disjoint (A ∪ X) Bv)
    (hnoAB : ∀ e, ¬(G.posEndpoint e ∈ A ∧ G.negEndpoint e ∈ Bv) ∧
      ¬(G.posEndpoint e ∈ Bv ∧ G.negEndpoint e ∈ A))
    (hX : (X.card : ℝ) ≤ s)
    (hdeg : ∀ i, ((G.incidentEdges i).card : ℝ) ≤ Δ)
    (hbmax : ∀ e, G.weights e ≤ bmax)
    (hβ : 0 < β) (hβ' : β ≤ 1 / 2)
    (hA_size : β * n ≤ ((A ∪ X).card : ℝ)) (hB_size : β * n ≤ (Bv.card : ℝ))
    (hconn : G.CombinatoriallyConnected) :
    β * (1 - β) * G.totalWeight / (s * Δ * bmax) ≤ groundedConditionNumber G r := by
  have hn : 0 < n := Fin.pos_iff_nonempty.mpr hconn.nonempty
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
  have hn2 : 1 < n := by
    by_contra hle
    have hone : n = 1 := by omega
    have hA_le : ((A ∪ X).card : ℝ) + (Bv.card : ℝ) ≤ n := by
      have hunion := Finset.card_union_of_disjoint hdisj
      have hle' : ((A ∪ X) ∪ Bv).card ≤ n := by
        simpa using Finset.card_le_card (Finset.subset_univ ((A ∪ X) ∪ Bv))
      rw [hunion] at hle'
      exact_mod_cast hle'
    have hβn_pos : (0 : ℝ) < β * n := mul_pos hβ hn_pos
    have hA_one : (1 : ℝ) ≤ ((A ∪ X).card : ℝ) := by
      have hpos : 0 < (A ∪ X).card := by
        have hcast : (0 : ℝ) < ((A ∪ X).card : ℝ) := lt_of_lt_of_le hβn_pos hA_size
        exact_mod_cast hcast
      exact_mod_cast hpos
    have hB_one : (1 : ℝ) ≤ (Bv.card : ℝ) := by
      have hpos : 0 < Bv.card := by
        have hcast : (0 : ℝ) < (Bv.card : ℝ) := lt_of_lt_of_le hβn_pos hB_size
        exact_mod_cast hcast
      exact_mod_cast hpos
    have hn_one : (n : ℝ) = 1 := by exact_mod_cast hone
    linarith
  have hbound := separator_lambda2_mul_le G A X Bv s Δ bmax β hcover hdisj hnoAB hX hdeg
    hbmax hβ hA_size hB_size hconn
  have hc_pos : 0 < β * (1 - β) * n := by
    have hone_sub : 0 < 1 - β := by linarith
    positivity
  have htotal_nonneg : 0 ≤ G.totalWeight :=
    Finset.sum_nonneg fun e _ ↦ (G.weights_pos e).le
  have htransfer := groundedConditionNumber_ge_of_lambda2_mul_le G r hconn hn2
    (β * (1 - β) * n) (s * Δ * bmax) (G.totalWeight / n) hc_pos
    (div_nonneg htotal_nonneg hn_pos.le)
    (totalWeight_div_card_le_groundedEigenvalueMax G r hn2) hbound
  convert htransfer using 1
  field_simp

/-- Theorem 1 for the grounded matrix in the letter's form, with half the constant:
`κ₂(B_r) ≥ (β (1 - β) / (s Δ)) max {b(E) / b_max, n}`. -/
theorem grounded_separator_kappa_bound_combined (G : WeightedGraph n m) (r : Fin n)
    (A X Bv : Finset (Fin n)) (s Δ bmax β : ℝ)
    (hcover : A ∪ X ∪ Bv = Finset.univ)
    (hdisj : Disjoint (A ∪ X) Bv)
    (hnoAB : ∀ e, ¬(G.posEndpoint e ∈ A ∧ G.negEndpoint e ∈ Bv) ∧
      ¬(G.posEndpoint e ∈ Bv ∧ G.negEndpoint e ∈ A))
    (hX : (X.card : ℝ) ≤ s)
    (hdeg : ∀ i, ((G.incidentEdges i).card : ℝ) ≤ Δ)
    (hbmax : ∀ e, G.weights e ≤ bmax)
    (hβ : 0 < β) (hβ' : β ≤ 1 / 2)
    (hA_size : β * n ≤ ((A ∪ X).card : ℝ)) (hB_size : β * n ≤ (Bv.card : ℝ))
    (hconn : G.CombinatoriallyConnected) :
    max (β * (1 - β) * G.totalWeight / (s * Δ * bmax))
        (β * (1 - β) * n / (s * Δ)) ≤ groundedConditionNumber G r :=
  max_le
    (grounded_separator_kappa_bound G r A X Bv s Δ bmax β hcover hdisj hnoAB hX hdeg
      hbmax hβ hβ' hA_size hB_size hconn)
    (grounded_separator_kappa_bound_topological G r A X Bv s Δ β hcover hdisj hnoAB hX
      hdeg hβ hβ' hA_size hB_size hconn)

/-- Proposition 1, total weight term, for the grounded matrix with half the constant. -/
theorem grounded_corridor_kappa_bound (G : WeightedGraph n m) (r : Fin n)
    (VS VT : Finset (Fin n)) (ℓ : ℕ) (p : Fin ℓ → Fin n)
    (EP : Finset (Fin m)) (C : CorridorTopology G VS VT ℓ p EP)
    (β : ℝ) (hβ : 0 < β)
    (hVS_size : β * n ≤ (VS.card : ℝ))
    (hVT_size : β * n ≤ (VT.card : ℝ))
    (hconn : G.CombinatoriallyConnected) :
    β ^ 2 * ((ℓ : ℝ) - 1) ^ 2 * G.totalWeight / (∑ e ∈ EP, G.weights e) ≤
      groundedConditionNumber G r := by
  have hℓn : ℓ ≤ n := by
    simpa using Fintype.card_le_of_injective p C.path_injective
  have hn2 : 1 < n :=
    lt_of_lt_of_le (lt_of_lt_of_le (by norm_num : 1 < 2) C.length_two) hℓn
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlength_pos : (0 : ℝ) < (ℓ : ℝ) - 1 :=
    sub_pos.mpr (by exact_mod_cast C.length_two)
  have hbound := corridor_lambda2_mul_le G VS VT ℓ C.length_two p EP β
    C.path_injective C.path_disjoint_left C.path_disjoint_right C.bulks_disjoint
    C.path_branch C.nonpath_internal hβ hVS_size hVT_size
  have hc_pos : 0 < β ^ 2 * n * ((ℓ : ℝ) - 1) ^ 2 := by positivity
  have htotal_nonneg : 0 ≤ G.totalWeight :=
    Finset.sum_nonneg fun e _ ↦ (G.weights_pos e).le
  have htransfer := groundedConditionNumber_ge_of_lambda2_mul_le G r hconn hn2
    (β ^ 2 * n * ((ℓ : ℝ) - 1) ^ 2) (∑ e ∈ EP, G.weights e) (G.totalWeight / n) hc_pos
    (div_nonneg htotal_nonneg hn_pos.le)
    (totalWeight_div_card_le_groundedEigenvalueMax G r hn2) hbound
  convert htransfer using 1
  field_simp

/-- Proposition 1, heaviest branch term, for the grounded matrix with half the constant. -/
theorem grounded_corridor_kappa_bound_edge (G : WeightedGraph n m) (r : Fin n)
    (VS VT : Finset (Fin n)) (ℓ : ℕ) (p : Fin ℓ → Fin n)
    (EP : Finset (Fin m)) (C : CorridorTopology G VS VT ℓ p EP)
    (β : ℝ) (hβ : 0 < β)
    (hVS_size : β * n ≤ (VS.card : ℝ))
    (hVT_size : β * n ≤ (VT.card : ℝ)) (e : Fin m)
    (hconn : G.CombinatoriallyConnected) :
    β ^ 2 * ((ℓ : ℝ) - 1) ^ 2 * ((n : ℝ) * G.weights e) / (∑ e ∈ EP, G.weights e) ≤
      groundedConditionNumber G r := by
  have hℓn : ℓ ≤ n := by
    simpa using Fintype.card_le_of_injective p C.path_injective
  have hn2 : 1 < n :=
    lt_of_lt_of_le (lt_of_lt_of_le (by norm_num : 1 < 2) C.length_two) hℓn
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlength_pos : (0 : ℝ) < (ℓ : ℝ) - 1 :=
    sub_pos.mpr (by exact_mod_cast C.length_two)
  have hbound := corridor_lambda2_mul_le G VS VT ℓ C.length_two p EP β
    C.path_injective C.path_disjoint_left C.path_disjoint_right C.bulks_disjoint
    C.path_branch C.nonpath_internal hβ hVS_size hVT_size
  have hc_pos : 0 < β ^ 2 * n * ((ℓ : ℝ) - 1) ^ 2 := by positivity
  have htransfer := groundedConditionNumber_ge_of_lambda2_mul_le G r hconn hn2
    (β ^ 2 * n * ((ℓ : ℝ) - 1) ^ 2) (∑ e ∈ EP, G.weights e) (G.weights e) hc_pos
    (G.weights_pos e).le (edgeWeight_le_groundedEigenvalueMax G r e) hbound
  convert htransfer using 1
  ring

/-- Proposition 1 for the grounded matrix in the letter's form, with half the constant. -/
theorem grounded_corridor_kappa_bound_combined (G : WeightedGraph n m) (r : Fin n)
    (VS VT : Finset (Fin n)) (ℓ : ℕ) (p : Fin ℓ → Fin n)
    (EP : Finset (Fin m)) (C : CorridorTopology G VS VT ℓ p EP)
    (β : ℝ) (hβ : 0 < β)
    (hVS_size : β * n ≤ (VS.card : ℝ))
    (hVT_size : β * n ≤ (VT.card : ℝ)) (e : Fin m)
    (hconn : G.CombinatoriallyConnected) :
    max (β ^ 2 * ((ℓ : ℝ) - 1) ^ 2 * G.totalWeight / (∑ e ∈ EP, G.weights e))
        (max (β ^ 2 * ((ℓ : ℝ) - 1) ^ 2 * ((n : ℝ) * G.weights e) /
            (∑ e ∈ EP, G.weights e))
          (β ^ 2 * n * ((ℓ : ℝ) - 1))) ≤ groundedConditionNumber G r :=
  max_le
    (grounded_corridor_kappa_bound G r VS VT ℓ p EP C β hβ hVS_size hVT_size hconn)
    (max_le
      (grounded_corridor_kappa_bound_edge G r VS VT ℓ p EP C β hβ hVS_size hVT_size e hconn)
      (grounded_corridor_kappa_bound_topological G r VS VT ℓ p EP C β hβ hVS_size hVT_size
        hconn))

namespace WeightedGraph

variable {k τ : ℕ}

/-- Corollary 1(i), first claim. A tree decomposition of width at most `τ ≤ n / 4 - 1` yields a
`(τ + 1, 1 / 4)` separation of the grid. -/
theorem exists_quarter_separation_of_tree_decomposition (G : WeightedGraph n m)
    (D : RootedTreeDecomposition G.toSimpleGraph k)
    (hn : 0 < n) (hwidth : D.HasWidthAtMost τ) (hτ : τ + 1 ≤ n / 4) :
    ∃ A X Bv : Finset (Fin n),
      A ∪ X ∪ Bv = Finset.univ ∧
      Disjoint (A ∪ X) Bv ∧
      (∀ e, ¬(G.posEndpoint e ∈ A ∧ G.negEndpoint e ∈ Bv) ∧
        ¬(G.posEndpoint e ∈ Bv ∧ G.negEndpoint e ∈ A)) ∧
      (X.card : ℝ) ≤ (τ : ℝ) + 1 ∧
      (n : ℝ) / 4 ≤ ((A ∪ X).card : ℝ) ∧
      (n : ℝ) / 4 ≤ (Bv.card : ℝ) := by
  classical
  obtain ⟨X, hXwidth, hcomponentHalf⟩ :=
    G.exists_balanced_bag_of_tree_decomposition D hn hwidth
  have hXτ : (X.card : ℝ) ≤ (τ : ℝ) + 1 := by
    exact_mod_cast hXwidth
  have hXquarterNat : X.card ≤ n / 4 := hXwidth.trans hτ
  have hXquarter : (X.card : ℝ) ≤ (n : ℝ) / 4 := by
    have hcast : (X.card : ℝ) ≤ ((n / 4 : ℕ) : ℝ) := by
      exact_mod_cast hXquarterNat
    exact hcast.trans Nat.cast_div_le
  let H := G.graphOff X
  let componentEquiv : H.ConnectedComponent ≃ Fin (Fintype.card H.ConnectedComponent) :=
    Fintype.equivFin H.ConnectedComponent
  let component : Fin (Fintype.card H.ConnectedComponent) → Finset (Fin n) :=
    fun i ↦ G.componentVerticesOff X (componentEquiv.symm i)
  have hparts : ∀ ⦃i j⦄, i ≠ j → Disjoint (component i) (component j) := by
    intro i j hij
    rw [Finset.disjoint_left]
    intro v hvi hvj
    simp only [component, WeightedGraph.componentVerticesOff, Finset.mem_filter,
      Finset.mem_univ, true_and] at hvi hvj
    obtain ⟨_, hi⟩ := hvi
    obtain ⟨_, hj⟩ := hvj
    have hc : componentEquiv.symm i = componentEquiv.symm j := hi.symm.trans hj
    exact hij (componentEquiv.symm.injective hc)
  have hXparts : ∀ i, Disjoint X (component i) := by
    intro i
    rw [Finset.disjoint_left]
    intro v hvX hvi
    simp only [component, WeightedGraph.componentVerticesOff, Finset.mem_filter,
      Finset.mem_univ, true_and] at hvi
    exact hvi.1 hvX
  have hcover : X ∪ Finset.univ.biUnion component = Finset.univ :=
    Finset.eq_univ_of_forall fun v ↦ by
      by_cases hvX : v ∈ X
      · exact Finset.mem_union_left _ hvX
      · apply Finset.mem_union_right
        rw [Finset.mem_biUnion]
        let c : H.ConnectedComponent := H.connectedComponentMk ⟨v, hvX⟩
        let i : Fin (Fintype.card H.ConnectedComponent) := componentEquiv c
        refine ⟨i, Finset.mem_univ i, ?_⟩
        change v ∈ G.componentVerticesOff X (componentEquiv.symm i)
        unfold WeightedGraph.componentVerticesOff
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨hvX, ?_⟩
        simp [H, i, c]
  have hcomponentHalf' : ∀ i, (component i).card ≤ n / 2 :=
    fun i ↦ hcomponentHalf (componentEquiv.symm i)
  have hedgeComponent : ∀ e, G.posEndpoint e ∉ X → G.negEndpoint e ∉ X →
      ∃ i, G.posEndpoint e ∈ component i ∧ G.negEndpoint e ∈ component i := by
    intro e hposX hnegX
    let u : {v : Fin n // v ∉ X} := ⟨G.posEndpoint e, hposX⟩
    let v : {v : Fin n // v ∉ X} := ⟨G.negEndpoint e, hnegX⟩
    have huv : H.Adj u v := ⟨e, Or.inl ⟨rfl, rfl⟩⟩
    let c : H.ConnectedComponent := H.connectedComponentMk u
    let i : Fin (Fintype.card H.ConnectedComponent) := componentEquiv c
    refine ⟨i, ?_, ?_⟩
    · change G.posEndpoint e ∈ G.componentVerticesOff X (componentEquiv.symm i)
      unfold WeightedGraph.componentVerticesOff
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨hposX, ?_⟩
      simp [H, i, c, u]
    · have hcomp : H.connectedComponentMk v = H.connectedComponentMk u :=
        (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj huv).symm
      change G.negEndpoint e ∈ G.componentVerticesOff X (componentEquiv.symm i)
      unfold WeightedGraph.componentVerticesOff
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨hnegX, ?_⟩
      simpa [H, i, c, v, u] using hcomp
  obtain ⟨A, Bv, hcover', hdisjoint, hnoCrossing, hA, hB⟩ :=
    component_partition_has_quarter_separation G X
      (Fintype.card H.ConnectedComponent) component hn hparts hXparts hcover
      hXquarter hcomponentHalf' hedgeComponent
  exact ⟨A, X, Bv, hcover', hdisjoint, hnoCrossing, hXτ, hA, hB⟩

/-- Corollary 1(i) for the grounded matrix with half the constant:
`κ₂(B_r) ≥ 3 max {b(E) / b_max, n} / (16 (τ + 1) Δ)`. -/
theorem grounded_treewidth_kappa_bound_of_tree_decomposition (G : WeightedGraph n m)
    (r : Fin n) (D : RootedTreeDecomposition G.toSimpleGraph k)
    (hwidth : D.HasWidthAtMost τ) (hτ : τ + 1 ≤ n / 4)
    (Δ bmax : ℝ)
    (hdeg : ∀ i, ((G.incidentEdges i).card : ℝ) ≤ Δ)
    (hbmax : ∀ e, G.weights e ≤ bmax)
    (hconn : G.CombinatoriallyConnected) :
    max (3 / 16 * G.totalWeight / (((τ : ℝ) + 1) * Δ * bmax))
        (3 / 16 * n / (((τ : ℝ) + 1) * Δ)) ≤ groundedConditionNumber G r := by
  obtain ⟨A, X, Bv, hcover, hdisj, hnoAB, hX, hA, hB⟩ :=
    G.exists_quarter_separation_of_tree_decomposition D r.pos hwidth hτ
  have hA' : (1 / 4 : ℝ) * n ≤ ((A ∪ X).card : ℝ) := by linarith
  have hB' : (1 / 4 : ℝ) * n ≤ (Bv.card : ℝ) := by linarith
  have h := grounded_separator_kappa_bound_combined G r A X Bv ((τ : ℝ) + 1) Δ bmax
    (1 / 4) hcover hdisj hnoAB hX hdeg hbmax (by norm_num) (by norm_num) hA' hB' hconn
  convert h using 2 <;> ring

end WeightedGraph

/-- Corollary 1(ii) for the grounded matrix with half the constant, from the quantitative
Lipton--Tarjan partition. -/
theorem grounded_planar_kappa_bound_of_lipton_partition (G : WeightedGraph n m) (r : Fin n)
    (A X Bv : Finset (Fin n)) (Δ bmax : ℝ) (hn : 288 ≤ n)
    (hcover : A ∪ X ∪ Bv = Finset.univ)
    (hdisj : Disjoint (A ∪ X) Bv)
    (hnoAB : ∀ e, ¬(G.posEndpoint e ∈ A ∧ G.negEndpoint e ∈ Bv) ∧
      ¬(G.posEndpoint e ∈ Bv ∧ G.negEndpoint e ∈ A))
    (hX : (X.card : ℝ) ≤ Real.sqrt (8 * n))
    (hA_upper : (A.card : ℝ) ≤ 2 * n / 3)
    (hB_upper : (Bv.card : ℝ) ≤ 2 * n / 3)
    (hdeg : ∀ i, ((G.incidentEdges i).card : ℝ) ≤ Δ)
    (hbmax : ∀ e, G.weights e ≤ bmax)
    (hconn : G.CombinatoriallyConnected) :
    max (5 / 36 * G.totalWeight / (Real.sqrt (8 * n) * Δ * bmax))
        (5 / 36 * n / (Real.sqrt (8 * n) * Δ)) ≤ groundedConditionNumber G r := by
  have hcardNat : (A ∪ X).card + Bv.card = n := by
    rw [← Finset.card_union_of_disjoint hdisj, hcover, Finset.card_univ, Fintype.card_fin]
  have hcard : ((A ∪ X).card : ℝ) + (Bv.card : ℝ) = n := by
    exact_mod_cast hcardNat
  have hXsixth : (X.card : ℝ) ≤ (n : ℝ) / 6 :=
    hX.trans (sqrt_eight_mul_card_le_sixth n hn)
  have hunionNat : (A ∪ X).card ≤ A.card + X.card := Finset.card_union_le A X
  have hunion : ((A ∪ X).card : ℝ) ≤ (A.card : ℝ) + X.card := by
    exact_mod_cast hunionNat
  have hA' : (1 / 6 : ℝ) * n ≤ ((A ∪ X).card : ℝ) := by linarith
  have hB' : (1 / 6 : ℝ) * n ≤ (Bv.card : ℝ) := by linarith
  have h := grounded_separator_kappa_bound_combined G r A X Bv (Real.sqrt (8 * n)) Δ bmax
    (1 / 6) hcover hdisj hnoAB hX hdeg hbmax (by norm_num) (by norm_num) hA' hB' hconn
  convert h using 2 <;> ring

end
