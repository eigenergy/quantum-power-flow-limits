import PowerFlowLimits.CutBounds

/-!
# Theorem 1 (thm:separator) and Corollary 1 (cor:tw): separations force polynomial conditioning

Part of the Lean 4 formalization of
"The Limits of Quantum Computers for Power Flow" (Khanpour and Talkington).
-/

open Finset BigOperators

noncomputable section

variable {n m : ℕ}

/-- Every boundary branch of `A ∪ X` touches `X`, given a cover with no
    `A`–`Bv` branches. -/
theorem boundaryEdges_subset_incident (G : WeightedGraph n m)
    (A X Bv : Finset (Fin n)) (hcover : A ∪ X ∪ Bv = Finset.univ)
    (hnoAB : ∀ e, ¬(G.posEndpoint e ∈ A ∧ G.negEndpoint e ∈ Bv) ∧
      ¬(G.posEndpoint e ∈ Bv ∧ G.negEndpoint e ∈ A)) :
    G.boundaryEdges (A ∪ X) ⊆ X.biUnion G.incidentEdges := by
  intro e he
  simp only [WeightedGraph.boundaryEdges, Finset.mem_filter, Finset.mem_univ,
    true_and] at he
  rw [Finset.mem_biUnion]
  have hmemBv : ∀ i : Fin n, i ∉ A ∪ X → i ∈ Bv := by
    intro i hi
    have := Finset.mem_univ i
    rw [← hcover] at this
    rcases Finset.mem_union.mp this with h | h
    · exact absurd h hi
    · exact h
  by_cases hp : G.posEndpoint e ∈ A ∪ X
  · have hq : G.negEndpoint e ∉ A ∪ X := fun hq => he (iff_of_true hp hq)
    have hqBv := hmemBv _ hq
    rcases Finset.mem_union.mp hp with hpA | hpX
    · exact absurd ⟨hpA, hqBv⟩ (hnoAB e).1
    · exact ⟨G.posEndpoint e, hpX, by
        simp [WeightedGraph.incidentEdges]⟩
  · have hq : G.negEndpoint e ∈ A ∪ X := by
      by_contra hq
      exact he (iff_of_false hp hq)
    have hpBv := hmemBv _ hp
    rcases Finset.mem_union.mp hq with hqA | hqX
    · exact absurd ⟨hpBv, hqA⟩ (hnoAB e).2
    · exact ⟨G.negEndpoint e, hqX, by
        simp [WeightedGraph.incidentEdges]⟩

/-- Theorem 1 (thm:separator): separators force polynomial conditioning.
    If `V = A ⊔ X ⊔ Bv` with no `A`–`Bv` branches, `|X| ≤ s`, degrees ≤ Δ,
    weights ≤ b_max, and both sides have size ≥ βn, then
    κ₊(B) ≥ 2β(1-β)·b(E)/(s·Δ·b_max). -/
theorem separator_kappa_bound (G : WeightedGraph n m)
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
    (hconn : G.Connected (fun _ => 1)) :
    2 * β * (1 - β) * G.totalWeight / (s * Δ * bmax) ≤
      effectiveConditionNumber G (fun _ => 1) := by
  have hn2 : 1 < n := hconn.one_lt
  have hn_pos : (0 : ℝ) < n := by
    have : (0 : ℕ) < n := by omega
    exact_mod_cast this
  set S : Finset (Fin n) := A ∪ X with hS_def
  have hβn_pos : (0 : ℝ) < β * n := mul_pos hβ hn_pos
  have hS_ne : S.Nonempty := by
    rw [← Finset.card_pos]
    have hcard_pos : (0 : ℝ) < (S.card : ℝ) := lt_of_lt_of_le hβn_pos hA_size
    exact_mod_cast hcard_pos
  have hS_proper : S ≠ Finset.univ := by
    intro h
    have hBv_empty : Bv = ∅ := by
      rw [← Finset.subset_empty]
      intro b hb
      exact absurd (h ▸ Finset.mem_univ b : b ∈ S)
        (Finset.disjoint_right.mp hdisj hb)
    rw [hBv_empty] at hB_size
    simp only [Finset.card_empty, Nat.cast_zero] at hB_size
    linarith
  -- the graph has at least one branch, so bmax > 0
  have hm_pos : 0 < m := by
    by_contra h
    push_neg at h
    have hm0 : m = 0 := by omega
    have hT3 := lambda2_mul_le_cut G S hS_ne hS_proper
    have hcw0 : G.cutWeight S = 0 := by
      unfold WeightedGraph.cutWeight
      subst hm0
      simp
    rw [hcw0, mul_zero] at hT3
    have hconn' := hconn
    unfold WeightedGraph.Connected at hconn'
    have hcard_lt : S.card < n := by
      have h := Finset.card_lt_card (Finset.ssubset_univ_iff.mpr hS_proper)
      simpa using h
    have hA_pos : (0 : ℝ) < (S.card : ℝ) * ((n : ℝ) - S.card) := by
      have h1 : (0 : ℝ) < S.card := lt_of_lt_of_le hβn_pos hA_size
      have h2 : (S.card : ℝ) < n := Nat.cast_lt.mpr hcard_lt
      exact mul_pos h1 (by linarith)
    nlinarith
  have hbmax_pos : 0 < bmax :=
    lt_of_lt_of_le (G.weights_pos ⟨0, hm_pos⟩) (hbmax ⟨0, hm_pos⟩)
  have hΔ_nn : 0 ≤ Δ := le_trans (Nat.cast_nonneg _) (hdeg ⟨0, by omega⟩)
  -- cut weight bound: b(∂S) ≤ s·Δ·b_max
  have hcw_le : G.cutWeight S ≤ s * Δ * bmax := by
    rw [cutWeight_eq_sum_boundary]
    have hcard_le : ((G.boundaryEdges S).card : ℝ) ≤ s * Δ := by
      have h1 : (G.boundaryEdges S).card ≤ ∑ x ∈ X, (G.incidentEdges x).card :=
        le_trans
          (Finset.card_le_card
            (boundaryEdges_subset_incident G A X Bv hcover hnoAB))
          Finset.card_biUnion_le
      calc ((G.boundaryEdges S).card : ℝ)
          ≤ ((∑ x ∈ X, (G.incidentEdges x).card : ℕ) : ℝ) := by exact_mod_cast h1
        _ = ∑ x ∈ X, ((G.incidentEdges x).card : ℝ) := by push_cast; rfl
        _ ≤ ∑ _x ∈ X, Δ := Finset.sum_le_sum fun x _ => hdeg x
        _ = (X.card : ℝ) * Δ := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ s * Δ := mul_le_mul_of_nonneg_right hX hΔ_nn
    calc ∑ e ∈ G.boundaryEdges S, G.weights e
        ≤ ∑ _e ∈ G.boundaryEdges S, bmax := Finset.sum_le_sum fun e _ => hbmax e
      _ = ((G.boundaryEdges S).card : ℝ) * bmax := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ s * Δ * bmax := mul_le_mul_of_nonneg_right hcard_le hbmax_pos.le
  -- γ = |S|/n lies in [β, 1-β]
  have hγ_lo : β ≤ (S.card : ℝ) / n := (le_div_iff₀ hn_pos).mpr (by linarith)
  have hγ_hi : (S.card : ℝ) / n ≤ 1 - β := by
    rw [div_le_iff₀ hn_pos]
    have hcard_sum : (S.card : ℝ) + Bv.card ≤ n := by
      have hunion := Finset.card_union_of_disjoint hdisj
      have hle : (S ∪ Bv).card ≤ n := by
        have := Finset.card_le_card (Finset.subset_univ (S ∪ Bv))
        simpa using this
      rw [hunion] at hle
      exact_mod_cast hle
    nlinarith
  -- cut weight is positive under connectivity
  have hcw_pos : 0 < G.cutWeight S := by
    have hT3 := lambda2_mul_le_cut G S hS_ne hS_proper
    have hconn' := hconn
    unfold WeightedGraph.Connected at hconn'
    have hcard_lt : S.card < n := by
      have h := Finset.card_lt_card (Finset.ssubset_univ_iff.mpr hS_proper)
      simpa using h
    have hA_pos : (0 : ℝ) < (S.card : ℝ) * ((n : ℝ) - S.card) := by
      have h1 : (0 : ℝ) < S.card := lt_of_lt_of_le hβn_pos hA_size
      have h2 : (S.card : ℝ) < n := Nat.cast_lt.mpr hcard_lt
      exact mul_pos h1 (by linarith)
    nlinarith [mul_pos hconn' hA_pos]
  have hden_pos : 0 < s * Δ * bmax := lt_of_lt_of_le hcw_pos hcw_le
  have hW_nn : 0 ≤ G.totalWeight :=
    Finset.sum_nonneg fun e _ => (G.weights_pos e).le
  -- monotone substitution into the Lemma 1 consequence
  refine le_trans ?_ (kappaPlus_ge_totalWeight G S hS_ne hS_proper hconn)
  have hnum : 2 * β * (1 - β) * G.totalWeight ≤
      2 * ((S.card : ℝ) / n) * (1 - (S.card : ℝ) / n) * G.totalWeight := by
    apply mul_le_mul_of_nonneg_right _ hW_nn
    nlinarith
  have hc_nonneg : 0 ≤ 2 * ((S.card : ℝ) / n) * (1 - (S.card : ℝ) / n) *
      G.totalWeight := by
    have h1 : (0 : ℝ) ≤ (S.card : ℝ) / n := le_trans hβ.le hγ_lo
    have h2 : (0 : ℝ) ≤ 1 - (S.card : ℝ) / n := by linarith
    positivity
  rw [div_le_div_iff₀ hden_pos hcw_pos]
  exact mul_le_mul hnum hcw_le hcw_pos.le hc_nonneg

/-- Corollary 1(i) (cor:tw), spectral content: a (τ+1, 1/4)-separation gives
    κ₊(B) ≥ (3/8)·b(E)/((τ+1)·Δ·b_max). The graph-theoretic input — every
    graph of treewidth τ ≤ n/4 - 1 admits such a separation (Cygan et al.,
    Ch. 7, plus the greedy component grouping) — is not available in mathlib
    and enters through the separation hypotheses. -/
theorem treewidth_kappa_bound (G : WeightedGraph n m)
    (A X Bv : Finset (Fin n)) (τ Δ bmax : ℝ)
    (hcover : A ∪ X ∪ Bv = Finset.univ)
    (hdisj : Disjoint (A ∪ X) Bv)
    (hnoAB : ∀ e, ¬(G.posEndpoint e ∈ A ∧ G.negEndpoint e ∈ Bv) ∧
      ¬(G.posEndpoint e ∈ Bv ∧ G.negEndpoint e ∈ A))
    (hX : (X.card : ℝ) ≤ τ + 1)
    (hdeg : ∀ i, ((G.incidentEdges i).card : ℝ) ≤ Δ)
    (hbmax : ∀ e, G.weights e ≤ bmax)
    (hA_size : (n : ℝ) / 4 ≤ ((A ∪ X).card : ℝ))
    (hB_size : (n : ℝ) / 4 ≤ (Bv.card : ℝ))
    (hconn : G.Connected (fun _ => 1)) :
    3 / 8 * G.totalWeight / ((τ + 1) * Δ * bmax) ≤
      effectiveConditionNumber G (fun _ => 1) := by
  have h := separator_kappa_bound G A X Bv (τ + 1) Δ bmax (1 / 4)
    hcover hdisj hnoAB hX hdeg hbmax (by norm_num) (by norm_num)
    (by linarith) (by linarith) hconn
  calc 3 / 8 * G.totalWeight / ((τ + 1) * Δ * bmax)
      = 2 * (1 / 4) * (1 - 1 / 4) * G.totalWeight / ((τ + 1) * Δ * bmax) := by
        ring
    _ ≤ effectiveConditionNumber G (fun _ => 1) := h

/-- Corollary 1(ii) (cor:tw), spectral content: a (√(8n), 1/6)-separation
    gives κ₊(B) ≥ (5/18)·b(E)/(√(8n)·Δ·b_max). The planar separator theorem
    (Lipton–Tarjan) producing such a separation for planar graphs with
    n ≥ 288 is not available in mathlib and enters through the separation
    hypotheses. -/
theorem planar_kappa_bound (G : WeightedGraph n m)
    (A X Bv : Finset (Fin n)) (Δ bmax : ℝ)
    (hcover : A ∪ X ∪ Bv = Finset.univ)
    (hdisj : Disjoint (A ∪ X) Bv)
    (hnoAB : ∀ e, ¬(G.posEndpoint e ∈ A ∧ G.negEndpoint e ∈ Bv) ∧
      ¬(G.posEndpoint e ∈ Bv ∧ G.negEndpoint e ∈ A))
    (hX : (X.card : ℝ) ≤ Real.sqrt (8 * n))
    (hdeg : ∀ i, ((G.incidentEdges i).card : ℝ) ≤ Δ)
    (hbmax : ∀ e, G.weights e ≤ bmax)
    (hA_size : (n : ℝ) / 6 ≤ ((A ∪ X).card : ℝ))
    (hB_size : (n : ℝ) / 6 ≤ (Bv.card : ℝ))
    (hconn : G.Connected (fun _ => 1)) :
    5 / 18 * G.totalWeight / (Real.sqrt (8 * n) * Δ * bmax) ≤
      effectiveConditionNumber G (fun _ => 1) := by
  have h := separator_kappa_bound G A X Bv (Real.sqrt (8 * n)) Δ bmax (1 / 6)
    hcover hdisj hnoAB hX hdeg hbmax (by norm_num) (by norm_num)
    (by linarith) (by linarith) hconn
  calc 5 / 18 * G.totalWeight / (Real.sqrt (8 * n) * Δ * bmax)
      = 2 * (1 / 6) * (1 - 1 / 6) * G.totalWeight /
        (Real.sqrt (8 * n) * Δ * bmax) := by ring
    _ ≤ effectiveConditionNumber G (fun _ => 1) := h

/-- Near-planar extension (remark after cor:tw, r2 revision): planarizing c
    line crossings and reapplying Lipton–Tarjan yields balanced separators of
    size ≤ 2√(8(n+c)), so part (ii) persists up to constants. As with
    Corollary 1, the separator existence is hypothesized. -/
theorem near_planar_kappa_bound (G : WeightedGraph n m)
    (A X Bv : Finset (Fin n)) (Δ bmax c : ℝ) (_hc : 0 ≤ c)
    (hcover : A ∪ X ∪ Bv = Finset.univ)
    (hdisj : Disjoint (A ∪ X) Bv)
    (hnoAB : ∀ e, ¬(G.posEndpoint e ∈ A ∧ G.negEndpoint e ∈ Bv) ∧
      ¬(G.posEndpoint e ∈ Bv ∧ G.negEndpoint e ∈ A))
    (hX : (X.card : ℝ) ≤ 2 * Real.sqrt (8 * ((n : ℝ) + c)))
    (hdeg : ∀ i, ((G.incidentEdges i).card : ℝ) ≤ Δ)
    (hbmax : ∀ e, G.weights e ≤ bmax)
    (hA_size : (n : ℝ) / 6 ≤ ((A ∪ X).card : ℝ))
    (hB_size : (n : ℝ) / 6 ≤ (Bv.card : ℝ))
    (hconn : G.Connected (fun _ => 1)) :
    5 / 36 * G.totalWeight / (Real.sqrt (8 * ((n : ℝ) + c)) * Δ * bmax) ≤
      effectiveConditionNumber G (fun _ => 1) := by
  have h := separator_kappa_bound G A X Bv (2 * Real.sqrt (8 * ((n : ℝ) + c)))
    Δ bmax (1 / 6) hcover hdisj hnoAB hX hdeg hbmax (by norm_num) (by norm_num)
    (by linarith) (by linarith) hconn
  calc 5 / 36 * G.totalWeight / (Real.sqrt (8 * ((n : ℝ) + c)) * Δ * bmax)
      = 2 * (1 / 6) * (1 - 1 / 6) * G.totalWeight /
        (2 * Real.sqrt (8 * ((n : ℝ) + c)) * Δ * bmax) := by
        ring
    _ ≤ effectiveConditionNumber G (fun _ => 1) := h

/-- Sharper cut bound than Theorem 1's counting estimate: the weighted cut of
    `A ∪ X` is at most the total *interface stiffness* Σ_{x∈X} d_x. The
    paper's b(∂S) ≤ s·Δ·b_max follows since each d_x ≤ Δ·b_max. -/
theorem cutWeight_le_sum_weightedDegree (G : WeightedGraph n m)
    (A X Bv : Finset (Fin n)) (hcover : A ∪ X ∪ Bv = Finset.univ)
    (hnoAB : ∀ e, ¬(G.posEndpoint e ∈ A ∧ G.negEndpoint e ∈ Bv) ∧
      ¬(G.posEndpoint e ∈ Bv ∧ G.negEndpoint e ∈ A)) :
    G.cutWeight (A ∪ X) ≤ ∑ x ∈ X, G.weightedDegree x := by
  rw [sum_weightedDegree_eq]
  unfold WeightedGraph.cutWeight
  refine Finset.sum_le_sum fun e _ => ?_
  have hw := (G.weights_pos e).le
  have hmemBv : ∀ i : Fin n, i ∉ A ∪ X → i ∈ Bv := by
    intro i hi
    have hu := Finset.mem_univ i
    rw [← hcover] at hu
    rcases Finset.mem_union.mp hu with h | h
    · exact absurd h hi
    · exact h
  by_cases hp : G.posEndpoint e ∈ A ∪ X <;> by_cases hq : G.negEndpoint e ∈ A ∪ X
  · -- interior edge: cut contribution 0
    rw [if_pos hp, if_pos hq]
    have : (0 : ℝ) ≤ (if G.posEndpoint e ∈ X then (1 : ℝ) else 0) +
        (if G.negEndpoint e ∈ X then (1 : ℝ) else 0) := by positivity
    nlinarith
  · -- boundary, S-side endpoint is pos; it must lie in X
    have hqBv := hmemBv _ hq
    have hpX : G.posEndpoint e ∈ X := by
      rcases Finset.mem_union.mp hp with hpA | hpX
      · exact absurd ⟨hpA, hqBv⟩ (hnoAB e).1
      · exact hpX
    rw [if_pos hp, if_neg hq, if_pos hpX]
    have : (0 : ℝ) ≤ if G.negEndpoint e ∈ X then (1 : ℝ) else 0 := by positivity
    nlinarith
  · -- boundary, S-side endpoint is neg; it must lie in X
    have hpBv := hmemBv _ hp
    have hqX : G.negEndpoint e ∈ X := by
      rcases Finset.mem_union.mp hq with hqA | hqX
      · exact absurd ⟨hpBv, hqA⟩ (hnoAB e).2
      · exact hqX
    rw [if_neg hp, if_pos hq, if_pos hqX]
    have : (0 : ℝ) ≤ if G.posEndpoint e ∈ X then (1 : ℝ) else 0 := by positivity
    nlinarith
  · -- both endpoints in Bv: cut contribution 0
    rw [if_neg hp, if_neg hq]
    have : (0 : ℝ) ≤ (if G.posEndpoint e ∈ X then (1 : ℝ) else 0) +
        (if G.negEndpoint e ∈ X then (1 : ℝ) else 0) := by positivity
    nlinarith

/-- Strengthening of Theorem 1: the denominator s·Δ·b_max is replaced by the
    interface stiffness Σ_{x∈X} d_x, which it always dominates. Strictly
    sharper whenever the separator is electrically weaker than the worst-case
    count s·Δ·b_max — the slow-coherency regime the paper appeals to. -/
theorem separator_kappa_bound_sharp (G : WeightedGraph n m)
    (A X Bv : Finset (Fin n)) (β : ℝ)
    (hcover : A ∪ X ∪ Bv = Finset.univ)
    (hdisj : Disjoint (A ∪ X) Bv)
    (hnoAB : ∀ e, ¬(G.posEndpoint e ∈ A ∧ G.negEndpoint e ∈ Bv) ∧
      ¬(G.posEndpoint e ∈ Bv ∧ G.negEndpoint e ∈ A))
    (hβ : 0 < β) (hβ' : β ≤ 1 / 2)
    (hA_size : β * n ≤ ((A ∪ X).card : ℝ)) (hB_size : β * n ≤ (Bv.card : ℝ))
    (hconn : G.Connected (fun _ => 1)) :
    2 * β * (1 - β) * G.totalWeight / (∑ x ∈ X, G.weightedDegree x) ≤
      effectiveConditionNumber G (fun _ => 1) := by
  have hn2 : 1 < n := hconn.one_lt
  have hn_pos : (0 : ℝ) < n := by
    have : (0 : ℕ) < n := by omega
    exact_mod_cast this
  set S : Finset (Fin n) := A ∪ X with hS_def
  have hβn_pos : (0 : ℝ) < β * n := mul_pos hβ hn_pos
  have hS_ne : S.Nonempty := by
    rw [← Finset.card_pos]
    have hcard_pos : (0 : ℝ) < (S.card : ℝ) := lt_of_lt_of_le hβn_pos hA_size
    exact_mod_cast hcard_pos
  have hS_proper : S ≠ Finset.univ := by
    intro h
    have hBv_empty : Bv = ∅ := by
      rw [← Finset.subset_empty]
      intro b hb
      exact absurd (h ▸ Finset.mem_univ b : b ∈ S)
        (Finset.disjoint_right.mp hdisj hb)
    rw [hBv_empty] at hB_size
    simp only [Finset.card_empty, Nat.cast_zero] at hB_size
    linarith
  have hcw_le : G.cutWeight S ≤ ∑ x ∈ X, G.weightedDegree x :=
    cutWeight_le_sum_weightedDegree G A X Bv hcover hnoAB
  have hγ_lo : β ≤ (S.card : ℝ) / n := (le_div_iff₀ hn_pos).mpr (by linarith)
  have hγ_hi : (S.card : ℝ) / n ≤ 1 - β := by
    rw [div_le_iff₀ hn_pos]
    have hcard_sum : (S.card : ℝ) + Bv.card ≤ n := by
      have hunion := Finset.card_union_of_disjoint hdisj
      have hle : (S ∪ Bv).card ≤ n := by
        have := Finset.card_le_card (Finset.subset_univ (S ∪ Bv))
        simpa using this
      rw [hunion] at hle
      exact_mod_cast hle
    nlinarith
  have hcw_pos : 0 < G.cutWeight S := by
    have hT3 := lambda2_mul_le_cut G S hS_ne hS_proper
    have hconn' := hconn
    unfold WeightedGraph.Connected at hconn'
    have hcard_lt : S.card < n := by
      have h := Finset.card_lt_card (Finset.ssubset_univ_iff.mpr hS_proper)
      simpa using h
    have hA_pos : (0 : ℝ) < (S.card : ℝ) * ((n : ℝ) - S.card) := by
      have h1 : (0 : ℝ) < S.card := lt_of_lt_of_le hβn_pos hA_size
      have h2 : (S.card : ℝ) < n := Nat.cast_lt.mpr hcard_lt
      exact mul_pos h1 (by linarith)
    nlinarith [mul_pos hconn' hA_pos]
  have hden_pos : 0 < ∑ x ∈ X, G.weightedDegree x :=
    lt_of_lt_of_le hcw_pos hcw_le
  have hW_nn : 0 ≤ G.totalWeight :=
    Finset.sum_nonneg fun e _ => (G.weights_pos e).le
  refine le_trans ?_ (kappaPlus_ge_totalWeight G S hS_ne hS_proper hconn)
  have hnum : 2 * β * (1 - β) * G.totalWeight ≤
      2 * ((S.card : ℝ) / n) * (1 - (S.card : ℝ) / n) * G.totalWeight := by
    apply mul_le_mul_of_nonneg_right _ hW_nn
    nlinarith
  have hc_nonneg : 0 ≤ 2 * ((S.card : ℝ) / n) * (1 - (S.card : ℝ) / n) *
      G.totalWeight := by
    have h1 : (0 : ℝ) ≤ (S.card : ℝ) / n := le_trans hβ.le hγ_lo
    have h2 : (0 : ℝ) ≤ 1 - (S.card : ℝ) / n := by linarith
    positivity
  rw [div_le_div_iff₀ hden_pos hcw_pos]
  exact mul_le_mul hnum hcw_le hcw_pos.le hc_nonneg

end
