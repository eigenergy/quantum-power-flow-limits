/-
Copyright (c) 2026 Cameron Khanpour and Samuel Talkington. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Cameron Khanpour, Samuel Talkington
-/
import PowerFlowLimits.CutBounds
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting

/-!
# Theorem 1 (thm:separator) and Corollary 1 (cor:tw): separations force polynomial conditioning

Part of the Lean 4 formalization of
"The Limits of Quantum Computers for Power Flow" (Khanpour and Talkington).
-/

open Finset BigOperators
open Filter Asymptotics

noncomputable section

variable {n m : ℕ}

/-- The simple graph induced by buses outside a candidate separator bag. -/
def WeightedGraph.graphOff (G : WeightedGraph n m) (X : Finset (Fin n)) :
    SimpleGraph {v : Fin n // v ∉ X} :=
  G.toSimpleGraph.induce {v | v ∉ X}

/-- Original bus labels in one connected component after deleting `X`. -/
noncomputable def WeightedGraph.componentVerticesOff
    (G : WeightedGraph n m) (X : Finset (Fin n))
    (c : (G.graphOff X).ConnectedComponent) : Finset (Fin n) :=
  by
    classical
    exact Finset.univ.filter fun v ↦
      ∃ hv : v ∉ X, (G.graphOff X).connectedComponentMk ⟨v, hv⟩ = c

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
    (hconn : G.CombinatoriallyConnected) :
    2 * β * (1 - β) * G.totalWeight / (s * Δ * bmax) ≤
      effectiveConditionNumber G (fun _ => 1) := by
  change G.toSimpleGraph.Connected at hconn
  have hn : 0 < n := Fin.pos_iff_nonempty.mpr hconn.nonempty
  have hn_pos : (0 : ℝ) < n := by
    exact_mod_cast hn
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
  have hcard_lt : S.card < n := by
    have h := Finset.card_lt_card (Finset.ssubset_univ_iff.mpr hS_proper)
    simpa using h
  have hn2 : 1 < n := lt_of_le_of_lt (Finset.one_le_card.mpr hS_ne) hcard_lt
  have hspec := combinatoriallyConnected_implies_spectralConnected G hconn hn2
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
    have hconn' := hspec
    unfold WeightedGraph.Connected at hconn'
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
    have hconn' := hspec
    unfold WeightedGraph.Connected at hconn'
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

/-- Finite linear-growth consequence of Theorem 1. A connected graph supplies `m ≥ n - 1`,
while a positive lower bound `ρ` on mean-to-maximum branch weight supplies total stiffness. -/
theorem separator_kappa_linear_bound (G : WeightedGraph n m)
    (A X Bv : Finset (Fin n)) (s Δ bmax β ρ : ℝ)
    (hcover : A ∪ X ∪ Bv = Finset.univ)
    (hdisj : Disjoint (A ∪ X) Bv)
    (hnoAB : ∀ e, ¬(G.posEndpoint e ∈ A ∧ G.negEndpoint e ∈ Bv) ∧
      ¬(G.posEndpoint e ∈ Bv ∧ G.negEndpoint e ∈ A))
    (hX : (X.card : ℝ) ≤ s)
    (hdeg : ∀ i, ((G.incidentEdges i).card : ℝ) ≤ Δ)
    (hbmax : ∀ e, G.weights e ≤ bmax)
    (hs : 0 < s) (hΔ : 0 < Δ) (hbmax_pos : 0 < bmax)
    (hβ : 0 < β) (hβ' : β ≤ 1 / 2) (hρ : 0 < ρ)
    (hA_size : β * n ≤ ((A ∪ X).card : ℝ))
    (hB_size : β * n ≤ (Bv.card : ℝ))
    (hmean : ρ * (m : ℝ) * bmax ≤ G.totalWeight)
    (hconn : G.CombinatoriallyConnected) :
    β * (1 - β) * ρ / (s * Δ) * n ≤
      effectiveConditionNumber G (fun _ ↦ 1) := by
  have hn : 0 < n := Fin.pos_iff_nonempty.mpr hconn.nonempty
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
  have hβn_pos : (0 : ℝ) < β * n := mul_pos hβ hn_pos
  have hAX_card_pos : 0 < (A ∪ X).card := by
    exact_mod_cast lt_of_lt_of_le hβn_pos hA_size
  have hB_card_pos : 0 < Bv.card := by
    exact_mod_cast lt_of_lt_of_le hβn_pos hB_size
  have hcard_sum : (A ∪ X).card + Bv.card ≤ n := by
    rw [← Finset.card_union_of_disjoint hdisj]
    simpa using Finset.card_le_card (Finset.subset_univ ((A ∪ X) ∪ Bv))
  have hn_two : 2 ≤ n := by omega
  have hm_nat : n - 1 ≤ m := G.card_sub_one_le_edges hconn
  have hm_half : (n : ℝ) / 2 ≤ m := by
    have hm_real : ((n - 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast hm_nat
    have hn_two_real : (2 : ℝ) ≤ n := by exact_mod_cast hn_two
    rw [Nat.cast_sub (by omega), Nat.cast_one] at hm_real
    linarith
  have hweight_lower : ρ * ((n : ℝ) / 2) * bmax ≤ G.totalWeight := by
    calc
      ρ * ((n : ℝ) / 2) * bmax ≤ ρ * (m : ℝ) * bmax := by gcongr
      _ ≤ G.totalWeight := hmean
  have hden_pos : 0 < s * Δ * bmax := by positivity
  have hcoeff_nonneg : 0 ≤ 2 * β * (1 - β) := by nlinarith
  calc
    β * (1 - β) * ρ / (s * Δ) * n =
        2 * β * (1 - β) * (ρ * (n / 2) * bmax) / (s * Δ * bmax) := by
      field_simp
    _ ≤ 2 * β * (1 - β) * G.totalWeight / (s * Δ * bmax) := by
      rw [div_le_div_iff_of_pos_right hden_pos]
      exact mul_le_mul_of_nonneg_left hweight_lower hcoeff_nonneg
    _ ≤ effectiveConditionNumber G (fun _ ↦ 1) :=
      separator_kappa_bound G A X Bv s Δ bmax β hcover hdisj hnoAB hX
        hdeg hbmax hβ hβ' hA_size hB_size hconn

/-- A uniform positive linear lower bound is the standard `Ω(n)` relation. -/
theorem isBigOmega_natCast_of_eventually_linear_lower_bound
    (κ : ℕ → ℝ) (c : ℝ) (hc : 0 < c)
    (hκ : ∀ᶠ k : ℕ in atTop, c * k ≤ κ k) :
    (fun k : ℕ ↦ (k : ℝ)) =O[atTop] κ := by
  refine Asymptotics.isBigO_iff''.2 ⟨c, hc, ?_⟩
  filter_upwards [hκ] with k hk
  have hk_cast : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  have hκ_nonneg : 0 ≤ κ k := (mul_nonneg hc.le hk_cast).trans hk
  simpa [Real.norm_eq_abs, abs_of_nonneg hk_cast, abs_of_nonneg hκ_nonneg] using hk

/-- The family-level `Ω(n)` consequence for uniformly bounded balanced separators, maximum degree,
and mean-to-maximum branch weight ratio. This is the separator form of the letter's grid-family
claim, independent of how the separator was obtained. -/
theorem separator_family_isBigOmega_linear
    (edgeCount : ℕ → ℕ)
    (G : (k : ℕ) → WeightedGraph k (edgeCount k))
    (A X Bv : (k : ℕ) → Finset (Fin k))
    (N : ℕ) (s Δ bmax β ρ : ℝ)
    (hs : 0 < s) (hΔ : 0 < Δ) (hbmax_pos : 0 < bmax)
    (hβ : 0 < β) (hβ' : β ≤ 1 / 2) (hρ : 0 < ρ)
    (hcover : ∀ k : ℕ, N ≤ k → A k ∪ X k ∪ Bv k = Finset.univ)
    (hdisj : ∀ k : ℕ, N ≤ k → Disjoint (A k ∪ X k) (Bv k))
    (hnoAB : ∀ k : ℕ, N ≤ k → ∀ e,
      ¬((G k).posEndpoint e ∈ A k ∧ (G k).negEndpoint e ∈ Bv k) ∧
        ¬((G k).posEndpoint e ∈ Bv k ∧ (G k).negEndpoint e ∈ A k))
    (hX : ∀ k : ℕ, N ≤ k → ((X k).card : ℝ) ≤ s)
    (hdeg : ∀ k : ℕ, N ≤ k → ∀ i,
      (((G k).incidentEdges i).card : ℝ) ≤ Δ)
    (hbmax : ∀ k : ℕ, N ≤ k → ∀ e, (G k).weights e ≤ bmax)
    (hA_size : ∀ k : ℕ, N ≤ k → β * k ≤ ((A k ∪ X k).card : ℝ))
    (hB_size : ∀ k : ℕ, N ≤ k → β * k ≤ ((Bv k).card : ℝ))
    (hmean : ∀ k : ℕ, N ≤ k →
      ρ * (edgeCount k : ℝ) * bmax ≤ (G k).totalWeight)
    (hconn : ∀ k : ℕ, N ≤ k → (G k).CombinatoriallyConnected) :
    (fun k : ℕ ↦ (k : ℝ)) =O[atTop]
      (fun k ↦ effectiveConditionNumber (G k) (fun _ ↦ 1)) := by
  apply isBigOmega_natCast_of_eventually_linear_lower_bound _
    (β * (1 - β) * ρ / (s * Δ))
  · have : 0 < 1 - β := by linarith
    positivity
  · rw [Filter.eventually_atTop]
    refine ⟨N, fun k hk ↦ ?_⟩
    exact separator_kappa_linear_bound (G k) (A k) (X k) (Bv k) s Δ bmax β ρ
      (hcover k hk) (hdisj k hk) (hnoAB k hk) (hX k hk) (hdeg k hk)
      (hbmax k hk) hs hΔ hbmax_pos hβ hβ' hρ (hA_size k hk) (hB_size k hk)
      (hmean k hk) (hconn k hk)

/-- Greedy grouping lemma used in the treewidth corollary. If every component has size at most
`N/2` and their total size is at least `3N/4`, some subcollection has size in `[N/4, N/2]`. -/
theorem exists_quarter_half_subcollection {ι : Type*} [Fintype ι]
    (weight : ι → ℝ) (N : ℝ) (hN : 0 < N)
    (hweight_upper : ∀ i, weight i ≤ N / 2)
    (htotal : 3 * N / 4 ≤ ∑ i, weight i) :
    ∃ S : Finset ι, N / 4 ≤ ∑ i ∈ S, weight i ∧
      ∑ i ∈ S, weight i ≤ N / 2 := by
  classical
  let qualifying := Finset.univ.powerset.filter fun S ↦ N / 4 ≤ ∑ i ∈ S, weight i
  have huniv_mem : (Finset.univ : Finset ι) ∈ qualifying := by
    simp only [qualifying, Finset.mem_filter, Finset.mem_powerset,
      Finset.subset_univ, true_and]
    linarith
  obtain ⟨S, hS_mem, hS_min⟩ :=
    Finset.exists_min_image qualifying Finset.card ⟨Finset.univ, huniv_mem⟩
  have hS_lower : N / 4 ≤ ∑ i ∈ S, weight i := by
    simpa [qualifying] using hS_mem
  by_cases hlarge : ∃ i ∈ S, N / 4 ≤ weight i
  · obtain ⟨i, _, hi⟩ := hlarge
    refine ⟨{i}, ?_, ?_⟩
    · simpa using hi
    · simpa using hweight_upper i
  · push_neg at hlarge
    have hS_nonempty : S.Nonempty := by
      by_contra hS_empty
      rw [Finset.not_nonempty_iff_eq_empty.mp hS_empty] at hS_lower
      simp only [Finset.sum_empty] at hS_lower
      linarith
    obtain ⟨e, he⟩ := hS_nonempty
    have herase_not_mem : S.erase e ∉ qualifying := by
      intro herase_mem
      have hcard_min := hS_min (S.erase e) herase_mem
      have hcard_erase := Finset.card_erase_add_one he
      omega
    have herase_lt : ∑ i ∈ S.erase e, weight i < N / 4 := by
      by_contra hnot
      push_neg at hnot
      apply herase_not_mem
      simp [qualifying, hnot]
    have he_lt : weight e < N / 4 := hlarge e he
    have hsum := Finset.sum_erase_add S weight he
    refine ⟨S, hS_lower, ?_⟩
    linarith

/-- Grouping the components left after deleting a small bag produces the explicit quarter-balanced
separator partition used by Corollary 1(i). -/
theorem component_partition_has_quarter_separation (G : WeightedGraph n m)
    (X : Finset (Fin n)) (k : ℕ) (component : Fin k → Finset (Fin n))
    (hn : 0 < n)
    (hparts : ∀ ⦃i j⦄, i ≠ j → Disjoint (component i) (component j))
    (hXparts : ∀ i, Disjoint X (component i))
    (hcover : X ∪ Finset.univ.biUnion component = Finset.univ)
    (hX_quarter : (X.card : ℝ) ≤ (n : ℝ) / 4)
    (hcomponent_half : ∀ i, (component i).card ≤ n / 2)
    (hedge_component : ∀ e, G.posEndpoint e ∉ X → G.negEndpoint e ∉ X →
      ∃ i, G.posEndpoint e ∈ component i ∧ G.negEndpoint e ∈ component i) :
    ∃ A Bv : Finset (Fin n),
      A ∪ X ∪ Bv = Finset.univ ∧
      Disjoint (A ∪ X) Bv ∧
      (∀ e, ¬(G.posEndpoint e ∈ A ∧ G.negEndpoint e ∈ Bv) ∧
        ¬(G.posEndpoint e ∈ Bv ∧ G.negEndpoint e ∈ A)) ∧
      (n : ℝ) / 4 ≤ ((A ∪ X).card : ℝ) ∧
      (n : ℝ) / 4 ≤ (Bv.card : ℝ) := by
  classical
  have hpairwise (I : Finset (Fin k)) : (I : Set (Fin k)).PairwiseDisjoint component := by
    intro i _ j _ hij
    exact hparts hij
  have hX_union : Disjoint X (Finset.univ.biUnion component) := by
    rw [Finset.disjoint_left]
    intro v hvX hvUnion
    obtain ⟨i, _, hvi⟩ := Finset.mem_biUnion.mp hvUnion
    exact Finset.disjoint_left.mp (hXparts i) hvX hvi
  have hcard_cover_nat : X.card + (Finset.univ.biUnion component).card = n := by
    rw [← Finset.card_union_of_disjoint hX_union, hcover, Finset.card_univ,
      Fintype.card_fin]
  have hcard_components : (Finset.univ.biUnion component).card =
      ∑ i, (component i).card :=
    Finset.card_biUnion (hpairwise Finset.univ)
  have htotal : 3 * (n : ℝ) / 4 ≤ ∑ i, ((component i).card : ℝ) := by
    have hcard_cover : (X.card : ℝ) + ((Finset.univ.biUnion component).card : ℝ) = n := by
      exact_mod_cast hcard_cover_nat
    have hcast_sum : ((∑ i, (component i).card : ℕ) : ℝ) =
        ∑ i, ((component i).card : ℝ) := by push_cast; rfl
    rw [hcard_components] at hcard_cover
    rw [hcast_sum] at hcard_cover
    linarith
  have hcomponent_half_real : ∀ i, ((component i).card : ℝ) ≤ (n : ℝ) / 2 := by
    intro i
    have hi := hcomponent_half i
    have hn_even_bound : (2 * (component i).card : ℕ) ≤ n := by omega
    have hn_even_bound_real : (2 : ℝ) * (component i).card ≤ n := by
      exact_mod_cast hn_even_bound
    linarith
  obtain ⟨I, hI_lower, hI_upper⟩ := exists_quarter_half_subcollection
    (fun i ↦ ((component i).card : ℝ)) n (by exact_mod_cast hn)
    hcomponent_half_real htotal
  let Bv := I.biUnion component
  let A := Finset.univ \ (X ∪ Bv)
  have hB_card_nat : Bv.card = ∑ i ∈ I, (component i).card :=
    Finset.card_biUnion (hpairwise I)
  have hB_card : (Bv.card : ℝ) = ∑ i ∈ I, ((component i).card : ℝ) := by
    rw [hB_card_nat]
    push_cast
    rfl
  have hXB : Disjoint X Bv := by
    rw [Finset.disjoint_left]
    intro v hvX hvB
    obtain ⟨i, _, hvi⟩ := Finset.mem_biUnion.mp hvB
    exact Finset.disjoint_left.mp (hXparts i) hvX hvi
  have hcover_AB : A ∪ X ∪ Bv = Finset.univ := by
    ext v
    simp only [A, Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and, iff_true]
    tauto
  have hdisj_AB : Disjoint (A ∪ X) Bv := by
    rw [Finset.disjoint_left]
    intro v hvAX hvB
    rcases Finset.mem_union.mp hvAX with hvA | hvX
    · exact (Finset.mem_sdiff.mp hvA).2 (Finset.mem_union.mpr (Or.inr hvB))
    · exact Finset.disjoint_left.mp hXB hvX hvB
  have hnoAB : ∀ e,
      ¬(G.posEndpoint e ∈ A ∧ G.negEndpoint e ∈ Bv) ∧
        ¬(G.posEndpoint e ∈ Bv ∧ G.negEndpoint e ∈ A) := by
    intro e
    constructor
    · rintro ⟨hposA, hnegB⟩
      have hposX : G.posEndpoint e ∉ X := by
        intro h
        exact (Finset.mem_sdiff.mp hposA).2 (Finset.mem_union.mpr (Or.inl h))
      have hnegX : G.negEndpoint e ∉ X :=
        fun h ↦ Finset.disjoint_left.mp hXB h hnegB
      obtain ⟨c, hposc, hnegc⟩ := hedge_component e hposX hnegX
      obtain ⟨i, hiI, hnegi⟩ := Finset.mem_biUnion.mp hnegB
      have hci : c = i := by
        by_contra hne
        exact Finset.disjoint_left.mp (hparts hne) hnegc hnegi
      have hposB : G.posEndpoint e ∈ Bv :=
        Finset.mem_biUnion.mpr ⟨i, hiI, hci ▸ hposc⟩
      exact (Finset.mem_sdiff.mp hposA).2 (Finset.mem_union.mpr (Or.inr hposB))
    · rintro ⟨hposB, hnegA⟩
      have hposX : G.posEndpoint e ∉ X :=
        fun h ↦ Finset.disjoint_left.mp hXB h hposB
      have hnegX : G.negEndpoint e ∉ X := by
        intro h
        exact (Finset.mem_sdiff.mp hnegA).2 (Finset.mem_union.mpr (Or.inl h))
      obtain ⟨c, hposc, hnegc⟩ := hedge_component e hposX hnegX
      obtain ⟨i, hiI, hposi⟩ := Finset.mem_biUnion.mp hposB
      have hci : c = i := by
        by_contra hne
        exact Finset.disjoint_left.mp (hparts hne) hposc hposi
      have hnegB : G.negEndpoint e ∈ Bv :=
        Finset.mem_biUnion.mpr ⟨i, hiI, hci ▸ hnegc⟩
      exact (Finset.mem_sdiff.mp hnegA).2 (Finset.mem_union.mpr (Or.inr hnegB))
  have hA_size : (n : ℝ) / 4 ≤ ((A ∪ X).card : ℝ) := by
    have hcard_nat : (A ∪ X).card + Bv.card = n := by
      rw [← Finset.card_union_of_disjoint hdisj_AB, hcover_AB, Finset.card_univ,
        Fintype.card_fin]
    have hcard : ((A ∪ X).card : ℝ) + (Bv.card : ℝ) = n := by
      exact_mod_cast hcard_nat
    rw [hB_card] at hcard
    linarith
  refine ⟨A, Bv, hcover_AB, hdisj_AB, hnoAB, hA_size, ?_⟩
  rw [hB_card]
  exact hI_lower

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
    (hconn : G.CombinatoriallyConnected) :
    3 / 8 * G.totalWeight / ((τ + 1) * Δ * bmax) ≤
      effectiveConditionNumber G (fun _ => 1) := by
  have h := separator_kappa_bound G A X Bv (τ + 1) Δ bmax (1 / 4)
    hcover hdisj hnoAB hX hdeg hbmax (by norm_num) (by norm_num)
    (by linarith) (by linarith) hconn
  calc 3 / 8 * G.totalWeight / ((τ + 1) * Δ * bmax)
      = 2 * (1 / 4) * (1 - 1 / 4) * G.totalWeight / ((τ + 1) * Δ * bmax) := by
        ring
    _ ≤ effectiveConditionNumber G (fun _ => 1) := h

/-- Corollary 1(i) from a small bag and the component partition left by deleting it. The remaining
external dependency is the tree-decomposition theorem producing such a bag. -/
theorem treewidth_kappa_bound_of_component_partition (G : WeightedGraph n m)
    (X : Finset (Fin n)) (k : ℕ) (component : Fin k → Finset (Fin n))
    (τ Δ bmax : ℝ) (hn : 0 < n)
    (hparts : ∀ ⦃i j⦄, i ≠ j → Disjoint (component i) (component j))
    (hXparts : ∀ i, Disjoint X (component i))
    (hcover : X ∪ Finset.univ.biUnion component = Finset.univ)
    (hX_tau : (X.card : ℝ) ≤ τ + 1)
    (hX_quarter : (X.card : ℝ) ≤ (n : ℝ) / 4)
    (hcomponent_half : ∀ i, (component i).card ≤ n / 2)
    (hedge_component : ∀ e, G.posEndpoint e ∉ X → G.negEndpoint e ∉ X →
      ∃ i, G.posEndpoint e ∈ component i ∧ G.negEndpoint e ∈ component i)
    (hdeg : ∀ i, ((G.incidentEdges i).card : ℝ) ≤ Δ)
    (hbmax : ∀ e, G.weights e ≤ bmax)
    (hconn : G.CombinatoriallyConnected) :
    3 / 8 * G.totalWeight / ((τ + 1) * Δ * bmax) ≤
      effectiveConditionNumber G (fun _ ↦ 1) := by
  obtain ⟨A, Bv, hcover', hdisj, hnoAB, hA_size, hB_size⟩ :=
    component_partition_has_quarter_separation G X k component hn hparts hXparts
      hcover hX_quarter hcomponent_half hedge_component
  exact treewidth_kappa_bound G A X Bv τ Δ bmax hcover' hdisj hnoAB hX_tau
    hdeg hbmax hA_size hB_size hconn

/-- Corollary 1(i) from one balanced bag. Connected components of the graph after deleting the bag
are constructed from mathlib's quotient by reachability, so disjointness, cover, and the absence of
cross-component branches are proved here rather than supplied as hypotheses. -/
theorem treewidth_kappa_bound_of_balanced_bag (G : WeightedGraph n m)
    (X : Finset (Fin n)) (τ Δ bmax : ℝ) (hn : 0 < n)
    (hX_tau : (X.card : ℝ) ≤ τ + 1)
    (hX_quarter : (X.card : ℝ) ≤ (n : ℝ) / 4)
    (hcomponent_half : ∀ c : (G.graphOff X).ConnectedComponent,
      (G.componentVerticesOff X c).card ≤ n / 2)
    (hdeg : ∀ i, ((G.incidentEdges i).card : ℝ) ≤ Δ)
    (hbmax : ∀ e, G.weights e ≤ bmax)
    (hconn : G.CombinatoriallyConnected) :
    3 / 8 * G.totalWeight / ((τ + 1) * Δ * bmax) ≤
      effectiveConditionNumber G (fun _ ↦ 1) := by
  classical
  let H := G.graphOff X
  let equivComponent : H.ConnectedComponent ≃ Fin (Fintype.card H.ConnectedComponent) :=
    Fintype.equivFin H.ConnectedComponent
  let component : Fin (Fintype.card H.ConnectedComponent) → Finset (Fin n) :=
    fun i ↦ G.componentVerticesOff X (equivComponent.symm i)
  have hparts : ∀ ⦃i j⦄, i ≠ j → Disjoint (component i) (component j) := by
    intro i j hij
    rw [Finset.disjoint_left]
    intro v hvi hvj
    simp only [component, WeightedGraph.componentVerticesOff, Finset.mem_filter,
      Finset.mem_univ, true_and] at hvi hvj
    obtain ⟨hviX, hi⟩ := hvi
    obtain ⟨_, hj⟩ := hvj
    have hc : equivComponent.symm i = equivComponent.symm j := hi.symm.trans hj
    exact hij (equivComponent.symm.injective hc)
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
      let i : Fin (Fintype.card H.ConnectedComponent) := equivComponent c
      refine ⟨i, Finset.mem_univ i, ?_⟩
      change v ∈ G.componentVerticesOff X (equivComponent.symm i)
      unfold WeightedGraph.componentVerticesOff
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨hvX, ?_⟩
      simp [H, i, c]
  have hcomponent_half' : ∀ i, (component i).card ≤ n / 2 :=
    fun i ↦ hcomponent_half (equivComponent.symm i)
  have hedge_component : ∀ e, G.posEndpoint e ∉ X → G.negEndpoint e ∉ X →
      ∃ i, G.posEndpoint e ∈ component i ∧ G.negEndpoint e ∈ component i := by
    intro e hposX hnegX
    let u : {v : Fin n // v ∉ X} := ⟨G.posEndpoint e, hposX⟩
    let v : {v : Fin n // v ∉ X} := ⟨G.negEndpoint e, hnegX⟩
    have huv : H.Adj u v := ⟨e, Or.inl ⟨rfl, rfl⟩⟩
    let c : H.ConnectedComponent := H.connectedComponentMk u
    let i : Fin (Fintype.card H.ConnectedComponent) := equivComponent c
    refine ⟨i, ?_, ?_⟩
    · change G.posEndpoint e ∈ G.componentVerticesOff X (equivComponent.symm i)
      unfold WeightedGraph.componentVerticesOff
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨hposX, ?_⟩
      simp [H, i, c, u]
    · have hcomp : H.connectedComponentMk v = H.connectedComponentMk u :=
        (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj huv).symm
      change G.negEndpoint e ∈ G.componentVerticesOff X (equivComponent.symm i)
      unfold WeightedGraph.componentVerticesOff
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨hnegX, ?_⟩
      simpa [H, i, c, v, u] using hcomp
  exact treewidth_kappa_bound_of_component_partition G X
    (Fintype.card H.ConnectedComponent) component τ Δ bmax hn hparts hXparts hcover
    hX_tau hX_quarter hcomponent_half' hedge_component hdeg hbmax hconn

/-- The numerical threshold in the planar part of Corollary 1. -/
theorem sqrt_eight_mul_card_le_sixth (n : ℕ) (hn : 288 ≤ n) :
    Real.sqrt (8 * n) ≤ (n : ℝ) / 6 := by
  have hn_real : (288 : ℝ) ≤ n := by exact_mod_cast hn
  have hn_nonneg : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hsqrt_nonneg : 0 ≤ Real.sqrt (8 * (n : ℝ)) := Real.sqrt_nonneg _
  have hsqrt_sq : (Real.sqrt (8 * (n : ℝ))) ^ 2 = 8 * n := by
    rw [Real.sq_sqrt]
    positivity
  have hprod : 0 ≤ (n : ℝ) * ((n : ℝ) - 288) :=
    mul_nonneg hn_nonneg (sub_nonneg.mpr hn_real)
  nlinarith

/-- Corollary 1(ii) (cor:tw), spectral content: a (√(8n), 1/6)-separation
    gives κ₊(B) ≥ (5/18)·b(E)/(√(8n)·Δ·b_max). The planar separator theorem
    (Lipton–Tarjan) producing such a separation for planar graphs with
    n ≥ 288 is not available in mathlib and enters through the separation
    hypotheses. -/
theorem kappa_bound_of_sqrt_separator_partition (G : WeightedGraph n m)
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
    (hconn : G.CombinatoriallyConnected) :
    5 / 18 * G.totalWeight / (Real.sqrt (8 * n) * Δ * bmax) ≤
      effectiveConditionNumber G (fun _ => 1) := by
  have h := separator_kappa_bound G A X Bv (Real.sqrt (8 * n)) Δ bmax (1 / 6)
    hcover hdisj hnoAB hX hdeg hbmax (by norm_num) (by norm_num)
    (by linarith) (by linarith) hconn
  calc 5 / 18 * G.totalWeight / (Real.sqrt (8 * n) * Δ * bmax)
      = 2 * (1 / 6) * (1 - 1 / 6) * G.totalWeight /
        (Real.sqrt (8 * n) * Δ * bmax) := by ring
    _ ≤ effectiveConditionNumber G (fun _ => 1) := h

/-- Corollary 1(ii) from the quantitative output of a Lipton--Tarjan partition. The planar
separator existence theorem itself remains an external graph-theoretic dependency. -/
theorem planar_kappa_bound_of_lipton_partition (G : WeightedGraph n m)
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
    5 / 18 * G.totalWeight / (Real.sqrt (8 * n) * Δ * bmax) ≤
      effectiveConditionNumber G (fun _ ↦ 1) := by
  have hcard_nat : (A ∪ X).card + Bv.card = n := by
    rw [← Finset.card_union_of_disjoint hdisj, hcover, Finset.card_univ,
      Fintype.card_fin]
  have hcard : ((A ∪ X).card : ℝ) + (Bv.card : ℝ) = n := by
    exact_mod_cast hcard_nat
  have hA_size : (n : ℝ) / 6 ≤ ((A ∪ X).card : ℝ) := by
    linarith
  have hX_sixth : (X.card : ℝ) ≤ (n : ℝ) / 6 :=
    hX.trans (sqrt_eight_mul_card_le_sixth n hn)
  have hunion_le_nat : (A ∪ X).card ≤ A.card + X.card := Finset.card_union_le A X
  have hunion_le : ((A ∪ X).card : ℝ) ≤ (A.card : ℝ) + X.card := by
    exact_mod_cast hunion_le_nat
  have hB_size : (n : ℝ) / 6 ≤ (Bv.card : ℝ) := by
    linarith
  exact kappa_bound_of_sqrt_separator_partition G A X Bv Δ bmax hcover hdisj hnoAB hX
    hdeg hbmax
    hA_size hB_size hconn

/-- Near-planar extension (remark after cor:tw): planarizing c line crossings and applying the
    vertex-cost form of Lipton–Tarjan yields balanced separators of size ≤ 2√(8(n+c)), so part (ii)
    persists up to constants. As with
    Corollary 1, the separator existence is hypothesized. -/
theorem kappa_bound_of_near_planar_partition (G : WeightedGraph n m)
    (A X Bv : Finset (Fin n)) (Δ bmax c : ℝ)
    (hcover : A ∪ X ∪ Bv = Finset.univ)
    (hdisj : Disjoint (A ∪ X) Bv)
    (hnoAB : ∀ e, ¬(G.posEndpoint e ∈ A ∧ G.negEndpoint e ∈ Bv) ∧
      ¬(G.posEndpoint e ∈ Bv ∧ G.negEndpoint e ∈ A))
    (hX : (X.card : ℝ) ≤ 2 * Real.sqrt (8 * ((n : ℝ) + c)))
    (hdeg : ∀ i, ((G.incidentEdges i).card : ℝ) ≤ Δ)
    (hbmax : ∀ e, G.weights e ≤ bmax)
    (hA_size : (n : ℝ) / 6 ≤ ((A ∪ X).card : ℝ))
    (hB_size : (n : ℝ) / 6 ≤ (Bv.card : ℝ))
    (hconn : G.CombinatoriallyConnected) :
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

end
