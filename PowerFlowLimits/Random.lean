import PowerFlowLimits.Separators
import Mathlib.Probability.Moments.SubGaussian

/-!
# Proposition 2 (prop:random): pathwise ill-conditioning with random susceptances

Part of the Lean 4 formalization of
"The Limits of Quantum Computers for Power Flow" (Khanpour and Talkington).
-/

open Finset BigOperators

noncomputable section

variable {n m : ℕ}

/-- Same topology, new branch susceptances. -/
def WeightedGraph.withWeights (G : WeightedGraph n m) (w : Fin m → ℝ)
    (hw : ∀ e, 0 < w e) : WeightedGraph n m :=
  { G with weights := w, weights_pos := hw }

/-- Proposition 2 (prop:random): pathwise ill-conditioning with random
    susceptances. Fix the topology of `G` (its own weights are irrelevant) with
    an (s,β)-separation, and let the branch susceptances `w e` be independent
    random variables in `(0, b_max]`. Writing `M = Σ_e E[w e]` (so `M = m·μ̄`
    in the paper's notation), with probability at least
    `1 - exp(-2ε²M²/(m·b_max²)) = 1 - exp(-2ε²mμ̄²/b_max²)` the effective
    condition number is at least `2β(1-β)(1-ε)M/(s·Δ·b_max)`.
    Boundedness enters through Hoeffding's lemma (mathlib's sub-Gaussian API);
    the cut estimate holds pathwise via `separator_kappa_bound`. Connectivity
    of the fixed topology is assumed per outcome, and `0 < s·Δ·b_max`,
    `0 < m` are recorded as explicit regularity hypotheses. -/
theorem random_kappa_bound {Ωs : Type*} [MeasurableSpace Ωs]
    (μ : MeasureTheory.Measure Ωs) [MeasureTheory.IsProbabilityMeasure μ]
    (G : WeightedGraph n m) (hm : 0 < m)
    (w : Fin m → Ωs → ℝ)
    (hw_meas : ∀ e, Measurable (w e))
    (hw_indep : ProbabilityTheory.iIndepFun w μ)
    (bmax : ℝ) (hw_mem : ∀ ω, ∀ e, w e ω ∈ Set.Ioc 0 bmax)
    (A X Bv : Finset (Fin n)) (s Δ β ε : ℝ)
    (hcover : A ∪ X ∪ Bv = Finset.univ)
    (hdisj : Disjoint (A ∪ X) Bv)
    (hnoAB : ∀ e, ¬(G.posEndpoint e ∈ A ∧ G.negEndpoint e ∈ Bv) ∧
      ¬(G.posEndpoint e ∈ Bv ∧ G.negEndpoint e ∈ A))
    (hX : (X.card : ℝ) ≤ s)
    (hdeg : ∀ i, ((G.incidentEdges i).card : ℝ) ≤ Δ)
    (hβ : 0 < β) (hβ' : β ≤ 1 / 2)
    (hA_size : β * n ≤ ((A ∪ X).card : ℝ)) (hB_size : β * n ≤ (Bv.card : ℝ))
    (hden : 0 < s * Δ * bmax)
    (hε : 0 < ε) (_hε' : ε < 1)
    (hconn : ∀ ω, (G.withWeights (fun e => w e ω)
      (fun e => (hw_mem ω e).1)).Connected (fun _ => 1)) :
    1 - Real.exp (-2 * ε ^ 2 * (∑ e, ∫ ω, w e ω ∂μ) ^ 2 / (m * bmax ^ 2)) ≤
      μ.real {ω | 2 * β * (1 - β) * ((1 - ε) * (∑ e, ∫ ω', w e ω' ∂μ)) /
        (s * Δ * bmax) ≤
        effectiveConditionNumber
          (G.withWeights (fun e => w e ω) (fun e => (hw_mem ω e).1))
          (fun _ => 1)} := by
  classical
  set M : ℝ := ∑ e, ∫ ω, w e ω ∂μ with hM_def
  -- ambient facts
  have hΩ : Nonempty Ωs := by
    by_contra h
    rw [not_nonempty_iff] at h
    have h1 : μ Set.univ = 1 := MeasureTheory.measure_univ
    rw [Set.univ_eq_empty_iff.mpr h] at h1
    simp at h1
  obtain ⟨ω₀⟩ := hΩ
  have hbmax_pos : 0 < bmax :=
    lt_of_lt_of_le (hw_mem ω₀ ⟨0, hm⟩).1 (hw_mem ω₀ ⟨0, hm⟩).2
  have hm_pos : (0 : ℝ) < m := by exact_mod_cast hm
  have hE_nn : ∀ e, 0 ≤ ∫ ω, w e ω ∂μ := fun e =>
    MeasureTheory.integral_nonneg fun ω => (hw_mem ω e).1.le
  have hM_nn : 0 ≤ M := Finset.sum_nonneg fun e _ => hE_nn e
  -- centered negated susceptances are sub-Gaussian (Hoeffding's lemma)
  set Y : Fin m → Ωs → ℝ := fun e ω => (∫ ω', w e ω' ∂μ) - w e ω with hY_def
  have hY_indep : ProbabilityTheory.iIndepFun Y μ :=
    hw_indep.comp (fun e => fun x => (∫ ω', w e ω' ∂μ) - x)
      (fun e => measurable_const.sub measurable_id)
  have hY_subG : ∀ e ∈ (Finset.univ : Finset (Fin m)),
      ProbabilityTheory.HasSubgaussianMGF (Y e) ((‖bmax‖₊ / 2) ^ 2) μ := by
    intro e _
    have hneg_mem : ∀ᵐ ω ∂μ, -(w e ω) ∈ Set.Icc (-bmax) 0 :=
      MeasureTheory.ae_of_all _ fun ω =>
        ⟨neg_le_neg (hw_mem ω e).2, neg_nonpos.mpr (hw_mem ω e).1.le⟩
    have h := ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc
      (X := fun ω => -(w e ω)) ((hw_meas e).neg.aemeasurable) hneg_mem
    have hc : ((‖(0 : ℝ) - -bmax‖₊ / 2) ^ 2 : NNReal) = (‖bmax‖₊ / 2) ^ 2 := by
      norm_num
    rw [hc] at h
    have hfun : (fun ω => -(w e ω) - ∫ ω', -(w e ω') ∂μ) = Y e := by
      funext ω
      rw [MeasureTheory.integral_neg]
      simp only [hY_def]
      ring
    rwa [hfun] at h
  -- Hoeffding tail bound for the total susceptance
  have hHoeff := ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun
    hY_indep hY_subG (ε := ε * M) (mul_nonneg hε.le hM_nn)
  have hsum_c : ((∑ _e : Fin m, ((‖bmax‖₊ / 2) ^ 2 : NNReal) : NNReal) : ℝ) =
      m * (bmax / 2) ^ 2 := by
    push_cast
    rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    rw [Real.norm_eq_abs, abs_of_pos hbmax_pos]
  have hexp_eq : -(ε * M) ^ 2 /
      (2 * ((∑ _e : Fin m, ((‖bmax‖₊ / 2) ^ 2 : NNReal) : NNReal) : ℝ)) =
      -2 * ε ^ 2 * M ^ 2 / (m * bmax ^ 2) := by
    rw [hsum_c]
    field_simp
  rw [hexp_eq] at hHoeff
  -- lower tail on Σw is contained in the upper tail on ΣY
  have hsubset1 : {ω | (∑ e, w e ω) < (1 - ε) * M} ⊆
      {ω | ε * M ≤ ∑ e, Y e ω} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    have hsum : ∑ e, Y e ω = M - ∑ e, w e ω := by
      simp only [hY_def, hM_def]
      rw [Finset.sum_sub_distrib]
    linarith
  have htail : μ.real {ω | (∑ e, w e ω) < (1 - ε) * M} ≤
      Real.exp (-2 * ε ^ 2 * M ^ 2 / (m * bmax ^ 2)) :=
    le_trans (MeasureTheory.measureReal_mono hsubset1) hHoeff
  -- pathwise: enough total susceptance forces the κ₊ bound
  have hsubset2 : {ω | (1 - ε) * M ≤ ∑ e, w e ω} ⊆
      {ω | 2 * β * (1 - β) * ((1 - ε) * M) / (s * Δ * bmax) ≤
        effectiveConditionNumber
          (G.withWeights (fun e => w e ω) (fun e => (hw_mem ω e).1))
          (fun _ => 1)} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    have hGω := separator_kappa_bound
      (G.withWeights (fun e => w e ω) (fun e => (hw_mem ω e).1))
      A X Bv s Δ bmax β hcover hdisj hnoAB hX hdeg
      (fun e => (hw_mem ω e).2) hβ hβ' hA_size hB_size (hconn ω)
    refine le_trans ?_ hGω
    have htw : (G.withWeights (fun e => w e ω)
        (fun e => (hw_mem ω e).1)).totalWeight = ∑ e, w e ω := rfl
    rw [htw, div_le_div_iff₀ hden hden]
    have hnum : 2 * β * (1 - β) * ((1 - ε) * M) ≤
        2 * β * (1 - β) * (∑ e, w e ω) := by
      apply mul_le_mul_of_nonneg_left hω
      have h1β : 0 ≤ 1 - β := by linarith
      have h2β : 0 ≤ 2 * β := by linarith
      exact mul_nonneg h2β h1β
    exact mul_le_mul_of_nonneg_right hnum hden.le
  -- assemble the probability bound
  have hW_meas : Measurable fun ω => ∑ e, w e ω :=
    Finset.measurable_sum _ fun e _ => hw_meas e
  have hmeas_lt : MeasurableSet {ω | (∑ e, w e ω) < (1 - ε) * M} :=
    measurableSet_lt hW_meas measurable_const
  have hcompl := MeasureTheory.measureReal_add_measureReal_compl (μ := μ) hmeas_lt
  have hclt : {ω | (∑ e, w e ω) < (1 - ε) * M}ᶜ =
      {ω | (1 - ε) * M ≤ ∑ e, w e ω} := by
    ext ω
    simp [not_lt]
  calc 1 - Real.exp (-2 * ε ^ 2 * M ^ 2 / (m * bmax ^ 2))
      ≤ 1 - μ.real {ω | (∑ e, w e ω) < (1 - ε) * M} := by linarith
    _ = μ.real {ω | (1 - ε) * M ≤ ∑ e, w e ω} := by
        rw [← hclt]
        have huniv : μ.real Set.univ = 1 := by
          simp [MeasureTheory.measureReal_def]
        linarith
    _ ≤ _ := MeasureTheory.measureReal_mono hsubset2

end
