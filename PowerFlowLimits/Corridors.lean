import PowerFlowLimits.CutBounds

/-!
# Proposition 1 (prop:corridor): corridors imply quadratic conditioning

Part of the Lean 4 formalization of
"The Limits of Quantum Computers for Power Flow" (Khanpour and Talkington).
-/

open Finset BigOperators

noncomputable section

variable {n m : ℕ}

/-- Proposition 1 (prop:corridor): corridors imply quadratic conditioning.
    `V = V_S ⊔ P ⊔ V_T` where `P = p_0 … p_{ℓ-1}` is a corridor: `EP` collects
    the ℓ-1 consecutive path branches, and every non-path branch lives
    entirely on the `V_S ∪ {p_0}` side or the `V_T ∪ {p_{ℓ-1}}` side (this
    encodes the paper's degree-two interior and endpoint attachment). If both
    bulk sides have ≥ βn nodes, then κ₊(B) ≥ 2β²(ℓ-1)²·b(E)/b(E_P).
    Test vector: -1 on V_S, +1 on V_T, linear ramp along the corridor. -/
theorem corridor_kappa_bound (G : WeightedGraph n m)
    (VS VT : Finset (Fin n)) (ℓ : ℕ) (hl : 2 ≤ ℓ)
    (p : Fin ℓ → Fin n) (EP : Finset (Fin m)) (β : ℝ)
    (hp_inj : Function.Injective p)
    (hdisjS : ∀ i, p i ∉ VS) (hdisjT : ∀ i, p i ∉ VT)
    (hST : Disjoint VS VT)
    (hpath : ∀ e ∈ EP, ∃ i : Fin ℓ, ∃ h : i.val + 1 < ℓ,
      (G.posEndpoint e = p i ∧ G.negEndpoint e = p ⟨i.val + 1, h⟩) ∨
      (G.posEndpoint e = p ⟨i.val + 1, h⟩ ∧ G.negEndpoint e = p i))
    (hnonpath : ∀ e ∉ EP,
      ((G.posEndpoint e ∈ VS ∨ G.posEndpoint e = p ⟨0, by omega⟩) ∧
       (G.negEndpoint e ∈ VS ∨ G.negEndpoint e = p ⟨0, by omega⟩)) ∨
      ((G.posEndpoint e ∈ VT ∨ G.posEndpoint e = p ⟨ℓ - 1, by omega⟩) ∧
       (G.negEndpoint e ∈ VT ∨ G.negEndpoint e = p ⟨ℓ - 1, by omega⟩)))
    (hβ : 0 < β)
    (hVS_size : β * n ≤ (VS.card : ℝ)) (hVT_size : β * n ≤ (VT.card : ℝ))
    (hconn : G.Connected (fun _ => 1)) :
    2 * β ^ 2 * ((ℓ : ℝ) - 1) ^ 2 * G.totalWeight / (∑ e ∈ EP, G.weights e) ≤
      effectiveConditionNumber G (fun _ => 1) := by
  classical
  have hn2 : 1 < n := hconn.one_lt
  have hn_pos : (0 : ℝ) < n := by
    have : (0 : ℕ) < n := by omega
    exact_mod_cast this
  have hβn_pos : (0 : ℝ) < β * n := mul_pos hβ hn_pos
  have hL_pos : (0 : ℝ) < (ℓ : ℝ) - 1 := by
    have : (2 : ℝ) ≤ ℓ := by exact_mod_cast hl
    linarith
  -- the ramp potential: -1 on V_S, +1 on V_T, linear along the corridor
  set x : Fin n → ℝ := fun v =>
    if h : ∃ i : Fin ℓ, p i = v then
      -1 + 2 * ((Classical.choose h : Fin ℓ) : ℝ) / ((ℓ : ℝ) - 1)
    else if v ∈ VS then -1 else 1
    with hx_def
  have hx_path : ∀ i : Fin ℓ, x (p i) = -1 + 2 * (i : ℝ) / ((ℓ : ℝ) - 1) := by
    intro i
    have hex : ∃ j : Fin ℓ, p j = p i := ⟨i, rfl⟩
    have hch : Classical.choose hex = i := hp_inj (Classical.choose_spec hex)
    simp only [hx_def]
    rw [dif_pos hex, hch]
  have hx_VS : ∀ v ∈ VS, x v = -1 := by
    intro v hv
    have hnex : ¬∃ i : Fin ℓ, p i = v := by
      rintro ⟨i, rfl⟩
      exact hdisjS i hv
    simp only [hx_def]
    rw [dif_neg hnex, if_pos hv]
  have hx_VT : ∀ v ∈ VT, x v = 1 := by
    intro v hv
    have hnex : ¬∃ i : Fin ℓ, p i = v := by
      rintro ⟨i, rfl⟩
      exact hdisjT i hv
    have hvS : v ∉ VS := Finset.disjoint_right.mp hST hv
    simp only [hx_def]
    rw [dif_neg hnex, if_neg hvS]
  have hx_p0 : x (p ⟨0, by omega⟩) = -1 := by
    rw [hx_path]
    have h0 : ((⟨0, by omega⟩ : Fin ℓ) : ℝ) = 0 := by simp
    rw [h0]
    ring
  have hx_plast : x (p ⟨ℓ - 1, by omega⟩) = 1 := by
    rw [hx_path]
    have h1 : ((⟨ℓ - 1, by omega⟩ : Fin ℓ) : ℝ) = (ℓ : ℝ) - 1 := by
      have h2 : ((ℓ - 1 : ℕ) : ℝ) = (ℓ : ℝ) - 1 := by
        rw [Nat.cast_sub (show 1 ≤ ℓ by omega), Nat.cast_one]
      simpa using h2
    rw [h1]
    field_simp
    norm_num
  have hval_S : ∀ v, (v ∈ VS ∨ v = p ⟨0, by omega⟩) → x v = -1 := by
    rintro v (hv | rfl)
    · exact hx_VS v hv
    · exact hx_p0
  have hval_T : ∀ v, (v ∈ VT ∨ v = p ⟨ℓ - 1, by omega⟩) → x v = 1 := by
    rintro v (hv | rfl)
    · exact hx_VT v hv
    · exact hx_plast
  have hvd_nonpath : ∀ e ∉ EP, voltageDrop G x e = 0 := by
    intro e he
    rw [voltageDrop_eq_endpoint_diff]
    rcases hnonpath e he with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [hval_S _ h1, hval_S _ h2]; ring
    · rw [hval_T _ h1, hval_T _ h2]; ring
  have hvd_path : ∀ e ∈ EP, (voltageDrop G x e) ^ 2 = 4 / ((ℓ : ℝ) - 1) ^ 2 := by
    intro e he
    obtain ⟨i, hi, hor⟩ := hpath e he
    have hcast : ((⟨i.val + 1, hi⟩ : Fin ℓ) : ℝ) = (i : ℝ) + 1 := by
      simp
    rcases hor with ⟨hpos, hneg⟩ | ⟨hpos, hneg⟩ <;>
      rw [voltageDrop_eq_endpoint_diff, hpos, hneg, hx_path, hx_path,
        hcast] <;>
      · field_simp
        ring
  -- edge sum: only corridor branches contribute
  set bEP : ℝ := ∑ e ∈ EP, G.weights e with hbEP_def
  have hbEP_nn : 0 ≤ bEP := Finset.sum_nonneg fun e _ => (G.weights_pos e).le
  have hQx : ∑ e, 1 * G.weights e * (voltageDrop G x e) ^ 2 =
      4 / ((ℓ : ℝ) - 1) ^ 2 * bEP := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ EP)]
    have hfilter_mem : Finset.univ.filter (· ∈ EP) = EP := by
      ext e; simp
    have hzero : ∀ e ∈ Finset.univ.filter (· ∉ EP),
        1 * G.weights e * (voltageDrop G x e) ^ 2 = 0 := by
      intro e he
      simp only [Finset.mem_filter] at he
      rw [hvd_nonpath e he.2]
      ring
    rw [hfilter_mem, Finset.sum_eq_zero hzero, add_zero, Finset.mul_sum]
    refine Finset.sum_congr rfl fun e he => ?_
    rw [hvd_path e he]
    ring
  -- center the potential
  set y : Fin n → ℝ := proj x with hy_def
  have hy_sum : ∑ v, y v = 0 := proj_sum_zero x (by omega)
  set c : ℝ := (∑ w, x w) / n with hc_def
  have hy_v : ∀ v, y v = x v - c := by
    intro v
    rw [hy_def, hc_def]
    rfl
  have hy_VS : ∀ v ∈ VS, y v = -1 - c := by
    intro v hv
    rw [hy_v, hx_VS v hv]
  have hy_VT : ∀ v ∈ VT, y v = 1 - c := by
    intro v hv
    rw [hy_v, hx_VT v hv]
  -- centered norm is at least 4β²n
  have hnorm : 4 * β ^ 2 * n ≤ ∑ v, y v ^ 2 := by
    set a : ℝ := (VS.card : ℝ) with ha_def
    set b : ℝ := (VT.card : ℝ) with hb_def
    have ha_pos : 0 < a := lt_of_lt_of_le hβn_pos hVS_size
    have hb_pos : 0 < b := lt_of_lt_of_le hβn_pos hVT_size
    have hab_le : a + b ≤ n := by
      have hcard := Finset.card_union_of_disjoint hST
      have hle : (VS ∪ VT).card ≤ n := by
        have := Finset.card_le_card (Finset.subset_univ (VS ∪ VT))
        simpa using this
      calc a + b = ((VS.card + VT.card : ℕ) : ℝ) := by push_cast; ring
        _ = (((VS ∪ VT).card : ℕ) : ℝ) := by rw [hcard]
        _ ≤ n := by exact_mod_cast hle
    have hsub : ∑ v ∈ VS ∪ VT, y v ^ 2 ≤ ∑ v, y v ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        fun v _ _ => sq_nonneg _
    have hsplit : ∑ v ∈ VS ∪ VT, y v ^ 2 =
        a * (-1 - c) ^ 2 + b * (1 - c) ^ 2 := by
      rw [Finset.sum_union hST]
      congr 1
      · rw [Finset.sum_congr rfl fun v hv => by rw [hy_VS v hv],
          Finset.sum_const, nsmul_eq_mul]
      · rw [Finset.sum_congr rfl fun v hv => by rw [hy_VT v hv],
          Finset.sum_const, nsmul_eq_mul]
    have hid : (a + b) * (a * (-1 - c) ^ 2 + b * (1 - c) ^ 2) =
        ((a + b) * c + (a - b)) ^ 2 + 4 * (a * b) := by ring
    have h4ab : 4 * ((β * n) * (β * n)) ≤ 4 * (a * b) := by
      have := mul_le_mul hVS_size hVT_size hβn_pos.le ha_pos.le
      linarith
    have hchain : (a + b) * (4 * β ^ 2 * n) ≤
        (a + b) * (a * (-1 - c) ^ 2 + b * (1 - c) ^ 2) := by
      rw [hid]
      have h1 : (a + b) * (4 * β ^ 2 * n) ≤ 4 * ((β * n) * (β * n)) := by
        nlinarith [hab_le, hn_pos, hβ, sq_nonneg β]
      nlinarith [sq_nonneg ((a + b) * c + (a - b))]
    have hab_pos : 0 < a + b := by linarith
    have hmin := le_of_mul_le_mul_left hchain hab_pos
    calc 4 * β ^ 2 * n ≤ a * (-1 - c) ^ 2 + b * (1 - c) ^ 2 := hmin
      _ = ∑ v ∈ VS ∪ VT, y v ^ 2 := hsplit.symm
      _ ≤ ∑ v, y v ^ 2 := hsub
  -- quadratic form of the centered potential
  have hvd_y : ∀ e, voltageDrop G y e = voltageDrop G x e := by
    intro e
    rw [voltageDrop_eq_endpoint_diff, voltageDrop_eq_endpoint_diff,
      hy_v, hy_v]
    ring
  have h_comm : ∑ v, (∑ w, G.laplacian (fun _ => 1) v w * y w) * y v =
      ∑ v, y v * ∑ w, G.laplacian (fun _ => 1) v w * y w := by
    apply Finset.sum_congr rfl; intro v _; ring
  have hQy : ∑ v, (∑ w, G.laplacian (fun _ => 1) v w * y w) * y v =
      4 / ((ℓ : ℝ) - 1) ^ 2 * bEP := by
    rw [h_comm, laplacian_quadratic, ← hQx]
    exact Finset.sum_congr rfl fun e _ => by rw [hvd_y e]
  -- λ₂ upper bound from the Rayleigh quotient of y
  have hden_pos : (0 : ℝ) < β ^ 2 * n * ((ℓ : ℝ) - 1) ^ 2 := by positivity
  have h_sup_le : laplacian_eigenvalue₂ G (fun _ => 1) ≤
      bEP / (β ^ 2 * n * ((ℓ : ℝ) - 1) ^ 2) := by
    have h_eq : laplacian_eigenvalue₂ G (fun _ => 1) =
        sSup {r : ℝ | ∀ (z : Fin n → ℝ), ∑ i, z i = 0 →
          r * (∑ i, z i ^ 2) ≤
            ∑ i, (∑ j, G.laplacian (fun _ => 1) i j * z j) * z i} := by
      unfold laplacian_eigenvalue₂; rfl
    rw [h_eq]
    refine csSup_le (lambda2_set_nonempty G) fun r hr => ?_
    have h := hr y hy_sum
    rw [hQy] at h
    by_cases hr0 : r ≤ 0
    · exact le_trans hr0 (by positivity)
    · push_neg at hr0
      rw [le_div_iff₀ hden_pos]
      have h1 : r * (4 * β ^ 2 * n) ≤ r * ∑ v, y v ^ 2 :=
        mul_le_mul_of_nonneg_left hnorm hr0.le
      have h2 : r * (4 * β ^ 2 * n) ≤ 4 / ((ℓ : ℝ) - 1) ^ 2 * bEP :=
        le_trans h1 h
      have hL2 : (0 : ℝ) < ((ℓ : ℝ) - 1) ^ 2 := by positivity
      have h3 : 4 / ((ℓ : ℝ) - 1) ^ 2 * bEP * ((ℓ : ℝ) - 1) ^ 2 = 4 * bEP := by
        field_simp
      nlinarith [mul_le_mul_of_nonneg_right h2 hL2.le]
  -- assemble the condition number bound
  have hconn' := hconn
  unfold WeightedGraph.Connected at hconn'
  have hbEP_pos : 0 < bEP := by
    by_contra hb
    push_neg at hb
    have hb0 : bEP = 0 := le_antisymm hb hbEP_nn
    rw [hb0] at h_sup_le
    simp only [zero_div] at h_sup_le
    linarith
  have hl2_mul : laplacian_eigenvalue₂ G (fun _ => 1) *
      (β ^ 2 * n * ((ℓ : ℝ) - 1) ^ 2) ≤ bEP :=
    (le_div_iff₀ hden_pos).mp h_sup_le
  have hlmax := two_totalWeight_div_card_le_lambdaMax G (by omega)
  have hW_nn : 0 ≤ G.totalWeight :=
    Finset.sum_nonneg fun e _ => (G.weights_pos e).le
  unfold effectiveConditionNumber
  rw [div_le_div_iff₀ hbEP_pos hconn']
  calc 2 * β ^ 2 * ((ℓ : ℝ) - 1) ^ 2 * G.totalWeight *
        laplacian_eigenvalue₂ G (fun _ => 1)
      = (2 * G.totalWeight / n) * (laplacian_eigenvalue₂ G (fun _ => 1) *
          (β ^ 2 * n * ((ℓ : ℝ) - 1) ^ 2)) := by
        field_simp
    _ ≤ (2 * G.totalWeight / n) * bEP :=
        mul_le_mul_of_nonneg_left hl2_mul
          (div_nonneg (by linarith) hn_pos.le)
    _ ≤ laplacianEigenvalueMax G (fun _ => 1) * bEP :=
        mul_le_mul_of_nonneg_right hlmax hbEP_pos.le

end
