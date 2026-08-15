/-
Copyright (c) 2026 Cameron Khanpour and Samuel Talkington. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Cameron Khanpour, Samuel Talkington
-/
import PowerFlowLimits.CutBounds

/-!
# Proposition 1 (prop:corridor): corridors imply quadratic conditioning

Part of the Lean 4 formalization of
"Proving the Limits of Quantum Power Flow" (Khanpour and Talkington).
-/

open Finset BigOperators
open Filter Asymptotics

noncomputable section

variable {n m : ℕ}

/-- The exact graph data asserted by Proposition 1's corridor prose. The path branches are
indexed once, the bus sets form a disjoint cover, and every other branch stays inside one bulk
together with its adjacent corridor endpoint. -/
structure CorridorTopology (G : WeightedGraph n m)
    (VS VT : Finset (Fin n)) (ℓ : ℕ) (p : Fin ℓ → Fin n)
    (EP : Finset (Fin m)) where
  length_two : 2 ≤ ℓ
  path_injective : Function.Injective p
  /-- The branch joining each consecutive pair of path vertices. -/
  pathEdge : Fin (ℓ - 1) → Fin m
  pathEdge_injective : Function.Injective pathEdge
  pathEdge_range : EP = Finset.univ.image pathEdge
  pathEdge_endpoints : ∀ i, ∃ j : Fin ℓ, ∃ h : j.val + 1 < ℓ,
    j.val = i.val ∧
      ((G.posEndpoint (pathEdge i) = p j ∧
          G.negEndpoint (pathEdge i) = p ⟨j.val + 1, h⟩) ∨
        (G.posEndpoint (pathEdge i) = p ⟨j.val + 1, h⟩ ∧
          G.negEndpoint (pathEdge i) = p j))
  path_disjoint_left : ∀ i, p i ∉ VS
  path_disjoint_right : ∀ i, p i ∉ VT
  bulks_disjoint : Disjoint VS VT
  vertex_cover : VS ∪ Finset.univ.image p ∪ VT = Finset.univ
  nonpath_internal : ∀ e ∉ EP,
    ((G.posEndpoint e ∈ VS ∨ G.posEndpoint e = p ⟨0, by omega⟩) ∧
      (G.negEndpoint e ∈ VS ∨ G.negEndpoint e = p ⟨0, by omega⟩)) ∨
    ((G.posEndpoint e ∈ VT ∨ G.posEndpoint e = p ⟨ℓ - 1, by omega⟩) ∧
      (G.negEndpoint e ∈ VT ∨ G.negEndpoint e = p ⟨ℓ - 1, by omega⟩))

/-- The exact corridor topology contains precisely `ℓ - 1` path branches. -/
theorem CorridorTopology.pathEdge_card {G : WeightedGraph n m}
    {VS VT : Finset (Fin n)} {ℓ : ℕ} {p : Fin ℓ → Fin n}
    {EP : Finset (Fin m)} (C : CorridorTopology G VS VT ℓ p EP) :
    EP.card = ℓ - 1 := by
  rw [C.pathEdge_range, Finset.card_image_of_injective _ C.pathEdge_injective,
    Finset.card_univ, Fintype.card_fin]

/-- The indexed corridor topology implies the branchwise premise used by the Rayleigh proof. -/
theorem CorridorTopology.path_branch {G : WeightedGraph n m}
    {VS VT : Finset (Fin n)} {ℓ : ℕ} {p : Fin ℓ → Fin n}
    {EP : Finset (Fin m)} (C : CorridorTopology G VS VT ℓ p EP) :
    ∀ e ∈ EP, ∃ i : Fin ℓ, ∃ h : i.val + 1 < ℓ,
      (G.posEndpoint e = p i ∧ G.negEndpoint e = p ⟨i.val + 1, h⟩) ∨
      (G.posEndpoint e = p ⟨i.val + 1, h⟩ ∧ G.negEndpoint e = p i) := by
  intro e he
  rw [C.pathEdge_range] at he
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp he
  obtain ⟨j, h, _, hj⟩ := C.pathEdge_endpoints i
  exact ⟨j, h, hj⟩

/-- The total weight of `ell - 1` corridor branches is at most
`(ell - 1) * b_max`. -/
theorem corridorWeight_le_length_mul_bmax (G : WeightedGraph n m)
    (EP : Finset (Fin m)) (ℓ : ℕ) (bmax : ℝ)
    (hℓ : 1 ≤ ℓ) (hcard : EP.card = ℓ - 1)
    (hbmax : ∀ e, G.weights e ≤ bmax) :
    ∑ e ∈ EP, G.weights e ≤ ((ℓ : ℝ) - 1) * bmax := by
  calc
    ∑ e ∈ EP, G.weights e ≤ ∑ _e ∈ EP, bmax :=
      Finset.sum_le_sum fun e _ ↦ hbmax e
    _ = (EP.card : ℝ) * bmax := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ = ((ℓ : ℝ) - 1) * bmax := by
      rw [hcard, Nat.cast_sub hℓ, Nat.cast_one]

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
    (hconn : G.CombinatoriallyConnected) :
    2 * β ^ 2 * ((ℓ : ℝ) - 1) ^ 2 * G.totalWeight / (∑ e ∈ EP, G.weights e) ≤
      effectiveConditionNumber G (fun _ => 1) := by
  classical
  have hℓn : ℓ ≤ n := by
    simpa using Fintype.card_le_of_injective p hp_inj
  have hn2 : 1 < n := by omega
  have hspec := combinatoriallyConnected_implies_spectralConnected G hconn hn2
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
        simpa using Finset.card_le_card (Finset.subset_univ (VS ∪ VT))
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
  have hconn' := hspec
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

/-- Proposition 1 with its prose topology packaged as one exact witness. -/
theorem corridor_kappa_bound_of_topology (G : WeightedGraph n m)
    (VS VT : Finset (Fin n)) (ℓ : ℕ) (p : Fin ℓ → Fin n)
    (EP : Finset (Fin m)) (C : CorridorTopology G VS VT ℓ p EP)
    (β : ℝ) (hβ : 0 < β)
    (hVS_size : β * n ≤ (VS.card : ℝ))
    (hVT_size : β * n ≤ (VT.card : ℝ))
    (hconn : G.CombinatoriallyConnected) :
    2 * β ^ 2 * ((ℓ : ℝ) - 1) ^ 2 * G.totalWeight /
        (∑ e ∈ EP, G.weights e) ≤
      effectiveConditionNumber G (fun _ ↦ 1) :=
  corridor_kappa_bound G VS VT ℓ C.length_two p EP β C.path_injective
    C.path_disjoint_left C.path_disjoint_right C.bulks_disjoint C.path_branch
    C.nonpath_internal hβ hVS_size hVT_size hconn

/-- The `ℓ = 2` specialization is a single tie branch. This recovers the tie branch mechanism;
its displayed coefficient is the corridor proposition's `2β²`. -/
theorem two_bus_corridor_kappa_bound (G : WeightedGraph n m)
    (VS VT : Finset (Fin n)) (p : Fin 2 → Fin n) (EP : Finset (Fin m))
    (C : CorridorTopology G VS VT 2 p EP) (β : ℝ) (hβ : 0 < β)
    (hVS_size : β * n ≤ (VS.card : ℝ))
    (hVT_size : β * n ≤ (VT.card : ℝ))
    (hconn : G.CombinatoriallyConnected) :
    2 * β ^ 2 * G.totalWeight / G.weights (C.pathEdge ⟨0, by omega⟩) ≤
      effectiveConditionNumber G (fun _ ↦ 1) := by
  have h := corridor_kappa_bound_of_topology G VS VT 2 p EP C β hβ
    hVS_size hVT_size hconn
  have hsum : ∑ e ∈ EP, G.weights e = G.weights (C.pathEdge ⟨0, by omega⟩) := by
    let pathEdge : Fin 1 → Fin m := C.pathEdge
    have hrange : EP = Finset.univ.image pathEdge := C.pathEdge_range
    change ∑ e ∈ EP, G.weights e = G.weights (pathEdge ⟨0, by omega⟩)
    rw [hrange]
    simp
  rw [hsum] at h
  norm_num at h ⊢
  exact h

/-- The finite quantitative form of the proposition's quadratic-growth sentence. A corridor whose
length is at least `α n`, together with a uniform mean-to-maximum weight ratio `ρ`, forces the
displayed `n²` lower bound. Connectedness supplies `m ≥ n - 1 ≥ n / 2`. -/
theorem corridor_kappa_quadratic_bound (G : WeightedGraph n m)
    (VS VT : Finset (Fin n)) (ℓ : ℕ) (p : Fin ℓ → Fin n)
    (EP : Finset (Fin m)) (C : CorridorTopology G VS VT ℓ p EP)
    (β α ρ bmax : ℝ) (hβ : 0 < β) (hα : 0 < α) (hρ : 0 < ρ)
    (hbmax_pos : 0 < bmax)
    (hVS_size : β * n ≤ (VS.card : ℝ))
    (hVT_size : β * n ≤ (VT.card : ℝ))
    (hbmax : ∀ e, G.weights e ≤ bmax)
    (hmean : ρ * (m : ℝ) * bmax ≤ G.totalWeight)
    (hmacro : α * n ≤ (ℓ : ℝ) - 1)
    (hconn : G.CombinatoriallyConnected) :
    β ^ 2 * α * ρ * (n : ℝ) ^ 2 ≤
      effectiveConditionNumber G (fun _ ↦ 1) := by
  have hℓn : ℓ ≤ n := by
    simpa using Fintype.card_le_of_injective p C.path_injective
  have hn_two : 2 ≤ n := le_trans C.length_two hℓn
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by omega) hn_two)
  have hlength_pos : 0 < (ℓ : ℝ) - 1 :=
    sub_pos.mpr (by exact_mod_cast C.length_two)
  have hℓ_one : 1 < ℓ := lt_of_lt_of_le (by norm_num) C.length_two
  have hℓ_one_le : 1 ≤ ℓ := hℓ_one.le
  have hEP_nonempty : EP.Nonempty := by
    have hℓsub : 0 < ℓ - 1 := Nat.sub_pos_iff_lt.mpr hℓ_one
    rw [← Finset.card_pos, C.pathEdge_card]
    exact hℓsub
  have hEP_pos : 0 < ∑ e ∈ EP, G.weights e :=
    Finset.sum_pos (fun e _ ↦ G.weights_pos e) hEP_nonempty
  have hEP_le : ∑ e ∈ EP, G.weights e ≤ ((ℓ : ℝ) - 1) * bmax :=
    corridorWeight_le_length_mul_bmax G EP ℓ bmax hℓ_one_le
      C.pathEdge_card hbmax
  have hm_nat : n - 1 ≤ m := G.card_sub_one_le_edges hconn
  have hm_half : (n : ℝ) / 2 ≤ m := by
    have hm_real : ((n - 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast hm_nat
    have hn_two_real : (2 : ℝ) ≤ n := by exact_mod_cast hn_two
    rw [Nat.cast_sub (by omega), Nat.cast_one] at hm_real
    linarith
  have hweight_lower : ρ * ((n : ℝ) / 2) * bmax ≤ G.totalWeight := by
    calc
      ρ * ((n : ℝ) / 2) * bmax ≤ ρ * (m : ℝ) * bmax := by
        gcongr
      _ ≤ G.totalWeight := hmean
  have htarget_nonneg : 0 ≤ β ^ 2 * α * ρ * (n : ℝ) ^ 2 := by positivity
  have hfirst :
      β ^ 2 * α * ρ * (n : ℝ) ^ 2 * (∑ e ∈ EP, G.weights e) ≤
        β ^ 2 * α * ρ * (n : ℝ) ^ 2 * (((ℓ : ℝ) - 1) * bmax) :=
    mul_le_mul_of_nonneg_left hEP_le htarget_nonneg
  have hsecond :
      β ^ 2 * α * ρ * (n : ℝ) ^ 2 * (((ℓ : ℝ) - 1) * bmax) ≤
        β ^ 2 * ρ * n * ((ℓ : ℝ) - 1) ^ 2 * bmax := by
    calc
      β ^ 2 * α * ρ * (n : ℝ) ^ 2 * (((ℓ : ℝ) - 1) * bmax) =
          (β ^ 2 * ρ * n * ((ℓ : ℝ) - 1) * bmax) * (α * n) := by ring
      _ ≤ (β ^ 2 * ρ * n * ((ℓ : ℝ) - 1) * bmax) * ((ℓ : ℝ) - 1) := by
        gcongr
      _ = β ^ 2 * ρ * n * ((ℓ : ℝ) - 1) ^ 2 * bmax := by ring
  have hthird :
      β ^ 2 * ρ * n * ((ℓ : ℝ) - 1) ^ 2 * bmax ≤
        2 * β ^ 2 * ((ℓ : ℝ) - 1) ^ 2 * G.totalWeight := by
    calc
      β ^ 2 * ρ * n * ((ℓ : ℝ) - 1) ^ 2 * bmax =
          2 * β ^ 2 * ((ℓ : ℝ) - 1) ^ 2 * (ρ * (n / 2) * bmax) := by ring
      _ ≤ 2 * β ^ 2 * ((ℓ : ℝ) - 1) ^ 2 * G.totalWeight := by
        gcongr
  have htarget_corridor :
      β ^ 2 * α * ρ * (n : ℝ) ^ 2 ≤
        2 * β ^ 2 * ((ℓ : ℝ) - 1) ^ 2 * G.totalWeight /
          (∑ e ∈ EP, G.weights e) := by
    rw [le_div_iff₀ hEP_pos]
    exact hfirst.trans (hsecond.trans hthird)
  exact htarget_corridor.trans
    (corridor_kappa_bound_of_topology G VS VT ℓ p EP C β hβ
      hVS_size hVT_size hconn)

/-- A uniform positive quadratic lower bound is precisely an `Ω(n²)` statement in mathlib's
asymptotics API: `n² = O(κ(n))` at `atTop`. -/
theorem isBigOmega_sq_of_eventually_quadratic_lower_bound
    (κ : ℕ → ℝ) (c : ℝ) (hc : 0 < c)
    (hκ : ∀ᶠ k : ℕ in atTop, c * (k : ℝ) ^ 2 ≤ κ k) :
    (fun k : ℕ ↦ (k : ℝ) ^ 2) =O[atTop] κ := by
  refine Asymptotics.isBigO_iff''.2 ⟨c, hc, ?_⟩
  filter_upwards [hκ] with k hk
  have hsq : 0 ≤ (k : ℝ) ^ 2 := sq_nonneg _
  have hκ_nonneg : 0 ≤ κ k := (mul_nonneg hc.le hsq).trans hk
  simpa [Real.norm_eq_abs, abs_of_nonneg hsq, abs_of_nonneg hκ_nonneg] using hk

/-- Proposition 1's family-level conclusion. The hypotheses give uniform constants beyond `N`:
the corridor occupies at least an `α` fraction of the buses, both bulk regions occupy at least a
`β` fraction, and mean susceptance is at least `ρ bmax`. The conclusion is the standard
`κ(n) = Ω(n²)` relation. -/
theorem corridor_family_isBigOmega_quadratic
    (edgeCount length : ℕ → ℕ)
    (G : (k : ℕ) → WeightedGraph k (edgeCount k))
    (VS VT : (k : ℕ) → Finset (Fin k))
    (p : (k : ℕ) → Fin (length k) → Fin k)
    (EP : (k : ℕ) → Finset (Fin (edgeCount k)))
    (N : ℕ) (β α ρ bmax : ℝ)
    (hβ : 0 < β) (hα : 0 < α) (hρ : 0 < ρ) (hbmax_pos : 0 < bmax)
    (hC : ∀ k : ℕ, N ≤ k →
      CorridorTopology (G k) (VS k) (VT k) (length k) (p k) (EP k))
    (hVS_size : ∀ k : ℕ, N ≤ k → β * k ≤ ((VS k).card : ℝ))
    (hVT_size : ∀ k : ℕ, N ≤ k → β * k ≤ ((VT k).card : ℝ))
    (hbmax : ∀ k : ℕ, N ≤ k → ∀ e, (G k).weights e ≤ bmax)
    (hmean : ∀ k : ℕ, N ≤ k →
      ρ * (edgeCount k : ℝ) * bmax ≤ (G k).totalWeight)
    (hmacro : ∀ k : ℕ, N ≤ k → α * k ≤ (length k : ℝ) - 1)
    (hconn : ∀ k : ℕ, N ≤ k → (G k).CombinatoriallyConnected) :
    (fun k : ℕ ↦ (k : ℝ) ^ 2) =O[atTop]
      (fun k ↦ effectiveConditionNumber (G k) (fun _ ↦ 1)) := by
  apply isBigOmega_sq_of_eventually_quadratic_lower_bound _ (β ^ 2 * α * ρ)
    (by positivity)
  rw [Filter.eventually_atTop]
  refine ⟨N, fun k hk ↦ ?_⟩
  exact corridor_kappa_quadratic_bound (G k) (VS k) (VT k) (length k) (p k)
    (EP k) (hC k hk) β α ρ bmax hβ hα hρ hbmax_pos
    (hVS_size k hk) (hVT_size k hk) (hbmax k hk) (hmean k hk)
    (hmacro k hk) (hconn k hk)

end
