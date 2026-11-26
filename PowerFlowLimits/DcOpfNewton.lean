/-
Copyright (c) 2026 Cameron Khanpour and Samuel Talkington. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Cameron Khanpour, Samuel Talkington
-/
import PowerFlowLimits.Grounded
import PowerFlowLimits.OptimalPowerFlow

/-!
# The DC optimal power flow Newton system

An interior point method for DC optimal power flow solves, at each iteration, a Newton system in
generation, retained voltage angles, and balance multipliers. Its matrix is

```
K = [ H    0     -Γᵀ ]
    [ 0    L_w    B̃ᵀ ]
    [ -Γ   B̃     0  ]
```

where `L_w` is the grounded Laplacian with the iteration dependent branch weights and `B̃` is the
susceptance Laplacian without the slack column. This file proves the letter's Proposition 3: a
balanced separator forces `κ₂(K) ≥ √(β n / s) / (2 Δ)` for every generation block `H`, every
generator map `Γ`, and every positive choice of the branch weights.

The condition number is expressed through singular value bounds. If `σmin ‖z‖ ≤ ‖K z‖ ≤ σmax ‖z‖`
for every `z`, then `σmax / σmin` is at least the stated quantity. When `K` is invertible this is
the statement about `κ₂(K)`, and when `K` is singular no positive `σmin` exists.
-/

open Finset BigOperators
open scoped Matrix

noncomputable section

variable {n m g : ℕ}

/-- Indicator vector of a bus set. -/
def busIndicator (S : Finset (Fin n)) : Fin n → ℝ := fun j ↦ if j ∈ S then 1 else 0

theorem sum_sq_busIndicator (S : Finset (Fin n)) :
    ∑ j, busIndicator S j ^ 2 = (S.card : ℝ) := by
  have hpoint : ∀ j, busIndicator S j ^ 2 = if j ∈ S then (1 : ℝ) else 0 := by
    intro j
    by_cases hj : j ∈ S <;> simp [busIndicator, hj]
  simp_rw [hpoint]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one]

/-- The indicator of a bus set changes only across the boundary branches of the set. -/
theorem abs_voltageDrop_busIndicator_le (G : WeightedGraph n m) (S : Finset (Fin n))
    (e : Fin m) :
    |voltageDrop G (busIndicator S) e| ≤ if e ∈ G.boundaryEdges S then 1 else 0 := by
  rw [voltageDrop_eq_endpoint_diff]
  simp only [busIndicator, WeightedGraph.boundaryEdges, Finset.mem_filter, Finset.mem_univ,
    true_and]
  by_cases hp : G.posEndpoint e ∈ S <;> by_cases hq : G.negEndpoint e ∈ S <;> simp [hp, hq]

/-- An incidence entry has magnitude at most one and vanishes away from the branch endpoints. -/
theorem WeightedGraph.abs_incidence_le (G : WeightedGraph n m) (i : Fin n) (e : Fin m) :
    |G.incidence i e| ≤ if i = G.posEndpoint e ∨ i = G.negEndpoint e then 1 else 0 := by
  by_cases hp : i = G.posEndpoint e
  · subst hp
    rw [G.incidence_posEndpoint]
    simp
  · by_cases hq : i = G.negEndpoint e
    · subst hq
      rw [G.incidence_negEndpoint]
      simp
    · rw [G.incidence_eq_zero_of_ne_endpoints e i hp hq]
      simp [hp, hq]

/-- Number of boundary branches of `S` that end at bus `i`. -/
def WeightedGraph.boundaryDegree (G : WeightedGraph n m) (S : Finset (Fin n))
    (i : Fin n) : ℕ :=
  ((G.boundaryEdges S).filter fun e ↦ i = G.posEndpoint e ∨ i = G.negEndpoint e).card

theorem WeightedGraph.boundaryDegree_le_degree (G : WeightedGraph n m)
    (S : Finset (Fin n)) (i : Fin n) :
    G.boundaryDegree S i ≤ (G.incidentEdges i).card := by
  unfold WeightedGraph.boundaryDegree WeightedGraph.incidentEdges
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _))

/-- Every boundary branch has two endpoints, so the boundary degrees sum to twice the cut size. -/
theorem WeightedGraph.sum_boundaryDegree (G : WeightedGraph n m) (S : Finset (Fin n)) :
    ∑ i, G.boundaryDegree S i = 2 * (G.boundaryEdges S).card := by
  unfold WeightedGraph.boundaryDegree
  simp_rw [Finset.card_filter]
  rw [Finset.sum_comm]
  have hinner : ∀ e : Fin m,
      (∑ i : Fin n, if i = G.posEndpoint e ∨ i = G.negEndpoint e then 1 else 0) = 2 := by
    intro e
    rw [← Finset.card_filter]
    have hpair : (Finset.univ.filter fun i : Fin n ↦
        i = G.posEndpoint e ∨ i = G.negEndpoint e) =
          {G.posEndpoint e, G.negEndpoint e} := by
      ext i
      simp
    rw [hpair, Finset.card_pair (G.endpoints_ne e)]
  rw [Finset.sum_congr rfl fun e _ ↦ hinner e, Finset.sum_const, smul_eq_mul, mul_comm]

/-- Each entry of `L 1_S` sums the weights of the branches that leave `S` at one bus. -/
theorem WeightedGraph.abs_laplacian_mulVec_busIndicator_le (G : WeightedGraph n m)
    (s : Fin m → ℝ) (S : Finset (Fin n)) (W : ℝ)
    (hs : ∀ e, 0 ≤ s e) (hW : ∀ e, G.weights e * s e ≤ W) (i : Fin n) :
    |∑ j, G.laplacian s i j * busIndicator S j| ≤ W * G.boundaryDegree S i := by
  classical
  have hmul : ∑ j, G.laplacian s i j * busIndicator S j =
      (G.laplacian s *ᵥ busIndicator S) i := rfl
  rw [hmul, laplacian_mulVec_apply]
  set T : Finset (Fin m) :=
    (G.boundaryEdges S).filter fun e ↦ i = G.posEndpoint e ∨ i = G.negEndpoint e with hT
  calc
    |∑ e, G.incidence i e * (G.weights e * s e) * voltageDrop G (busIndicator S) e| ≤
        ∑ e, |G.incidence i e * (G.weights e * s e) *
          voltageDrop G (busIndicator S) e| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ e, (if e ∈ T then W else 0) := by
      refine Finset.sum_le_sum fun e _ ↦ ?_
      have hw_nonneg : 0 ≤ G.weights e * s e := mul_nonneg (G.weights_pos e).le (hs e)
      have hA := G.abs_incidence_le i e
      have hd := abs_voltageDrop_busIndicator_le G S e
      rw [abs_mul, abs_mul, abs_of_nonneg hw_nonneg]
      by_cases hb : e ∈ G.boundaryEdges S
      · by_cases hi : i = G.posEndpoint e ∨ i = G.negEndpoint e
        · have hmem : e ∈ T := by
            rw [hT, Finset.mem_filter]
            exact ⟨hb, hi⟩
          rw [if_pos hmem]
          rw [if_pos hi] at hA
          rw [if_pos hb] at hd
          have hW_nonneg : 0 ≤ W := hw_nonneg.trans (hW e)
          have h1 : |G.incidence i e| * (G.weights e * s e) ≤ 1 * W :=
            mul_le_mul hA (hW e) hw_nonneg zero_le_one
          have h2 : |G.incidence i e| * (G.weights e * s e) *
              |voltageDrop G (busIndicator S) e| ≤ 1 * W * 1 :=
            mul_le_mul h1 hd (abs_nonneg _) (by linarith)
          linarith
        · have hnot : e ∉ T := by
            rw [hT, Finset.mem_filter]
            exact fun h ↦ hi h.2
          rw [if_neg hnot]
          rw [if_neg hi] at hA
          have hzero : |G.incidence i e| = 0 := le_antisymm hA (abs_nonneg _)
          rw [hzero]
          simp
      · have hnot : e ∉ T := by
          rw [hT, Finset.mem_filter]
          exact fun h ↦ hb h.1
        rw [if_neg hnot]
        rw [if_neg hb] at hd
        have hzero : |voltageDrop G (busIndicator S) e| = 0 := le_antisymm hd (abs_nonneg _)
        rw [hzero]
        simp
    _ = W * G.boundaryDegree S i := by
      rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_comm]
      rfl

/-- The squared norm of `L 1_S` is controlled by the cut size, the maximum degree, and the largest
branch weight. -/
theorem WeightedGraph.sum_sq_laplacian_mulVec_busIndicator_le (G : WeightedGraph n m)
    (s : Fin m → ℝ) (S : Finset (Fin n)) (Δ W : ℝ)
    (hs : ∀ e, 0 ≤ s e) (hW : ∀ e, G.weights e * s e ≤ W)
    (hdeg : ∀ i, ((G.incidentEdges i).card : ℝ) ≤ Δ) :
    ∑ i, (∑ j, G.laplacian s i j * busIndicator S j) ^ 2 ≤
      2 * Δ * (G.boundaryEdges S).card * W ^ 2 := by
  have hterm : ∀ i, (∑ j, G.laplacian s i j * busIndicator S j) ^ 2 ≤
      W ^ 2 * (Δ * G.boundaryDegree S i) := by
    intro i
    have habs := G.abs_laplacian_mulVec_busIndicator_le s S W hs hW i
    have hc_nonneg : (0 : ℝ) ≤ G.boundaryDegree S i := Nat.cast_nonneg _
    have hc_le : (G.boundaryDegree S i : ℝ) ≤ Δ :=
      le_trans (by exact_mod_cast G.boundaryDegree_le_degree S i) (hdeg i)
    calc
      (∑ j, G.laplacian s i j * busIndicator S j) ^ 2 =
          |∑ j, G.laplacian s i j * busIndicator S j| ^ 2 := (sq_abs _).symm
      _ ≤ (W * G.boundaryDegree S i) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) habs 2
      _ = W ^ 2 * ((G.boundaryDegree S i : ℝ) * G.boundaryDegree S i) := by ring
      _ ≤ W ^ 2 * (Δ * G.boundaryDegree S i) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hc_le hc_nonneg) (sq_nonneg W)
  have hcast : ∑ i, (G.boundaryDegree S i : ℝ) = 2 * ((G.boundaryEdges S).card : ℝ) := by
    exact_mod_cast G.sum_boundaryDegree S
  calc
    ∑ i, (∑ j, G.laplacian s i j * busIndicator S j) ^ 2 ≤
        ∑ i, W ^ 2 * (Δ * G.boundaryDegree S i) := Finset.sum_le_sum fun i _ ↦ hterm i
    _ = W ^ 2 * Δ * ∑ i, (G.boundaryDegree S i : ℝ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      ring
    _ = 2 * Δ * (G.boundaryEdges S).card * W ^ 2 := by
      rw [hcast]
      ring

/-- A diagonal Laplacian entry at an endpoint of a branch is at least the weight of the branch. -/
theorem WeightedGraph.weight_mul_scale_le_laplacian_diag (G : WeightedGraph n m)
    (s : Fin m → ℝ) (hs : ∀ e, 0 ≤ s e) (e : Fin m) (i : Fin n)
    (hi : i = G.posEndpoint e ∨ i = G.negEndpoint e) :
    G.weights e * s e ≤ G.laplacian s i i := by
  unfold WeightedGraph.laplacian
  have hnonneg : ∀ f ∈ (Finset.univ : Finset (Fin m)),
      0 ≤ G.incidence i f * (G.weights f * s f) * G.incidence i f := by
    intro f _
    have hform : G.incidence i f * (G.weights f * s f) * G.incidence i f =
        (G.weights f * s f) * G.incidence i f ^ 2 := by ring
    rw [hform]
    exact mul_nonneg (mul_nonneg (G.weights_pos f).le (hs f)) (sq_nonneg _)
  have hsingle : G.incidence i e * (G.weights e * s e) * G.incidence i e ≤
      ∑ f, G.incidence i f * (G.weights f * s f) * G.incidence i f :=
    Finset.single_le_sum hnonneg (Finset.mem_univ e)
  have hvalue : G.incidence i e * (G.weights e * s e) * G.incidence i e =
      G.weights e * s e := by
    rcases hi with rfl | rfl
    · rw [G.incidence_posEndpoint]
      ring
    · rw [G.incidence_negEndpoint]
      ring
  linarith

/-- Every branch keeps an endpoint after the slack bus is deleted. -/
theorem WeightedGraph.exists_retained_endpoint (G : WeightedGraph n m) (r : Fin n)
    (e : Fin m) :
    ∃ i : GroundedIndex r, (i : Fin n) = G.posEndpoint e ∨ (i : Fin n) = G.negEndpoint e := by
  by_cases hpos : G.posEndpoint e = r
  · have hneg : G.negEndpoint e ≠ r := fun h ↦ G.endpoints_ne e (hpos.trans h.symm)
    exact ⟨⟨G.negEndpoint e, hneg⟩, Or.inr rfl⟩
  · exact ⟨⟨G.posEndpoint e, hpos⟩, Or.inl rfl⟩

/-- A sum over the retained buses equals the sum over all buses when the slack term vanishes. -/
theorem sum_groundedIndex_eq (r : Fin n) (f : Fin n → ℝ) (hf : f r = 0) :
    ∑ j : GroundedIndex r, f j = ∑ j, f j := by
  rw [Fintype.sum_eq_add_sum_subtype_ne f r, hf, zero_add]

/-- A sum of nonnegative terms over the retained buses is at most the sum over all buses. -/
theorem sum_groundedIndex_le (r : Fin n) (f : Fin n → ℝ) (hf : 0 ≤ f r) :
    ∑ j : GroundedIndex r, f j ≤ ∑ j, f j := by
  rw [Fintype.sum_eq_add_sum_subtype_ne f r]
  linarith

/-- Coordinates of the DC-OPF Newton system: generation, retained angles, and balance
multipliers. -/
abbrev DcOpfNewtonIndex (g : ℕ) (r : Fin n) := Fin g ⊕ (GroundedIndex r ⊕ Fin n)

/-- The Newton matrix of a DC-OPF interior point iteration. `H` is the generation block, `Γ` maps
generators to buses, and `scale` holds the positive ratios between the iteration dependent branch
weights and the branch susceptances. -/
def WeightedGraph.dcOpfNewtonMatrix (G : WeightedGraph n m) (r : Fin n)
    (H : Matrix (Fin g) (Fin g) ℝ) (Γ : Matrix (Fin n) (Fin g) ℝ) (scale : Fin m → ℝ) :
    Matrix (DcOpfNewtonIndex g r) (DcOpfNewtonIndex g r) ℝ :=
  Matrix.of fun x y ↦
    match x, y with
    | .inl a, .inl b => H a b
    | .inl _, .inr (.inl _) => 0
    | .inl a, .inr (.inr k) => -Γ k a
    | .inr (.inl _), .inl _ => 0
    | .inr (.inl i), .inr (.inl j) => G.laplacian scale i j
    | .inr (.inl i), .inr (.inr k) => G.laplacian (fun _ ↦ 1) k i
    | .inr (.inr k), .inl a => -Γ k a
    | .inr (.inr k), .inr (.inl j) => G.laplacian (fun _ ↦ 1) k j
    | .inr (.inr _), .inr (.inr _) => 0

/-- Embed an angle vector into the Newton coordinates with zero generation and multipliers. -/
def angleEmbedding (g : ℕ) (r : Fin n) (x : Fin n → ℝ) : DcOpfNewtonIndex g r → ℝ :=
  Sum.elim (fun _ ↦ 0) (Sum.elim (fun j ↦ x j) (fun _ ↦ 0))

theorem sum_sq_angleEmbedding (r : Fin n) (x : Fin n → ℝ) (hx : x r = 0) :
    ∑ y, angleEmbedding g r x y ^ 2 = ∑ j, x j ^ 2 := by
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [angleEmbedding, Sum.elim_inl, Sum.elim_inr]
  have hzero : ∀ (ι : Type) [Fintype ι], ∑ _i : ι, (0 : ℝ) ^ 2 = 0 := by
    intro ι _
    simp
  rw [hzero, hzero, zero_add, add_zero]
  exact sum_groundedIndex_eq r (fun j ↦ x j ^ 2) (by simp [hx])

/-- The Newton matrix sends an angle vector to the pair `(L_w x, B x)`. -/
theorem WeightedGraph.dcOpfNewtonMatrix_mulVec_angleEmbedding (G : WeightedGraph n m)
    (r : Fin n) (H : Matrix (Fin g) (Fin g) ℝ) (Γ : Matrix (Fin n) (Fin g) ℝ)
    (scale : Fin m → ℝ) (x : Fin n → ℝ) (hx : x r = 0) :
    G.dcOpfNewtonMatrix r H Γ scale *ᵥ angleEmbedding g r x =
      Sum.elim (fun _ ↦ 0)
        (Sum.elim (fun i : GroundedIndex r ↦ ∑ j, G.laplacian scale i j * x j)
          (fun k ↦ ∑ j, G.laplacian (fun _ ↦ 1) k j * x j)) := by
  funext y
  rcases y with a | i | k
  · simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, WeightedGraph.dcOpfNewtonMatrix,
      angleEmbedding]
  · simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
      WeightedGraph.dcOpfNewtonMatrix, angleEmbedding, Matrix.of_apply, Sum.elim_inl,
      Sum.elim_inr, mul_zero, Finset.sum_const_zero, zero_add, add_zero]
    exact sum_groundedIndex_eq r (fun j ↦ G.laplacian scale i j * x j) (by simp [hx])
  · simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
      WeightedGraph.dcOpfNewtonMatrix, angleEmbedding, Matrix.of_apply, Sum.elim_inl,
      Sum.elim_inr, mul_zero, Finset.sum_const_zero, zero_add, add_zero]
    exact sum_groundedIndex_eq r (fun j ↦ G.laplacian (fun _ ↦ 1) k j * x j) (by simp [hx])

/-- Every entry of a matrix is bounded by any upper bound on its largest singular value. -/
theorem abs_entry_le_of_singular_upper {ι : Type*} [Fintype ι]
    (K : Matrix ι ι ℝ) (σmax : ℝ) (hσmax : 0 ≤ σmax)
    (hupper : ∀ z : ι → ℝ, ∑ y, ((K *ᵥ z) y) ^ 2 ≤ σmax ^ 2 * ∑ y, z y ^ 2)
    (x₀ y₀ : ι) : |K x₀ y₀| ≤ σmax := by
  classical
  have hz := hupper (fun y ↦ if y = y₀ then 1 else 0)
  have hsum : ∑ y, (if y = y₀ then (1 : ℝ) else 0) ^ 2 = 1 := by simp
  have hmul : (K *ᵥ fun y ↦ if y = y₀ then (1 : ℝ) else 0) x₀ = K x₀ y₀ := by
    simp [Matrix.mulVec, dotProduct]
  have hsingle : ((K *ᵥ fun y ↦ if y = y₀ then (1 : ℝ) else 0) x₀) ^ 2 ≤
      ∑ y, ((K *ᵥ fun y ↦ if y = y₀ then (1 : ℝ) else 0) y) ^ 2 :=
    Finset.single_le_sum (f := fun y ↦ ((K *ᵥ fun y ↦ if y = y₀ then (1 : ℝ) else 0) y) ^ 2)
      (fun y _ ↦ sq_nonneg _) (Finset.mem_univ x₀)
  rw [hsum, mul_one] at hz
  rw [hmul] at hsingle
  have hsq : |K x₀ y₀| ^ 2 ≤ σmax ^ 2 := by
    rw [sq_abs]
    exact hsingle.trans hz
  exact (sq_le_sq₀ (abs_nonneg _) hσmax).mp hsq

/-- The letter's Proposition 3. If the grid has maximum degree `Δ` and an `(s, β)` separation,
then every pair of singular value bounds of the DC-OPF Newton matrix satisfies
`σmax / σmin ≥ √(β n / s) / (2 Δ)`. The bound holds for every generation block, every generator
map, and every positive choice of the iteration dependent branch weights. -/
theorem WeightedGraph.dcOpfNewton_condition_bound (G : WeightedGraph n m) (r : Fin n)
    (H : Matrix (Fin g) (Fin g) ℝ) (Γ : Matrix (Fin n) (Fin g) ℝ)
    (scale : Fin m → ℝ) (hscale : ∀ e, 0 < scale e)
    (A X Bv : Finset (Fin n)) (s Δ β : ℝ)
    (hcover : A ∪ X ∪ Bv = Finset.univ)
    (hdisj : Disjoint (A ∪ X) Bv)
    (hnoAB : ∀ e, ¬(G.posEndpoint e ∈ A ∧ G.negEndpoint e ∈ Bv) ∧
      ¬(G.posEndpoint e ∈ Bv ∧ G.negEndpoint e ∈ A))
    (hX : (X.card : ℝ) ≤ s)
    (hdeg : ∀ i, ((G.incidentEdges i).card : ℝ) ≤ Δ)
    (hβ : 0 < β)
    (hA_size : β * n ≤ ((A ∪ X).card : ℝ)) (hB_size : β * n ≤ (Bv.card : ℝ))
    (σmin σmax : ℝ) (hσmin : 0 < σmin) (hσmax : 0 ≤ σmax)
    (hlower : ∀ z : DcOpfNewtonIndex g r → ℝ,
      σmin ^ 2 * ∑ y, z y ^ 2 ≤ ∑ y, ((G.dcOpfNewtonMatrix r H Γ scale *ᵥ z) y) ^ 2)
    (hupper : ∀ z : DcOpfNewtonIndex g r → ℝ,
      ∑ y, ((G.dcOpfNewtonMatrix r H Γ scale *ᵥ z) y) ^ 2 ≤ σmax ^ 2 * ∑ y, z y ^ 2) :
    Real.sqrt (β * n / s) / (2 * Δ) ≤ σmax / σmin := by
  classical
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast r.pos
  have hΔ_nonneg : 0 ≤ Δ := le_trans (Nat.cast_nonneg _) (hdeg r)
  -- the largest singular value dominates both families of branch weights
  have hentry := abs_entry_le_of_singular_upper (G.dcOpfNewtonMatrix r H Γ scale) σmax hσmax
    hupper
  have hscaled_le : ∀ e, G.weights e * scale e ≤ σmax := by
    intro e
    obtain ⟨i, hi⟩ := G.exists_retained_endpoint r e
    have hdiag := G.weight_mul_scale_le_laplacian_diag scale (fun f ↦ (hscale f).le) e i hi
    have hbound := hentry (.inr (.inl i)) (.inr (.inl i))
    have hvalue : G.dcOpfNewtonMatrix r H Γ scale (.inr (.inl i)) (.inr (.inl i)) =
        G.laplacian scale i i := rfl
    rw [hvalue] at hbound
    exact hdiag.trans ((le_abs_self _).trans hbound)
  have hunit_le : ∀ e, G.weights e * (fun _ : Fin m ↦ (1 : ℝ)) e ≤ σmax := by
    intro e
    obtain ⟨i, hi⟩ := G.exists_retained_endpoint r e
    have hdiag := G.weight_mul_scale_le_laplacian_diag (fun _ ↦ 1) (fun _ ↦ zero_le_one) e i hi
    have hbound := hentry (.inr (.inr i)) (.inr (.inl i))
    have hvalue : G.dcOpfNewtonMatrix r H Γ scale (.inr (.inr (i : Fin n))) (.inr (.inl i)) =
        G.laplacian (fun _ ↦ 1) i i := rfl
    rw [hvalue] at hbound
    exact hdiag.trans ((le_abs_self _).trans hbound)
  -- the side of the separation that excludes the slack bus
  have hmemBv : ∀ v, v ∈ Bv ↔ v ∉ A ∪ X := by
    intro v
    constructor
    · intro hv hAX
      exact Finset.disjoint_left.mp hdisj hAX hv
    · intro hv
      have hmem := Finset.mem_univ v
      rw [← hcover] at hmem
      rcases Finset.mem_union.mp hmem with h | h
      · exact absurd h hv
      · exact h
  obtain ⟨S, hrS, hS_size, hS_boundary⟩ : ∃ S : Finset (Fin n),
      r ∉ S ∧ β * n ≤ (S.card : ℝ) ∧ G.boundaryEdges S = G.boundaryEdges (A ∪ X) := by
    by_cases hr : r ∈ Bv
    · exact ⟨A ∪ X, (hmemBv r).mp hr, hA_size, rfl⟩
    · refine ⟨Bv, hr, hB_size, ?_⟩
      ext e
      simp only [WeightedGraph.boundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and,
        hmemBv]
      tauto
  have hcard_le : ((G.boundaryEdges S).card : ℝ) ≤ s * Δ := by
    rw [hS_boundary]
    have hboundary : (G.boundaryEdges (A ∪ X)).card ≤
        ∑ x ∈ X, (G.incidentEdges x).card :=
      le_trans
        (Finset.card_le_card (boundaryEdges_subset_incident G A X Bv hcover hnoAB))
        Finset.card_biUnion_le
    calc
      ((G.boundaryEdges (A ∪ X)).card : ℝ) ≤
          ((∑ x ∈ X, (G.incidentEdges x).card : ℕ) : ℝ) := by
        exact_mod_cast hboundary
      _ = ∑ x ∈ X, ((G.incidentEdges x).card : ℝ) := by push_cast; rfl
      _ ≤ ∑ _x ∈ X, Δ := Finset.sum_le_sum fun x _ ↦ hdeg x
      _ = (X.card : ℝ) * Δ := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ s * Δ := mul_le_mul_of_nonneg_right hX hΔ_nonneg
  -- the test vector is the indicator of that side, placed in the angle coordinates
  have hxr : busIndicator S r = 0 := by simp [busIndicator, hrS]
  have hlow := hlower (angleEmbedding g r (busIndicator S))
  rw [sum_sq_angleEmbedding r _ hxr, sum_sq_busIndicator,
    G.dcOpfNewtonMatrix_mulVec_angleEmbedding r H Γ scale _ hxr,
    Fintype.sum_sum_type, Fintype.sum_sum_type] at hlow
  simp only [Sum.elim_inl, Sum.elim_inr] at hlow
  have hzero : ∑ _a : Fin g, (0 : ℝ) ^ 2 = 0 := by simp
  rw [hzero, zero_add] at hlow
  have hangle : ∑ i : GroundedIndex r, (∑ j, G.laplacian scale i j * busIndicator S j) ^ 2 ≤
      ∑ i, (∑ j, G.laplacian scale i j * busIndicator S j) ^ 2 :=
    sum_groundedIndex_le r (fun i ↦ (∑ j, G.laplacian scale i j * busIndicator S j) ^ 2)
      (sq_nonneg _)
  have hL := G.sum_sq_laplacian_mulVec_busIndicator_le scale S Δ σmax
    (fun e ↦ (hscale e).le) hscaled_le hdeg
  have hB := G.sum_sq_laplacian_mulVec_busIndicator_le (fun _ ↦ 1) S Δ σmax
    (fun _ ↦ zero_le_one) hunit_le hdeg
  have hcut : 2 * Δ * ((G.boundaryEdges S).card : ℝ) * σmax ^ 2 ≤
      2 * Δ * (s * Δ) * σmax ^ 2 := by
    have hfactor : 0 ≤ 2 * Δ := by positivity
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcard_le hfactor)
      (sq_nonneg σmax)
  have hσmin_sq : 0 < σmin ^ 2 := pow_pos hσmin 2
  have hkey : σmin ^ 2 * (β * n) ≤ 4 * s * Δ ^ 2 * σmax ^ 2 := by
    have hsize : σmin ^ 2 * (β * n) ≤ σmin ^ 2 * (S.card : ℝ) :=
      mul_le_mul_of_nonneg_left hS_size hσmin_sq.le
    nlinarith [hsize, hlow, hangle, hL, hB, hcut]
  have hprod_pos : 0 < 4 * s * Δ ^ 2 * σmax ^ 2 :=
    lt_of_lt_of_le (mul_pos hσmin_sq (mul_pos hβ hn_pos)) hkey
  have hs_pos : 0 < s := by
    by_contra hs
    push_neg at hs
    have hnonneg : 0 ≤ Δ ^ 2 * σmax ^ 2 := by positivity
    nlinarith
  have hΔ_pos : 0 < Δ := by
    refine lt_of_le_of_ne hΔ_nonneg ?_
    intro hzero
    rw [← hzero] at hprod_pos
    norm_num at hprod_pos
  have hratio : β * n / s ≤ (2 * Δ * σmax / σmin) ^ 2 := by
    rw [div_le_iff₀ hs_pos, div_pow, div_mul_eq_mul_div, le_div_iff₀ hσmin_sq]
    nlinarith [hkey]
  have hsqrt : Real.sqrt (β * n / s) ≤ 2 * Δ * σmax / σmin :=
    Real.sqrt_le_iff.mpr ⟨by positivity, hratio⟩
  calc
    Real.sqrt (β * n / s) / (2 * Δ) ≤ (2 * Δ * σmax / σmin) / (2 * Δ) :=
      div_le_div_of_nonneg_right hsqrt (by positivity)
    _ = σmax / σmin := by
      field_simp

/-- The angle block of the Newton matrix is the grounded Laplacian with the rescaled weights. -/
theorem WeightedGraph.dcOpfNewtonMatrix_angle_block (G : WeightedGraph n m) (r : Fin n)
    (H : Matrix (Fin g) (Fin g) ℝ) (Γ : Matrix (Fin n) (Fin g) ℝ)
    (scale : Fin m → ℝ) (hscale : ∀ e, 0 < scale e) (i j : GroundedIndex r) :
    G.dcOpfNewtonMatrix r H Γ scale (.inr (.inl i)) (.inr (.inl j)) =
      groundedLaplacian
        (G.withWeights (fun e ↦ scale e * G.weights e)
          (fun e ↦ mul_pos (hscale e) (G.weights_pos e))) r i j := by
  change G.laplacian scale i j = _
  rw [groundedLaplacian_apply]
  unfold WeightedGraph.laplacian
  refine Finset.sum_congr rfl fun e _ ↦ ?_
  simp only [WeightedGraph.withWeights]
  ring

/-- The barrier Hessian block `L_w` of the Newton system inherits the grounded separator bound at
every iterate: `κ₂(L_w) ≥ β (1 - β) n / (s Δ)` for every positive choice of the weights. -/
theorem WeightedGraph.dcOpfGroundedBlock_condition_bound (G : WeightedGraph n m) (r : Fin n)
    (scale : Fin m → ℝ) (hscale : ∀ e, 0 < scale e)
    (A X Bv : Finset (Fin n)) (s Δ β : ℝ)
    (hcover : A ∪ X ∪ Bv = Finset.univ)
    (hdisj : Disjoint (A ∪ X) Bv)
    (hnoAB : ∀ e, ¬(G.posEndpoint e ∈ A ∧ G.negEndpoint e ∈ Bv) ∧
      ¬(G.posEndpoint e ∈ Bv ∧ G.negEndpoint e ∈ A))
    (hX : (X.card : ℝ) ≤ s)
    (hdeg : ∀ i, ((G.incidentEdges i).card : ℝ) ≤ Δ)
    (hβ : 0 < β) (hβ' : β ≤ 1 / 2)
    (hA_size : β * n ≤ ((A ∪ X).card : ℝ)) (hB_size : β * n ≤ (Bv.card : ℝ))
    (hconn : G.CombinatoriallyConnected) :
    β * (1 - β) * n / (s * Δ) ≤
      groundedConditionNumber
        (G.withWeights (fun e ↦ scale e * G.weights e)
          (fun e ↦ mul_pos (hscale e) (G.weights_pos e))) r :=
  grounded_separator_kappa_bound_topological
    (G.withWeights (fun e ↦ scale e * G.weights e)
      (fun e ↦ mul_pos (hscale e) (G.weights_pos e)))
    r A X Bv s Δ β hcover hdisj hnoAB hX hdeg hβ hβ' hA_size hB_size
    ((G.withWeights_combinatoriallyConnected_iff _ _).mpr hconn)

end
