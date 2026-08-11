/-
Copyright (c) 2026 Cameron Khanpour and Samuel Talkington. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Cameron Khanpour, Samuel Talkington
-/
import PowerFlowLimits.Graph

/-!
# The susceptance Laplacian: quadratic form, voltage drops, trace, and diagonal

Part of the Lean 4 formalization of
"The Limits of Quantum Computers for Power Flow" (Khanpour and Talkington).
-/

open Finset BigOperators

noncomputable section

variable {n m : ℕ}

/-- Symmetric diagonal dominance for a real square matrix. -/
def Matrix.IsSymmetricDiagonallyDominant {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) : Prop :=
  (∀ i j, M i j = M j i) ∧
    ∀ i, ∑ j ∈ (Finset.univ.erase i), |M i j| ≤ M i i

/-- Weighted Laplacian matrix entry: L_s(i,j) = Σ_e A_{ie} (w_e s_e) A_{je}. -/
def WeightedGraph.laplacian (G : WeightedGraph n m) (s : Fin m → ℝ)
    (i j : Fin n) : ℝ :=
  ∑ e, G.incidence i e * (G.weights e * s e) * G.incidence j e

/-- Voltage drop across edge e: Δx_e = aₑᵀ x = Σᵢ A_{i,e} xᵢ. -/
@[irreducible] def voltageDrop (G : WeightedGraph n m) (x : Fin n → ℝ) (e : Fin m) : ℝ :=
  ∑ i, G.incidence i e * x i

/-- The Laplacian is symmetric: L_s(i,j) = L_s(j,i). -/
theorem WeightedGraph.laplacian_symmetric (G : WeightedGraph n m) (s : Fin m → ℝ)
    (i j : Fin n) :
    G.laplacian s i j = G.laplacian s j i := by
  unfold WeightedGraph.laplacian
  apply Finset.sum_congr rfl
  intro e _; ring

/-- Off-diagonal entries of a positive weighted Laplacian are nonpositive. -/
theorem WeightedGraph.laplacian_offDiag_nonpos (G : WeightedGraph n m)
    (i j : Fin n) (hij : i ≠ j) :
    G.laplacian (fun _ ↦ 1) i j ≤ 0 := by
  unfold WeightedGraph.laplacian
  refine Finset.sum_nonpos fun e _ ↦ ?_
  rcases G.incidence_values i e with hi | hi | hi <;>
    rcases G.incidence_values j e with hj | hj | hj
  · have hie := G.negEndpoint_unique e i hi
    have hje := G.negEndpoint_unique e j hj
    exact (hij (hie.trans hje.symm)).elim
  · rw [hi, hj]
    norm_num
  · rw [hi, hj]
    simpa using neg_nonpos.mpr (G.weights_pos e).le
  · rw [hi, hj]
    norm_num
  · rw [hi, hj]
    norm_num
  · rw [hi, hj]
    norm_num
  · rw [hi, hj]
    simpa using neg_nonpos.mpr (G.weights_pos e).le
  · rw [hi, hj]
    norm_num
  · have hie := G.posEndpoint_unique e i hi
    have hje := G.posEndpoint_unique e j hj
    exact (hij (hie.trans hje.symm)).elim

/-- The Laplacian kills the all-ones vector: Σ_j L_s(i,j) = 0. -/
theorem WeightedGraph.laplacian_kernel (G : WeightedGraph n m) (s : Fin m → ℝ)
    (i : Fin n) :
    ∑ j, G.laplacian s i j = 0 := by
  simp only [WeightedGraph.laplacian]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro e _
  have h_col : ∑ j : Fin n, G.incidence j e = 0 := G.incidence_col_sum e
  trans (G.incidence i e * (G.weights e * s e) * ∑ j : Fin n, G.incidence j e)
  · rw [Finset.mul_sum]
  · rw [h_col, mul_zero]

/-- The unit-switching susceptance Laplacian is symmetric diagonally dominant. -/
theorem WeightedGraph.unitLaplacian_isSDD (G : WeightedGraph n m) :
    Matrix.IsSymmetricDiagonallyDominant (G.laplacian (fun _ ↦ 1)) := by
  constructor
  · exact G.laplacian_symmetric (fun _ ↦ 1)
  · intro i
    have habs : ∑ j ∈ (Finset.univ.erase i), |G.laplacian (fun _ ↦ 1) i j| =
        -∑ j ∈ (Finset.univ.erase i), G.laplacian (fun _ ↦ 1) i j := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      rw [abs_of_nonpos
        (G.laplacian_offDiag_nonpos i j (Finset.mem_erase.mp hj).1.symm)]
    have hrow := G.laplacian_kernel (fun _ ↦ 1) i
    have hsplit := Finset.sum_erase_add Finset.univ
      (fun j ↦ G.laplacian (fun _ ↦ 1) i j) (Finset.mem_univ i)
    rw [habs]
    rw [hrow] at hsplit
    linarith

/-- The Laplacian quadratic form equals the edge sum of squared voltage drops:
    xᵀ L_s x = Σ_e s_e w_e (Δx_e)². -/
theorem laplacian_quadratic (G : WeightedGraph n m) (s : Fin m → ℝ) (x : Fin n → ℝ) :
    ∑ i, x i * ∑ j, G.laplacian s i j * x j =
      ∑ e, s e * G.weights e * (voltageDrop G x e) ^ 2 := by
  simp only [WeightedGraph.laplacian, voltageDrop, sq]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro e _
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  ring

private theorem sq_sub_le_two_mul_sq (a b : ℝ) :
    (a - b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
  nlinarith [sq_nonneg (a + b)]

/-- Voltage drop equals endpoint difference: Δx_e = x_{pos} - x_{neg}. -/
theorem voltageDrop_eq_endpoint_diff (G : WeightedGraph n m) (x : Fin n → ℝ) (e : Fin m) :
    voltageDrop G x e = x (G.posEndpoint e) - x (G.negEndpoint e) := by
  rw [voltageDrop]
  let ipos := G.posEndpoint e
  let ineg := G.negEndpoint e
  have hneq : ipos ≠ ineg := G.endpoints_ne e
  have hpointwise : ∀ i : Fin n,
      G.incidence i e * x i =
        (if i = ipos then x ipos else 0) + (if i = ineg then -(x ineg) else 0) := by
    intro i
    by_cases hi_pos : i = ipos
    · subst hi_pos
      rw [G.incidence_posEndpoint]
      simp [hneq]
    · by_cases hi_neg : i = ineg
      · subst hi_neg
        rw [G.incidence_negEndpoint]
        simp [hi_pos]
      · rw [G.incidence_eq_zero_of_ne_endpoints e i hi_pos hi_neg]
        simp [hi_pos, hi_neg]
  simp_rw [hpointwise, Finset.sum_add_distrib]
  simp [Finset.sum_ite_eq', Finset.mem_univ]
  ring

/-- Voltage drop squared bounded by endpoint squares:
    (Δx_e)² ≤ 2(x_{pos}² + x_{neg}²). -/
theorem voltageDrop_sq_le_endpoint_sq (G : WeightedGraph n m) (x : Fin n → ℝ) (e : Fin m) :
    (voltageDrop G x e) ^ 2 ≤
      2 * (x (G.posEndpoint e) ^ 2 + x (G.negEndpoint e) ^ 2) := by
  rw [voltageDrop_eq_endpoint_diff]
  exact sq_sub_le_two_mul_sq _ _

/-- Trace identity: Σ_i B_ii = 2 b(E), since each incidence column has
    squared norm 2. -/
theorem laplacian_diag_sum (G : WeightedGraph n m) :
    ∑ i, G.laplacian (fun _ => 1) i i = 2 * G.totalWeight := by
  unfold WeightedGraph.laplacian WeightedGraph.totalWeight
  rw [Finset.sum_comm]
  have h_col : ∀ e : Fin m,
      ∑ i, G.incidence i e * (G.weights e * 1) * G.incidence i e =
        2 * G.weights e := by
    intro e
    calc ∑ i, G.incidence i e * (G.weights e * 1) * G.incidence i e
        = G.weights e * ∑ i, G.incidence i e ^ 2 := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ = 2 * G.weights e := by rw [G.incidence_col_sq_sum_eq_two]; ring
  rw [Finset.sum_congr rfl fun e _ => h_col e, ← Finset.mul_sum]

theorem weightedDegree_eq_diag (G : WeightedGraph n m) (i : Fin n) :
    G.weightedDegree i = G.laplacian (fun _ => 1) i i := by
  unfold WeightedGraph.weightedDegree WeightedGraph.incidentEdges
    WeightedGraph.laplacian
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun e _ => ?_
  by_cases h1 : i = G.posEndpoint e
  · rw [if_pos (Or.inl h1), h1, G.incidence_posEndpoint]
    ring
  · by_cases h2 : i = G.negEndpoint e
    · rw [if_pos (Or.inr h2), h2, G.incidence_negEndpoint]
      ring
    · rw [if_neg (by tauto), G.incidence_eq_zero_of_ne_endpoints e i h1 h2]
      ring

end
