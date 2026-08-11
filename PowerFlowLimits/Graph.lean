/-
Copyright (c) 2026 Cameron Khanpour and Samuel Talkington. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Cameron Khanpour, Samuel Talkington
-/
import Mathlib.Tactic

/-!
# Weighted graphs: oriented incidence structure, endpoints, cuts, and degrees

Part of the Lean 4 formalization of
"The Limits of Quantum Computers for Power Flow" (Khanpour and Talkington).
-/

open Finset BigOperators

noncomputable section

variable {n m : ℕ}

/-- A weighted graph with `n` nodes and `m` edges. -/
structure WeightedGraph (n m : ℕ) where
  /-- Edge weights w ∈ ℝ^m, all positive -/
  weights : Fin m → ℝ
  weights_pos : ∀ e, 0 < weights e
  /-- Oriented incidence matrix: A_{i,e} ∈ {-1, 0, +1} -/
  incidence : Fin n → Fin m → ℝ
  /-- Each column has a unique +1 endpoint. -/
  incidence_pos_unique : ∀ e, ∃! i, incidence i e = 1
  /-- Each column has a unique -1 endpoint. -/
  incidence_neg_unique : ∀ e, ∃! i, incidence i e = -1
  /-- Each column sums to zero (oriented edges) -/
  incidence_col_sum : ∀ e, ∑ i, incidence i e = 0
  /-- Each column has entries in {-1, 0, +1} -/
  incidence_values : ∀ i e, incidence i e = -1 ∨ incidence i e = 0 ∨ incidence i e = 1

namespace WeightedGraph

/-- The unique head of edge `e`, where the incidence column equals `+1`. -/
def posEndpoint (G : WeightedGraph n m) (e : Fin m) : Fin n :=
  Classical.choose <| ExistsUnique.exists (G.incidence_pos_unique e)

/-- The unique tail of edge `e`, where the incidence column equals `-1`. -/
def negEndpoint (G : WeightedGraph n m) (e : Fin m) : Fin n :=
  Classical.choose <| ExistsUnique.exists (G.incidence_neg_unique e)

theorem incidence_posEndpoint (G : WeightedGraph n m) (e : Fin m) :
    G.incidence (G.posEndpoint e) e = 1 :=
  Classical.choose_spec <| ExistsUnique.exists (G.incidence_pos_unique e)

theorem incidence_negEndpoint (G : WeightedGraph n m) (e : Fin m) :
    G.incidence (G.negEndpoint e) e = -1 :=
  Classical.choose_spec <| ExistsUnique.exists (G.incidence_neg_unique e)

theorem posEndpoint_unique (G : WeightedGraph n m) (e : Fin m) (i : Fin n)
    (hi : G.incidence i e = 1) :
    i = G.posEndpoint e :=
  ExistsUnique.unique (G.incidence_pos_unique e) hi (G.incidence_posEndpoint e)

theorem negEndpoint_unique (G : WeightedGraph n m) (e : Fin m) (i : Fin n)
    (hi : G.incidence i e = -1) :
    i = G.negEndpoint e :=
  ExistsUnique.unique (G.incidence_neg_unique e) hi (G.incidence_negEndpoint e)

theorem endpoints_ne (G : WeightedGraph n m) (e : Fin m) :
    G.posEndpoint e ≠ G.negEndpoint e := by
  intro h
  have hpos := G.incidence_posEndpoint e
  have hneg := G.incidence_negEndpoint e
  have hneg' : G.incidence (G.posEndpoint e) e = -1 := by simpa [h] using hneg
  linarith [hpos, hneg']

theorem incidence_eq_zero_of_ne_endpoints (G : WeightedGraph n m) (e : Fin m) (i : Fin n)
    (hpos : i ≠ G.posEndpoint e) (hneg : i ≠ G.negEndpoint e) :
    G.incidence i e = 0 := by
  rcases G.incidence_values i e with h | h | h
  · exact (hneg (G.negEndpoint_unique e i h)).elim
  · exact h
  · exact (hpos (G.posEndpoint_unique e i h)).elim

theorem incidence_col_sq_sum_eq_two (G : WeightedGraph n m) (e : Fin m) :
    ∑ i : Fin n, G.incidence i e ^ 2 = 2 := by
  let ipos := G.posEndpoint e
  let ineg := G.negEndpoint e
  have hneq : ipos ≠ ineg := G.endpoints_ne e
  have hpointwise : ∀ i : Fin n,
      G.incidence i e ^ 2 =
        (if i = ipos then 1 else 0) + (if i = ineg then 1 else 0) := by
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
  norm_num

end WeightedGraph

/-- Standard basis vector: 1 at position i₀, 0 elsewhere. -/
def stdBasis (i₀ : Fin n) : Fin n → ℝ := fun j => if j = i₀ then 1 else 0

/-- Orthogonal projector onto 1⊥: (Pv)ᵢ = vᵢ - (∑ⱼ vⱼ)/n -/
def proj (v : Fin n → ℝ) : Fin n → ℝ :=
  fun i => v i - (∑ j, v j) / (n : ℝ)

theorem proj_sum_zero (v : Fin n → ℝ) (hn : 0 < n) :
    ∑ i, proj v i = 0 := by
  simp only [proj]
  rw [Finset.sum_sub_distrib]
  have : ∑ _i : Fin n, (∑ j, v j) / (n : ℝ) = ∑ j, v j := by
    rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    exact mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hn))
  rw [this, sub_self]

/-- Total branch susceptance b(E) = Σ_e b_e. -/
def WeightedGraph.totalWeight (G : WeightedGraph n m) : ℝ :=
  ∑ e, G.weights e

/-- Same branch topology and incidence matrix with new positive susceptances. -/
def WeightedGraph.withWeights (G : WeightedGraph n m) (w : Fin m → ℝ)
    (hw : ∀ e, 0 < w e) : WeightedGraph n m :=
  { G with weights := w, weights_pos := hw }

/-- Weighted cut b(∂S): each edge contributes its weight iff exactly one
    endpoint lies in `S` (the squared indicator difference is 1 on boundary
    edges and 0 otherwise). -/
def WeightedGraph.cutWeight (G : WeightedGraph n m) (S : Finset (Fin n)) : ℝ :=
  ∑ e, G.weights e *
    ((if G.posEndpoint e ∈ S then (1 : ℝ) else 0) -
     (if G.negEndpoint e ∈ S then (1 : ℝ) else 0)) ^ 2

/-- Branches incident to node `i`. -/
def WeightedGraph.incidentEdges (G : WeightedGraph n m) (i : Fin n) : Finset (Fin m) :=
  Finset.univ.filter fun e => i = G.posEndpoint e ∨ i = G.negEndpoint e

/-- Boundary branches of a node set: exactly one endpoint inside. -/
def WeightedGraph.boundaryEdges (G : WeightedGraph n m) (S : Finset (Fin n)) :
    Finset (Fin m) :=
  Finset.univ.filter fun e => ¬((G.posEndpoint e ∈ S) ↔ (G.negEndpoint e ∈ S))

/-- The quadratic-form cut weight is the plain sum over boundary branches. -/
theorem cutWeight_eq_sum_boundary (G : WeightedGraph n m) (S : Finset (Fin n)) :
    G.cutWeight S = ∑ e ∈ G.boundaryEdges S, G.weights e := by
  unfold WeightedGraph.cutWeight WeightedGraph.boundaryEdges
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun e _ => ?_
  by_cases hp : G.posEndpoint e ∈ S <;> by_cases hq : G.negEndpoint e ∈ S <;>
    simp [hp, hq]

/-- Weighted degree d_i = Σ_{e ∋ i} b_e: the diagonal of the susceptance
    Laplacian. -/
def WeightedGraph.weightedDegree (G : WeightedGraph n m) (i : Fin n) : ℝ :=
  ∑ e ∈ G.incidentEdges i, G.weights e

/-- Total separator degree as an edge sum: Σ_{x∈X} d_x counts each branch
    once per endpoint it has in X. -/
theorem sum_weightedDegree_eq (G : WeightedGraph n m) (X : Finset (Fin n)) :
    ∑ x ∈ X, G.weightedDegree x =
      ∑ e, G.weights e *
        ((if G.posEndpoint e ∈ X then (1 : ℝ) else 0) +
         (if G.negEndpoint e ∈ X then (1 : ℝ) else 0)) := by
  unfold WeightedGraph.weightedDegree WeightedGraph.incidentEdges
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  have hne := G.endpoints_ne e
  have hsplit : ∀ x : Fin n,
      (if x = G.posEndpoint e ∨ x = G.negEndpoint e then G.weights e else 0) =
        (if x = G.posEndpoint e then G.weights e else 0) +
        (if x = G.negEndpoint e then G.weights e else 0) := by
    intro x
    by_cases h1 : x = G.posEndpoint e
    · subst h1
      rw [if_pos (Or.inl rfl), if_pos rfl, if_neg hne]
      ring
    · by_cases h2 : x = G.negEndpoint e
      · subst h2
        rw [if_pos (Or.inr rfl), if_neg h1, if_pos rfl]
        ring
      · rw [if_neg (by tauto), if_neg h1, if_neg h2]
        ring
  simp_rw [hsplit, Finset.sum_add_distrib, Finset.sum_ite_eq' X,
    mul_add]
  congr 1 <;> by_cases hp : G.posEndpoint e ∈ X <;>
    by_cases hq : G.negEndpoint e ∈ X <;> simp [hp, hq]

end
