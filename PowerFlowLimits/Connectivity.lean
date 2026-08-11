/-
Copyright (c) 2026 Cameron Khanpour and Samuel Talkington. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Cameron Khanpour, Samuel Talkington
-/
import PowerFlowLimits.Laplacian
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Combinatorial connectivity and the weighted Laplacian kernel

The weighted multigraph has a simple underlying adjacency relation. Positive branch weights imply
that the kernel of its weighted Laplacian consists exactly of functions that are constant on the
connected components of that underlying graph.
-/

open Finset BigOperators
open scoped Matrix

noncomputable section

variable {n m : ℕ}

/-- The simple graph obtained by forgetting orientation, multiplicity, and branch weights. -/
def WeightedGraph.toSimpleGraph (G : WeightedGraph n m) : SimpleGraph (Fin n) where
  Adj i j := ∃ e,
    (G.posEndpoint e = i ∧ G.negEndpoint e = j) ∨
      (G.posEndpoint e = j ∧ G.negEndpoint e = i)
  symm := by
    rintro i j ⟨e, h | h⟩
    · exact ⟨e, Or.inr ⟨h.1, h.2⟩⟩
    · exact ⟨e, Or.inl ⟨h.1, h.2⟩⟩
  loopless := ⟨by
    intro i
    rintro ⟨e, h | h⟩
    · exact G.endpoints_ne e (h.1.trans h.2.symm)
    · exact G.endpoints_ne e (h.1.trans h.2.symm)⟩

/-- Ordinary graph connectivity of the buses and branches. -/
def WeightedGraph.CombinatoriallyConnected (G : WeightedGraph n m) : Prop :=
  G.toSimpleGraph.Connected

@[simp]
theorem WeightedGraph.withWeights_combinatoriallyConnected_iff (G : WeightedGraph n m)
    (w : Fin m → ℝ) (hw : ∀ e, 0 < w e) :
    (G.withWeights w hw).CombinatoriallyConnected ↔ G.CombinatoriallyConnected :=
  Iff.rfl

@[simp]
theorem WeightedGraph.toSimpleGraph_adj (G : WeightedGraph n m) (i j : Fin n) :
    G.toSimpleGraph.Adj i j ↔ ∃ e,
      (G.posEndpoint e = i ∧ G.negEndpoint e = j) ∨
        (G.posEndpoint e = j ∧ G.negEndpoint e = i) :=
  Iff.rfl

theorem WeightedGraph.posEndpoint_adj_negEndpoint (G : WeightedGraph n m) (e : Fin m) :
    G.toSimpleGraph.Adj (G.posEndpoint e) (G.negEndpoint e) :=
  ⟨e, Or.inl ⟨rfl, rfl⟩⟩

/-- The simple edge underlying a branch. Parallel branches map to the same simple edge. -/
def WeightedGraph.branchToSimpleEdge (G : WeightedGraph n m) (e : Fin m) :
    G.toSimpleGraph.edgeSet :=
  ⟨s(G.posEndpoint e, G.negEndpoint e), G.posEndpoint_adj_negEndpoint e⟩

/-- Every simple edge is represented by at least one branch. -/
theorem WeightedGraph.branchToSimpleEdge_surjective (G : WeightedGraph n m) :
    Function.Surjective G.branchToSimpleEdge := by
  rintro ⟨edge, hedge⟩
  induction edge using Sym2.inductionOn with
  | _ u v =>
      change G.toSimpleGraph.Adj u v at hedge
      rcases hedge with ⟨e, h | h⟩
      · refine ⟨e, Subtype.ext ?_⟩
        rcases h with ⟨rfl, rfl⟩
        rfl
      · refine ⟨e, Subtype.ext ?_⟩
        rcases h with ⟨rfl, rfl⟩
        exact Sym2.eq_swap

/-- A connected weighted multigraph on `n` buses has at least `n - 1` branches. -/
theorem WeightedGraph.card_sub_one_le_edges (G : WeightedGraph n m)
    (hconn : G.CombinatoriallyConnected) :
    n - 1 ≤ m := by
  classical
  letI : Fintype G.toSimpleGraph.edgeSet := Fintype.ofFinite _
  have hedge_card : Fintype.card G.toSimpleGraph.edgeSet ≤ m := by
    simpa using Fintype.card_le_of_surjective G.branchToSimpleEdge
      G.branchToSimpleEdge_surjective
  have hconnected := hconn.card_vert_le_card_edgeSet_add_one
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at hconnected
  rw [Nat.card_eq_fintype_card] at hconnected
  omega

/-- Matrix multiplication by the weighted Laplacian, expressed as a sum of branch drops. -/
theorem laplacian_mulVec_apply (G : WeightedGraph n m) (s : Fin m → ℝ)
    (x : Fin n → ℝ) (i : Fin n) :
    (G.laplacian s *ᵥ x) i =
      ∑ e, G.incidence i e * (G.weights e * s e) * voltageDrop G x e := by
  simp only [Matrix.mulVec, dotProduct, WeightedGraph.laplacian, voltageDrop]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ ↦ ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  ring

/-- A vector is in the weighted Laplacian kernel exactly when it agrees across every branch. -/
theorem laplacian_mulVec_eq_zero_iff_forall_adj (G : WeightedGraph n m)
    (x : Fin n → ℝ) :
    G.laplacian (fun _ ↦ 1) *ᵥ x = 0 ↔
      ∀ i j, G.toSimpleGraph.Adj i j → x i = x j := by
  classical
  constructor
  · intro hmul i j hij
    have hquad : ∑ i, x i * ∑ j, G.laplacian (fun _ ↦ 1) i j * x j = 0 := by
      apply Finset.sum_eq_zero
      intro v _
      have hv := congrFun hmul v
      simpa [Matrix.mulVec] using congrArg (x v * ·) hv
    have henergy : ∑ e, G.weights e * (voltageDrop G x e) ^ 2 = 0 := by
      calc
        ∑ e, G.weights e * (voltageDrop G x e) ^ 2 =
            ∑ e, 1 * G.weights e * (voltageDrop G x e) ^ 2 := by simp
        _ = ∑ i, x i * ∑ j, G.laplacian (fun _ ↦ 1) i j * x j :=
          (laplacian_quadratic G (fun _ ↦ 1) x).symm
        _ = 0 := hquad
    obtain ⟨e, he⟩ := hij
    have hterm_nonneg : ∀ f ∈ (Finset.univ : Finset (Fin m)),
        0 ≤ G.weights f * (voltageDrop G x f) ^ 2 := by
      intro f _
      exact mul_nonneg (G.weights_pos f).le (sq_nonneg _)
    have hterm_le : G.weights e * (voltageDrop G x e) ^ 2 ≤
        ∑ f, G.weights f * (voltageDrop G x f) ^ 2 :=
      Finset.single_le_sum hterm_nonneg (Finset.mem_univ e)
    rw [henergy] at hterm_le
    have hterm_zero : G.weights e * (voltageDrop G x e) ^ 2 = 0 :=
      le_antisymm hterm_le (mul_nonneg (G.weights_pos e).le (sq_nonneg _))
    have hdrop_sq : (voltageDrop G x e) ^ 2 = 0 :=
      (mul_eq_zero.mp hterm_zero).resolve_left (ne_of_gt (G.weights_pos e))
    have hends : x (G.posEndpoint e) = x (G.negEndpoint e) := by
      rw [voltageDrop_eq_endpoint_diff, sq_eq_zero_iff, sub_eq_zero] at hdrop_sq
      exact hdrop_sq
    rcases he with h | h
    · simpa [h.1, h.2] using hends
    · simpa [h.1, h.2] using hends.symm
  · intro hadj
    funext i
    rw [Pi.zero_apply, laplacian_mulVec_apply]
    apply Finset.sum_eq_zero
    intro e _
    have hends := hadj _ _ (G.posEndpoint_adj_negEndpoint e)
    rw [voltageDrop_eq_endpoint_diff, hends, sub_self]
    ring

/-- On a combinatorially connected weighted graph, the Laplacian kernel is the constants. -/
theorem laplacian_mulVec_eq_zero_iff_constant (G : WeightedGraph n m)
    (hconn : G.CombinatoriallyConnected) (x : Fin n → ℝ) :
    G.laplacian (fun _ ↦ 1) *ᵥ x = 0 ↔ ∃ c, x = fun _ ↦ c := by
  classical
  change G.toSimpleGraph.Connected at hconn
  constructor
  · intro hmul
    have hadj := (laplacian_mulVec_eq_zero_iff_forall_adj G x).mp hmul
    have hsimple : G.toSimpleGraph.lapMatrix ℝ *ᵥ x = 0 :=
      (SimpleGraph.lapMatrix_mulVec_eq_zero_iff_forall_adj G.toSimpleGraph).mpr hadj
    have hreach :=
      (SimpleGraph.lapMatrix_mulVec_eq_zero_iff_forall_reachable G.toSimpleGraph).mp hsimple
    let root : Fin n := Classical.choice hconn.nonempty
    refine ⟨x root, funext fun i ↦ ?_⟩
    exact hreach i root (hconn.preconnected i root)
  · rintro ⟨c, rfl⟩
    apply (laplacian_mulVec_eq_zero_iff_forall_adj G _).mpr
    intro i j _
    rfl

/-- Euclidean bus vectors whose coordinates sum to zero. -/
def zeroSumSubspace (n : ℕ) : Submodule ℝ (EuclideanSpace ℝ (Fin n)) where
  carrier := {x | ∑ i, x i = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    simpa [Finset.sum_add_distrib] using congrArg₂ (· + ·) hx hy
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_setOf_eq, PiLp.smul_apply, smul_eq_mul]
    rw [← Finset.mul_sum, hx, mul_zero]

/-- The coordinate sum as a linear functional on the Euclidean bus space. -/
def coordinateSumLinearMap (n : ℕ) : Module.Dual ℝ (EuclideanSpace ℝ (Fin n)) where
  toFun x := ∑ i, x i
  map_add' := fun x y ↦ by simp [Finset.sum_add_distrib]
  map_smul' := fun c x ↦ by simp [← Finset.mul_sum]

theorem coordinateSumLinearMap_ne_zero (hn : 0 < n) : coordinateSumLinearMap n ≠ 0 := by
  let i : Fin n := ⟨0, hn⟩
  let x : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (Pi.single i 1)
  intro hzero
  have h := LinearMap.congr_fun hzero x
  simp [coordinateSumLinearMap, x, i] at h

theorem zeroSumSubspace_eq_ker (n : ℕ) :
    zeroSumSubspace n = LinearMap.ker (coordinateSumLinearMap n) := by
  ext x
  rfl

/-- The balanced bus space has the expected codimension one. -/
theorem finrank_zeroSumSubspace (hn : 0 < n) :
    Module.finrank ℝ (zeroSumSubspace n) = n - 1 := by
  have hdim := Module.Dual.finrank_ker_add_one_of_ne_zero (coordinateSumLinearMap_ne_zero hn)
  rw [← zeroSumSubspace_eq_ker, finrank_euclideanSpace_fin] at hdim
  omega

/-- Weighted voltage drops, with square-root weights so their Euclidean norm is the energy. -/
def WeightedGraph.weightedDropLinearMap (G : WeightedGraph n m) :
    zeroSumSubspace n →ₗ[ℝ] EuclideanSpace ℝ (Fin m) where
  toFun x := WithLp.toLp 2 fun e ↦
    Real.sqrt (G.weights e) * voltageDrop G (fun i ↦ x.1 i) e
  map_add' := by
    intro x y
    ext e
    simp only [voltageDrop_eq_endpoint_diff, Submodule.coe_add, PiLp.add_apply]
    ring
  map_smul' := by
    intro c x
    ext e
    simp only [RingHom.id_apply, voltageDrop_eq_endpoint_diff, SetLike.val_smul,
      PiLp.smul_apply, smul_eq_mul]
    ring

@[simp]
theorem WeightedGraph.weightedDropLinearMap_apply (G : WeightedGraph n m)
    (x : zeroSumSubspace n) (e : Fin m) :
    G.weightedDropLinearMap x e =
      Real.sqrt (G.weights e) * voltageDrop G (fun i ↦ x.1 i) e :=
  rfl

/-- The squared norm of the weighted drop map is the weighted Laplacian energy. -/
theorem WeightedGraph.weightedDropLinearMap_norm_sq (G : WeightedGraph n m)
    (x : zeroSumSubspace n) :
    ‖G.weightedDropLinearMap x‖ ^ 2 =
      ∑ e, G.weights e * (voltageDrop G (fun i ↦ x.1 i) e) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  refine Finset.sum_congr rfl fun e _ ↦ ?_
  rw [G.weightedDropLinearMap_apply, Real.norm_eq_abs, sq_abs, mul_pow,
    Real.sq_sqrt (G.weights_pos e).le]

/-- On a connected graph with at least one bus, the weighted drop map is injective. -/
theorem WeightedGraph.weightedDropLinearMap_injective (G : WeightedGraph n m)
    (hconn : G.CombinatoriallyConnected) (hn : 0 < n) :
    Function.Injective G.weightedDropLinearMap := by
  intro x y hxy
  apply Subtype.ext
  ext i
  let z : Fin n → ℝ := fun j ↦ x.1 j - y.1 j
  have hdrop : ∀ e, voltageDrop G z e = 0 := by
    intro e
    have he := congrArg (fun v : EuclideanSpace ℝ (Fin m) ↦ v e) hxy
    simp only [G.weightedDropLinearMap_apply] at he
    have hsqrt : 0 < Real.sqrt (G.weights e) := Real.sqrt_pos.2 (G.weights_pos e)
    simp only [z, voltageDrop_eq_endpoint_diff] at he ⊢
    nlinarith
  have hadj : ∀ i j, G.toSimpleGraph.Adj i j → z i = z j := by
    intro u v huv
    rcases huv with ⟨e, h | h⟩
    · have he := hdrop e
      rw [voltageDrop_eq_endpoint_diff] at he
      rcases h with ⟨rfl, rfl⟩
      exact sub_eq_zero.mp he
    · have he := hdrop e
      rw [voltageDrop_eq_endpoint_diff] at he
      rcases h with ⟨rfl, rfl⟩
      exact (sub_eq_zero.mp he).symm
  have hmul : G.laplacian (fun _ ↦ 1) *ᵥ z = 0 :=
    (laplacian_mulVec_eq_zero_iff_forall_adj G z).mpr hadj
  obtain ⟨c, hc⟩ := (laplacian_mulVec_eq_zero_iff_constant G hconn z).mp hmul
  have hxsum : ∑ j, x.1 j = 0 := x.2
  have hysum : ∑ j, y.1 j = 0 := y.2
  have hzsum : ∑ j, z j = 0 := by
    rw [show (∑ j, z j) = (∑ j, x.1 j) - ∑ j, y.1 j by
      simp only [z, Finset.sum_sub_distrib]]
    rw [hxsum, hysum, sub_self]
  have hnc : (n : ℝ) * c = 0 := by
    simpa [hc, Finset.sum_const, Finset.card_fin, nsmul_eq_mul] using hzsum
  have hc0 : c = 0 := (mul_eq_zero.mp hnc).resolve_left (Nat.cast_ne_zero.mpr hn.ne')
  have hzi : z i = 0 := by simp [hc, hc0]
  exact sub_eq_zero.mp hzi

end
