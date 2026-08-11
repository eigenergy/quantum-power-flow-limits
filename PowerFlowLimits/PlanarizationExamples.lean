/-
Copyright (c) 2026 Cameron Khanpour and Samuel Talkington. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Cameron Khanpour, Samuel Talkington
-/
import PowerFlowLimits.PlanarSeparator

/-!
# Compiling examples for the planarization boundary cases

These examples exercise empty and repeated crossing schedules, a crossing-only separator, and two
parallel original branches.
-/

open Finset BigOperators

noncomputable section

/-- Two buses joined by two distinct parallel branches. -/
def parallelTwoBusGraph : WeightedGraph 2 2 where
  weights := fun _ ↦ 1
  weights_pos := by simp
  incidence := fun i _ ↦ if i = 0 then -1 else 1
  incidence_pos_unique := by
    intro e
    refine ⟨1, by simp, ?_⟩
    intro i hi
    fin_cases i
    · norm_num at hi
    · rfl
  incidence_neg_unique := by
    intro e
    refine ⟨0, by simp, ?_⟩
    intro i hi
    fin_cases i
    · rfl
    · norm_num at hi
  incidence_col_sum := by
    intro e
    simp [Fin.sum_univ_two]
  incidence_values := by
    intro i e
    fin_cases i <;> simp

@[simp]
theorem parallelTwoBusGraph_negEndpoint (e : Fin 2) : parallelTwoBusGraph.negEndpoint e = 0 := by
  symm
  exact parallelTwoBusGraph.negEndpoint_unique e 0 (by simp [parallelTwoBusGraph])

@[simp]
theorem parallelTwoBusGraph_posEndpoint (e : Fin 2) : parallelTwoBusGraph.posEndpoint e = 1 := by
  symm
  exact parallelTwoBusGraph.posEndpoint_unique e 1 (by simp [parallelTwoBusGraph])

/-- The crossing-free schedule. -/
def zeroCrossingSchedule : CrossingSchedule parallelTwoBusGraph 0 where
  carriers := Fin.elim0
  carriers_ne := fun x ↦ Fin.elim0 x
  along := fun _ ↦ []
  along_nodup := by simp
  mem_along_iff := fun _ x ↦ Fin.elim0 x

/-- One crossing between the two parallel branches. -/
def oneCrossingSchedule : CrossingSchedule parallelTwoBusGraph 1 where
  carriers := fun _ ↦ (0, 1)
  carriers_ne := by simp
  along := fun _ ↦ [0]
  along_nodup := by simp
  mem_along_iff := by
    intro e x
    fin_cases e <;> fin_cases x <;> simp

/-- Two distinct crossings between the same pair of branches. -/
def repeatedCrossingSchedule : CrossingSchedule parallelTwoBusGraph 2 where
  carriers := fun _ ↦ (0, 1)
  carriers_ne := by simp
  along := fun _ ↦ [0, 1]
  along_nodup := by simp
  mem_along_iff := by
    intro e x
    fin_cases e <;> fin_cases x <;> simp

@[simp]
theorem oneCrossingSchedule_route (e : Fin 2) :
    oneCrossingSchedule.route e = [Sum.inl 0, Sum.inr 0, Sum.inl 1] := by
  simp [CrossingSchedule.route, oneCrossingSchedule]

example (e : Fin 2) :
    zeroCrossingSchedule.route e = [Sum.inl 0, Sum.inl 1] := by
  simp [CrossingSchedule.route, zeroCrossingSchedule]

example (e : Fin 2) :
    oneCrossingSchedule.route e = [Sum.inl 0, Sum.inr 0, Sum.inl 1] := by
  simp

example : repeatedCrossingSchedule.carriers 0 = repeatedCrossingSchedule.carriers 1 := rfl

example (e : Fin 2) :
    repeatedCrossingSchedule.route e =
      [Sum.inl 0, Sum.inr 0, Sum.inr 1, Sum.inl 1] := by
  simp [CrossingSchedule.route, repeatedCrossingSchedule]

/-- The two scheduled carriers are different branch indices with identical original endpoints. -/
example :
    parallelTwoBusGraph.negEndpoint 0 = parallelTwoBusGraph.negEndpoint 1 ∧
      parallelTwoBusGraph.posEndpoint 0 = parallelTwoBusGraph.posEndpoint 1 := by
  simp

private theorem consecutive_isInfix {V : Type*} {vertices : List V} {u v : V}
    (h : CrossingSchedule.Consecutive vertices u v) : [u, v] <:+: vertices := by
  rcases h with ⟨before, after, rfl⟩
  exact ⟨before, after, by simp⟩

theorem oneCrossingSchedule_not_adjacent_original_buses :
    ¬oneCrossingSchedule.planarizedGraph.Adj (Sum.inl 0) (Sum.inl 1) := by
  rw [oneCrossingSchedule.planarizedGraph_adj_iff]
  rintro ⟨_, e, hforward | hreverse⟩
  · rw [oneCrossingSchedule_route] at hforward
    have hinfix := consecutive_isInfix hforward
    have hnot : ¬[Sum.inl (0 : Fin 2), Sum.inl (1 : Fin 2)] <:+:
        [Sum.inl (0 : Fin 2), Sum.inr (0 : Fin 1), Sum.inl (1 : Fin 2)] := by
      decide
    exact hnot hinfix
  · rw [oneCrossingSchedule_route] at hreverse
    have hinfix := consecutive_isInfix hreverse
    have hnot : ¬[Sum.inl (1 : Fin 2), Sum.inl (0 : Fin 2)] <:+:
        [Sum.inl (0 : Fin 2), Sum.inr (0 : Fin 1), Sum.inl (1 : Fin 2)] := by
      decide
    exact hnot hinfix

/-- A valid Lipton--Tarjan output whose separator is exactly the inserted crossing vertex. -/
def crossingOnlyPartition :
    VertexCostPartition oneCrossingSchedule.planarizedGraph busCost where
  left := {Sum.inl 0}
  separator := {Sum.inr 0}
  right := {Sum.inl 1}
  cover := by
    ext z
    cases z with
    | inl v => fin_cases v <;> simp
    | inr x => fin_cases x; simp
  disjoint_left_separator := by simp
  disjoint_left_right := by simp
  disjoint_separator_right := by simp
  no_left_right := by
    intro u v huv
    rintro ⟨hu, hv⟩
    simp only [Finset.mem_singleton] at hu hv
    subst u
    subst v
    exact oneCrossingSchedule_not_adjacent_original_buses huv
  separator_card_le := by
    have hsqrt_nonneg : 0 ≤ Real.sqrt (8 * (Fintype.card (PlanarizedVertex 2 1) : ℝ)) :=
      Real.sqrt_nonneg _
    have hsqrt_sq : (Real.sqrt (8 * (Fintype.card (PlanarizedVertex 2 1) : ℝ))) ^ 2 =
        8 * (Fintype.card (PlanarizedVertex 2 1) : ℝ) := by
      rw [Real.sq_sqrt]
      positivity
    norm_num [CrossingSchedule.card_planarizedVertex] at hsqrt_nonneg hsqrt_sq ⊢
  left_cost_le := by norm_num [busCost]
  right_cost_le := by norm_num [busCost]

example : crossingOnlyPartition.separator = {Sum.inr 0} := rfl

example :
    parallelTwoBusGraph.negEndpoint 0 ∈
      oneCrossingSchedule.projectedSeparator crossingOnlyPartition.separator := by
  exact oneCrossingSchedule.first_carrier_endpoint_mem_projectedSeparator
    (Q := crossingOnlyPartition.separator) (x := 0)
    (by simp [crossingOnlyPartition])
