/-
Copyright (c) 2026 Cameron Khanpour and Samuel Talkington. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Cameron Khanpour, Samuel Talkington
-/
import PowerFlowLimits.Connectivity
import Mathlib.Combinatorics.SimpleGraph.Walks.Basic

/-!
# Planarizing a weighted multigraph at a finite crossing schedule

A crossing schedule records the two original branches that meet at every crossing and the order in
which each branch encounters its crossings. Replacing every crossing by a new vertex gives a simple
graph on `n + c` vertices. Parallel original branches remain distinct at the schedule level even
though the result is a simple graph.
-/

open Finset

noncomputable section

variable {n m c : ℕ}

/-- Original buses together with the vertices inserted at crossings. -/
abbrev PlanarizedVertex (n c : ℕ) := Fin n ⊕ Fin c

/-- Combinatorial data of a drawing with finitely many ordinary pairwise crossings.

The `along` list fixes the order of crossings on each oriented branch. Its membership condition says
that every crossing lies on exactly its two carriers. Distinct crossing indices allow the same pair
of branches to cross more than once. -/
structure CrossingSchedule (G : WeightedGraph n m) (c : ℕ) where
  /-- The two original branches meeting at each crossing. -/
  carriers : Fin c → Fin m × Fin m
  /-- An ordinary crossing never has the same branch as both carriers. -/
  carriers_ne : ∀ x, (carriers x).1 ≠ (carriers x).2
  /-- Crossings encountered along each branch, from its negative to its positive endpoint. -/
  along : Fin m → List (Fin c)
  /-- A branch does not encounter the same crossing twice. -/
  along_nodup : ∀ e, (along e).Nodup
  /-- A crossing occurs on a branch exactly when that branch is one of its two carriers. -/
  mem_along_iff : ∀ e x, x ∈ along e ↔ e = (carriers x).1 ∨ e = (carriers x).2

namespace CrossingSchedule

variable {G : WeightedGraph n m} (S : CrossingSchedule G c)

/-- The vertices encountered while following an original branch through the planarization. -/
def route (e : Fin m) : List (PlanarizedVertex n c) :=
  Sum.inl (G.negEndpoint e) :: (S.along e).map Sum.inr ++ [Sum.inl (G.posEndpoint e)]

@[simp]
theorem route_head (e : Fin m) : (S.route e).head? = some (Sum.inl (G.negEndpoint e)) := by
  simp [route]

@[simp]
theorem route_getLast (e : Fin m) :
    (S.route e).getLast? = some (Sum.inl (G.posEndpoint e)) := by
  change (([Sum.inl (G.negEndpoint e)] ++ (S.along e).map Sum.inr) ++
    [Sum.inl (G.posEndpoint e)]).getLast? = _
  rw [List.getLast?_append_of_ne_nil _ (by simp)]
  rfl

@[simp]
theorem crossing_mem_route_iff (e : Fin m) (x : Fin c) :
    Sum.inr x ∈ S.route e ↔ e = (S.carriers x).1 ∨ e = (S.carriers x).2 := by
  simp [route, S.mem_along_iff]

@[simp]
theorem bus_mem_route_iff (e : Fin m) (v : Fin n) :
    Sum.inl v ∈ S.route e ↔ v = G.negEndpoint e ∨ v = G.posEndpoint e := by
  simp [route, eq_comm]

theorem route_nodup (e : Fin m) : (S.route e).Nodup := by
  let insertCrossing : Fin c → PlanarizedVertex n c := Sum.inr
  have hcrossings : ((S.along e).map insertCrossing).Nodup :=
    (S.along_nodup e).map Sum.inr_injective
  rw [route]
  refine (List.nodup_cons.mpr ⟨?_, hcrossings⟩).append (by simp) ?_
  · simp [insertCrossing]
  · simp [List.disjoint_singleton, insertCrossing, G.endpoints_ne e]

/-- Two vertices occur consecutively in a list, in the displayed order. -/
def Consecutive {V : Type*} (vertices : List V) (u v : V) : Prop :=
  ∃ before after, vertices = before ++ u :: v :: after

/-- The planarized simple graph: two distinct vertices are adjacent exactly when they are
consecutive along the route of an original branch. -/
def planarizedGraph : SimpleGraph (PlanarizedVertex n c) where
  Adj u v := u ≠ v ∧ ∃ e, Consecutive (S.route e) u v ∨ Consecutive (S.route e) v u
  symm := by
    rintro u v ⟨hne, e, h⟩
    exact ⟨hne.symm, e, h.symm⟩
  loopless := ⟨by simp⟩

@[simp]
theorem planarizedGraph_adj_iff (u v : PlanarizedVertex n c) :
    S.planarizedGraph.Adj u v ↔
      u ≠ v ∧ ∃ e, Consecutive (S.route e) u v ∨ Consecutive (S.route e) v u :=
  Iff.rfl

private theorem consecutive_ne_of_nodup {V : Type*} {vertices : List V} {u v : V}
    (hnodup : vertices.Nodup) (h : Consecutive vertices u v) : u ≠ v := by
  rintro rfl
  rcases h with ⟨before, after, rfl⟩
  have htail : (u :: u :: after).Nodup := hnodup.of_append_right
  have hnotmem : u ∉ u :: after := (List.nodup_cons.mp htail).1
  exact hnotmem (by simp)

/-- The branch route is a chain in the planarized graph. -/
theorem route_isChain (e : Fin m) :
    List.IsChain S.planarizedGraph.Adj (S.route e) := by
  rw [List.isChain_iff_forall_rel_of_append_cons_cons]
  intro u v before after hroute
  have hconsecutive : Consecutive (S.route e) u v := ⟨before, after, hroute⟩
  exact ⟨consecutive_ne_of_nodup (S.route_nodup e) hconsecutive,
    e, Or.inl hconsecutive⟩

private theorem exists_walk_with_support_of_isChain {V : Type*} (H : SimpleGraph V) :
    ∀ (middle : List V) (u v : V), List.IsChain H.Adj (u :: middle ++ [v]) →
      ∃ p : H.Walk u v, p.support = u :: middle ++ [v] := by
  intro middle
  induction middle with
  | nil =>
      intro u v hchain
      change List.IsChain H.Adj [u, v] at hchain
      have huv : H.Adj u v := List.isChain_pair.mp hchain
      exact ⟨SimpleGraph.Walk.cons huv SimpleGraph.Walk.nil, rfl⟩
  | cons x xs ih =>
      intro u v hchain
      change List.IsChain H.Adj (u :: x :: xs ++ [v]) at hchain
      cases hchain with
      | cons_cons hux htail =>
          rcases ih x v htail with ⟨p, hp⟩
          exact ⟨SimpleGraph.Walk.cons hux p, by simp [hp]⟩

/-- Every original branch becomes a walk from its negative endpoint to its positive endpoint. -/
theorem exists_route_walk (e : Fin m) :
    ∃ p : S.planarizedGraph.Walk (Sum.inl (G.negEndpoint e)) (Sum.inl (G.posEndpoint e)),
      p.support = S.route e := by
  apply exists_walk_with_support_of_isChain S.planarizedGraph (S.along e |>.map Sum.inr)
    (Sum.inl (G.negEndpoint e)) (Sum.inl (G.posEndpoint e))
  exact S.route_isChain e

/-- The planarization has exactly `n + c` vertices. -/
theorem card_planarizedVertex : Fintype.card (PlanarizedVertex n c) = n + c := by
  simp [PlanarizedVertex]

end CrossingSchedule
