/-
Copyright (c) 2026 Cameron Khanpour and Samuel Talkington. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Cameron Khanpour, Samuel Talkington
-/
import PowerFlowLimits.Separators
import Mathlib.Data.Finset.Max

/-!
# Finite rooted trees and balanced tree-decomposition bags

Mathlib 4.28 has no tree decomposition or treewidth API. This file starts the missing
Corollary 1(i) dependency with a finite rooted-tree model and a kernel-checked weighted centroid
theorem. The later graph bridge uses this centroid for the bags of a standard tree decomposition.
-/

open Finset

noncomputable section

/-- A finite rooted tree represented by a parent map and a strictly decreasing depth certificate.
Every nonroot node points toward the root. -/
structure FiniteRootedTree (k : ℕ) where
  /-- Distinguished root node. -/
  root : Fin k
  /-- Parent of each node, with the root as its own parent. -/
  parent : Fin k → Fin k
  /-- Rank that strictly decreases along every nonroot parent edge. -/
  depth : Fin k → ℕ
  parent_root : parent root = root
  parent_depth_lt : ∀ v, v ≠ root → depth (parent v) < depth v

namespace FiniteRootedTree

variable {k : ℕ} (T : FiniteRootedTree k)

/-- One upward parent step. -/
def ParentStep (u v : Fin k) : Prop := u ≠ T.root ∧ T.parent u = v

/-- `v` lies in the rooted subtree at `t`. -/
def IsDescendant (t v : Fin k) : Prop :=
  Relation.ReflTransGen T.ParentStep v t

theorem isDescendant_refl (t : Fin k) : T.IsDescendant t t :=
  Relation.ReflTransGen.refl

theorem isDescendant_root (v : Fin k) : T.IsDescendant T.root v := by
  generalize hd : T.depth v = d
  induction d using Nat.strong_induction_on generalizing v with
  | h d ih =>
      by_cases hv : v = T.root
      · subst v
        exact T.isDescendant_refl T.root
      · have hpdepth : T.depth (T.parent v) < d := by
          simpa [hd] using T.parent_depth_lt v hv
        have hp : T.IsDescendant T.root (T.parent v) :=
          ih (T.depth (T.parent v)) hpdepth (T.parent v) rfl
        exact hp.head ⟨hv, rfl⟩

theorem parent_ne_self (v : Fin k) (hv : v ≠ T.root) : T.parent v ≠ v := by
  intro hp
  have hdepth := T.parent_depth_lt v hv
  rw [hp] at hdepth
  exact (Nat.lt_irrefl _ hdepth)

/-- The undirected simple graph represented by the parent map. -/
def toSimpleGraph : SimpleGraph (Fin k) where
  Adj u v := T.ParentStep u v ∨ T.ParentStep v u
  symm := by
    intro u v h
    exact h.symm
  loopless := ⟨by
    intro v h
    rcases h with h | h
    · exact T.parent_ne_self v h.1 h.2
    · exact T.parent_ne_self v h.1 h.2⟩

theorem isDescendant_parent_of_ne {t v : Fin k}
    (h : T.IsDescendant t v) (hvt : v ≠ t) :
    T.IsDescendant t (T.parent v) := by
  rcases h.cases_head with h | ⟨u, hvu, hut⟩
  · exact False.elim (hvt h)
  · simpa [hvu.2] using hut

theorem isDescendant_of_parent {t v : Fin k}
    (h : T.IsDescendant t (T.parent v)) : T.IsDescendant t v := by
  by_cases hv : v = T.root
  · subst v
    simpa [T.parent_root] using h
  · exact h.head ⟨hv, rfl⟩

/-- Descendancy relative to a deleted node is constant across every remaining tree edge. -/
theorem isDescendant_iff_of_adj {t u v : Fin k}
    (hadj : T.toSimpleGraph.Adj u v) (hut : u ≠ t) (hvt : v ≠ t) :
    T.IsDescendant t u ↔ T.IsDescendant t v := by
  rcases hadj with huv | hvu
  · constructor
    · intro hu
      have hp := T.isDescendant_parent_of_ne hu hut
      simpa [huv.2] using hp
    · intro hv
      apply T.isDescendant_of_parent
      simpa [huv.2] using hv
  · constructor
    · intro hu
      apply T.isDescendant_of_parent
      simpa [hvu.2] using hu
    · intro hv
      have hp := T.isDescendant_parent_of_ne hv hvt
      simpa [hvu.2] using hp

theorem isDescendant_trans {a b v : Fin k}
    (hvb : T.IsDescendant b v) (hba : T.IsDescendant a b) :
    T.IsDescendant a v :=
  hvb.trans hba

/-- Every strict descendant lies below a child of the ancestor. -/
theorem exists_child_ancestor {t v : Fin k}
    (hdesc : T.IsDescendant t v) (hvt : v ≠ t) :
    ∃ c : Fin k, c ≠ t ∧ T.parent c = t ∧ T.IsDescendant c v := by
  rcases hdesc.cases_tail with h | ⟨c, hvc, hct⟩
  · exact False.elim (hvt h.symm)
  · have hct_ne : c ≠ t := by
      intro h
      subst t
      exact T.parent_ne_self c hct.1 hct.2
    exact ⟨c, hct_ne, hct.2, hvc⟩

/-- Total node weight. -/
def totalWeight (weight : Fin k → ℕ) : ℕ :=
  ∑ v, weight v

/-- Weight assigned to the rooted subtree at `t`. -/
noncomputable def subtreeWeight (weight : Fin k → ℕ) (t : Fin k) : ℕ := by
  classical
  exact ∑ v with T.IsDescendant t v, weight v

theorem subtreeWeight_root (weight : Fin k → ℕ) :
    T.subtreeWeight weight T.root = totalWeight weight := by
  classical
  simp [subtreeWeight, totalWeight, T.isDescendant_root]

/-- A weighted centroid certificate in parent-map form. Child subtrees and the region above the
centroid each carry at most half of the total weight. -/
theorem exists_weighted_centroid (weight : Fin k → ℕ)
    (htotal : 0 < totalWeight weight) :
    ∃ t : Fin k,
      2 * (totalWeight weight - T.subtreeWeight weight t) ≤ totalWeight weight ∧
      ∀ c : Fin k, c ≠ t → T.parent c = t →
        2 * T.subtreeWeight weight c ≤ totalWeight weight := by
  classical
  let heavy : Finset (Fin k) :=
    Finset.univ.filter fun t ↦ totalWeight weight < 2 * T.subtreeWeight weight t
  have hroot : T.root ∈ heavy := by
    simp only [heavy, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [T.subtreeWeight_root]
    omega
  obtain ⟨t, ht, htmax⟩ :=
    Finset.exists_max_image heavy T.depth ⟨T.root, hroot⟩
  refine ⟨t, ?_, ?_⟩
  · have ht_heavy : totalWeight weight < 2 * T.subtreeWeight weight t :=
      (Finset.mem_filter.mp ht).2
    omega
  · intro c hct hparent
    by_contra hbound
    have hc_heavy : c ∈ heavy := by
      simp only [heavy, Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    have hcroot : c ≠ T.root := by
      intro hc
      subst c
      rw [T.parent_root] at hparent
      exact hct hparent
    have hdepth := T.parent_depth_lt c hcroot
    rw [hparent] at hdepth
    exact (Nat.not_lt_of_ge (htmax c hc_heavy)) hdepth

/-- The parent tree after deleting one node. -/
def treeOff (t : Fin k) : SimpleGraph {v : Fin k // v ≠ t} :=
  T.toSimpleGraph.induce {v | v ≠ t}

theorem isDescendant_iff_of_reachable {t : Fin k}
    {u v : {x : Fin k // x ≠ t}} (hreach : (T.treeOff t).Reachable u v) :
    T.IsDescendant t u ↔ T.IsDescendant t v := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
  induction hreach with
  | refl => exact Iff.rfl
  | @tail a b hab hadj ih =>
      exact ih.trans (T.isDescendant_iff_of_adj hadj a.property b.property)

theorem isDescendant_iff_of_adj_of_parent_deleted {t child u v : Fin k}
    (hparent : T.parent child = t)
    (hadj : T.toSimpleGraph.Adj u v) (hut : u ≠ t) (hvt : v ≠ t) :
    T.IsDescendant child u ↔ T.IsDescendant child v := by
  by_cases hu : u = child
  · subst u
    have hvdesc : T.IsDescendant child v := by
      rcases hadj with huv | hvu
      · exact False.elim (hvt (huv.2.symm.trans hparent))
      · exact Relation.ReflTransGen.single hvu
    exact ⟨fun _ ↦ hvdesc, fun _ ↦ T.isDescendant_refl child⟩
  · by_cases hv : v = child
    · subst v
      have hudesc : T.IsDescendant child u := by
        rcases hadj with huv | hvu
        · exact Relation.ReflTransGen.single huv
        · exact False.elim (hut (hvu.2.symm.trans hparent))
      exact ⟨fun _ ↦ T.isDescendant_refl child, fun _ ↦ hudesc⟩
    · exact T.isDescendant_iff_of_adj hadj hu hv

theorem isDescendant_iff_of_reachable_child {t child : Fin k}
    (hparent : T.parent child = t) {u v : {x : Fin k // x ≠ t}}
    (hreach : (T.treeOff t).Reachable u v) :
    T.IsDescendant child u ↔ T.IsDescendant child v := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
  induction hreach with
  | refl => exact Iff.rfl
  | @tail a b hab hadj ih =>
      exact ih.trans (T.isDescendant_iff_of_adj_of_parent_deleted
        hparent hadj a.property b.property)

/-- Weight in one connected component of the parent tree after deleting `t`. -/
noncomputable def componentWeight (weight : Fin k → ℕ) (t : Fin k)
    (c : (T.treeOff t).ConnectedComponent) : ℕ := by
  classical
  exact ∑ v with ∃ hv : v ≠ t,
    (T.treeOff t).connectedComponentMk ⟨v, hv⟩ = c, weight v

/-- Weight outside the rooted subtree at `t`. -/
noncomputable def outsideWeight (weight : Fin k → ℕ) (t : Fin k) : ℕ := by
  classical
  exact ∑ v with ¬T.IsDescendant t v, weight v

theorem subtreeWeight_add_outsideWeight (weight : Fin k → ℕ) (t : Fin k) :
    T.subtreeWeight weight t + T.outsideWeight weight t = totalWeight weight := by
  classical
  simp only [subtreeWeight, outsideWeight, totalWeight]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun v ↦ T.IsDescendant t v) weight]

/-- The weighted centroid controls every actual component after its deletion. -/
theorem exists_weighted_centroid_component_bound (weight : Fin k → ℕ)
    (htotal : 0 < totalWeight weight) :
    ∃ t : Fin k, ∀ c : (T.treeOff t).ConnectedComponent,
      2 * T.componentWeight weight t c ≤ totalWeight weight := by
  classical
  obtain ⟨t, habove, hchildren⟩ := T.exists_weighted_centroid weight htotal
  refine ⟨t, ?_⟩
  intro component
  induction component using SimpleGraph.ConnectedComponent.ind with
  | _ r =>
      by_cases hrdesc : T.IsDescendant t r.1
      · obtain ⟨child, hchild_ne, hparent, hrchild⟩ :=
          T.exists_child_ancestor hrdesc r.2
        have hcomponent_le : T.componentWeight weight t
            ((T.treeOff t).connectedComponentMk r) ≤ T.subtreeWeight weight child := by
          unfold componentWeight subtreeWeight
          apply Finset.sum_le_sum_of_subset
          intro v hv
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
          obtain ⟨hvt, hcomponent⟩ := hv
          have hreach := SimpleGraph.ConnectedComponent.exact hcomponent
          have hsame := T.isDescendant_iff_of_reachable_child hparent hreach
          exact hsame.mpr hrchild
        exact le_trans (Nat.mul_le_mul_left 2 hcomponent_le)
          (hchildren child hchild_ne hparent)
      · have hcomponent_le : T.componentWeight weight t
            ((T.treeOff t).connectedComponentMk r) ≤ T.outsideWeight weight t := by
          unfold componentWeight outsideWeight
          apply Finset.sum_le_sum_of_subset
          intro v hv
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
          obtain ⟨hvt, hcomponent⟩ := hv
          have hreach := SimpleGraph.ConnectedComponent.exact hcomponent
          have hsame := T.isDescendant_iff_of_reachable hreach
          exact fun hvdesc ↦ hrdesc (hsame.mp hvdesc)
        have hout :
            T.outsideWeight weight t = totalWeight weight - T.subtreeWeight weight t := by
          have hsplit := T.subtreeWeight_add_outsideWeight weight t
          omega
        rw [hout] at hcomponent_le
        exact le_trans (Nat.mul_le_mul_left 2 hcomponent_le) habove

end FiniteRootedTree

/-- A standard tree decomposition, with its finite tree presented by a rooted parent map. -/
structure RootedTreeDecomposition {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (k : ℕ) where
  /-- Tree indexing the decomposition bags. -/
  tree : FiniteRootedTree k
  /-- Graph vertices assigned to each tree node. -/
  bag : Fin k → Finset V
  vertex_mem : ∀ v : V, ∃ t, v ∈ bag t
  edge_mem : ∀ {u v : V}, G.Adj u v → ∃ t, u ∈ bag t ∧ v ∈ bag t
  running : ∀ v : V,
    (tree.toSimpleGraph.induce {t | v ∈ bag t}).Preconnected

namespace RootedTreeDecomposition

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {k : ℕ} (D : RootedTreeDecomposition G k)

/-- Width at most `τ` means every bag contains at most `τ + 1` vertices. -/
def HasWidthAtMost (τ : ℕ) : Prop :=
  ∀ t, (D.bag t).card ≤ τ + 1

/-- A chosen bag occurrence for each graph vertex. -/
noncomputable def home (v : V) : Fin k :=
  Classical.choose (D.vertex_mem v)

omit [Fintype V] in theorem home_mem (v : V) : v ∈ D.bag (D.home v) :=
  Classical.choose_spec (D.vertex_mem v)

/-- Number of graph vertices assigned to one decomposition node. -/
noncomputable def homeWeight (t : Fin k) : ℕ := by
  classical
  exact ∑ v, if D.home v = t then 1 else 0

theorem totalWeight_homeWeight :
    FiniteRootedTree.totalWeight D.homeWeight = Fintype.card V := by
  classical
  unfold FiniteRootedTree.totalWeight homeWeight
  rw [Finset.sum_comm]
  simp

/-- The tree node chosen for a vertex outside the bag at `t`, viewed after deleting `t`. -/
noncomputable def homeOff (t : Fin k) (v : V) (hv : v ∉ D.bag t) :
    {q : Fin k // q ≠ t} :=
  ⟨D.home v, fun h ↦ hv (h ▸ D.home_mem v)⟩

/- Connected bag occurrences give a path from `home v` to any other occurrence while avoiding a
bag that does not contain `v`. -/
omit [Fintype V] in
theorem home_reachable_bag_off
    (t : Fin k) (v : V) (hv : v ∉ D.bag t)
    (q : Fin k) (hvq : v ∈ D.bag q) :
    (D.tree.treeOff t).Reachable (D.homeOff t v hv)
      ⟨q, fun h ↦ hv (h ▸ hvq)⟩ := by
  let occurrenceGraph := D.tree.toSimpleGraph.induce {q | v ∈ D.bag q}
  let f : occurrenceGraph →g D.tree.treeOff t :=
    { toFun := fun x ↦ ⟨x.1, fun h ↦ hv (h ▸ x.2)⟩
      map_rel' := by
        intro a b hab
        exact hab }
  exact (D.running v ⟨D.home v, D.home_mem v⟩ ⟨q, hvq⟩).map f

/- Adjacent graph vertices outside one bag have homes in the same component of the deleted
decomposition tree. -/
omit [Fintype V] in
theorem home_reachable_of_adj_outside (t : Fin k) {u v : V}
    (hadj : G.Adj u v) (hu : u ∉ D.bag t) (hv : v ∉ D.bag t) :
    (D.tree.treeOff t).Reachable (D.homeOff t u hu) (D.homeOff t v hv) := by
  obtain ⟨q, huq, hvq⟩ := D.edge_mem hadj
  exact (D.home_reachable_bag_off t u hu q huq).trans
    (D.home_reachable_bag_off t v hv q hvq).symm

/-- Graph vertices whose chosen homes lie in one component of the deleted decomposition tree. -/
noncomputable def homeComponentVertices (t : Fin k)
    (c : (D.tree.treeOff t).ConnectedComponent) : Finset V := by
  classical
  exact Finset.univ.filter fun v ↦ ∃ hv : D.home v ≠ t,
    (D.tree.treeOff t).connectedComponentMk ⟨D.home v, hv⟩ = c

theorem componentWeight_homeWeight_eq_card (t : Fin k)
    (c : (D.tree.treeOff t).ConnectedComponent) :
    D.tree.componentWeight D.homeWeight t c = (D.homeComponentVertices t c).card := by
  classical
  unfold FiniteRootedTree.componentWeight homeWeight homeComponentVertices
  rw [Finset.sum_comm]
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro v _
  by_cases hv : ∃ h : D.home v ≠ t,
      (D.tree.treeOff t).connectedComponentMk ⟨D.home v, h⟩ = c
  · rw [if_pos hv]
    obtain ⟨hhome, hcomponent⟩ := hv
    rw [Finset.sum_eq_single (D.home v)]
    · simp [hhome, hcomponent]
    · intro q hq hqne
      simp [hqne.symm]
    · intro hnot
      exact False.elim (hnot <| by simp)
  · rw [if_neg hv]
    apply Finset.sum_eq_zero
    intro q hq
    by_cases hqv : D.home v = q
    · subst q
      simp [hv]
    · simp [hqv]

/-- The original graph after deleting one decomposition bag. -/
def graphOff (t : Fin k) : SimpleGraph {v : V // v ∉ D.bag t} :=
  G.induce {v | v ∉ D.bag t}

/-- Original vertices in one graph component after deleting a decomposition bag. -/
noncomputable def graphComponentVertices (t : Fin k)
    (c : (D.graphOff t).ConnectedComponent) : Finset V := by
  classical
  exact Finset.univ.filter fun v ↦ ∃ hv : v ∉ D.bag t,
    (D.graphOff t).connectedComponentMk ⟨v, hv⟩ = c

omit [Fintype V] in
theorem home_component_eq_of_reachable {t : Fin k}
    {u v : {x : V // x ∉ D.bag t}} (hreach : (D.graphOff t).Reachable u v) :
    (D.tree.treeOff t).connectedComponentMk (D.homeOff t u u.property) =
      (D.tree.treeOff t).connectedComponentMk (D.homeOff t v v.property) := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
  induction hreach with
  | refl => rfl
  | @tail a b hab hadj ih =>
      exact ih.trans <| SimpleGraph.ConnectedComponent.sound <|
        D.home_reachable_of_adj_outside t hadj a.property b.property

theorem graphComponentVertices_subset_homeComponent (t : Fin k)
    (r : {v : V // v ∉ D.bag t}) :
    D.graphComponentVertices t ((D.graphOff t).connectedComponentMk r) ⊆
      D.homeComponentVertices t
        ((D.tree.treeOff t).connectedComponentMk (D.homeOff t r r.property)) := by
  classical
  intro v hv
  simp only [graphComponentVertices, Finset.mem_filter, Finset.mem_univ,
    true_and] at hv
  obtain ⟨hvt, hcomponent⟩ := hv
  have hreach := SimpleGraph.ConnectedComponent.exact hcomponent
  have hhomes := D.home_component_eq_of_reachable hreach
  simp only [homeComponentVertices, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨(D.homeOff t v hvt).property, hhomes⟩

/-- Every finite tree decomposition has a bag whose deletion leaves graph components with at most
half of the graph vertices. -/
theorem exists_balanced_bag (hcard : 0 < Fintype.card V) :
    ∃ t : Fin k, ∀ c : (D.graphOff t).ConnectedComponent,
      2 * (D.graphComponentVertices t c).card ≤ Fintype.card V := by
  rw [← D.totalWeight_homeWeight] at hcard ⊢
  obtain ⟨t, hcentroid⟩ :=
    D.tree.exists_weighted_centroid_component_bound D.homeWeight hcard
  refine ⟨t, ?_⟩
  intro component
  induction component using SimpleGraph.ConnectedComponent.ind with
  | _ r =>
      exact le_trans
        (Nat.mul_le_mul_left 2 <| by
          rw [D.componentWeight_homeWeight_eq_card]
          exact Finset.card_le_card (D.graphComponentVertices_subset_homeComponent t r))
        (hcentroid _)

end RootedTreeDecomposition

namespace WeightedGraph

variable {n m k τ : ℕ}

/-- The balanced-bag theorem specialized to the weighted graph's underlying simple graph. -/
theorem exists_balanced_bag_of_tree_decomposition (G : WeightedGraph n m)
    (D : RootedTreeDecomposition G.toSimpleGraph k)
    (hn : 0 < n) (hwidth : D.HasWidthAtMost τ) :
    ∃ X : Finset (Fin n), X.card ≤ τ + 1 ∧
      ∀ c : (G.graphOff X).ConnectedComponent,
        (G.componentVerticesOff X c).card ≤ n / 2 := by
  obtain ⟨t, hbalanced⟩ := D.exists_balanced_bag (by simpa using hn)
  refine ⟨D.bag t, hwidth t, ?_⟩
  intro component
  have htwo : 2 * (G.componentVerticesOff (D.bag t) component).card ≤ n := by
    simpa [RootedTreeDecomposition.graphComponentVertices,
      WeightedGraph.componentVerticesOff, RootedTreeDecomposition.graphOff] using
      hbalanced component
  omega

/-- Corollary 1(i) from the standard tree decomposition axioms. This includes the balanced bag
instead of assuming a separator. -/
theorem treewidth_kappa_bound_of_tree_decomposition (G : WeightedGraph n m)
    (D : RootedTreeDecomposition G.toSimpleGraph k)
    (hn : 0 < n) (hwidth : D.HasWidthAtMost τ) (hτ : τ + 1 ≤ n / 4)
    (Δ bmax : ℝ)
    (hdeg : ∀ i, ((G.incidentEdges i).card : ℝ) ≤ Δ)
    (hbmax : ∀ e, G.weights e ≤ bmax)
    (hconn : G.CombinatoriallyConnected) :
    3 / 8 * G.totalWeight / (((τ : ℝ) + 1) * Δ * bmax) ≤
      effectiveConditionNumber G (fun _ ↦ 1) := by
  obtain ⟨X, hX_width, hcomponent⟩ :=
    G.exists_balanced_bag_of_tree_decomposition D hn hwidth
  have hX_tau : (X.card : ℝ) ≤ (τ : ℝ) + 1 := by
    exact_mod_cast hX_width
  have hX_quarter_nat : X.card ≤ n / 4 := hX_width.trans hτ
  have hX_quarter : (X.card : ℝ) ≤ (n : ℝ) / 4 := by
    have hcast : (X.card : ℝ) ≤ ((n / 4 : ℕ) : ℝ) := by
      exact_mod_cast hX_quarter_nat
    exact le_trans hcast Nat.cast_div_le
  exact treewidth_kappa_bound_of_balanced_bag G X (τ : ℝ) Δ bmax hn
    hX_tau hX_quarter hcomponent hdeg hbmax hconn

/-- Corollary 1(i), topology-only form, from the standard tree decomposition axioms. -/
theorem treewidth_kappa_bound_of_tree_decomposition_topological (G : WeightedGraph n m)
    (D : RootedTreeDecomposition G.toSimpleGraph k)
    (hn : 0 < n) (hwidth : D.HasWidthAtMost τ) (hτ : τ + 1 ≤ n / 4)
    (Δ : ℝ)
    (hdeg : ∀ i, ((G.incidentEdges i).card : ℝ) ≤ Δ)
    (hconn : G.CombinatoriallyConnected) :
    3 / 8 * n / (((τ : ℝ) + 1) * Δ) ≤
      effectiveConditionNumber G (fun _ ↦ 1) := by
  obtain ⟨X, hX_width, hcomponent⟩ :=
    G.exists_balanced_bag_of_tree_decomposition D hn hwidth
  have hX_tau : (X.card : ℝ) ≤ (τ : ℝ) + 1 := by exact_mod_cast hX_width
  have hX_quarter_nat : X.card ≤ n / 4 := hX_width.trans hτ
  have hX_quarter : (X.card : ℝ) ≤ (n : ℝ) / 4 := by
    have hcast : (X.card : ℝ) ≤ ((n / 4 : ℕ) : ℝ) := by exact_mod_cast hX_quarter_nat
    exact hcast.trans Nat.cast_div_le
  exact treewidth_kappa_bound_of_balanced_bag_topological G X (τ : ℝ) Δ hn
    hX_tau hX_quarter hcomponent hdeg hconn

/-- The weighted and topology-only tree decomposition bounds hold simultaneously. -/
theorem treewidth_kappa_bound_of_tree_decomposition_combined (G : WeightedGraph n m)
    (D : RootedTreeDecomposition G.toSimpleGraph k)
    (hn : 0 < n) (hwidth : D.HasWidthAtMost τ) (hτ : τ + 1 ≤ n / 4)
    (Δ bmax : ℝ)
    (hdeg : ∀ i, ((G.incidentEdges i).card : ℝ) ≤ Δ)
    (hbmax : ∀ e, G.weights e ≤ bmax)
    (hconn : G.CombinatoriallyConnected) :
    max (3 / 8 * G.totalWeight / (((τ : ℝ) + 1) * Δ * bmax))
        (3 / 8 * n / (((τ : ℝ) + 1) * Δ)) ≤
      effectiveConditionNumber G (fun _ ↦ 1) := by
  apply max_le
  · exact G.treewidth_kappa_bound_of_tree_decomposition D hn hwidth hτ Δ bmax
      hdeg hbmax hconn
  · exact G.treewidth_kappa_bound_of_tree_decomposition_topological D hn hwidth hτ Δ
      hdeg hconn

end WeightedGraph

end
