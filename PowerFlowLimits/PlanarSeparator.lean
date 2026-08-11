/-
Copyright (c) 2026 Cameron Khanpour and Samuel Talkington. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Cameron Khanpour, Samuel Talkington
-/
import PowerFlowLimits.Planarization
import PowerFlowLimits.Separators
import Mathlib.Data.Finset.Preimage

/-!
# Projecting planar separators through the crossing construction

The topological statement remains an explicit dependency. `PlanarityPredicate` supplies the notion
of planarity, and `LiptonTarjanVertexCostTheorem` is a theorem-valued premise with the quantitative
conclusion of the vertex-cost form of Lipton--Tarjan. Everything from that boundary to the original
power grid separator and condition number estimate is proved here.
-/

open Finset BigOperators

noncomputable section

variable {n m c : ℕ}

/-- An external notion of planarity. The repository does not add an axiom or a plane topology. -/
abbrev PlanarityPredicate := (V : Type) → SimpleGraph V → Prop

/-- Quantitative output of the vertex-cost planar separator theorem. -/
structure VertexCostPartition {V : Type} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (cost : V → ℝ) where
  left : Finset V
  separator : Finset V
  right : Finset V
  cover : left ∪ separator ∪ right = Finset.univ
  disjoint_left_separator : Disjoint left separator
  disjoint_left_right : Disjoint left right
  disjoint_separator_right : Disjoint separator right
  no_left_right : ∀ u v, H.Adj u v → ¬(u ∈ left ∧ v ∈ right)
  separator_card_le : (separator.card : ℝ) ≤ Real.sqrt (8 * Fintype.card V)
  left_cost_le : ∑ v ∈ left, cost v ≤ 2 / 3
  right_cost_le : ∑ v ∈ right, cost v ≤ 2 / 3

/-- The precise external theorem boundary used by this development. -/
def LiptonTarjanVertexCostTheorem (Planar : PlanarityPredicate) : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (H : SimpleGraph V) (cost : V → ℝ),
    (∀ v, 0 ≤ cost v) → (∑ v, cost v) ≤ 1 → Planar V H →
      Nonempty (VertexCostPartition H cost)

/-- Normalized bus cost `1 / n` on an original bus and zero on an inserted crossing. -/
def busCost : PlanarizedVertex n c → ℝ
  | Sum.inl _ => 1 / n
  | Sum.inr _ => 0

@[simp]
theorem busCost_inl (v : Fin n) :
    busCost (Sum.inl v : PlanarizedVertex n c) = 1 / n := rfl

@[simp]
theorem busCost_inr (x : Fin c) : busCost (Sum.inr x : PlanarizedVertex n c) = 0 := rfl

theorem busCost_nonnegative (z : PlanarizedVertex n c) : 0 ≤ busCost z := by
  cases z <;> simp

@[simp]
theorem sum_busCost_univ (hn : 0 < n) : ∑ z : PlanarizedVertex n c, busCost z = 1 := by
  rw [Fintype.sum_sum_type]
  simp [busCost, hn.ne']

/-- Original buses whose inserted copies belong to a planarized vertex set. -/
def originalBuses (Q : Finset (PlanarizedVertex n c)) : Finset (Fin n) :=
  Q.preimage Sum.inl Sum.inl_injective.injOn

@[simp]
theorem mem_originalBuses_iff (Q : Finset (PlanarizedVertex n c)) (v : Fin n) :
    v ∈ originalBuses Q ↔ Sum.inl v ∈ Q := by
  simp [originalBuses]

theorem sum_busCost_eq_originalBuses_card (Q : Finset (PlanarizedVertex n c)) :
    ∑ z ∈ Q, busCost z = (originalBuses Q).card / (n : ℝ) := by
  classical
  rw [originalBuses, Finset.card_preimage,
    ← Finset.sum_boole (R := ℝ) (fun z : PlanarizedVertex n c ↦ z ∈ Set.range Sum.inl) Q]
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun z _ ↦ ?_
  cases z with
  | inl v => simp [busCost]
  | inr x => simp [busCost]

namespace CrossingSchedule

variable {G : WeightedGraph n m} (S : CrossingSchedule G c)

/-- First chosen original bus when projecting a planarized separator vertex. -/
def firstProjection : PlanarizedVertex n c → Fin n
  | Sum.inl v => v
  | Sum.inr x => G.negEndpoint (S.carriers x).1

/-- Second chosen original bus when projecting a planarized separator vertex. -/
def secondProjection : PlanarizedVertex n c → Fin n
  | Sum.inl v => v
  | Sum.inr x => G.negEndpoint (S.carriers x).2

/-- Replace every crossing separator vertex by one endpoint of each of its two carrier branches. -/
def projectedSeparator (Q : Finset (PlanarizedVertex n c)) : Finset (Fin n) :=
  Q.image S.firstProjection ∪ Q.image S.secondProjection

@[simp]
theorem mem_projectedSeparator_of_bus {Q : Finset (PlanarizedVertex n c)} {v : Fin n}
    (hv : Sum.inl v ∈ Q) : v ∈ S.projectedSeparator Q := by
  exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨Sum.inl v, hv, rfl⟩)

theorem first_carrier_endpoint_mem_projectedSeparator
    {Q : Finset (PlanarizedVertex n c)} {x : Fin c} (hx : Sum.inr x ∈ Q) :
    G.negEndpoint (S.carriers x).1 ∈ S.projectedSeparator Q := by
  exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨Sum.inr x, hx, rfl⟩)

theorem second_carrier_endpoint_mem_projectedSeparator
    {Q : Finset (PlanarizedVertex n c)} {x : Fin c} (hx : Sum.inr x ∈ Q) :
    G.negEndpoint (S.carriers x).2 ∈ S.projectedSeparator Q := by
  exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨Sum.inr x, hx, rfl⟩)

theorem projectedSeparator_card_le_twice (Q : Finset (PlanarizedVertex n c)) :
    (S.projectedSeparator Q).card ≤ 2 * Q.card := by
  calc
    (S.projectedSeparator Q).card
        ≤ (Q.image S.firstProjection).card + (Q.image S.secondProjection).card :=
      Finset.card_union_le _ _
    _ ≤ Q.card + Q.card := Nat.add_le_add (Finset.card_image_le) (Finset.card_image_le)
    _ = 2 * Q.card := by omega

end CrossingSchedule

/-- A separator of the original bus graph obtained from a planarized separator. -/
structure ProjectedNearPlanarPartition (G : WeightedGraph n m) (c : ℕ) where
  left : Finset (Fin n)
  separator : Finset (Fin n)
  right : Finset (Fin n)
  cover : left ∪ separator ∪ right = Finset.univ
  disjoint_union_right : Disjoint (left ∪ separator) right
  no_left_right_branch : ∀ e,
    ¬(G.posEndpoint e ∈ left ∧ G.negEndpoint e ∈ right) ∧
      ¬(G.posEndpoint e ∈ right ∧ G.negEndpoint e ∈ left)
  separator_card_le : (separator.card : ℝ) ≤ 2 * Real.sqrt (8 * ((n : ℝ) + c))
  left_card_le : (left.card : ℝ) ≤ 2 * n / 3
  right_card_le : (right.card : ℝ) ≤ 2 * n / 3

namespace VertexCostPartition

variable {V : Type} [Fintype V] [DecidableEq V] {H : SimpleGraph V} {cost : V → ℝ}

/-- A walk joining the two sides of a vertex partition visits its separator. -/
theorem walk_hits_separator (P : VertexCostPartition H cost) {u v : V} (p : H.Walk u v)
    (hu : u ∈ P.left) (hv : v ∈ P.right) :
    ∃ z ∈ p.support, z ∈ P.separator := by
  induction p with
  | nil =>
      exact (Finset.disjoint_left.mp P.disjoint_left_right hu hv).elim
  | @cons u w v huw p ih =>
      have hw_univ : w ∈ (Finset.univ : Finset V) := Finset.mem_univ w
      rw [← P.cover] at hw_univ
      simp only [Finset.mem_union] at hw_univ
      rcases hw_univ with (hw_left | hw_separator) | hw_right
      · rcases ih hw_left hv with ⟨z, hzsupport, hzseparator⟩
        exact ⟨z, by simp [hzsupport], hzseparator⟩
      · exact ⟨w, by simp, hw_separator⟩
      · exact (P.no_left_right u w huw ⟨hu, hw_right⟩).elim

end VertexCostPartition

namespace CrossingSchedule

variable {G : WeightedGraph n m} (S : CrossingSchedule G c)

/-- Buses assigned to the left after moving all projected separator endpoints into the separator. -/
def projectedLeft (P : VertexCostPartition S.planarizedGraph busCost) : Finset (Fin n) :=
  originalBuses P.left \ S.projectedSeparator P.separator

/-- Right-side buses after moving projected separator endpoints into the separator. -/
def projectedRight (P : VertexCostPartition S.planarizedGraph busCost) : Finset (Fin n) :=
  originalBuses P.right \ S.projectedSeparator P.separator

private theorem route_disjoint_separator_of_endpoints_not_projected
    (P : VertexCostPartition S.planarizedGraph busCost) (e : Fin m)
    (hneg : G.negEndpoint e ∉ S.projectedSeparator P.separator)
    (hpos : G.posEndpoint e ∉ S.projectedSeparator P.separator) :
    ∀ z ∈ S.route e, z ∉ P.separator := by
  intro z hzroute hzseparator
  cases z with
  | inl v =>
      rw [S.bus_mem_route_iff] at hzroute
      rcases hzroute with rfl | rfl
      · exact hneg (S.mem_projectedSeparator_of_bus hzseparator)
      · exact hpos (S.mem_projectedSeparator_of_bus hzseparator)
  | inr x =>
      rw [S.crossing_mem_route_iff] at hzroute
      rcases hzroute with he | he
      · subst e
        exact hneg (S.first_carrier_endpoint_mem_projectedSeparator hzseparator)
      · subst e
        exact hneg (S.second_carrier_endpoint_mem_projectedSeparator hzseparator)

private theorem no_projected_left_right_branch
    (P : VertexCostPartition S.planarizedGraph busCost) (e : Fin m) :
    ¬(G.posEndpoint e ∈ S.projectedLeft P ∧ G.negEndpoint e ∈ S.projectedRight P) ∧
      ¬(G.posEndpoint e ∈ S.projectedRight P ∧ G.negEndpoint e ∈ S.projectedLeft P) := by
  rcases S.exists_route_walk e with ⟨p, hp⟩
  have route_avoids (hneg : G.negEndpoint e ∉ S.projectedSeparator P.separator)
      (hpos : G.posEndpoint e ∉ S.projectedSeparator P.separator) :
      ¬∃ z ∈ p.support, z ∈ P.separator := by
    rintro ⟨z, hzsupport, hzseparator⟩
    rw [hp] at hzsupport
    exact S.route_disjoint_separator_of_endpoints_not_projected P e hneg hpos z hzsupport
      hzseparator
  constructor
  · rintro ⟨hpos_left, hneg_right⟩
    have hpos_left' : Sum.inl (G.posEndpoint e) ∈ P.left := by
      exact (mem_originalBuses_iff _ _).mp (Finset.mem_sdiff.mp hpos_left).1
    have hneg_right' : Sum.inl (G.negEndpoint e) ∈ P.right := by
      exact (mem_originalBuses_iff _ _).mp (Finset.mem_sdiff.mp hneg_right).1
    have hhit := P.walk_hits_separator p.reverse hpos_left' hneg_right'
    have hneg_not := (Finset.mem_sdiff.mp hneg_right).2
    have hpos_not := (Finset.mem_sdiff.mp hpos_left).2
    apply route_avoids hneg_not hpos_not
    rcases hhit with ⟨z, hzsupport, hzseparator⟩
    exact ⟨z, by simpa [SimpleGraph.Walk.support_reverse] using hzsupport, hzseparator⟩
  · rintro ⟨hpos_right, hneg_left⟩
    have hneg_left' : Sum.inl (G.negEndpoint e) ∈ P.left := by
      exact (mem_originalBuses_iff _ _).mp (Finset.mem_sdiff.mp hneg_left).1
    have hpos_right' : Sum.inl (G.posEndpoint e) ∈ P.right := by
      exact (mem_originalBuses_iff _ _).mp (Finset.mem_sdiff.mp hpos_right).1
    have hhit := P.walk_hits_separator p hneg_left' hpos_right'
    exact route_avoids (Finset.mem_sdiff.mp hneg_left).2
      (Finset.mem_sdiff.mp hpos_right).2 hhit

private theorem projected_cover (P : VertexCostPartition S.planarizedGraph busCost) :
    S.projectedLeft P ∪ S.projectedSeparator P.separator ∪ S.projectedRight P =
      Finset.univ := by
  ext v
  simp only [Finset.mem_union, Finset.mem_univ, iff_true]
  by_cases hv_separator : v ∈ S.projectedSeparator P.separator
  · exact Or.inl (Or.inr hv_separator)
  · have hv_univ : (Sum.inl v : PlanarizedVertex n c) ∈ Finset.univ := Finset.mem_univ _
    rw [← P.cover] at hv_univ
    simp only [Finset.mem_union] at hv_univ
    rcases hv_univ with (hv_left | hv_planar_separator) | hv_right
    · apply Or.inl
      apply Or.inl
      rw [projectedLeft, Finset.mem_sdiff]
      exact ⟨(mem_originalBuses_iff _ _).mpr hv_left, hv_separator⟩
    · exact (hv_separator (S.mem_projectedSeparator_of_bus hv_planar_separator)).elim
    · apply Or.inr
      rw [projectedRight, Finset.mem_sdiff]
      exact ⟨(mem_originalBuses_iff _ _).mpr hv_right, hv_separator⟩

private theorem projected_disjoint_union_right
    (P : VertexCostPartition S.planarizedGraph busCost) :
    Disjoint (S.projectedLeft P ∪ S.projectedSeparator P.separator) (S.projectedRight P) := by
  rw [Finset.disjoint_left]
  intro v hv_union hv_right
  rcases Finset.mem_union.mp hv_union with hv_left | hv_separator
  · have hv_planar_left : Sum.inl v ∈ P.left :=
      (mem_originalBuses_iff _ _).mp (Finset.mem_sdiff.mp hv_left).1
    have hv_planar_right : Sum.inl v ∈ P.right :=
      (mem_originalBuses_iff _ _).mp (Finset.mem_sdiff.mp hv_right).1
    exact Finset.disjoint_left.mp P.disjoint_left_right hv_planar_left hv_planar_right
  · exact (Finset.mem_sdiff.mp hv_right).2 hv_separator

/-- The complete projection of a Lipton--Tarjan partition to the original bus graph. -/
def projectVertexCostPartition
    (hn : 0 < n) (P : VertexCostPartition S.planarizedGraph busCost) :
    ProjectedNearPlanarPartition G c where
  left := S.projectedLeft P
  separator := S.projectedSeparator P.separator
  right := S.projectedRight P
  cover := S.projected_cover P
  disjoint_union_right := S.projected_disjoint_union_right P
  no_left_right_branch := S.no_projected_left_right_branch P
  separator_card_le := by
    have hcard_nat := S.projectedSeparator_card_le_twice P.separator
    have hcard : ((S.projectedSeparator P.separator).card : ℝ) ≤
        2 * (P.separator.card : ℝ) := by exact_mod_cast hcard_nat
    calc
      ((S.projectedSeparator P.separator).card : ℝ)
          ≤ 2 * (P.separator.card : ℝ) := hcard
      _ ≤ 2 * Real.sqrt (8 * Fintype.card (PlanarizedVertex n c)) :=
        mul_le_mul_of_nonneg_left P.separator_card_le (by norm_num)
      _ = 2 * Real.sqrt (8 * ((n : ℝ) + c)) := by
        rw [CrossingSchedule.card_planarizedVertex]
        norm_num
  left_card_le := by
    have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
    have hsubset : S.projectedLeft P ⊆ originalBuses P.left := Finset.sdiff_subset
    have hcard_nat : (S.projectedLeft P).card ≤ (originalBuses P.left).card :=
      Finset.card_le_card hsubset
    have hcard : ((S.projectedLeft P).card : ℝ) ≤ (originalBuses P.left).card := by
      exact_mod_cast hcard_nat
    have hcost : ((originalBuses P.left).card : ℝ) / n ≤ 2 / 3 := by
      rw [← sum_busCost_eq_originalBuses_card]
      exact P.left_cost_le
    have horiginal : ((originalBuses P.left).card : ℝ) ≤ 2 * n / 3 := by
      have hmul := (div_le_iff₀ hnreal).mp hcost
      nlinarith
    exact hcard.trans horiginal
  right_card_le := by
    have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
    have hsubset : S.projectedRight P ⊆ originalBuses P.right := Finset.sdiff_subset
    have hcard_nat : (S.projectedRight P).card ≤ (originalBuses P.right).card :=
      Finset.card_le_card hsubset
    have hcard : ((S.projectedRight P).card : ℝ) ≤ (originalBuses P.right).card := by
      exact_mod_cast hcard_nat
    have hcost : ((originalBuses P.right).card : ℝ) / n ≤ 2 / 3 := by
      rw [← sum_busCost_eq_originalBuses_card]
      exact P.right_cost_le
    have horiginal : ((originalBuses P.right).card : ℝ) ≤ 2 * n / 3 := by
      have hmul := (div_le_iff₀ hnreal).mp hcost
      nlinarith
    exact hcard.trans horiginal

end CrossingSchedule

/-- The numerical near-planarity hypothesis puts the projected separator below `n / 6`. -/
theorem twice_sqrt_eight_crossing_card_le_sixth (n c : ℕ)
    (hsmall : 1152 * (n + c) ≤ n ^ 2) :
    2 * Real.sqrt (8 * ((n : ℝ) + c)) ≤ (n : ℝ) / 6 := by
  have hsmall_real : (1152 : ℝ) * ((n : ℝ) + c) ≤ (n : ℝ) ^ 2 := by
    exact_mod_cast hsmall
  have hnonneg : 0 ≤ 8 * ((n : ℝ) + c) := by positivity
  have hsqrt_nonneg : 0 ≤ Real.sqrt (8 * ((n : ℝ) + c)) := Real.sqrt_nonneg _
  have hsqrt_sq : (Real.sqrt (8 * ((n : ℝ) + c))) ^ 2 =
      8 * ((n : ℝ) + c) := Real.sq_sqrt hnonneg
  nlinarith

namespace CrossingSchedule

variable {G : WeightedGraph n m} (S : CrossingSchedule G c)

/-- Apply the external vertex-cost separator theorem and project its output to original buses. -/
theorem exists_projectedNearPlanarPartition (Planar : PlanarityPredicate)
    (hLT : LiptonTarjanVertexCostTheorem Planar) (hn : 0 < n)
    (hplanar : Planar _ S.planarizedGraph) :
    Nonempty (ProjectedNearPlanarPartition G c) := by
  have htotal : (∑ z : PlanarizedVertex n c, busCost z) ≤ 1 :=
    (sum_busCost_univ hn).le
  rcases hLT (PlanarizedVertex n c) S.planarizedGraph busCost busCost_nonnegative htotal
      hplanar with ⟨P⟩
  exact ⟨S.projectVertexCostPartition hn P⟩

/-- Near-planar condition-number bound obtained from an explicit crossing schedule, a planarity
certificate for its planarization, and the theorem-valued Lipton--Tarjan dependency. -/
theorem nearPlanar_kappa_bound (Planar : PlanarityPredicate)
    (hLT : LiptonTarjanVertexCostTheorem Planar) (hplanar : Planar _ S.planarizedGraph)
    (hsmall : 1152 * (n + c) ≤ n ^ 2) (Δ bmax : ℝ)
    (hdeg : ∀ i, ((G.incidentEdges i).card : ℝ) ≤ Δ)
    (hbmax : ∀ e, G.weights e ≤ bmax)
    (hconn : G.CombinatoriallyConnected) :
    5 / 36 * G.totalWeight / (Real.sqrt (8 * ((n : ℝ) + c)) * Δ * bmax) ≤
      effectiveConditionNumber G (fun _ ↦ 1) := by
  have hn : 0 < n := Fin.pos_iff_nonempty.mpr hconn.nonempty
  rcases S.exists_projectedNearPlanarPartition Planar hLT hn hplanar with ⟨Q⟩
  have hseparator_sixth : (Q.separator.card : ℝ) ≤ (n : ℝ) / 6 :=
    Q.separator_card_le.trans (twice_sqrt_eight_crossing_card_le_sixth n c hsmall)
  have hcard_nat : (Q.left ∪ Q.separator).card + Q.right.card = n := by
    rw [← Finset.card_union_of_disjoint Q.disjoint_union_right, Q.cover,
      Finset.card_univ, Fintype.card_fin]
  have hcard : ((Q.left ∪ Q.separator).card : ℝ) + (Q.right.card : ℝ) = n := by
    exact_mod_cast hcard_nat
  have hunion_le_nat : (Q.left ∪ Q.separator).card ≤ Q.left.card + Q.separator.card :=
    Finset.card_union_le _ _
  have hunion_le : ((Q.left ∪ Q.separator).card : ℝ) ≤
      (Q.left.card : ℝ) + Q.separator.card := by
    exact_mod_cast hunion_le_nat
  have hleft_size : (n : ℝ) / 6 ≤ ((Q.left ∪ Q.separator).card : ℝ) := by
    nlinarith [Q.right_card_le]
  have hright_size : (n : ℝ) / 6 ≤ (Q.right.card : ℝ) := by
    nlinarith [Q.left_card_le, hseparator_sixth, hunion_le]
  exact kappa_bound_of_near_planar_partition G Q.left Q.separator Q.right Δ bmax c
    Q.cover Q.disjoint_union_right Q.no_left_right_branch Q.separator_card_le hdeg hbmax
    hleft_size hright_size hconn

end CrossingSchedule

/-- Exact output needed from Lipton--Tarjan when the original bus graph itself is planar. -/
structure OriginalPlanarPartition (G : WeightedGraph n m) where
  left : Finset (Fin n)
  separator : Finset (Fin n)
  right : Finset (Fin n)
  cover : left ∪ separator ∪ right = Finset.univ
  disjoint_union_right : Disjoint (left ∪ separator) right
  no_left_right_branch : ∀ e,
    ¬(G.posEndpoint e ∈ left ∧ G.negEndpoint e ∈ right) ∧
      ¬(G.posEndpoint e ∈ right ∧ G.negEndpoint e ∈ left)
  separator_card_le : (separator.card : ℝ) ≤ Real.sqrt (8 * n)
  left_card_le : (left.card : ℝ) ≤ 2 * n / 3
  right_card_le : (right.card : ℝ) ≤ 2 * n / 3

/-- Normalized vertex cost `1 / n` for the exact planar corollary. -/
def unitVertexCost (_v : Fin n) : ℝ := 1 / n

theorem unitVertexCost_nonnegative (v : Fin n) : 0 ≤ unitVertexCost v := by
  exact div_nonneg (by norm_num) (Nat.cast_nonneg n)

@[simp]
theorem sum_unitVertexCost_univ (hn : 0 < n) : ∑ v : Fin n, unitVertexCost v = 1 := by
  simp [unitVertexCost, hn.ne']

theorem sum_unitVertexCost_eq_card (Q : Finset (Fin n)) :
    ∑ v ∈ Q, unitVertexCost v = Q.card / (n : ℝ) := by
  simp [unitVertexCost, div_eq_mul_inv]

/-- Construct the exact planar partition directly from the same theorem-valued dependency. -/
theorem exists_originalPlanarPartition (Planar : PlanarityPredicate)
    (hLT : LiptonTarjanVertexCostTheorem Planar) (G : WeightedGraph n m)
    (hn : 0 < n) (hplanar : Planar _ G.toSimpleGraph) : Nonempty (OriginalPlanarPartition G) := by
  have htotal : (∑ v : Fin n, unitVertexCost v) ≤ 1 := (sum_unitVertexCost_univ hn).le
  rcases hLT (Fin n) G.toSimpleGraph unitVertexCost unitVertexCost_nonnegative htotal hplanar with
    ⟨P⟩
  refine ⟨⟨P.left, P.separator, P.right, P.cover, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact Finset.disjoint_union_left.mpr
      ⟨P.disjoint_left_right, P.disjoint_separator_right⟩
  · intro e
    constructor
    · exact P.no_left_right _ _ (G.posEndpoint_adj_negEndpoint e)
    · rintro ⟨hpos, hneg⟩
      exact P.no_left_right _ _ (G.posEndpoint_adj_negEndpoint e).symm ⟨hneg, hpos⟩
  · simpa using P.separator_card_le
  · have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
    have hcost : (P.left.card : ℝ) / n ≤ 2 / 3 := by
      rw [← sum_unitVertexCost_eq_card]
      exact P.left_cost_le
    have hmul := (div_le_iff₀ hnreal).mp hcost
    nlinarith
  · have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
    have hcost : (P.right.card : ℝ) / n ≤ 2 / 3 := by
      rw [← sum_unitVertexCost_eq_card]
      exact P.right_cost_le
    have hmul := (div_le_iff₀ hnreal).mp hcost
    nlinarith

/-- Exact planar part of Corollary 1 from a planarity certificate and Lipton--Tarjan. -/
theorem planar_kappa_bound_from_lipton_tarjan (Planar : PlanarityPredicate)
    (hLT : LiptonTarjanVertexCostTheorem Planar) (G : WeightedGraph n m)
    (hplanar : Planar _ G.toSimpleGraph) (hn : 288 ≤ n) (Δ bmax : ℝ)
    (hdeg : ∀ i, ((G.incidentEdges i).card : ℝ) ≤ Δ)
    (hbmax : ∀ e, G.weights e ≤ bmax)
    (hconn : G.CombinatoriallyConnected) :
    5 / 18 * G.totalWeight / (Real.sqrt (8 * n) * Δ * bmax) ≤
      effectiveConditionNumber G (fun _ ↦ 1) := by
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  rcases exists_originalPlanarPartition Planar hLT G hnpos hplanar with ⟨Q⟩
  exact planar_kappa_bound_of_lipton_partition G Q.left Q.separator Q.right Δ bmax hn
    Q.cover Q.disjoint_union_right Q.no_left_right_branch Q.separator_card_le Q.left_card_le
    Q.right_card_le hdeg hbmax hconn
