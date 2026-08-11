/-
Copyright (c) 2026 Power Flow Limits contributors. All rights reserved.
Released under the MIT license. See LICENSE for details.
-/

import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Tactic

/-!
# Independent definitions for the trusted claim surface

This module imports only Mathlib. The definitions below are intentionally small replicas of the
definitions reachable from the public theorem statements.
-/

open Finset BigOperators
open Matrix
open scoped Matrix

noncomputable section

set_option autoImplicit false

variable {n m : ℕ}

/-- A weighted graph with `n` vertices and `m` edges. -/
structure WeightedGraph (n m : ℕ) where
  weights : Fin m → ℝ
  weights_pos : ∀ e, 0 < weights e
  incidence : Fin n → Fin m → ℝ
  incidence_pos_unique : ∀ e, ∃! i, incidence i e = 1
  incidence_neg_unique : ∀ e, ∃! i, incidence i e = -1
  incidence_col_sum : ∀ e, ∑ i, incidence i e = 0
  incidence_values : ∀ i e, incidence i e = -1 ∨ incidence i e = 0 ∨ incidence i e = 1

namespace WeightedGraph

def posEndpoint (G : WeightedGraph n m) (e : Fin m) : Fin n :=
  Classical.choose <| ExistsUnique.exists (G.incidence_pos_unique e)

def negEndpoint (G : WeightedGraph n m) (e : Fin m) : Fin n :=
  Classical.choose <| ExistsUnique.exists (G.incidence_neg_unique e)

theorem incidence_posEndpoint (G : WeightedGraph n m) (e : Fin m) :
    G.incidence (G.posEndpoint e) e = 1 :=
  Classical.choose_spec <| ExistsUnique.exists (G.incidence_pos_unique e)

theorem incidence_negEndpoint (G : WeightedGraph n m) (e : Fin m) :
    G.incidence (G.negEndpoint e) e = -1 :=
  Classical.choose_spec <| ExistsUnique.exists (G.incidence_neg_unique e)

theorem endpoints_ne (G : WeightedGraph n m) (e : Fin m) :
    G.posEndpoint e ≠ G.negEndpoint e := by
  intro h
  have hpos := G.incidence_posEndpoint e
  have hneg := G.incidence_negEndpoint e
  have hneg' : G.incidence (G.posEndpoint e) e = -1 := by simpa [h] using hneg
  linarith [hpos, hneg']

end WeightedGraph

def WeightedGraph.totalWeight (G : WeightedGraph n m) : ℝ :=
  ∑ e, G.weights e

def WeightedGraph.withWeights (G : WeightedGraph n m) (w : Fin m → ℝ)
    (hw : ∀ e, 0 < w e) : WeightedGraph n m :=
  { G with weights := w, weights_pos := hw }

def WeightedGraph.cutWeight (G : WeightedGraph n m) (S : Finset (Fin n)) : ℝ :=
  ∑ e, G.weights e *
    ((if G.posEndpoint e ∈ S then (1 : ℝ) else 0) -
     (if G.negEndpoint e ∈ S then (1 : ℝ) else 0)) ^ 2

def WeightedGraph.incidentEdges (G : WeightedGraph n m) (i : Fin n) : Finset (Fin m) :=
  Finset.univ.filter fun e => i = G.posEndpoint e ∨ i = G.negEndpoint e

def WeightedGraph.laplacian (G : WeightedGraph n m) (s : Fin m → ℝ)
    (i j : Fin n) : ℝ :=
  ∑ e, G.incidence i e * (G.weights e * s e) * G.incidence j e

@[irreducible] def voltageDrop (G : WeightedGraph n m) (x : Fin n → ℝ) (e : Fin m) : ℝ :=
  ∑ i, G.incidence i e * x i

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

def WeightedGraph.CombinatoriallyConnected (G : WeightedGraph n m) : Prop :=
  G.toSimpleGraph.Connected

@[irreducible] def laplacian_eigenvalue₂ (G : WeightedGraph n m) (s : Fin m → ℝ) : ℝ :=
  sSup {r : ℝ | ∀ (x : Fin n → ℝ), ∑ i, x i = 0 →
    r * (∑ i, x i ^ 2) ≤ ∑ i, (∑ j, G.laplacian s i j * x j) * x i}

def WeightedGraph.Connected (G : WeightedGraph n m) (s : Fin m → ℝ) : Prop :=
  0 < laplacian_eigenvalue₂ G s

def laplacianEigenvalueMax (G : WeightedGraph n m) (s : Fin m → ℝ) : ℝ :=
  sInf {r : ℝ | ∀ x : Fin n → ℝ,
    ∑ i, (∑ j, G.laplacian s i j * x j) * x i ≤ r * ∑ i, x i ^ 2}

def effectiveConditionNumber (G : WeightedGraph n m) (s : Fin m → ℝ) : ℝ :=
  laplacianEigenvalueMax G s / laplacian_eigenvalue₂ G s

/-- A finite rooted tree represented by a parent map and a decreasing depth certificate. -/
structure FiniteRootedTree (k : ℕ) where
  root : Fin k
  parent : Fin k → Fin k
  depth : Fin k → ℕ
  parent_root : parent root = root
  parent_depth_lt : ∀ v, v ≠ root → depth (parent v) < depth v

namespace FiniteRootedTree

variable {k : ℕ} (T : FiniteRootedTree k)

def ParentStep (u v : Fin k) : Prop := u ≠ T.root ∧ T.parent u = v

theorem parent_ne_self (v : Fin k) (hv : v ≠ T.root) : T.parent v ≠ v := by
  intro hp
  have hdepth := T.parent_depth_lt v hv
  rw [hp] at hdepth
  exact (Nat.lt_irrefl _ hdepth)

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

end FiniteRootedTree

structure RootedTreeDecomposition {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (k : ℕ) where
  tree : FiniteRootedTree k
  bag : Fin k → Finset V
  vertex_mem : ∀ v : V, ∃ t, v ∈ bag t
  edge_mem : ∀ {u v : V}, G.Adj u v → ∃ t, u ∈ bag t ∧ v ∈ bag t
  running : ∀ v : V,
    (tree.toSimpleGraph.induce {t | v ∈ bag t}).Preconnected

namespace RootedTreeDecomposition

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {k : ℕ} (D : RootedTreeDecomposition G k)

def HasWidthAtMost (τ : ℕ) : Prop :=
  ∀ t, (D.bag t).card ≤ τ + 1

end RootedTreeDecomposition

@[irreducible] def groundedLaplacianEigenvalueMin (G : WeightedGraph n m)
    (r : Fin n) : ℝ :=
  sSup {a : ℝ | ∀ (x : Fin n → ℝ), x r = 0 →
    a * (∑ i, x i ^ 2) ≤
      ∑ i, (∑ j, G.laplacian (fun _ ↦ 1) i j * x j) * x i}

def groundedLaplacianEigenvalueMax (G : WeightedGraph n m) (r : Fin n) : ℝ :=
  sInf {a : ℝ | ∀ (x : Fin n → ℝ), x r = 0 →
    ∑ i, (∑ j, G.laplacian (fun _ ↦ 1) i j * x j) * x i ≤
      a * ∑ i, x i ^ 2}

def groundedConditionNumber (G : WeightedGraph n m) (r : Fin n) : ℝ :=
  groundedLaplacianEigenvalueMax G r / groundedLaplacianEigenvalueMin G r

def WeightedGraph.acActiveInjection (G : WeightedGraph n m)
    (θ : Fin n → ℝ) (i : Fin n) : ℝ :=
  ∑ e, G.incidence i e * G.weights e * Real.sin (voltageDrop G θ e)

def WeightedGraph.acAngleJacobian (G : WeightedGraph n m)
    (θ : Fin n → ℝ) (i j : Fin n) : ℝ :=
  ∑ e, G.incidence i e * G.weights e * Real.cos (voltageDrop G θ e) *
    G.incidence j e

def WeightedGraph.dcBranchFlow (G : WeightedGraph n m)
    (θ : Fin n → ℝ) (e : Fin m) : ℝ :=
  G.weights e * voltageDrop G θ e

def WeightedGraph.dcOpfBarrierScale (G : WeightedGraph n m)
    (limit : Fin m → ℝ) (μ : ℝ) (θ : Fin n → ℝ) (e : Fin m) : ℝ :=
  μ * G.weights e *
    (((limit e - G.dcBranchFlow θ e) ^ 2)⁻¹ +
      ((limit e + G.dcBranchFlow θ e) ^ 2)⁻¹)

def WeightedGraph.dcOpfNetworkBlock (G : WeightedGraph n m)
    (limit : Fin m → ℝ) (μ : ℝ) (θ : Fin n → ℝ) (i j : Fin n) : ℝ :=
  ∑ e, G.incidence i e *
    (G.dcOpfBarrierScale limit μ θ e * G.weights e) * G.incidence j e

namespace RHSQueryHardness

def sqNorm {d : ℕ} (x : Fin d → ℝ) : ℝ :=
  dotProduct x x

def sqDistance {d : ℕ} (x y : Fin d → ℝ) : ℝ :=
  sqNorm (x - y)

def IsBalanced {d : ℕ} (p : Fin d → ℝ) : Prop :=
  ∑ i, p i = 0

structure BalancedModePair (d : ℕ) where
  fast : Fin d → ℝ
  slow : Fin d → ℝ
  fast_balanced : IsBalanced fast
  slow_balanced : IsBalanced slow
  fast_normalized : sqNorm fast = 1
  slow_normalized : sqNorm slow = 1
  orthogonal : dotProduct fast slow = 0

namespace BalancedModePair

def embed {d : ℕ} (P : BalancedModePair d) (z : Fin 2 → ℝ) : Fin d → ℝ :=
  z 0 • P.fast + z 1 • P.slow

end BalancedModePair

def preparedPlus (κ : ℝ) : Fin 2 → ℝ := fun i ↦
  if i = 0 then κ / Real.sqrt (κ ^ 2 + 1) else 1 / Real.sqrt (κ ^ 2 + 1)

def preparedMinus (κ : ℝ) : Fin 2 → ℝ := fun i ↦
  if i = 0 then κ / Real.sqrt (κ ^ 2 + 1) else -1 / Real.sqrt (κ ^ 2 + 1)

def inverseMap (κ : ℝ) (x : Fin 2 → ℝ) : Fin 2 → ℝ := fun i ↦
  if i = 0 then x i else κ * x i

def solutionPlus : Fin 2 → ℝ := fun i ↦
  if i = 0 then 1 / Real.sqrt 2 else 1 / Real.sqrt 2

def solutionMinus : Fin 2 → ℝ := fun i ↦
  if i = 0 then 1 / Real.sqrt 2 else -1 / Real.sqrt 2

def balancedPreparedPlus {d : ℕ} (P : BalancedModePair d) (κ : ℝ) : Fin d → ℝ :=
  P.embed (preparedPlus κ)

def balancedPreparedMinus {d : ℕ} (P : BalancedModePair d) (κ : ℝ) : Fin d → ℝ :=
  P.embed (preparedMinus κ)

def balancedSolutionPlus {d : ℕ} (P : BalancedModePair d) : Fin d → ℝ :=
  P.embed solutionPlus

def balancedSolutionMinus {d : ℕ} (P : BalancedModePair d) : Fin d → ℝ :=
  P.embed solutionMinus

def fin2Zero : Fin 2 := ⟨0, Nat.zero_lt_succ 1⟩

def fin2One : Fin 2 := ⟨1, Nat.lt_succ_self 1⟩

def preparationOraclePlus (κ : ℝ) (x : Fin 2 → ℝ) : Fin 2 → ℝ := fun i ↦
  if i = fin2Zero then (κ * x fin2Zero - x fin2One) / Real.sqrt (κ ^ 2 + 1)
  else (x fin2Zero + κ * x fin2One) / Real.sqrt (κ ^ 2 + 1)

def preparationOracleMinus (κ : ℝ) (x : Fin 2 → ℝ) : Fin 2 → ℝ := fun i ↦
  if i = fin2Zero then (κ * x fin2Zero + x fin2One) / Real.sqrt (κ ^ 2 + 1)
  else (-x fin2Zero + κ * x fin2One) / Real.sqrt (κ ^ 2 + 1)

def preparationBasis : Fin 2 → ℝ := fun i ↦ if i = 0 then 1 else 0

end RHSQueryHardness

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

/-- Original buses together with the vertices inserted at crossings. -/
abbrev PlanarizedVertex (n c : ℕ) := Fin n ⊕ Fin c

/-- Combinatorial data of a drawing with finitely many ordinary pairwise crossings. -/
structure CrossingSchedule (G : WeightedGraph n m) (c : ℕ) where
  carriers : Fin c → Fin m × Fin m
  carriers_ne : ∀ x, (carriers x).1 ≠ (carriers x).2
  along : Fin m → List (Fin c)
  along_nodup : ∀ e, (along e).Nodup
  mem_along_iff : ∀ e x, x ∈ along e ↔ e = (carriers x).1 ∨ e = (carriers x).2

namespace CrossingSchedule

variable {c : ℕ} {G : WeightedGraph n m} (S : CrossingSchedule G c)

def route (e : Fin m) : List (PlanarizedVertex n c) :=
  Sum.inl (G.negEndpoint e) :: (S.along e).map Sum.inr ++ [Sum.inl (G.posEndpoint e)]

def Consecutive {V : Type*} (vertices : List V) (u v : V) : Prop :=
  ∃ before after, vertices = before ++ u :: v :: after

def planarizedGraph : SimpleGraph (PlanarizedVertex n c) where
  Adj u v := u ≠ v ∧ ∃ e, Consecutive (S.route e) u v ∨ Consecutive (S.route e) v u
  symm := by
    rintro u v ⟨hne, e, h⟩
    exact ⟨hne.symm, e, h.symm⟩
  loopless := ⟨by simp⟩

end CrossingSchedule

/-- An external notion of planarity. -/
abbrev PlanarityPredicate := (V : Type) → SimpleGraph V → Prop

/-- Quantitative output of the vertex cost planar separator theorem. -/
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

/-- The precise external theorem boundary used by the public claims. -/
def LiptonTarjanVertexCostTheorem (Planar : PlanarityPredicate) : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (H : SimpleGraph V) (cost : V → ℝ),
    (∀ v, 0 ≤ cost v) → (∑ v, cost v) ≤ 1 → Planar V H →
      Nonempty (VertexCostPartition H cost)

namespace PaperClaims

structure ControlledPreparationHybridBound {d : ℕ}
    (pair : RHSQueryHardness.BalancedModePair d) (qSolve : ℕ)
    (condition distance gap constant : ℝ)
    (preparePlus prepareMinus preparePlusInv prepareMinusInv :
      (Fin 2 → ℝ) → Fin 2 → ℝ) : Prop where
  plus_prepares : pair.embed (preparePlus RHSQueryHardness.preparationBasis) =
    RHSQueryHardness.balancedPreparedPlus pair condition
  minus_prepares : pair.embed (prepareMinus RHSQueryHardness.preparationBasis) =
    RHSQueryHardness.balancedPreparedMinus pair condition
  plus_left_inverse : Function.LeftInverse preparePlusInv preparePlus
  plus_right_inverse : Function.RightInverse preparePlusInv preparePlus
  minus_left_inverse : Function.LeftInverse prepareMinusInv prepareMinus
  minus_right_inverse : Function.RightInverse prepareMinusInv prepareMinus
  plus_norm : ∀ x, RHSQueryHardness.sqNorm (preparePlus x) = RHSQueryHardness.sqNorm x
  minus_norm : ∀ x, RHSQueryHardness.sqNorm (prepareMinus x) = RHSQueryHardness.sqNorm x
  plus_inv_norm :
    ∀ x, RHSQueryHardness.sqNorm (preparePlusInv x) = RHSQueryHardness.sqNorm x
  minus_inv_norm :
    ∀ x, RHSQueryHardness.sqNorm (prepareMinusInv x) = RHSQueryHardness.sqNorm x
  condition_pos : 0 < condition
  gap_pos : 0 < gap
  constant_pos : 0 < constant
  output_distance_sq : distance ^ 2 = RHSQueryHardness.sqDistance
    (RHSQueryHardness.balancedSolutionPlus pair)
    (RHSQueryHardness.balancedSolutionMinus pair)
  separated : gap ≤ distance
  progress : condition * distance ≤ constant * qSolve

structure PureStateTomographyBound {index state : Type*}
    [NormedAddCommGroup state] [InnerProductSpace ℝ state] [FiniteDimensional ℝ state]
    (target : index → state) (calls : index → ℝ) (basis : state)
    (prepare prepareInv : index → state → state)
    (error successProbability constant : ℝ) : Prop where
  dimension_pos : 0 < Module.finrank ℝ state
  basis_normalized : ‖basis‖ = 1
  normalized : ∀ p, ‖target p‖ = 1
  prepares : ∀ p, prepare p basis = target p
  left_inverse : ∀ p, Function.LeftInverse (prepareInv p) (prepare p)
  right_inverse : ∀ p, Function.RightInverse (prepareInv p) (prepare p)
  prepare_norm : ∀ p x, ‖prepare p x‖ = ‖x‖
  inverse_norm : ∀ p x, ‖prepareInv p x‖ = ‖x‖
  error_pos : 0 < error
  error_lt_one : error < 1
  success_gt_half : 1 / 2 < successProbability
  constant_pos : 0 < constant
  lowerBound : ∃ p, constant * ((Module.finrank ℝ state : ℝ) / error) ≤ calls p

/-- The external solve-time upper bound for a classical SDD solver instantiated on the fixed
graph. The logarithmic factor records the accuracy and failure-probability dependence of the
cited algorithm. -/
structure ClassicalSDDSolveBound {index : Type*} (G : WeightedGraph n m)
    (solveTime : index → ℝ) (constant logFactor : ℝ) : Prop where
  constant_nonnegative : 0 ≤ constant
  logFactor_nonnegative : 0 ≤ logFactor
  upperBound : ∀ p, solveTime p ≤ constant * m * logFactor

/-- The external gate lower bound for loading a generic dense classical vector without QRAM in
the cited one-qubit rotation and CNOT circuit model. -/
structure DenseLoadingBound {index : Type*} (d : ℕ) (isDense : index → Prop)
    (loadTime : index → ℝ) (constant : ℝ) : Prop where
  constant_pos : 0 < constant
  lowerBound : ∀ p, isDense p → constant * d ≤ loadTime p

structure GraphHardPairCertificate (G : WeightedGraph n m) where
  /-- The orthonormal extreme modes constructed from the graph Laplacian. -/
  pair : RHSQueryHardness.BalancedModePair n
  condition_pos : 0 < effectiveConditionNumber G (fun _ ↦ 1)
  fastEigen : ∀ i, ∑ j, G.laplacian (fun _ ↦ 1) i j * pair.fast j =
    laplacianEigenvalueMax G (fun _ ↦ 1) * pair.fast i
  slowEigen : ∀ i, ∑ j, G.laplacian (fun _ ↦ 1) i j * pair.slow j =
    laplacian_eigenvalue₂ G (fun _ ↦ 1) * pair.slow i
  preparedPlus_normalized : RHSQueryHardness.sqNorm
    (RHSQueryHardness.balancedPreparedPlus pair
      (effectiveConditionNumber G (fun _ ↦ 1))) = 1
  preparedMinus_normalized : RHSQueryHardness.sqNorm
    (RHSQueryHardness.balancedPreparedMinus pair
      (effectiveConditionNumber G (fun _ ↦ 1))) = 1
  inputGap : RHSQueryHardness.sqDistance
      (RHSQueryHardness.balancedPreparedPlus pair
        (effectiveConditionNumber G (fun _ ↦ 1)))
      (RHSQueryHardness.balancedPreparedMinus pair
        (effectiveConditionNumber G (fun _ ↦ 1))) =
    4 / (effectiveConditionNumber G (fun _ ↦ 1) ^ 2 + 1)
  solutionPlus_normalized :
    RHSQueryHardness.sqNorm (RHSQueryHardness.balancedSolutionPlus pair) = 1
  solutionMinus_normalized :
    RHSQueryHardness.sqNorm (RHSQueryHardness.balancedSolutionMinus pair) = 1
  outputGap : RHSQueryHardness.sqDistance
      (RHSQueryHardness.balancedSolutionPlus pair)
      (RHSQueryHardness.balancedSolutionMinus pair) = 2
  oraclePlus_prepares : RHSQueryHardness.preparationOraclePlus
      (effectiveConditionNumber G (fun _ ↦ 1)) RHSQueryHardness.preparationBasis =
    RHSQueryHardness.preparedPlus (effectiveConditionNumber G (fun _ ↦ 1))
  oracleMinus_prepares : RHSQueryHardness.preparationOracleMinus
      (effectiveConditionNumber G (fun _ ↦ 1)) RHSQueryHardness.preparationBasis =
    RHSQueryHardness.preparedMinus (effectiveConditionNumber G (fun _ ↦ 1))
  oraclePlus_inverse : ∀ x, RHSQueryHardness.preparationOraclePlus
      (effectiveConditionNumber G (fun _ ↦ 1))
      (RHSQueryHardness.preparationOracleMinus
        (effectiveConditionNumber G (fun _ ↦ 1)) x) = x
  oracleMinus_inverse : ∀ x, RHSQueryHardness.preparationOracleMinus
      (effectiveConditionNumber G (fun _ ↦ 1))
      (RHSQueryHardness.preparationOraclePlus
        (effectiveConditionNumber G (fun _ ↦ 1)) x) = x
  inversePlus : RHSQueryHardness.inverseMap
      (effectiveConditionNumber G (fun _ ↦ 1))
      (RHSQueryHardness.preparedPlus (effectiveConditionNumber G (fun _ ↦ 1))) =
    fun i ↦ (effectiveConditionNumber G (fun _ ↦ 1) * Real.sqrt 2 /
      Real.sqrt (effectiveConditionNumber G (fun _ ↦ 1) ^ 2 + 1)) *
        RHSQueryHardness.solutionPlus i
  inverseMinus : RHSQueryHardness.inverseMap
      (effectiveConditionNumber G (fun _ ↦ 1))
      (RHSQueryHardness.preparedMinus (effectiveConditionNumber G (fun _ ↦ 1))) =
    fun i ↦ (effectiveConditionNumber G (fun _ ↦ 1) * Real.sqrt 2 /
      Real.sqrt (effectiveConditionNumber G (fun _ ↦ 1) ^ 2 + 1)) *
        RHSQueryHardness.solutionMinus i
  inverseGainRatio :
    (1 / laplacian_eigenvalue₂ G (fun _ ↦ 1)) /
        (1 / laplacianEigenvalueMax G (fun _ ↦ 1)) =
      effectiveConditionNumber G (fun _ ↦ 1)
  solvePlus : G.laplacian (fun _ ↦ 1) *ᵥ
      ((effectiveConditionNumber G (fun _ ↦ 1) * Real.sqrt 2 /
          Real.sqrt (effectiveConditionNumber G (fun _ ↦ 1) ^ 2 + 1)) •
        RHSQueryHardness.balancedSolutionPlus pair) =
    laplacianEigenvalueMax G (fun _ ↦ 1) •
      RHSQueryHardness.balancedPreparedPlus pair
        (effectiveConditionNumber G (fun _ ↦ 1))
  solveMinus : G.laplacian (fun _ ↦ 1) *ᵥ
      ((effectiveConditionNumber G (fun _ ↦ 1) * Real.sqrt 2 /
          Real.sqrt (effectiveConditionNumber G (fun _ ↦ 1) ^ 2 + 1)) •
        RHSQueryHardness.balancedSolutionMinus pair) =
    laplacianEigenvalueMax G (fun _ ↦ 1) •
      RHSQueryHardness.balancedPreparedMinus pair
        (effectiveConditionNumber G (fun _ ↦ 1))

end PaperClaims

end
