/-
Copyright (c) 2026 Cameron Khanpour and Samuel Talkington. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Cameron Khanpour, Samuel Talkington
-/
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# Counterexamples to instancewise query lower bounds

This extension records a diagonal family showing that a condition number alone does not imply an
instancewise matrix oracle query lower bound. It is separate from the manuscript claim surface.
-/

open Finset BigOperators Matrix

noncomputable section

namespace PowerFlowLimits.Extensions.QueryCounterexamples

/-- A positive two-dimensional diagonal linear-system instance. -/
structure DiagonalQLSInstance where
  /-- Positive diagonal entries. -/
  diagonal : Fin 2 → ℝ
  diagonal_pos : ∀ i, 0 < diagonal i
  /-- Prepared right hand side. -/
  rhs : Fin 2 → ℝ

namespace DiagonalQLSInstance

/-- The represented diagonal matrix. -/
def matrix (I : DiagonalQLSInstance) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.diagonal I.diagonal

/-- The exact classical solution. -/
def solution (I : DiagonalQLSInstance) : Fin 2 → ℝ :=
  fun i ↦ I.rhs i / I.diagonal i

/-- The exact spectral condition number for a positive diagonal `2 × 2` matrix. -/
def conditionNumber (I : DiagonalQLSInstance) : ℝ :=
  max (I.diagonal 0) (I.diagonal 1) / min (I.diagonal 0) (I.diagonal 1)

theorem matrix_mulVec_solution (I : DiagonalQLSInstance) :
    I.matrix *ᵥ I.solution = I.rhs := by
  funext i
  unfold matrix
  rw [Matrix.mulVec_diagonal]
  unfold solution
  field_simp [ne_of_gt (I.diagonal_pos i)]

/-- `diag(1, 1/κ)` with right hand side `e₀`. -/
def eigenvectorFamily (κ : ℝ) (hκ : 0 < κ) : DiagonalQLSInstance where
  diagonal := fun i ↦ if i = 0 then 1 else 1 / κ
  diagonal_pos := by
    intro i
    split_ifs
    · norm_num
    · exact one_div_pos.mpr hκ
  rhs := fun i ↦ if i = 0 then 1 else 0

theorem eigenvectorFamily_conditionNumber (κ : ℝ) (hκ : 1 ≤ κ) :
    (eigenvectorFamily κ (lt_of_lt_of_le zero_lt_one hκ)).conditionNumber = κ := by
  have hκpos : 0 < κ := lt_of_lt_of_le zero_lt_one hκ
  change max 1 (1 / κ) / min 1 (1 / κ) = κ
  have hinv_le : 1 / κ ≤ 1 := (div_le_one hκpos).mpr hκ
  rw [max_eq_left hinv_le, min_eq_right hinv_le]
  · field_simp

theorem eigenvectorFamily_solution_eq_rhs (κ : ℝ) (hκ : 0 < κ) :
    (eigenvectorFamily κ hκ).solution = (eigenvectorFamily κ hκ).rhs := by
  funext i
  fin_cases i <;> simp [solution, eigenvectorFamily]

end DiagonalQLSInstance

/-- A state-preparation algorithm with an explicit matrix oracle query count. -/
structure DiagonalQLSAlgorithm where
  /-- State prepared from the right hand side. -/
  prepare : (Fin 2 → ℝ) → (Fin 2 → ℝ)
  /-- Number of matrix oracle calls. -/
  matrixQueries : ℕ

namespace DiagonalQLSAlgorithm

/-- Pass the prepared right hand side through without querying the matrix oracle. -/
def passThrough : DiagonalQLSAlgorithm where
  prepare := id
  matrixQueries := 0

/-- The algorithm prepares the exact solution of the instance. -/
def Solves (A : DiagonalQLSAlgorithm) (I : DiagonalQLSInstance) : Prop :=
  A.prepare I.rhs = I.solution

theorem passThrough_solves_eigenvectorFamily (κ : ℝ) (hκ : 0 < κ) :
    passThrough.Solves (DiagonalQLSInstance.eigenvectorFamily κ hκ) :=
  (DiagonalQLSInstance.eigenvectorFamily_solution_eq_rhs κ hκ).symm

/-- A single uniform zero-query algorithm solves instances with arbitrarily large condition
number. Thus condition number alone cannot give an instancewise `Ω(κ)` query lower bound. -/
theorem zero_query_solver_at_arbitrary_condition (κ : ℝ) (hκ : 1 ≤ κ) :
    ∃ I : DiagonalQLSInstance,
      I.conditionNumber = κ ∧ passThrough.Solves I ∧ passThrough.matrixQueries = 0 := by
  let hκpos : 0 < κ := lt_of_lt_of_le zero_lt_one hκ
  exact ⟨DiagonalQLSInstance.eigenvectorFamily κ hκpos,
    DiagonalQLSInstance.eigenvectorFamily_conditionNumber κ hκ,
    passThrough_solves_eigenvectorFamily κ hκpos, rfl⟩

end DiagonalQLSAlgorithm

end PowerFlowLimits.Extensions.QueryCounterexamples

end
