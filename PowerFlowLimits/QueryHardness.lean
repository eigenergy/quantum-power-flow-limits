/-
Copyright (c) 2026 Cameron Khanpour and Samuel Talkington. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Cameron Khanpour, Samuel Talkington
-/
import PowerFlowLimits.Eigenvalues
import Mathlib.Algebra.Order.Chebyshev

/-!
# Right hand side oracle hardness and local observables

This module isolates the balanced hard input, coded phase family, and local observable algebra for
Proposition 3. Matrix and right hand side oracle calls are tracked separately. The two-state hard
pair changes only the prepared right hand side: its input states approach one another as the
condition number grows, while the normalized solution states remain a fixed distance apart.

The hybrid theorem is deliberately stated with its one-query progress bound as a premise. Proving
that premise for a concrete quantum oracle representation is the remaining model-specific step;
no matrix-oracle lower bound is assumed here.
-/

open Finset BigOperators Matrix

noncomputable section

/-- Resource and accuracy fields that must be fixed by a quantum linear-system claim. -/
structure QLSOracleModel where
  /-- Calls to the matrix oracle. -/
  matrixQueries : ℕ
  /-- Calls to the right hand side preparation oracle or its inverse. -/
  rhsQueries : ℕ
  /-- Allowed error in the prepared solution state. -/
  targetStateError : ℝ
  /-- Allowed observable estimation error. -/
  observableError : ℝ
  /-- Required probability of success. -/
  successProbability : ℝ

namespace QLSOracleModel

/-- Total matrix and right hand side oracle calls. -/
def totalQueries (model : QLSOracleModel) : ℕ :=
  model.matrixQueries + model.rhsQueries

end QLSOracleModel

namespace RHSQueryHardness

/-- Squared Euclidean norm, used instead of the function-space supremum norm. -/
def sqNorm {d : ℕ} (x : Fin d → ℝ) : ℝ :=
  dotProduct x x

/-- Squared Euclidean distance. -/
def sqDistance {d : ℕ} (x y : Fin d → ℝ) : ℝ :=
  sqNorm (x - y)

/-- A lossless net injection: its entries sum to zero, equivalently it lies in `span(1)^⊥`. -/
def IsBalanced {d : ℕ} (p : Fin d → ℝ) : Prop :=
  ∑ i, p i = 0

/-- Unit-weight star Laplacian on one center and `r` leaves.  This explicit family supplies the
joint hard instance used in Proposition 3. -/
def starLaplacianAction (r : ℕ) (x : Fin (r + 1) → ℝ) : Fin (r + 1) → ℝ :=
  Fin.cases ((r : ℝ) * x 0 - ∑ j : Fin r, x j.succ)
    (fun j ↦ x j.succ - x 0)

/-- The radial fast mode of the unit star. -/
def starFast (r : ℕ) : Fin (r + 1) → ℝ :=
  Fin.cases (-(r : ℝ)) (fun _ ↦ 1)

/-- A leaf codeword, extended by zero at the star center. -/
def starSlow {r : ℕ} (z : Fin r → ℝ) : Fin (r + 1) → ℝ :=
  Fin.cases 0 z

theorem starFast_balanced (r : ℕ) : IsBalanced (starFast r) := by
  simp [IsBalanced, starFast, Fin.sum_univ_succ]

theorem starSlow_balanced {r : ℕ} (z : Fin r → ℝ) (hz : ∑ j, z j = 0) :
    IsBalanced (starSlow z) := by
  simpa [IsBalanced, starSlow, Fin.sum_univ_succ] using hz

/-- The radial star mode has eigenvalue `r+1`. -/
theorem starLaplacianAction_fast (r : ℕ) :
    starLaplacianAction r (starFast r) = (r + 1 : ℝ) • starFast r := by
  funext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simp [starLaplacianAction, starFast]
    ring
  · simp [starLaplacianAction, starFast]
    ring

/-- Every zero-sum leaf codeword is a slow star eigenmode with eigenvalue one. -/
theorem starLaplacianAction_slow {r : ℕ} (z : Fin r → ℝ) (hz : ∑ j, z j = 0) :
    starLaplacianAction r (starSlow z) = starSlow z := by
  funext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simp [starLaplacianAction, starSlow, hz]
  · simp [starLaplacianAction, starSlow]

theorem starSlow_sqNorm {r : ℕ} (z : Fin r → ℝ) :
    sqNorm (starSlow z) = sqNorm z := by
  simp [sqNorm, dotProduct, starSlow, Fin.sum_univ_succ]

theorem starFast_dot_starSlow {r : ℕ} (z : Fin r → ℝ) (hz : ∑ j, z j = 0) :
    dotProduct (starFast r) (starSlow z) = 0 := by
  simpa [dotProduct, starFast, starSlow, Fin.sum_univ_succ] using hz

theorem starFast_sqNorm (r : ℕ) :
    sqNorm (starFast r) = (r : ℝ) * (r + 1) := by
  simp [sqNorm, dotProduct, starFast, Fin.sum_univ_succ]
  ring

/-- Exact Rayleigh numerator on the balanced subspace of the unit star. -/
theorem starLaplacian_energy_of_balanced (r : ℕ) (x : Fin (r + 1) → ℝ)
    (hx : IsBalanced x) :
    dotProduct x (starLaplacianAction r x) =
      sqNorm x + (r + 1 : ℝ) * (x 0) ^ 2 := by
  have hx' : x 0 + ∑ j : Fin r, x j.succ = 0 := by
    simpa [IsBalanced, Fin.sum_univ_succ] using hx
  simp only [dotProduct, sqNorm, starLaplacianAction, Fin.sum_univ_succ,
    Fin.cases_zero, Fin.cases_succ]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  rw [← Finset.sum_mul]
  have hmul := congrArg (fun y : ℝ ↦ 2 * x 0 * y) hx'
  ring_nf at hmul
  ring_nf
  linarith

theorem starLaplacian_rayleigh_lower (r : ℕ) (x : Fin (r + 1) → ℝ)
    (hx : IsBalanced x) :
    sqNorm x ≤ dotProduct x (starLaplacianAction r x) := by
  rw [starLaplacian_energy_of_balanced r x hx]
  have hnonneg : 0 ≤ (r + 1 : ℝ) * (x 0) ^ 2 := by positivity
  linarith

theorem starLaplacian_rayleigh_upper (r : ℕ) (x : Fin (r + 1) → ℝ)
    (hx : IsBalanced x) :
    dotProduct x (starLaplacianAction r x) ≤ (r + 1 : ℝ) * sqNorm x := by
  have hx' : x 0 + ∑ j : Fin r, x j.succ = 0 := by
    simpa [IsBalanced, Fin.sum_univ_succ] using hx
  have hsqeq : (x 0) ^ 2 = (∑ j : Fin r, x j.succ) ^ 2 := by
    have h := congrArg (fun y : ℝ ↦ y ^ 2) hx'
    nlinarith
  have hcs : (∑ j : Fin r, x j.succ) ^ 2 ≤
      (r : ℝ) * ∑ j : Fin r, (x j.succ) ^ 2 := by
    simpa using (sq_sum_le_card_mul_sum_sq
      (s := (Finset.univ : Finset (Fin r))) (f := fun j ↦ x j.succ))
  have hcenter : (x 0) ^ 2 ≤ (r : ℝ) * ∑ j : Fin r, (x j.succ) ^ 2 :=
    hsqeq.le.trans hcs
  rw [starLaplacian_energy_of_balanced r x hx]
  have hnorm : sqNorm x = (x 0) ^ 2 + ∑ j : Fin r, (x j.succ) ^ 2 := by
    simp [sqNorm, dotProduct, Fin.sum_univ_succ, sq]
  rw [hnorm]
  nlinarith

theorem isBalanced_iff_dotProduct_one_eq_zero {d : ℕ} (p : Fin d → ℝ) :
    IsBalanced p ↔ dotProduct (fun _ ↦ 1) p = 0 := by
  simp [IsBalanced, dotProduct]

/-- Two orthonormal balanced modes. For a connected Laplacian these are instantiated by a
largest-eigenvalue mode and a Fiedler mode. -/
structure BalancedModePair (d : ℕ) where
  /-- Normalized high eigenvalue mode. -/
  fast : Fin d → ℝ
  /-- Normalized low positive eigenvalue mode. -/
  slow : Fin d → ℝ
  fast_balanced : IsBalanced fast
  slow_balanced : IsBalanced slow
  fast_normalized : sqNorm fast = 1
  slow_normalized : sqNorm slow = 1
  orthogonal : dotProduct fast slow = 0

namespace BalancedModePair

/-- Isometric coordinate embedding of the two hard modes into the bus space. -/
def embed {d : ℕ} (P : BalancedModePair d) (z : Fin 2 → ℝ) : Fin d → ℝ :=
  z 0 • P.fast + z 1 • P.slow

theorem embed_balanced {d : ℕ} (P : BalancedModePair d) (z : Fin 2 → ℝ) :
    IsBalanced (P.embed z) := by
  have hfast : ∑ i, P.fast i = 0 := P.fast_balanced
  have hslow : ∑ i, P.slow i = 0 := P.slow_balanced
  simp [IsBalanced, embed, Finset.sum_add_distrib, ← Finset.mul_sum, hfast, hslow]

theorem slow_dot_fast {d : ℕ} (P : BalancedModePair d) :
    dotProduct P.slow P.fast = 0 := by
  rw [dotProduct_comm, P.orthogonal]

theorem embed_sqNorm {d : ℕ} (P : BalancedModePair d) (z : Fin 2 → ℝ) :
    sqNorm (P.embed z) = sqNorm z := by
  have hfast : dotProduct P.fast P.fast = 1 := P.fast_normalized
  have hslow : dotProduct P.slow P.slow = 1 := P.slow_normalized
  simp [sqNorm, embed, add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul,
    hfast, hslow, P.orthogonal, P.slow_dot_fast]

theorem embed_sqDistance {d : ℕ} (P : BalancedModePair d) (z w : Fin 2 → ℝ) :
    sqDistance (P.embed z) (P.embed w) = sqDistance z w := by
  have hsub : P.embed z - P.embed w = P.embed (z - w) := by
    ext i
    simp [embed]
    ring
  rw [sqDistance, hsub, P.embed_sqNorm, sqDistance]

end BalancedModePair

/-- The canonical hard prepared state in the two extreme restricted singular directions. -/
def preparedPlus (κ : ℝ) : Fin 2 → ℝ := fun i ↦
  if i = 0 then κ / Real.sqrt (κ ^ 2 + 1) else 1 / Real.sqrt (κ ^ 2 + 1)

/-- The other canonical hard prepared state. -/
def preparedMinus (κ : ℝ) : Fin 2 → ℝ := fun i ↦
  if i = 0 then κ / Real.sqrt (κ ^ 2 + 1) else -1 / Real.sqrt (κ ^ 2 + 1)

/-- An inverse whose singular gains on the two canonical directions are `1` and `κ`. -/
def inverseMap (κ : ℝ) (x : Fin 2 → ℝ) : Fin 2 → ℝ := fun i ↦
  if i = 0 then x i else κ * x i

/-- First normalized solution state of the hard pair. -/
def solutionPlus : Fin 2 → ℝ := fun i ↦
  if i = 0 then 1 / Real.sqrt 2 else 1 / Real.sqrt 2

/-- Second normalized solution state of the hard pair. -/
def solutionMinus : Fin 2 → ℝ := fun i ↦
  if i = 0 then 1 / Real.sqrt 2 else -1 / Real.sqrt 2

theorem preparedPlus_normalized (κ : ℝ) :
    sqNorm (preparedPlus κ) = 1 := by
  have hpos : 0 < κ ^ 2 + 1 := by positivity
  have hsqrt : Real.sqrt (κ ^ 2 + 1) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hpos)
  simp [sqNorm, dotProduct, preparedPlus, Fin.sum_univ_two]
  field_simp [hsqrt]
  nlinarith [Real.sq_sqrt hpos.le]

theorem preparedMinus_normalized (κ : ℝ) :
    sqNorm (preparedMinus κ) = 1 := by
  have hpos : 0 < κ ^ 2 + 1 := by positivity
  have hsqrt : Real.sqrt (κ ^ 2 + 1) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hpos)
  simp [sqNorm, dotProduct, preparedMinus, Fin.sum_univ_two]
  field_simp [hsqrt]
  nlinarith [Real.sq_sqrt hpos.le]

theorem inverseMap_preparedPlus (κ : ℝ) :
    inverseMap κ (preparedPlus κ) =
      fun i ↦ (κ * Real.sqrt 2 / Real.sqrt (κ ^ 2 + 1)) * solutionPlus i := by
  have hsqrt2 : Real.sqrt 2 ≠ 0 := by positivity
  funext i
  fin_cases i <;> simp [inverseMap, preparedPlus, solutionPlus]
  <;> field_simp [hsqrt2]

theorem inverseMap_preparedMinus (κ : ℝ) :
    inverseMap κ (preparedMinus κ) =
      fun i ↦ (κ * Real.sqrt 2 / Real.sqrt (κ ^ 2 + 1)) * solutionMinus i := by
  have hsqrt2 : Real.sqrt 2 ≠ 0 := by positivity
  funext i
  fin_cases i <;> simp [inverseMap, preparedMinus, solutionMinus]
  <;> field_simp [hsqrt2]

theorem prepared_sqDistance (κ : ℝ) (hκ : 0 < κ) :
    sqDistance (preparedPlus κ) (preparedMinus κ) = 4 / (κ ^ 2 + 1) := by
  have hpos : 0 < κ ^ 2 + 1 := by positivity
  have hsqrt : Real.sqrt (κ ^ 2 + 1) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hpos)
  simp [sqDistance, sqNorm, dotProduct, preparedPlus, preparedMinus, Fin.sum_univ_two]
  field_simp [hsqrt]
  nlinarith [Real.sq_sqrt hpos.le]

/-- Scalar form of the hard input distance, kept independent of coordinate encodings. -/
theorem canonical_input_gap_sq (κ : ℝ) (hκ : 0 < κ) :
    (2 / Real.sqrt (κ ^ 2 + 1)) ^ 2 = 4 / (κ ^ 2 + 1) := by
  have hpos : 0 < κ ^ 2 + 1 := by positivity
  have hsqrt : Real.sqrt (κ ^ 2 + 1) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hpos)
  field_simp [hsqrt]
  nlinarith [Real.sq_sqrt hpos.le]

/-- The two coordinates used by the canonical preparation oracles. Named coordinates keep their
definitions independent of elaborator generated bounds proofs. -/
def fin2Zero : Fin 2 := ⟨0, Nat.zero_lt_succ 1⟩

/-- Coordinate one in `Fin 2`. -/
def fin2One : Fin 2 := ⟨1, Nat.lt_succ_self 1⟩

/-- Canonical real preparation oracle for the `+` hard input.  It is the plane rotation whose
first column is `preparedPlus κ`. -/
def preparationOraclePlus (κ : ℝ) (x : Fin 2 → ℝ) : Fin 2 → ℝ := fun i ↦
  if i = fin2Zero then (κ * x fin2Zero - x fin2One) / Real.sqrt (κ ^ 2 + 1)
  else (x fin2Zero + κ * x fin2One) / Real.sqrt (κ ^ 2 + 1)

/-- Canonical real preparation oracle for the `-` hard input.  It is both the inverse of
`preparationOraclePlus κ` and the plane rotation whose first column is `preparedMinus κ`. -/
def preparationOracleMinus (κ : ℝ) (x : Fin 2 → ℝ) : Fin 2 → ℝ := fun i ↦
  if i = fin2Zero then (κ * x fin2Zero + x fin2One) / Real.sqrt (κ ^ 2 + 1)
  else (-x fin2Zero + κ * x fin2One) / Real.sqrt (κ ^ 2 + 1)

/-- The distinguished input basis state for the canonical preparation oracles. -/
def preparationBasis : Fin 2 → ℝ := fun i ↦ if i = 0 then 1 else 0

theorem preparationOraclePlus_prepares (κ : ℝ) :
    preparationOraclePlus κ preparationBasis = preparedPlus κ := by
  funext i
  fin_cases i <;>
    simp [preparationOraclePlus, preparationBasis, preparedPlus, fin2Zero, fin2One]

theorem preparationOracleMinus_prepares (κ : ℝ) :
    preparationOracleMinus κ preparationBasis = preparedMinus κ := by
  funext i
  fin_cases i <;>
    simp [preparationOracleMinus, preparationBasis, preparedMinus, fin2Zero, fin2One]

/-- The two canonical preparation oracles are exact inverses. -/
theorem preparationOraclePlus_comp_minus (κ : ℝ) (hκ : 0 < κ) (x : Fin 2 → ℝ) :
    preparationOraclePlus κ (preparationOracleMinus κ x) = x := by
  have hpos : 0 < κ ^ 2 + 1 := by positivity
  have hsqrt : Real.sqrt (κ ^ 2 + 1) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hpos)
  funext i
  fin_cases i <;> simp [preparationOraclePlus, preparationOracleMinus, fin2Zero, fin2One]
  <;> field_simp [hsqrt]
  <;> rw [Real.sq_sqrt hpos.le]
  <;> ring

theorem preparationOracleMinus_comp_plus (κ : ℝ) (hκ : 0 < κ) (x : Fin 2 → ℝ) :
    preparationOracleMinus κ (preparationOraclePlus κ x) = x := by
  have hpos : 0 < κ ^ 2 + 1 := by positivity
  have hsqrt : Real.sqrt (κ ^ 2 + 1) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hpos)
  funext i
  fin_cases i <;> simp [preparationOraclePlus, preparationOracleMinus, fin2Zero, fin2One]
  <;> field_simp [hsqrt]
  <;> rw [Real.sq_sqrt hpos.le]
  <;> ring

/-- Exact squared operator action of the oracle difference.  Thus its Euclidean operator norm is
`2 / sqrt (κ²+1) = O(1/κ)`.  The inverse pair has the same difference because the two oracles
swap under inversion. -/
theorem preparationOracle_gap_sq (κ : ℝ) (hκ : 0 < κ) (x : Fin 2 → ℝ) :
    sqDistance (preparationOraclePlus κ x) (preparationOracleMinus κ x) =
      (4 / (κ ^ 2 + 1)) * sqNorm x := by
  have hpos : 0 < κ ^ 2 + 1 := by positivity
  have hsqrt : Real.sqrt (κ ^ 2 + 1) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hpos)
  simp [sqDistance, sqNorm, dotProduct, preparationOraclePlus, preparationOracleMinus,
    fin2Zero, fin2One, Fin.sum_univ_two]
  field_simp [hsqrt]
  nlinarith [Real.sq_sqrt hpos.le]

/-- Coefficients of a coded right hand side.  The first coordinate is a common fast mode and
the second is a codeword in a slow eigenspace.  Multiplication by the Laplacian suppresses the
informative coordinate by the inverse gain ratio `κ`. -/
def codedPrepared (κ α : ℝ) : Fin 2 → ℝ := fun i ↦
  if i = 0 then κ / Real.sqrt (κ ^ 2 + α ^ 2)
  else α / Real.sqrt (κ ^ 2 + α ^ 2)

/-- Coefficients of the normalized solution corresponding to `codedPrepared`. -/
def codedSolution (α : ℝ) : Fin 2 → ℝ := fun i ↦
  if i = 0 then 1 / Real.sqrt (1 + α ^ 2)
  else α / Real.sqrt (1 + α ^ 2)

theorem codedPrepared_normalized (κ α : ℝ) (hκ : 0 < κ) :
    sqNorm (codedPrepared κ α) = 1 := by
  have hpos : 0 < κ ^ 2 + α ^ 2 := by positivity
  have hsqrt : Real.sqrt (κ ^ 2 + α ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hpos)
  simp [sqNorm, dotProduct, codedPrepared, Fin.sum_univ_two]
  field_simp [hsqrt]
  nlinarith [Real.sq_sqrt hpos.le]

theorem codedSolution_normalized (α : ℝ) :
    sqNorm (codedSolution α) = 1 := by
  have hpos : 0 < 1 + α ^ 2 := by positivity
  have hsqrt : Real.sqrt (1 + α ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hpos)
  simp [sqNorm, dotProduct, codedSolution, Fin.sum_univ_two]
  field_simp [hsqrt]
  nlinarith [Real.sq_sqrt hpos.le]

/-- Applying inverse gains `1` and `κ` to a coded prepared state yields its coded solution,
up to the displayed positive normalization scalar. -/
theorem inverseMap_codedPrepared (κ α : ℝ) :
    inverseMap κ (codedPrepared κ α) =
      fun i ↦ (κ * Real.sqrt (1 + α ^ 2) / Real.sqrt (κ ^ 2 + α ^ 2)) *
        codedSolution α i := by
  have hsqrt : Real.sqrt (1 + α ^ 2) ≠ 0 := by positivity
  funext i
  fin_cases i <;> simp [inverseMap, codedPrepared, codedSolution]
  <;> field_simp [hsqrt]

/-- The informative amplitude of the prepared right hand side is at most the solution signal
amplitude divided by the inverse gain ratio.  This is the condition number factor in the joint
fractional phase reduction. -/
theorem codedPrepared_signal_le (κ α : ℝ) (hκ : 0 < κ) (hα : 0 ≤ α) :
    α / Real.sqrt (κ ^ 2 + α ^ 2) ≤ α / κ := by
  have hsq : κ ^ 2 ≤ κ ^ 2 + α ^ 2 := by nlinarith [sq_nonneg α]
  have hsqrt : κ ≤ Real.sqrt (κ ^ 2 + α ^ 2) := by
    have h := Real.sqrt_le_sqrt hsq
    simpa [Real.sqrt_sq_eq_abs, abs_of_pos hκ] using h
  exact div_le_div_of_nonneg_left hα hκ hsqrt

theorem solutionPlus_normalized : sqNorm solutionPlus = 1 := by
  have hsqrt : Real.sqrt 2 ≠ 0 := by positivity
  simp [sqNorm, dotProduct, solutionPlus]
  field_simp [hsqrt]
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

theorem solutionMinus_normalized : sqNorm solutionMinus = 1 := by
  have hsqrt : Real.sqrt 2 ≠ 0 := by positivity
  simp [sqNorm, dotProduct, solutionMinus, Fin.sum_univ_two]
  field_simp [hsqrt]
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

theorem solution_sqDistance : sqDistance solutionPlus solutionMinus = 2 := by
  have hsqrt : Real.sqrt 2 ≠ 0 := by positivity
  simp [sqDistance, sqNorm, dotProduct, solutionPlus, solutionMinus, Fin.sum_univ_two]
  field_simp [hsqrt]
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- The canonical hard inputs embedded into two balanced Laplacian modes. -/
def balancedPreparedPlus {d : ℕ} (P : BalancedModePair d) (κ : ℝ) : Fin d → ℝ :=
  P.embed (preparedPlus κ)

/-- The second canonical hard input embedded into balanced Laplacian modes. -/
def balancedPreparedMinus {d : ℕ} (P : BalancedModePair d) (κ : ℝ) : Fin d → ℝ :=
  P.embed (preparedMinus κ)

/-- The corresponding normalized solution states in the balanced bus space. -/
def balancedSolutionPlus {d : ℕ} (P : BalancedModePair d) : Fin d → ℝ :=
  P.embed solutionPlus

/-- The second normalized solution state embedded into the balanced bus space. -/
def balancedSolutionMinus {d : ℕ} (P : BalancedModePair d) : Fin d → ℝ :=
  P.embed solutionMinus

theorem balancedPreparedPlus_balanced {d : ℕ} (P : BalancedModePair d) (κ : ℝ) :
    IsBalanced (balancedPreparedPlus P κ) :=
  P.embed_balanced _

theorem balancedPreparedMinus_balanced {d : ℕ} (P : BalancedModePair d) (κ : ℝ) :
    IsBalanced (balancedPreparedMinus P κ) :=
  P.embed_balanced _

theorem balancedSolutionPlus_balanced {d : ℕ} (P : BalancedModePair d) :
    IsBalanced (balancedSolutionPlus P) :=
  P.embed_balanced _

theorem balancedSolutionMinus_balanced {d : ℕ} (P : BalancedModePair d) :
    IsBalanced (balancedSolutionMinus P) :=
  P.embed_balanced _

theorem balancedPreparedPlus_normalized {d : ℕ} (P : BalancedModePair d) (κ : ℝ) :
    sqNorm (balancedPreparedPlus P κ) = 1 := by
  rw [balancedPreparedPlus, P.embed_sqNorm, preparedPlus_normalized]

theorem balancedPreparedMinus_normalized {d : ℕ} (P : BalancedModePair d) (κ : ℝ) :
    sqNorm (balancedPreparedMinus P κ) = 1 := by
  rw [balancedPreparedMinus, P.embed_sqNorm, preparedMinus_normalized]

theorem balancedPrepared_sqDistance {d : ℕ} (P : BalancedModePair d) (κ : ℝ)
    (hκ : 0 < κ) :
    sqDistance (balancedPreparedPlus P κ) (balancedPreparedMinus P κ) =
      4 / (κ ^ 2 + 1) := by
  rw [balancedPreparedPlus, balancedPreparedMinus, P.embed_sqDistance, prepared_sqDistance κ hκ]

theorem balancedSolutionPlus_normalized {d : ℕ} (P : BalancedModePair d) :
    sqNorm (balancedSolutionPlus P) = 1 := by
  rw [balancedSolutionPlus, P.embed_sqNorm, solutionPlus_normalized]

theorem balancedSolutionMinus_normalized {d : ℕ} (P : BalancedModePair d) :
    sqNorm (balancedSolutionMinus P) = 1 := by
  rw [balancedSolutionMinus, P.embed_sqNorm, solutionMinus_normalized]

theorem balancedSolution_sqDistance {d : ℕ} (P : BalancedModePair d) :
    sqDistance (balancedSolutionPlus P) (balancedSolutionMinus P) = 2 := by
  rw [balancedSolutionPlus, balancedSolutionMinus, P.embed_sqDistance, solution_sqDistance]

/-- The inverse gains on the Fiedler and largest-eigenvalue modes have ratio `κ₊`. -/
theorem inverse_gain_ratio_eq_kappaPlus (lambdaTwo lambdaMax : ℝ)
    (hlambdaTwo : 0 < lambdaTwo) (hlambdaMax : 0 < lambdaMax) :
    (1 / lambdaTwo) / (1 / lambdaMax) = lambdaMax / lambdaTwo := by
  field_simp

/-- For a spectrally connected Laplacian, the ratio of its extreme pseudoinverse gains is the
pseudo condition number `κ₊(B)`. -/
theorem laplacian_inverse_gain_ratio_eq_kappaPlus {n m : ℕ} (G : WeightedGraph n m)
    (hconn : G.Connected (fun _ ↦ 1))
    (hlambdaMax : 0 < laplacianEigenvalueMax G (fun _ ↦ 1)) :
    (1 / laplacian_eigenvalue₂ G (fun _ ↦ 1)) /
        (1 / laplacianEigenvalueMax G (fun _ ↦ 1)) =
      effectiveConditionNumber G (fun _ ↦ 1) := by
  unfold effectiveConditionNumber
  exact inverse_gain_ratio_eq_kappaPlus _ _ hconn hlambdaMax

/-- On two balanced extreme modes, a solve map with inverse gains `1` and `κ` sends the first
hard input to a scalar multiple of the first hard solution state. -/
theorem solve_balancedPreparedPlus {d : ℕ} (P : BalancedModePair d) (κ : ℝ)
    (solve : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ))
    (hfast : solve P.fast = P.fast) (hslow : solve P.slow = κ • P.slow) :
    solve (balancedPreparedPlus P κ) =
      (κ * Real.sqrt 2 / Real.sqrt (κ ^ 2 + 1)) • balancedSolutionPlus P := by
  have hsqrt2 : Real.sqrt 2 ≠ 0 := by positivity
  simp only [balancedPreparedPlus, balancedSolutionPlus, BalancedModePair.embed,
    LinearMap.map_add, LinearMap.map_smul, hfast, hslow]
  ext i
  simp [preparedPlus, solutionPlus]
  field_simp [hsqrt2]

/-- The corresponding identity for the second hard input. -/
theorem solve_balancedPreparedMinus {d : ℕ} (P : BalancedModePair d) (κ : ℝ)
    (solve : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ))
    (hfast : solve P.fast = P.fast) (hslow : solve P.slow = κ • P.slow) :
    solve (balancedPreparedMinus P κ) =
      (κ * Real.sqrt 2 / Real.sqrt (κ ^ 2 + 1)) • balancedSolutionMinus P := by
  have hsqrt2 : Real.sqrt 2 ≠ 0 := by positivity
  simp only [balancedPreparedMinus, balancedSolutionMinus, BalancedModePair.embed,
    LinearMap.map_add, LinearMap.map_smul, hfast, hslow]
  ext i
  simp [preparedMinus, solutionMinus]
  field_simp [hsqrt2]

/-- The coded version of the two-mode solve identity. The slow vector can be any normalized
codeword in a common slow eigenspace, so the identity applies simultaneously to a phase code. -/
theorem solve_codedPrepared {d : ℕ} (P : BalancedModePair d) (κ α : ℝ)
    (solve : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ))
    (hfast : solve P.fast = P.fast) (hslow : solve P.slow = κ • P.slow) :
    solve (P.embed (codedPrepared κ α)) =
      (κ * Real.sqrt (1 + α ^ 2) / Real.sqrt (κ ^ 2 + α ^ 2)) •
        P.embed (codedSolution α) := by
  have hsqrt : Real.sqrt (1 + α ^ 2) ≠ 0 := by positivity
  simp only [BalancedModePair.embed, LinearMap.map_add, LinearMap.map_smul, hfast, hslow]
  ext i
  simp [codedPrepared, codedSolution]
  field_simp [hsqrt]

/-- Real expectation value of an observable. -/
def observableExpectation {d : ℕ} (ψ : Fin d → ℝ)
    (M : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  dotProduct ψ (M *ᵥ ψ)

/-- A rank-one real observable `v vᵀ`. -/
def rankOneObservable {d : ℕ} (v : Fin d → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  vecMulVec v v

/-- The bus observable `e_i e_iᵀ`. -/
def busObservable {d : ℕ} (i : Fin d) : Matrix (Fin d) (Fin d) ℝ :=
  rankOneObservable (Pi.single i 1)

/-- The branch observable `(e_i-e_j)(e_i-e_j)ᵀ`. -/
def branchObservable {d : ℕ} (i j : Fin d) : Matrix (Fin d) (Fin d) ℝ :=
  rankOneObservable (Pi.single i 1 - Pi.single j 1)

theorem observableExpectation_rankOne {d : ℕ} (v ψ : Fin d → ℝ) :
    observableExpectation ψ (rankOneObservable v) = (dotProduct v ψ) ^ 2 := by
  simp only [observableExpectation, rankOneObservable, Matrix.vecMulVec_mulVec,
    dotProduct_smul]
  rw [dotProduct_comm ψ v]
  change (dotProduct v ψ) * (dotProduct v ψ) = (dotProduct v ψ) ^ 2
  ring

theorem observableExpectation_bus {d : ℕ} (i : Fin d) (ψ : Fin d → ℝ) :
    observableExpectation ψ (busObservable i) = (ψ i) ^ 2 := by
  rw [busObservable, observableExpectation_rankOne]
  rw [single_one_dotProduct]

theorem observableExpectation_branch {d : ℕ} (i j : Fin d) (ψ : Fin d → ℝ) :
    observableExpectation ψ (branchObservable i j) = (ψ i - ψ j) ^ 2 := by
  rw [branchObservable, observableExpectation_rankOne]
  rw [sub_dotProduct, single_one_dotProduct, single_one_dotProduct]

/-- The two normalized hard solution states expressed in arbitrary orthonormal singular modes. -/
def modeSolutionPlus {d : ℕ} (uMin uMax : Fin d → ℝ) : Fin d → ℝ :=
  fun i ↦ (uMin i + uMax i) / Real.sqrt 2

/-- The normalized difference of two orthonormal singular modes. -/
def modeSolutionMinus {d : ℕ} (uMin uMax : Fin d → ℝ) : Fin d → ℝ :=
  fun i ↦ (uMin i - uMax i) / Real.sqrt 2

theorem bus_observable_gap {d : ℕ} (uMin uMax : Fin d → ℝ) (i : Fin d) :
    observableExpectation (modeSolutionPlus uMin uMax) (busObservable i) -
        observableExpectation (modeSolutionMinus uMin uMax) (busObservable i) =
      2 * uMin i * uMax i := by
  rw [observableExpectation_bus, observableExpectation_bus]
  have hsqrt : Real.sqrt 2 ≠ 0 := by positivity
  simp [modeSolutionPlus, modeSolutionMinus]
  field_simp [hsqrt]
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

theorem branch_observable_gap {d : ℕ} (uMin uMax : Fin d → ℝ) (i j : Fin d) :
    observableExpectation (modeSolutionPlus uMin uMax) (branchObservable i j) -
        observableExpectation (modeSolutionMinus uMin uMax) (branchObservable i j) =
      2 * (uMin i - uMin j) * (uMax i - uMax j) := by
  rw [observableExpectation_branch, observableExpectation_branch]
  have hsqrt : Real.sqrt 2 ≠ 0 := by positivity
  simp [modeSolutionPlus, modeSolutionMinus]
  field_simp [hsqrt]
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- Estimates accurate to one quarter of a nonzero expectation gap remain separated by at least
half the gap. This is the readout step used for the intended local observable claim. -/
theorem estimates_separated_of_quarter_gap
    (exactPlus exactMinus estimatePlus estimateMinus gap : ℝ)
    (hgap : |exactPlus - exactMinus| = gap)
    (hplus : |estimatePlus - exactPlus| ≤ gap / 4)
    (hminus : |estimateMinus - exactMinus| ≤ gap / 4) :
    gap / 2 ≤ |estimatePlus - estimateMinus| := by
  have hdiff :
      |(estimatePlus - estimateMinus) - (exactPlus - exactMinus)| ≤
        |estimatePlus - exactPlus| + |estimateMinus - exactMinus| := by
    calc
      |(estimatePlus - estimateMinus) - (exactPlus - exactMinus)| =
          |(estimatePlus - exactPlus) - (estimateMinus - exactMinus)| := by ring_nf
      _ ≤ |estimatePlus - exactPlus| + |estimateMinus - exactMinus| := abs_sub _ _
  have htriangle :
      |exactPlus - exactMinus| ≤ |estimatePlus - estimateMinus| +
        |(estimatePlus - estimateMinus) - (exactPlus - exactMinus)| := by
    calc
      |exactPlus - exactMinus| =
          |(estimatePlus - estimateMinus) -
            ((estimatePlus - estimateMinus) - (exactPlus - exactMinus))| := by ring_nf
      _ ≤ |estimatePlus - estimateMinus| +
          |(estimatePlus - estimateMinus) - (exactPlus - exactMinus)| := abs_sub _ _
  rw [hgap] at htriangle
  linarith

/-- Telescoping form of the hybrid argument. The concrete oracle model must prove `hstep`. -/
theorem hybrid_distance_le (distance : ℕ → ℝ) (δ : ℝ)
    (hzero : distance 0 = 0)
    (hstep : ∀ t, distance (t + 1) ≤ distance t + δ) (q : ℕ) :
    distance q ≤ q * δ := by
  induction q with
  | zero => simp [hzero]
  | succ q ih =>
      calc
        distance (q + 1) ≤ distance q + δ := hstep q
        _ ≤ q * δ + δ := by linarith
        _ = (((q + 1 : ℕ) : ℝ) * δ) := by push_cast; ring

/-- Arithmetic conclusion of a hybrid argument with progress at most `C/κ` per RHS query. -/
theorem rhs_query_lower_bound (q : ℕ) (distance gap C κ : ℝ)
    (hκ : 0 < κ) (hC : 0 < C)
    (hseparate : gap ≤ distance)
    (hprogress : κ * distance ≤ C * q) :
    gap * κ / C ≤ q := by
  have h : gap * κ ≤ C * q := by nlinarith
  exact (div_le_iff₀ hC).2 (by simpa [mul_comm] using h)

end RHSQueryHardness
