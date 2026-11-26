/-
Copyright (c) 2026 Cameron Khanpour and Samuel Talkington. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Cameron Khanpour, Samuel Talkington
-/
import PowerFlowLimits.ACPowerFlow
import PowerFlowLimits.DcOpfNewton
import PowerFlowLimits.GroundedTransfer
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Data.Matrix.Block

/-!
# The first Newton system of lossless AC power flow

At a lossless flat start, the active power and angle block of the Newton Jacobian is the
susceptance Laplacian and the off diagonal blocks vanish. The Jacobian of the reduced system is
therefore `J = diag(B_r, J_QV)`, and `κ₂(J) ≥ κ₂(B_r)`. This file proves

* the two off diagonal blocks vanish at flat angles, as derivatives of the nonlinear injection
  maps,
* a block diagonal matrix inherits the singular value bounds of each block, and
* singular value bounds of the grounded Laplacian control its eigenvalue condition number.

Together with `ACPowerFlow.lean` and `GroundedTransfer.lean`, every bound of Section II holds for
the first Newton system with its constant halved.
-/

open Finset BigOperators
open scoped Matrix

noncomputable section

variable {n m : ℕ}

/-- Lossless active injection at bus `i` with voltage magnitudes `V`. Each branch contributes
`Aᵢₑ bₑ V₊ V₋ sin((Aᵀθ)ₑ)`. -/
def WeightedGraph.acActivePower (G : WeightedGraph n m)
    (θ V : Fin n → ℝ) (i : Fin n) : ℝ :=
  ∑ e, G.incidence i e * G.weights e * V (G.posEndpoint e) * V (G.negEndpoint e) *
    Real.sin (voltageDrop G θ e)

/-- Lossless reactive injection at bus `i`. Each incident branch contributes
`bₑ (Vᵢ² - V₊ V₋ cos((Aᵀθ)ₑ))`, and `shunt` holds the bus shunt susceptances. -/
def WeightedGraph.acReactivePower (G : WeightedGraph n m) (shunt : Fin n → ℝ)
    (θ V : Fin n → ℝ) (i : Fin n) : ℝ :=
  shunt i * V i ^ 2 +
    ∑ e, G.incidence i e ^ 2 * G.weights e *
      (V i ^ 2 - V (G.posEndpoint e) * V (G.negEndpoint e) * Real.cos (voltageDrop G θ e))

/-- With unit voltage magnitudes the active injection is the one of `ACPowerFlow.lean`. -/
theorem WeightedGraph.acActivePower_unit_voltage (G : WeightedGraph n m) (θ : Fin n → ℝ) :
    G.acActivePower θ (fun _ ↦ 1) = G.acActiveInjection θ := by
  funext i
  unfold WeightedGraph.acActivePower WeightedGraph.acActiveInjection
  refine Finset.sum_congr rfl fun e _ ↦ ?_
  ring

/-- At flat angles the lossless active injections vanish for every voltage magnitude profile. -/
theorem WeightedGraph.acActivePower_flat_angle (G : WeightedGraph n m) (V : Fin n → ℝ)
    (i : Fin n) :
    G.acActivePower (fun _ ↦ 0) V i = 0 := by
  unfold WeightedGraph.acActivePower
  refine Finset.sum_eq_zero fun e _ ↦ ?_
  have hdrop : voltageDrop G (fun _ ↦ (0 : ℝ)) e = 0 := by
    rw [voltageDrop_eq_endpoint_diff]
    ring
  rw [hdrop, Real.sin_zero, mul_zero]

/-- The active power and voltage magnitude block of the Jacobian vanishes at flat angles. -/
theorem WeightedGraph.hasDerivAt_acActivePower_voltage_flat (G : WeightedGraph n m)
    (V h : Fin n → ℝ) (i : Fin n) (t : ℝ) :
    HasDerivAt (fun u ↦ G.acActivePower (fun _ ↦ 0) (fun v ↦ V v + u * h v) i) 0 t := by
  have hconst : (fun u : ℝ ↦ G.acActivePower (fun _ ↦ 0) (fun v ↦ V v + u * h v) i) =
      fun _ ↦ (0 : ℝ) := by
    funext u
    exact G.acActivePower_flat_angle _ i
  rw [hconst]
  exact hasDerivAt_const t 0

/-- The reactive power and angle block of the Jacobian vanishes at flat angles. -/
theorem WeightedGraph.hasDerivAt_acReactivePower_angle_flat (G : WeightedGraph n m)
    (shunt V h : Fin n → ℝ) (i : Fin n) :
    HasDerivAt (fun t ↦ G.acReactivePower shunt (fun v ↦ t * h v) V i) 0 0 := by
  have hdrop : ∀ (e : Fin m) (t : ℝ),
      voltageDrop G (fun v ↦ t * h v) e = t * voltageDrop G h e := by
    intro e t
    rw [voltageDrop_eq_endpoint_diff, voltageDrop_eq_endpoint_diff]
    ring
  have hedge : ∀ e : Fin m, HasDerivAt
      (fun t ↦ G.incidence i e ^ 2 * G.weights e *
        (V i ^ 2 - V (G.posEndpoint e) * V (G.negEndpoint e) *
          Real.cos (voltageDrop G (fun v ↦ t * h v) e))) 0 0 := by
    intro e
    have hlinear : HasDerivAt (fun t : ℝ ↦ t * voltageDrop G h e) (voltageDrop G h e) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).mul_const (voltageDrop G h e)
    have hcos := hlinear.cos
    have hproduct := hcos.const_mul (V (G.posEndpoint e) * V (G.negEndpoint e))
    have hsub := hproduct.const_sub (V i ^ 2)
    have hscaled := hsub.const_mul (G.incidence i e ^ 2 * G.weights e)
    simp only [hdrop]
    convert hscaled using 1
    simp
  have hsum := HasDerivAt.fun_sum fun e (_he : e ∈ Finset.univ) ↦ hedge e
  have hall := hsum.const_add (shunt i * V i ^ 2)
  simpa [WeightedGraph.acReactivePower] using hall

/-- A block diagonal matrix inherits the singular value bounds of its first block. -/
theorem blockDiagonal_singular_bounds {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι ι ℝ) (C : Matrix κ κ ℝ) (σmin σmax : ℝ)
    (hlower : ∀ z : ι ⊕ κ → ℝ,
      σmin ^ 2 * ∑ y, z y ^ 2 ≤ ∑ y, ((Matrix.fromBlocks A 0 0 C *ᵥ z) y) ^ 2)
    (hupper : ∀ z : ι ⊕ κ → ℝ,
      ∑ y, ((Matrix.fromBlocks A 0 0 C *ᵥ z) y) ^ 2 ≤ σmax ^ 2 * ∑ y, z y ^ 2) :
    (∀ x : ι → ℝ, σmin ^ 2 * ∑ i, x i ^ 2 ≤ ∑ i, ((A *ᵥ x) i) ^ 2) ∧
      ∀ x : ι → ℝ, ∑ i, ((A *ᵥ x) i) ^ 2 ≤ σmax ^ 2 * ∑ i, x i ^ 2 := by
  have hmul : ∀ x : ι → ℝ,
      Matrix.fromBlocks A 0 0 C *ᵥ Sum.elim x (0 : κ → ℝ) = Sum.elim (A *ᵥ x) 0 := by
    intro x
    rw [Matrix.fromBlocks_mulVec]
    simp
  have hnorm : ∀ x : ι → ℝ, ∑ y, (Sum.elim x (0 : κ → ℝ) y) ^ 2 = ∑ i, x i ^ 2 := by
    intro x
    rw [Fintype.sum_sum_type]
    simp
  have himage : ∀ x : ι → ℝ,
      ∑ y, ((Matrix.fromBlocks A 0 0 C *ᵥ Sum.elim x (0 : κ → ℝ)) y) ^ 2 =
        ∑ i, ((A *ᵥ x) i) ^ 2 := by
    intro x
    rw [hmul, Fintype.sum_sum_type]
    simp
  constructor
  · intro x
    have h := hlower (Sum.elim x 0)
    rwa [hnorm, himage] at h
  · intro x
    have h := hupper (Sum.elim x 0)
    rwa [hnorm, himage] at h

/-- For a symmetric positive semidefinite matrix, a lower bound on the smallest singular value is
a lower bound on the Rayleigh quotient. -/
theorem rayleigh_lower_of_singular_lower {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (hsymm : A.IsHermitian)
    (hpsd : ∀ x : ι → ℝ, 0 ≤ ∑ i, (A *ᵥ x) i * x i)
    (σ : ℝ) (hσ : 0 ≤ σ)
    (hlower : ∀ x : ι → ℝ, σ ^ 2 * ∑ i, x i ^ 2 ≤ ∑ i, ((A *ᵥ x) i) ^ 2)
    (x : ι → ℝ) :
    σ * ∑ i, x i ^ 2 ≤ ∑ i, (A *ᵥ x) i * x i := by
  classical
  rcases isEmpty_or_nonempty ι with hempty | hnonempty
  · simp
  let T : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι := Matrix.toEuclideanLin A
  have hT : T.IsSymmetric := (Matrix.isHermitian_iff_isSymmetric).mp hsymm
  have hinner : ∀ z : EuclideanSpace ℝ ι,
      inner ℝ (T z) z = ∑ i, (A *ᵥ WithLp.ofLp z) i * z i := by
    intro z
    change inner ℝ (WithLp.toLp 2 (A *ᵥ WithLp.ofLp z)) z = _
    simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  have hnormsq : ∀ z : EuclideanSpace ℝ ι, ‖z‖ ^ 2 = ∑ i, z i ^ 2 := by
    intro z
    rw [EuclideanSpace.norm_sq_eq]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [Real.norm_eq_abs, sq_abs]
  have hrayleigh_nonneg : ∀ z : {z : EuclideanSpace ℝ ι // z ≠ 0},
      0 ≤ inner ℝ (T z) z / ‖(z : EuclideanSpace ℝ ι)‖ ^ 2 := by
    intro z
    refine div_nonneg ?_ (sq_nonneg _)
    rw [hinner]
    exact hpsd (WithLp.ofLp (z : EuclideanSpace ℝ ι))
  have hbdd : BddBelow (Set.range fun z : {z : EuclideanSpace ℝ ι // z ≠ 0} ↦
      inner ℝ (T z) z / ‖(z : EuclideanSpace ℝ ι)‖ ^ 2) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨z, rfl⟩
    exact hrayleigh_nonneg z
  set μ : ℝ := ⨅ z : {z : EuclideanSpace ℝ ι // z ≠ 0},
    inner ℝ (T z) z / ‖(z : EuclideanSpace ℝ ι)‖ ^ 2 with hμ
  have heig : Module.End.HasEigenvalue T μ := by
    simpa only [hμ, RCLike.re_to_real] using hT.hasEigenvalue_iInf_of_finiteDimensional
  obtain ⟨v, hv⟩ := heig.exists_hasEigenvector
  have hv_ne : v ≠ 0 := hv.2
  have hv_eq : T v = μ • v := hv.apply_eq_smul
  haveI : Nonempty {z : EuclideanSpace ℝ ι // z ≠ 0} := ⟨⟨v, hv_ne⟩⟩
  have hμ_nonneg : 0 ≤ μ := le_ciInf hrayleigh_nonneg
  have hv_normsq_pos : 0 < ∑ i, v i ^ 2 := by
    rw [← hnormsq]
    exact sq_pos_of_pos (norm_pos_iff.mpr hv_ne)
  -- the eigenvector shows that the singular value bound is at most the smallest eigenvalue
  have hσ_le : σ ≤ μ := by
    have hlow := hlower (WithLp.ofLp v)
    have himage : ∑ i, ((A *ᵥ WithLp.ofLp v) i) ^ 2 = μ ^ 2 * ∑ i, v i ^ 2 := by
      have hcoord : ∀ i, (A *ᵥ WithLp.ofLp v) i = μ * v i := by
        intro i
        have hi : (WithLp.toLp 2 (A *ᵥ WithLp.ofLp v) : EuclideanSpace ℝ ι) i = (μ • v) i :=
          congrArg (fun z : EuclideanSpace ℝ ι ↦ z i) hv_eq
        simpa using hi
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [hcoord i]
      ring
    rw [himage] at hlow
    have hsq : σ ^ 2 ≤ μ ^ 2 := le_of_mul_le_mul_right hlow hv_normsq_pos
    exact (sq_le_sq₀ hσ hμ_nonneg).mp hsq
  by_cases hx : x = 0
  · subst hx
    simp
  · have hxE : (WithLp.toLp 2 x : EuclideanSpace ℝ ι) ≠ 0 := by
      intro hzero
      apply hx
      have := congrArg WithLp.ofLp hzero
      simpa using this
    have hq := ciInf_le hbdd
      (⟨WithLp.toLp 2 x, hxE⟩ : {z : EuclideanSpace ℝ ι // z ≠ 0})
    change μ ≤ inner ℝ (T (WithLp.toLp 2 x)) (WithLp.toLp 2 x) /
      ‖(WithLp.toLp 2 x : EuclideanSpace ℝ ι)‖ ^ 2 at hq
    rw [hinner, hnormsq] at hq
    have hx_pos : 0 < ∑ i, x i ^ 2 := by
      have hpos : 0 < ‖(WithLp.toLp 2 x : EuclideanSpace ℝ ι)‖ ^ 2 :=
        sq_pos_of_pos (norm_pos_iff.mpr hxE)
      rw [hnormsq] at hpos
      simpa using hpos
    have hq' : μ ≤ (∑ i, (A *ᵥ x) i * x i) / ∑ i, x i ^ 2 := by
      simpa using hq
    have hmul := (le_div_iff₀ hx_pos).mp hq'
    exact (mul_le_mul_of_nonneg_right hσ_le hx_pos.le).trans hmul

/-- Restrict a bus vector to the retained buses. -/
def retainedPart (r : Fin n) (x : Fin n → ℝ) : GroundedIndex r → ℝ := fun i ↦ x i

theorem groundedLaplacian_mulVec_retainedPart (G : WeightedGraph n m) (r : Fin n)
    (x : Fin n → ℝ) (hx : x r = 0) (i : GroundedIndex r) :
    (groundedLaplacian G r *ᵥ retainedPart r x) i =
      ∑ j, G.laplacian (fun _ ↦ 1) i j * x j := by
  change ∑ j : GroundedIndex r, G.laplacian (fun _ ↦ 1) i j * x j = _
  exact sum_groundedIndex_eq r (fun j ↦ G.laplacian (fun _ ↦ 1) i j * x j) (by simp [hx])

theorem sum_sq_retainedPart (r : Fin n) (x : Fin n → ℝ) (hx : x r = 0) :
    ∑ i, retainedPart r x i ^ 2 = ∑ i, x i ^ 2 :=
  sum_groundedIndex_eq r (fun i ↦ x i ^ 2) (by simp [hx])

theorem grounded_quadratic_retainedPart (G : WeightedGraph n m) (r : Fin n)
    (x : Fin n → ℝ) (hx : x r = 0) :
    ∑ i, (groundedLaplacian G r *ᵥ retainedPart r x) i * retainedPart r x i =
      ∑ i, (∑ j, G.laplacian (fun _ ↦ 1) i j * x j) * x i := by
  simp_rw [groundedLaplacian_mulVec_retainedPart G r x hx]
  exact sum_groundedIndex_eq r
    (fun i ↦ (∑ j, G.laplacian (fun _ ↦ 1) i j * x j) * x i) (by simp [hx])

/-- Extend a vector on the retained buses by zero at the slack bus. -/
def extendByZero (r : Fin n) (x : GroundedIndex r → ℝ) : Fin n → ℝ :=
  fun i ↦ if h : i = r then 0 else x ⟨i, h⟩

theorem extendByZero_slack (r : Fin n) (x : GroundedIndex r → ℝ) :
    extendByZero r x r = 0 := by
  simp [extendByZero]

theorem retainedPart_extendByZero (r : Fin n) (x : GroundedIndex r → ℝ) :
    retainedPart r (extendByZero r x) = x := by
  funext i
  simp [retainedPart, extendByZero, i.2]

/-- The grounded Laplacian is positive semidefinite. -/
theorem groundedLaplacian_quadratic_nonneg (G : WeightedGraph n m) (r : Fin n)
    (x : GroundedIndex r → ℝ) :
    0 ≤ ∑ i, (groundedLaplacian G r *ᵥ x) i * x i := by
  have h := grounded_quadratic_retainedPart G r (extendByZero r x) (extendByZero_slack r x)
  rw [retainedPart_extendByZero] at h
  rw [h]
  have hcomm : ∑ i, (∑ j, G.laplacian (fun _ ↦ 1) i j * extendByZero r x j) *
      extendByZero r x i =
        ∑ i, extendByZero r x i * ∑ j, G.laplacian (fun _ ↦ 1) i j * extendByZero r x j := by
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    ring
  rw [hcomm, laplacian_quadratic]
  exact Finset.sum_nonneg fun e _ ↦
    mul_nonneg (mul_nonneg zero_le_one (G.weights_pos e).le) (sq_nonneg _)

theorem groundedLaplacian_isHermitian (G : WeightedGraph n m) (r : Fin n) :
    (groundedLaplacian G r).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, star_trivial, groundedLaplacian_apply]
  exact G.laplacian_symmetric (fun _ ↦ 1) j i

/-- Singular value bounds of the grounded Laplacian control its eigenvalue condition number:
`κ₂(B_r) ≤ σmax / σmin`. -/
theorem groundedConditionNumber_le_of_singular_bounds (G : WeightedGraph n m) (r : Fin n)
    (hn : 1 < n) (σmin σmax : ℝ) (hσmin : 0 < σmin) (hσmax : 0 ≤ σmax)
    (hlower : ∀ x : GroundedIndex r → ℝ,
      σmin ^ 2 * ∑ i, x i ^ 2 ≤ ∑ i, ((groundedLaplacian G r *ᵥ x) i) ^ 2)
    (hupper : ∀ x : GroundedIndex r → ℝ,
      ∑ i, ((groundedLaplacian G r *ᵥ x) i) ^ 2 ≤ σmax ^ 2 * ∑ i, x i ^ 2) :
    groundedConditionNumber G r ≤ σmax / σmin := by
  classical
  -- the smallest singular value bound is a Rayleigh lower bound
  have hmin_mem : σmin ∈ {a : ℝ | ∀ (x : Fin n → ℝ), x r = 0 →
      a * (∑ i, x i ^ 2) ≤
        ∑ i, (∑ j, G.laplacian (fun _ ↦ 1) i j * x j) * x i} := by
    intro x hx
    have h := rayleigh_lower_of_singular_lower (groundedLaplacian G r)
      (groundedLaplacian_isHermitian G r) (groundedLaplacian_quadratic_nonneg G r)
      σmin hσmin.le hlower (retainedPart r x)
    rwa [sum_sq_retainedPart r x hx, grounded_quadratic_retainedPart G r x hx] at h
  have hmin_le : σmin ≤ groundedLaplacianEigenvalueMin G r := by
    unfold groundedLaplacianEigenvalueMin
    exact le_csSup (groundedEigenvalueMin_set_bddAbove G r hn) hmin_mem
  -- the largest singular value bound is a Rayleigh upper bound
  have hmax_mem : σmax ∈ {a : ℝ | ∀ (x : Fin n → ℝ), x r = 0 →
      ∑ i, (∑ j, G.laplacian (fun _ ↦ 1) i j * x j) * x i ≤
        a * ∑ i, x i ^ 2} := by
    intro x hx
    have hup := hupper (retainedPart r x)
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (GroundedIndex r))
      (fun i ↦ (groundedLaplacian G r *ᵥ retainedPart r x) i) (retainedPart r x)
    have hquad_nonneg := groundedLaplacian_quadratic_nonneg G r (retainedPart r x)
    rw [grounded_quadratic_retainedPart G r x hx] at hcs hquad_nonneg
    rw [sum_sq_retainedPart r x hx] at hcs hup
    have hsum_nonneg : 0 ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg fun i _ ↦ sq_nonneg _
    have hsq : (∑ i, (∑ j, G.laplacian (fun _ ↦ 1) i j * x j) * x i) ^ 2 ≤
        (σmax * ∑ i, x i ^ 2) ^ 2 := by
      calc
        (∑ i, (∑ j, G.laplacian (fun _ ↦ 1) i j * x j) * x i) ^ 2 ≤
            (∑ i, ((groundedLaplacian G r *ᵥ retainedPart r x) i) ^ 2) *
              ∑ i, x i ^ 2 := hcs
        _ ≤ (σmax ^ 2 * ∑ i, x i ^ 2) * ∑ i, x i ^ 2 :=
          mul_le_mul_of_nonneg_right hup hsum_nonneg
        _ = (σmax * ∑ i, x i ^ 2) ^ 2 := by ring
    exact (sq_le_sq₀ hquad_nonneg (mul_nonneg hσmax hsum_nonneg)).mp hsq
  have hmax_bdd : BddBelow {a : ℝ | ∀ (x : Fin n → ℝ), x r = 0 →
      ∑ i, (∑ j, G.laplacian (fun _ ↦ 1) i j * x j) * x i ≤
        a * ∑ i, x i ^ 2} := by
    letI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
    obtain ⟨i, hi⟩ := exists_ne r
    refine ⟨groundedLaplacian G r ⟨i, hi⟩ ⟨i, hi⟩, ?_⟩
    intro a ha
    have hx_r : stdBasis i r = 0 := by
      simp [stdBasis, Ne.symm hi]
    have h := ha (stdBasis i) hx_r
    have hquad : ∑ j, (∑ k, G.laplacian (fun _ ↦ 1) j k * stdBasis i k) * stdBasis i j =
        groundedLaplacian G r ⟨i, hi⟩ ⟨i, hi⟩ := by
      simp [stdBasis, groundedLaplacian, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ]
    have hsq : ∑ j, stdBasis i j ^ 2 = 1 := by
      simp [stdBasis, sq, Finset.sum_ite_eq', Finset.mem_univ]
    rw [hquad, hsq, mul_one] at h
    exact h
  have hmax_le : groundedLaplacianEigenvalueMax G r ≤ σmax := by
    unfold groundedLaplacianEigenvalueMax
    exact csInf_le hmax_bdd hmax_mem
  have hmin_pos : 0 < groundedLaplacianEigenvalueMin G r := lt_of_lt_of_le hσmin hmin_le
  unfold groundedConditionNumber
  exact (div_le_div_of_nonneg_right hmax_le hmin_pos.le).trans
    (div_le_div_of_nonneg_left hσmax hσmin hmin_le)

/-- The first Newton system of lossless AC power flow. For `J = diag(B_r, J_QV)` with an
arbitrary reactive power and voltage magnitude block, every pair of singular value bounds of `J`
satisfies `σmax / σmin ≥ κ₂(B_r)`. -/
theorem flatStart_blockDiagonal_condition_bound (G : WeightedGraph n m) (r : Fin n)
    (hn : 1 < n) {κ : Type*} [Fintype κ] (JQV : Matrix κ κ ℝ)
    (σmin σmax : ℝ) (hσmin : 0 < σmin) (hσmax : 0 ≤ σmax)
    (hlower : ∀ z : GroundedIndex r ⊕ κ → ℝ,
      σmin ^ 2 * ∑ y, z y ^ 2 ≤
        ∑ y, ((Matrix.fromBlocks (groundedLaplacian G r) 0 0 JQV *ᵥ z) y) ^ 2)
    (hupper : ∀ z : GroundedIndex r ⊕ κ → ℝ,
      ∑ y, ((Matrix.fromBlocks (groundedLaplacian G r) 0 0 JQV *ᵥ z) y) ^ 2 ≤
        σmax ^ 2 * ∑ y, z y ^ 2) :
    groundedConditionNumber G r ≤ σmax / σmin := by
  classical
  obtain ⟨hlowerA, hupperA⟩ :=
    blockDiagonal_singular_bounds (groundedLaplacian G r) JQV σmin σmax hlower hupper
  exact groundedConditionNumber_le_of_singular_bounds G r hn σmin σmax hσmin hσmax
    hlowerA hupperA

end
