/-
Copyright (c) 2026 Cameron Khanpour and Samuel Talkington. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Cameron Khanpour, Samuel Talkington
-/

import PowerFlowLimits.QueryHardness
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Extreme Laplacian modes on the balanced subspace

This module restricts the unit weighted Laplacian to the zero sum bus subspace. It proves that
the restricted operator is symmetric and invertible for a connected graph, then connects its
extreme modes to the two mode hard instance used by the right hand side query bounds.
-/

set_option autoImplicit false

open Finset BigOperators Matrix
open scoped Matrix

noncomputable section

namespace SpectralHardPair

variable {n m : ℕ}

/-- The unit weighted Laplacian as an endomorphism of Euclidean bus space. -/
def laplacianOperator (G : WeightedGraph n m) :
    EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
  Matrix.toEuclideanLin (G.laplacian (fun _ ↦ 1))

@[simp]
theorem laplacianOperator_apply (G : WeightedGraph n m)
    (x : EuclideanSpace ℝ (Fin n)) :
    laplacianOperator G x = WithLp.toLp 2 (G.laplacian (fun _ ↦ 1) *ᵥ WithLp.ofLp x) :=
  rfl

/-- Symmetry of the Laplacian matrix gives a symmetric Euclidean endomorphism. -/
theorem laplacianOperator_isSymmetric (G : WeightedGraph n m) :
    (laplacianOperator G).IsSymmetric := by
  unfold laplacianOperator
  rw [← Matrix.isHermitian_iff_isSymmetric]
  ext i j
  simp only [Matrix.conjTranspose_apply, star_trivial]
  exact G.laplacian_symmetric (fun _ ↦ 1) j i

/-- The Laplacian preserves the zero sum subspace. -/
theorem laplacianOperator_mem_zeroSum (G : WeightedGraph n m)
    (x : EuclideanSpace ℝ (Fin n)) :
    laplacianOperator G x ∈ zeroSumSubspace n := by
  change ∑ i, (G.laplacian (fun _ ↦ 1) *ᵥ WithLp.ofLp x) i = 0
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro j _
  rw [← Finset.sum_mul]
  have hcol : ∑ i, G.laplacian (fun _ ↦ 1) i j = 0 := by
    simpa only [G.laplacian_symmetric (fun _ ↦ 1)] using
      G.laplacian_kernel (fun _ ↦ 1) j
  rw [hcol, zero_mul]

/-- The unit Laplacian restricted to balanced vectors. -/
def restrictedLaplacian (G : WeightedGraph n m) :
    zeroSumSubspace n →ₗ[ℝ] zeroSumSubspace n :=
  (laplacianOperator G).restrict fun x _ ↦ laplacianOperator_mem_zeroSum G x

@[simp]
theorem restrictedLaplacian_coe (G : WeightedGraph n m) (x : zeroSumSubspace n) :
    (restrictedLaplacian G x : EuclideanSpace ℝ (Fin n)) = laplacianOperator G x :=
  rfl

/-- The balanced restriction remains symmetric. -/
theorem restrictedLaplacian_isSymmetric (G : WeightedGraph n m) :
    (restrictedLaplacian G).IsSymmetric :=
  (laplacianOperator_isSymmetric G).restrict_invariant fun x _ ↦
    laplacianOperator_mem_zeroSum G x

/-- Connectedness makes the balanced restriction injective. -/
theorem restrictedLaplacian_injective (G : WeightedGraph n m)
    (hconn : G.CombinatoriallyConnected) (hn : 0 < n) :
    Function.Injective (restrictedLaplacian G) := by
  intro x y hxy
  have hzero : restrictedLaplacian G (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have hzero' := congrArg (fun z : zeroSumSubspace n ↦
    (z : EuclideanSpace ℝ (Fin n))) hzero
  have hmul : G.laplacian (fun _ ↦ 1) *ᵥ (fun i ↦ (x - y : zeroSumSubspace n).1 i) = 0 := by
    apply WithLp.toLp_injective 2
    simpa only [restrictedLaplacian_coe, laplacianOperator_apply, map_zero,
      WithLp.toLp_zero] using hzero'
  obtain ⟨c, hc⟩ :=
    (laplacian_mulVec_eq_zero_iff_constant G hconn _).mp hmul
  have hsum : ∑ i, (x - y : zeroSumSubspace n).1 i = 0 := (x - y).2
  have hnc : (n : ℝ) * c = 0 := by
    rw [hc] at hsum
    simpa [Finset.sum_const, Finset.card_fin, nsmul_eq_mul] using hsum
  have hc0 : c = 0 :=
    (mul_eq_zero.mp hnc).resolve_left (Nat.cast_ne_zero.mpr hn.ne')
  apply Subtype.ext
  apply WithLp.ofLp_injective 2
  funext i
  have hi := congrFun hc i
  rw [hc0] at hi
  exact sub_eq_zero.mp hi

/-- The exact balanced solve equivalence for a connected Laplacian. -/
def restrictedLaplacianEquiv (G : WeightedGraph n m)
    (hconn : G.CombinatoriallyConnected) (hn : 0 < n) :
    zeroSumSubspace n ≃ₗ[ℝ] zeroSumSubspace n :=
  LinearEquiv.ofInjectiveEndo (restrictedLaplacian G)
    (restrictedLaplacian_injective G hconn hn)

/-- The inverse of the balanced Laplacian restriction. -/
def balancedSolve (G : WeightedGraph n m)
    (hconn : G.CombinatoriallyConnected) (hn : 0 < n) :
    zeroSumSubspace n →ₗ[ℝ] zeroSumSubspace n :=
  (restrictedLaplacianEquiv G hconn hn).symm.toLinearMap

@[simp]
theorem restrictedLaplacian_balancedSolve (G : WeightedGraph n m)
    (hconn : G.CombinatoriallyConnected) (hn : 0 < n) (x : zeroSumSubspace n) :
    restrictedLaplacian G (balancedSolve G hconn hn x) = x :=
  (restrictedLaplacianEquiv G hconn hn).apply_symm_apply x

@[simp]
theorem balancedSolve_restrictedLaplacian (G : WeightedGraph n m)
    (hconn : G.CombinatoriallyConnected) (hn : 0 < n) (x : zeroSumSubspace n) :
    balancedSolve G hconn hn (restrictedLaplacian G x) = x :=
  (restrictedLaplacianEquiv G hconn hn).symm_apply_apply x

/-- The solve equivalence scales a nonzero Laplacian eigenmode by the reciprocal eigenvalue. -/
theorem balancedSolve_eigenvector (G : WeightedGraph n m)
    (hconn : G.CombinatoriallyConnected) (hn : 0 < n) (v : zeroSumSubspace n)
    (lambda : ℝ) (hlambda : lambda ≠ 0)
    (hv : restrictedLaplacian G v = lambda • v) :
    balancedSolve G hconn hn v = lambda⁻¹ • v := by
  apply restrictedLaplacian_injective G hconn hn
  rw [restrictedLaplacian_balancedSolve, map_smul, hv]
  simp [hlambda]

/-- With at least two buses, the balanced subspace contains a nonzero vector. -/
theorem zeroSumSubspace_nontrivial (hn : 1 < n) : Nontrivial (zeroSumSubspace n) := by
  let i₀ : Fin n := ⟨0, by omega⟩
  let i₁ : Fin n := ⟨1, by omega⟩
  have hi : i₀ ≠ i₁ := by
    intro h
    have := congrArg Fin.val h
    simp only [i₀, i₁] at this
    omega
  let v : EuclideanSpace ℝ (Fin n) :=
    WithLp.toLp 2 fun i ↦ _root_.stdBasis i₀ i - _root_.stdBasis i₁ i
  have hv : v ∈ zeroSumSubspace n := by
    change ∑ i, (_root_.stdBasis i₀ i - _root_.stdBasis i₁ i) = 0
    simp [_root_.stdBasis, Finset.sum_sub_distrib]
  refine ⟨⟨⟨v, hv⟩, 0, ?_⟩⟩
  intro h
  have h₀ := congrArg (fun z : zeroSumSubspace n ↦
    (z : EuclideanSpace ℝ (Fin n)) i₀) h
  simp [v, _root_.stdBasis, hi] at h₀

/-- Inner product with the Laplacian action is the coordinate quadratic form. -/
theorem inner_laplacianOperator_self (G : WeightedGraph n m)
    (x : EuclideanSpace ℝ (Fin n)) :
    inner ℝ (laplacianOperator G x) x =
      ∑ i, (∑ j, G.laplacian (fun _ ↦ 1) i j * x j) * x i := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, laplacianOperator_apply,
    Matrix.mulVec, dotProduct]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

/-- The Euclidean norm squared is the sum of coordinate squares. -/
theorem euclidean_norm_sq (x : EuclideanSpace ℝ (Fin n)) :
    ‖x‖ ^ 2 = ∑ i, x i ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  exact Finset.sum_congr rfl fun i _ ↦ by
    rw [Real.norm_eq_abs, sq_abs]

theorem zeroSum_norm_sq (x : zeroSumSubspace n) :
    ‖x‖ ^ 2 = ∑ i, x.1 i ^ 2 := by
  change ‖(x.1 : EuclideanSpace ℝ (Fin n))‖ ^ 2 = _
  exact euclidean_norm_sq x.1

theorem inner_restrictedLaplacian_self (G : WeightedGraph n m) (x : zeroSumSubspace n) :
    inner ℝ (restrictedLaplacian G x) x =
      ∑ i, (∑ j, G.laplacian (fun _ ↦ 1) i j * x.1 j) * x.1 i := by
  change inner ℝ (laplacianOperator G (x : EuclideanSpace ℝ (Fin n))) x = _
  exact inner_laplacianOperator_self G x

theorem restrictedRayleigh_eq_coordinate (G : WeightedGraph n m) (x : zeroSumSubspace n) :
    inner ℝ (restrictedLaplacian G x) x / ‖x‖ ^ 2 =
      (∑ i, (∑ j, G.laplacian (fun _ ↦ 1) i j * x.1 j) * x.1 i) /
        ∑ i, x.1 i ^ 2 := by
  rw [inner_restrictedLaplacian_self, zeroSum_norm_sq]

/-- The Laplacian inner product is the positive weighted edge energy. -/
theorem inner_laplacianOperator_self_eq_energy (G : WeightedGraph n m)
    (x : EuclideanSpace ℝ (Fin n)) :
    inner ℝ (laplacianOperator G x) x =
      ∑ e, G.weights e * voltageDrop G (fun i ↦ x i) e ^ 2 := by
  rw [inner_laplacianOperator_self]
  calc
    ∑ i, (∑ j, G.laplacian (fun _ ↦ 1) i j * x j) * x i =
        ∑ i, x i * ∑ j, G.laplacian (fun _ ↦ 1) i j * x j := by
      exact Finset.sum_congr rfl fun i _ ↦ by ring
    _ = ∑ e, (1 : ℝ) * G.weights e * voltageDrop G (fun i ↦ x i) e ^ 2 :=
      laplacian_quadratic G (fun _ ↦ 1) (fun i ↦ x i)
    _ = ∑ e, G.weights e * voltageDrop G (fun i ↦ x i) e ^ 2 := by simp

/-- The minimum Rayleigh quotient of the balanced Laplacian restriction. -/
def restrictedEigenvalueMin (G : WeightedGraph n m) : ℝ :=
  ⨅ x : {x : zeroSumSubspace n // x ≠ 0},
    inner ℝ (restrictedLaplacian G x) x / ‖(x : zeroSumSubspace n)‖ ^ 2

/-- The maximum Rayleigh quotient of the balanced Laplacian restriction. -/
def restrictedEigenvalueMax (G : WeightedGraph n m) : ℝ :=
  ⨆ x : {x : zeroSumSubspace n // x ≠ 0},
    inner ℝ (restrictedLaplacian G x) x / ‖(x : zeroSumSubspace n)‖ ^ 2

/-- The maximum Rayleigh quotient of the Laplacian on the full bus space. -/
def fullEigenvalueMax (G : WeightedGraph n m) : ℝ :=
  ⨆ x : {x : EuclideanSpace ℝ (Fin n) // x ≠ 0},
    inner ℝ (laplacianOperator G x) x / ‖(x : EuclideanSpace ℝ (Fin n))‖ ^ 2

theorem restrictedRayleigh_nonneg (G : WeightedGraph n m) (x : zeroSumSubspace n) :
    0 ≤ inner ℝ (restrictedLaplacian G x) x / ‖x‖ ^ 2 := by
  apply div_nonneg
  · change 0 ≤ inner ℝ (laplacianOperator G (x : EuclideanSpace ℝ (Fin n))) x
    rw [inner_laplacianOperator_self_eq_energy]
    exact Finset.sum_nonneg fun e _ ↦
      mul_nonneg (G.weights_pos e).le (sq_nonneg _)
  · exact sq_nonneg _

theorem restrictedRayleigh_bddBelow (G : WeightedGraph n m) :
    BddBelow (Set.range fun x : {x : zeroSumSubspace n // x ≠ 0} ↦
      inner ℝ (restrictedLaplacian G x) x / ‖(x : zeroSumSubspace n)‖ ^ 2) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨x, rfl⟩
  exact restrictedRayleigh_nonneg G x

theorem restrictedRayleigh_bddAbove (G : WeightedGraph n m) :
    BddAbove (Set.range fun x : {x : zeroSumSubspace n // x ≠ 0} ↦
      inner ℝ (restrictedLaplacian G x) x / ‖(x : zeroSumSubspace n)‖ ^ 2) := by
  obtain ⟨C, hC⟩ := lambdaMax_set_nonempty G (fun _ ↦ 1)
  refine ⟨C, ?_⟩
  rintro _ ⟨x, rfl⟩
  have hnorm : 0 < ‖(x : zeroSumSubspace n)‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr x.2)
  rw [div_le_iff₀ hnorm, inner_restrictedLaplacian_self, zeroSum_norm_sq]
  exact hC (fun i ↦ x.1.1 i)

theorem fullRayleigh_bddAbove (G : WeightedGraph n m) :
    BddAbove (Set.range fun x : {x : EuclideanSpace ℝ (Fin n) // x ≠ 0} ↦
      inner ℝ (laplacianOperator G x) x /
        ‖(x : EuclideanSpace ℝ (Fin n))‖ ^ 2) := by
  obtain ⟨C, hC⟩ := lambdaMax_set_nonempty G (fun _ ↦ 1)
  refine ⟨C, ?_⟩
  rintro _ ⟨x, rfl⟩
  have hnorm : 0 < ‖(x : EuclideanSpace ℝ (Fin n))‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr x.2)
  rw [div_le_iff₀ hnorm, inner_laplacianOperator_self, euclidean_norm_sq]
  exact hC x

/-- The minimum balanced Rayleigh quotient is attained by a nonzero eigenvector. -/
theorem exists_restrictedEigenvector_min (G : WeightedGraph n m) (hn : 1 < n) :
    ∃ v : zeroSumSubspace n,
      v ≠ 0 ∧ restrictedLaplacian G v = restrictedEigenvalueMin G • v := by
  letI := zeroSumSubspace_nontrivial hn
  have heig : Module.End.HasEigenvalue (restrictedLaplacian G) (restrictedEigenvalueMin G) := by
    simpa only [restrictedEigenvalueMin, RCLike.re_to_real] using
      (restrictedLaplacian_isSymmetric G).hasEigenvalue_iInf_of_finiteDimensional
  obtain ⟨v, hv⟩ := heig.exists_hasEigenvector
  exact ⟨v, hv.2, hv.apply_eq_smul⟩

/-- The maximum full space Rayleigh quotient is attained by a nonzero eigenvector. -/
theorem exists_fullEigenvector_max (G : WeightedGraph n m) (hn : 0 < n) :
    ∃ v : EuclideanSpace ℝ (Fin n),
      v ≠ 0 ∧ laplacianOperator G v = fullEigenvalueMax G • v := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  have heig : Module.End.HasEigenvalue (laplacianOperator G) (fullEigenvalueMax G) := by
    simpa only [fullEigenvalueMax, RCLike.re_to_real] using
      (laplacianOperator_isSymmetric G).hasEigenvalue_iSup_of_finiteDimensional
  obtain ⟨v, hv⟩ := heig.exists_hasEigenvector
  exact ⟨v, hv.2, hv.apply_eq_smul⟩

/-- The minimum eigenvalue of the balanced restriction is the variational `lambda₂`. -/
theorem restrictedEigenvalueMin_eq_lambda2 (G : WeightedGraph n m) (hn : 1 < n) :
    restrictedEigenvalueMin G = laplacian_eigenvalue₂ G (fun _ ↦ 1) := by
  have hmin_mem : restrictedEigenvalueMin G ∈
      {r : ℝ | ∀ (x : Fin n → ℝ), ∑ i, x i = 0 →
        r * ∑ i, x i ^ 2 ≤
          ∑ i, (∑ j, G.laplacian (fun _ ↦ 1) i j * x j) * x i} := by
    intro x hx
    by_cases hx0 : x = 0
    · subst x
      simp
    · let xE : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 x
      let z : zeroSumSubspace n := ⟨xE, by simpa [xE] using hx⟩
      have hxE : xE ≠ 0 := by
        intro h
        apply hx0
        apply WithLp.toLp_injective 2
        simpa [xE] using h
      have hz : z ≠ 0 := by
        intro h
        exact hxE (congrArg Subtype.val h)
      have hq := ciInf_le (restrictedRayleigh_bddBelow G)
        (⟨z, hz⟩ : {w : zeroSumSubspace n // w ≠ 0})
      change restrictedEigenvalueMin G ≤
        inner ℝ (restrictedLaplacian G z) z / ‖z‖ ^ 2 at hq
      rw [restrictedRayleigh_eq_coordinate] at hq
      have hq' : restrictedEigenvalueMin G ≤
          (∑ i, (∑ j, G.laplacian (fun _ ↦ 1) i j * x j) * x i) /
            ∑ i, x i ^ 2 := by
        simpa [z, xE] using hq
      have hsq_pos : 0 < ∑ i, x i ^ 2 := by
        have : 0 < ‖xE‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hxE)
        simpa [xE, euclidean_norm_sq] using this
      exact (le_div_iff₀ hsq_pos).mp hq'
  have hmin_le : restrictedEigenvalueMin G ≤
      laplacian_eigenvalue₂ G (fun _ ↦ 1) := by
    unfold laplacian_eigenvalue₂
    exact le_csSup (lambda2_set_bddAbove G hn) hmin_mem
  obtain ⟨v, hv0, hv⟩ := exists_restrictedEigenvector_min G hn
  have hvnorm : 0 < ∑ i, v.1 i ^ 2 := by
    rw [← zeroSum_norm_sq]
    exact sq_pos_of_pos (norm_pos_iff.mpr hv0)
  have henergy :
      ∑ i, (∑ j, G.laplacian (fun _ ↦ 1) i j * v.1 j) * v.1 i =
        restrictedEigenvalueMin G * ∑ i, v.1 i ^ 2 := by
    rw [← inner_restrictedLaplacian_self, hv, real_inner_smul_left,
      real_inner_self_eq_norm_sq, zeroSum_norm_sq]
  have hlambda_le : laplacian_eigenvalue₂ G (fun _ ↦ 1) ≤
      restrictedEigenvalueMin G := by
    unfold laplacian_eigenvalue₂
    refine csSup_le (lambda2_set_nonempty G) ?_
    intro r hr
    have hrv := hr (fun i ↦ v.1 i) v.2
    rw [henergy] at hrv
    nlinarith
  exact le_antisymm hmin_le hlambda_le

/-- The maximum full space Rayleigh quotient is the existing variational `lambdaMax`. -/
theorem fullEigenvalueMax_eq_lambdaMax (G : WeightedGraph n m) (hn : 0 < n) :
    fullEigenvalueMax G = laplacianEigenvalueMax G (fun _ ↦ 1) := by
  let upperBounds : Set ℝ := {r : ℝ | ∀ x : Fin n → ℝ,
    ∑ i, (∑ j, G.laplacian (fun _ ↦ 1) i j * x j) * x i ≤
      r * ∑ i, x i ^ 2}
  have hmax_mem : fullEigenvalueMax G ∈ upperBounds := by
    intro x
    by_cases hx0 : x = 0
    · subst x
      simp
    · let xE : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 x
      have hxE : xE ≠ 0 := by
        intro h
        apply hx0
        apply WithLp.toLp_injective 2
        simpa [xE] using h
      have hq := le_ciSup (fullRayleigh_bddAbove G)
        (⟨xE, hxE⟩ : {w : EuclideanSpace ℝ (Fin n) // w ≠ 0})
      change inner ℝ (laplacianOperator G xE) xE / ‖xE‖ ^ 2 ≤
        fullEigenvalueMax G at hq
      rw [inner_laplacianOperator_self, euclidean_norm_sq] at hq
      have hq' :
          (∑ i, (∑ j, G.laplacian (fun _ ↦ 1) i j * x j) * x i) /
              ∑ i, x i ^ 2 ≤ fullEigenvalueMax G := by
        simpa [xE] using hq
      have hsq_pos : 0 < ∑ i, x i ^ 2 := by
        have : 0 < ‖xE‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hxE)
        simpa [xE, euclidean_norm_sq] using this
      exact (div_le_iff₀ hsq_pos).mp hq'
  have hbounds_bddBelow : BddBelow upperBounds := by
    let i₀ : Fin n := ⟨0, hn⟩
    let x₀ : Fin n → ℝ := _root_.stdBasis i₀
    let q := ∑ i, (∑ j, G.laplacian (fun _ ↦ 1) i j * x₀ j) * x₀ i
    refine ⟨q, ?_⟩
    intro r hr
    have h := hr x₀
    have hx₀_sq : ∑ i, x₀ i ^ 2 = 1 := by
      simp [x₀, _root_.stdBasis]
    simpa [q, hx₀_sq] using h
  have hlambda_le : laplacianEigenvalueMax G (fun _ ↦ 1) ≤ fullEigenvalueMax G := by
    unfold laplacianEigenvalueMax
    exact csInf_le hbounds_bddBelow hmax_mem
  obtain ⟨v, hv0, hv⟩ := exists_fullEigenvector_max G hn
  have hvnorm : 0 < ∑ i, v i ^ 2 := by
    rw [← euclidean_norm_sq]
    exact sq_pos_of_pos (norm_pos_iff.mpr hv0)
  have henergy :
      ∑ i, (∑ j, G.laplacian (fun _ ↦ 1) i j * v j) * v i =
        fullEigenvalueMax G * ∑ i, v i ^ 2 := by
    rw [← inner_laplacianOperator_self, hv, real_inner_smul_left,
      real_inner_self_eq_norm_sq, euclidean_norm_sq]
  have hmax_le : fullEigenvalueMax G ≤ laplacianEigenvalueMax G (fun _ ↦ 1) := by
    unfold laplacianEigenvalueMax
    refine le_csInf (lambdaMax_set_nonempty G (fun _ ↦ 1)) ?_
    intro r hr
    have hrv := hr (fun i ↦ v i)
    rw [henergy] at hrv
    nlinarith
  exact le_antisymm hmax_le hlambda_le

/-- A connected graph with at least two buses has a positive largest Laplacian eigenvalue. -/
theorem lambdaMax_pos_of_combinatoriallyConnected (G : WeightedGraph n m)
    (hconn : G.CombinatoriallyConnected) (hn : 1 < n) :
    0 < laplacianEigenvalueMax G (fun _ ↦ 1) := by
  have hm : 0 < m := by
    have hedge := G.card_sub_one_le_edges hconn
    omega
  let e : Fin m := ⟨0, hm⟩
  have hbound := two_mul_weight_le_lambdaMax G e
  nlinarith [G.weights_pos e]

/-- The largest full space mode is balanced because its eigenvalue is positive. -/
theorem fullMaxEigenvector_mem_zeroSum (G : WeightedGraph n m)
    (hconn : G.CombinatoriallyConnected) (hn : 1 < n)
    (v : EuclideanSpace ℝ (Fin n))
    (hv : laplacianOperator G v = laplacianEigenvalueMax G (fun _ ↦ 1) • v) :
    v ∈ zeroSumSubspace n := by
  have hsum := laplacianOperator_mem_zeroSum G v
  change ∑ i, (laplacianOperator G v) i = 0 at hsum
  rw [hv] at hsum
  simp only [PiLp.smul_apply, smul_eq_mul, ← Finset.mul_sum] at hsum
  exact (mul_eq_zero.mp hsum).resolve_left
    (lambdaMax_pos_of_combinatoriallyConnected G hconn hn).ne'

/-- The maximum Rayleigh quotient on the balanced restriction is the existing `lambdaMax`. -/
theorem restrictedEigenvalueMax_eq_lambdaMax (G : WeightedGraph n m)
    (hconn : G.CombinatoriallyConnected) (hn : 1 < n) :
    restrictedEigenvalueMax G = laplacianEigenvalueMax G (fun _ ↦ 1) := by
  letI := zeroSumSubspace_nontrivial hn
  have hex : ∃ x : zeroSumSubspace n, x ≠ 0 := exists_ne 0
  letI : Nonempty {x : zeroSumSubspace n // x ≠ 0} :=
    ⟨⟨Classical.choose hex, Classical.choose_spec hex⟩⟩
  have hrestricted_le_full : restrictedEigenvalueMax G ≤ fullEigenvalueMax G := by
    unfold restrictedEigenvalueMax
    refine ciSup_le fun x ↦ ?_
    have hxE : (x.1 : EuclideanSpace ℝ (Fin n)) ≠ 0 := by
      intro h
      apply x.2
      exact Subtype.ext h
    have hq := le_ciSup (fullRayleigh_bddAbove G)
      (⟨x.1, hxE⟩ : {w : EuclideanSpace ℝ (Fin n) // w ≠ 0})
    change inner ℝ (restrictedLaplacian G x) x / ‖(x : zeroSumSubspace n)‖ ^ 2 ≤
      fullEigenvalueMax G
    simpa only [restrictedLaplacian_coe] using hq
  obtain ⟨v, hv0, hv⟩ := exists_fullEigenvector_max G (by omega)
  have hv' : laplacianOperator G v =
      laplacianEigenvalueMax G (fun _ ↦ 1) • v := by
    rw [← fullEigenvalueMax_eq_lambdaMax G (by omega)]
    exact hv
  let z : zeroSumSubspace n :=
    ⟨v, fullMaxEigenvector_mem_zeroSum G hconn hn v hv'⟩
  have hz0 : z ≠ 0 := by
    intro h
    exact hv0 (congrArg Subtype.val h)
  have hzEig : restrictedLaplacian G z = fullEigenvalueMax G • z := by
    apply Subtype.ext
    exact hv
  have hq := le_ciSup (restrictedRayleigh_bddAbove G)
    (⟨z, hz0⟩ : {w : zeroSumSubspace n // w ≠ 0})
  change inner ℝ (restrictedLaplacian G z) z / ‖z‖ ^ 2 ≤
    restrictedEigenvalueMax G at hq
  have hquotient : inner ℝ (restrictedLaplacian G z) z / ‖z‖ ^ 2 =
      fullEigenvalueMax G := by
    rw [hzEig, real_inner_smul_left, real_inner_self_eq_norm_sq]
    field_simp [norm_ne_zero_iff.mpr hz0]
  rw [hquotient] at hq
  calc
    restrictedEigenvalueMax G = fullEigenvalueMax G :=
      le_antisymm hrestricted_le_full hq
    _ = laplacianEigenvalueMax G (fun _ ↦ 1) :=
      fullEigenvalueMax_eq_lambdaMax G (by omega)

/-- Normalize a nonzero vector in a real normed space. -/
def normalizeVector {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (v : E) : E :=
  ‖v‖⁻¹ • v

theorem normalizeVector_norm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : E) (hv : v ≠ 0) :
    ‖normalizeVector v‖ = 1 := by
  rw [normalizeVector, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_nonneg (norm_nonneg v), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]

theorem map_normalizeVector_eigen {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : E →ₗ[ℝ] E) (v : E) (lambda : ℝ) (hv : T v = lambda • v) :
    T (normalizeVector v) = lambda • normalizeVector v := by
  simp only [normalizeVector, map_smul, hv, smul_smul]
  rw [mul_comm]

/-- Turn a balanced coordinate vector into an element of the zero sum subspace. -/
def asZeroSumVector (p : Fin n → ℝ) (hp : RHSQueryHardness.IsBalanced p) :
    zeroSumSubspace n :=
  ⟨WithLp.toLp 2 p, hp⟩

/-- Orthonormal extreme modes equipped with their exact Laplacian eigen equations. -/
structure ExtremeLaplacianModes (G : WeightedGraph n m) where
  /-- The normalized orthogonal balanced coordinate modes. -/
  pair : RHSQueryHardness.BalancedModePair n
  fastEigen :
    restrictedLaplacian G (asZeroSumVector pair.fast pair.fast_balanced) =
      laplacianEigenvalueMax G (fun _ ↦ 1) •
        asZeroSumVector pair.fast pair.fast_balanced
  slowEigen :
    restrictedLaplacian G (asZeroSumVector pair.slow pair.slow_balanced) =
      laplacian_eigenvalue₂ G (fun _ ↦ 1) •
        asZeroSumVector pair.slow pair.slow_balanced

/-- Connected Laplacians with distinct extreme positive eigenvalues supply the hard mode pair. -/
theorem exists_extremeLaplacianModes (G : WeightedGraph n m)
    (hconn : G.CombinatoriallyConnected) (hn : 1 < n)
    (hextreme : laplacian_eigenvalue₂ G (fun _ ↦ 1) <
      laplacianEigenvalueMax G (fun _ ↦ 1)) :
    Nonempty (ExtremeLaplacianModes G) := by
  obtain ⟨slow₀, hslow₀_ne, hslow₀_eig⟩ := exists_restrictedEigenvector_min G hn
  have hslow₀_eig' : restrictedLaplacian G slow₀ =
      laplacian_eigenvalue₂ G (fun _ ↦ 1) • slow₀ := by
    rw [← restrictedEigenvalueMin_eq_lambda2 G hn]
    exact hslow₀_eig
  obtain ⟨fast₀E, hfast₀_ne, hfast₀_eig⟩ := exists_fullEigenvector_max G (by omega)
  have hfast₀_eig' : laplacianOperator G fast₀E =
      laplacianEigenvalueMax G (fun _ ↦ 1) • fast₀E := by
    rw [← fullEigenvalueMax_eq_lambdaMax G (by omega)]
    exact hfast₀_eig
  have hmax_pos := lambdaMax_pos_of_combinatoriallyConnected G hconn hn
  have hfast₀_sum : ∑ i, fast₀E i = 0 := by
    have hsum := laplacianOperator_mem_zeroSum G fast₀E
    change ∑ i, (laplacianOperator G fast₀E) i = 0 at hsum
    rw [hfast₀_eig'] at hsum
    simp only [PiLp.smul_apply, smul_eq_mul, ← Finset.mul_sum] at hsum
    exact (mul_eq_zero.mp hsum).resolve_left hmax_pos.ne'
  let fast₀ : zeroSumSubspace n := ⟨fast₀E, hfast₀_sum⟩
  have hfast₀_eig'': restrictedLaplacian G fast₀ =
      laplacianEigenvalueMax G (fun _ ↦ 1) • fast₀ := by
    apply Subtype.ext
    exact hfast₀_eig'
  let slow := normalizeVector slow₀
  let fast := normalizeVector fast₀
  have hslow_norm : ‖slow‖ = 1 := normalizeVector_norm slow₀ hslow₀_ne
  have hfast₀_ne : fast₀ ≠ 0 := by
    intro h
    exact hfast₀_ne (congrArg Subtype.val h)
  have hfast_norm : ‖fast‖ = 1 := normalizeVector_norm fast₀ hfast₀_ne
  have hslow_eig : restrictedLaplacian G slow =
      laplacian_eigenvalue₂ G (fun _ ↦ 1) • slow :=
    map_normalizeVector_eigen _ _ _ hslow₀_eig'
  have hfast_eig : restrictedLaplacian G fast =
      laplacianEigenvalueMax G (fun _ ↦ 1) • fast :=
    map_normalizeVector_eigen _ _ _ hfast₀_eig''
  have horthogonal : inner ℝ fast slow = 0 := by
    have hsym := restrictedLaplacian_isSymmetric G fast slow
    rw [hfast_eig, hslow_eig, real_inner_smul_left, real_inner_smul_right] at hsym
    nlinarith
  have hfast_sqNorm : RHSQueryHardness.sqNorm (fun i ↦ fast.1 i) = 1 := by
    have h : ‖fast‖ ^ 2 = 1 := by rw [hfast_norm]; norm_num
    rw [zeroSum_norm_sq] at h
    simpa [RHSQueryHardness.sqNorm, dotProduct, pow_two] using h
  have hslow_sqNorm : RHSQueryHardness.sqNorm (fun i ↦ slow.1 i) = 1 := by
    have h : ‖slow‖ ^ 2 = 1 := by rw [hslow_norm]; norm_num
    rw [zeroSum_norm_sq] at h
    simpa [RHSQueryHardness.sqNorm, dotProduct, pow_two] using h
  have hdot : dotProduct (fun i ↦ fast.1 i) (fun i ↦ slow.1 i) = 0 := by
    have hinnerE : inner ℝ (fast.1 : EuclideanSpace ℝ (Fin n)) slow.1 = 0 := horthogonal
    rw [EuclideanSpace.inner_eq_star_dotProduct] at hinnerE
    rw [dotProduct_comm]
    simpa only [star_trivial] using hinnerE
  let P : RHSQueryHardness.BalancedModePair n :=
    { fast := fun i ↦ fast.1 i
      slow := fun i ↦ slow.1 i
      fast_balanced := fast.2
      slow_balanced := slow.2
      fast_normalized := hfast_sqNorm
      slow_normalized := hslow_sqNorm
      orthogonal := hdot }
  refine ⟨⟨P, ?_, ?_⟩⟩
  · simpa [P, asZeroSumVector] using hfast_eig
  · simpa [P, asZeroSumVector] using hslow_eig

/-- A fixed choice of the extreme Laplacian modes supplied by the spectral theorem. -/
def extremeLaplacianModes (G : WeightedGraph n m)
    (hconn : G.CombinatoriallyConnected) (hn : 1 < n)
    (hextreme : laplacian_eigenvalue₂ G (fun _ ↦ 1) <
      laplacianEigenvalueMax G (fun _ ↦ 1)) :
    ExtremeLaplacianModes G :=
  Classical.choice (exists_extremeLaplacianModes G hconn hn hextreme)

/-- Embed the canonical two-dimensional oracle space into the graph's extreme balanced modes. -/
def graphPairEmbedding {G : WeightedGraph n m} (M : ExtremeLaplacianModes G)
    (z : Fin 2 → ℝ) : Fin n → ℝ :=
  M.pair.embed z

theorem graphPairEmbedding_balanced {G : WeightedGraph n m}
    (M : ExtremeLaplacianModes G) (z : Fin 2 → ℝ) :
    RHSQueryHardness.IsBalanced (graphPairEmbedding M z) :=
  M.pair.embed_balanced z

/-- The graph pair embedding preserves the Euclidean squared norm. -/
theorem graphPairEmbedding_sqNorm {G : WeightedGraph n m}
    (M : ExtremeLaplacianModes G) (z : Fin 2 → ℝ) :
    RHSQueryHardness.sqNorm (graphPairEmbedding M z) =
      RHSQueryHardness.sqNorm z :=
  M.pair.embed_sqNorm z

/-- The graph pair embedding preserves Euclidean squared distances. -/
theorem graphPairEmbedding_sqDistance {G : WeightedGraph n m}
    (M : ExtremeLaplacianModes G) (z w : Fin 2 → ℝ) :
    RHSQueryHardness.sqDistance (graphPairEmbedding M z) (graphPairEmbedding M w) =
      RHSQueryHardness.sqDistance z w :=
  M.pair.embed_sqDistance z w

/-- Recover the two extreme mode coefficients of a bus space vector. -/
def graphPairCoordinates {G : WeightedGraph n m} (M : ExtremeLaplacianModes G)
    (x : Fin n → ℝ) : Fin 2 → ℝ := fun i ↦
  if i = 0 then dotProduct M.pair.fast x else dotProduct M.pair.slow x

theorem fast_dot_graphPairEmbedding {G : WeightedGraph n m}
    (M : ExtremeLaplacianModes G) (z : Fin 2 → ℝ) :
    dotProduct M.pair.fast (graphPairEmbedding M z) = z 0 := by
  have hfast : dotProduct M.pair.fast M.pair.fast = 1 := by
    simpa [RHSQueryHardness.sqNorm] using M.pair.fast_normalized
  simp [graphPairEmbedding, RHSQueryHardness.BalancedModePair.embed,
    dotProduct_add, dotProduct_smul, hfast, M.pair.orthogonal]

theorem slow_dot_graphPairEmbedding {G : WeightedGraph n m}
    (M : ExtremeLaplacianModes G) (z : Fin 2 → ℝ) :
    dotProduct M.pair.slow (graphPairEmbedding M z) = z 1 := by
  have hslow : dotProduct M.pair.slow M.pair.slow = 1 := by
    simpa [RHSQueryHardness.sqNorm] using M.pair.slow_normalized
  simp [graphPairEmbedding, RHSQueryHardness.BalancedModePair.embed,
    dotProduct_add, dotProduct_smul, hslow, M.pair.slow_dot_fast]

/-- Coefficient recovery is a left inverse of the pair embedding. -/
@[simp]
theorem graphPairCoordinates_embedding {G : WeightedGraph n m}
    (M : ExtremeLaplacianModes G) (z : Fin 2 → ℝ) :
    graphPairCoordinates M (graphPairEmbedding M z) = z := by
  funext i
  fin_cases i <;>
    simp [graphPairCoordinates, fast_dot_graphPairEmbedding, slow_dot_graphPairEmbedding]

/-- The canonical plus preparation oracle transported to the graph's extreme mode subspace. -/
def graphPreparationOraclePlus {G : WeightedGraph n m} (M : ExtremeLaplacianModes G)
    (kappa : ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  graphPairEmbedding M
    (RHSQueryHardness.preparationOraclePlus kappa (graphPairCoordinates M x))

/-- The canonical minus preparation oracle transported to the graph's extreme mode subspace. -/
def graphPreparationOracleMinus {G : WeightedGraph n m} (M : ExtremeLaplacianModes G)
    (kappa : ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  graphPairEmbedding M
    (RHSQueryHardness.preparationOracleMinus kappa (graphPairCoordinates M x))

theorem canonicalPreparationOraclePlus_sqNorm (kappa : ℝ) (z : Fin 2 → ℝ) :
    RHSQueryHardness.sqNorm (RHSQueryHardness.preparationOraclePlus kappa z) =
      RHSQueryHardness.sqNorm z := by
  have hpos : 0 < kappa ^ 2 + 1 := by positivity
  have hsqrt : Real.sqrt (kappa ^ 2 + 1) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hpos)
  simp [RHSQueryHardness.sqNorm, dotProduct, RHSQueryHardness.preparationOraclePlus,
    RHSQueryHardness.fin2Zero, RHSQueryHardness.fin2One, Fin.sum_univ_two]
  field_simp [hsqrt]
  nlinarith [Real.sq_sqrt hpos.le]

theorem canonicalPreparationOracleMinus_sqNorm (kappa : ℝ) (z : Fin 2 → ℝ) :
    RHSQueryHardness.sqNorm (RHSQueryHardness.preparationOracleMinus kappa z) =
      RHSQueryHardness.sqNorm z := by
  have hpos : 0 < kappa ^ 2 + 1 := by positivity
  have hsqrt : Real.sqrt (kappa ^ 2 + 1) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hpos)
  simp [RHSQueryHardness.sqNorm, dotProduct, RHSQueryHardness.preparationOracleMinus,
    RHSQueryHardness.fin2Zero, RHSQueryHardness.fin2One, Fin.sum_univ_two]
  field_simp [hsqrt]
  nlinarith [Real.sq_sqrt hpos.le]

theorem canonicalPreparationOraclePlus_sqDistance (kappa : ℝ)
    (z w : Fin 2 → ℝ) :
    RHSQueryHardness.sqDistance (RHSQueryHardness.preparationOraclePlus kappa z)
        (RHSQueryHardness.preparationOraclePlus kappa w) =
      RHSQueryHardness.sqDistance z w := by
  have hsub :
      RHSQueryHardness.preparationOraclePlus kappa z -
          RHSQueryHardness.preparationOraclePlus kappa w =
        RHSQueryHardness.preparationOraclePlus kappa (z - w) := by
    funext i
    fin_cases i <;>
      simp [RHSQueryHardness.preparationOraclePlus, RHSQueryHardness.fin2Zero,
        RHSQueryHardness.fin2One] <;>
      ring
  rw [RHSQueryHardness.sqDistance, hsub, canonicalPreparationOraclePlus_sqNorm,
    RHSQueryHardness.sqDistance]

theorem canonicalPreparationOracleMinus_sqDistance (kappa : ℝ)
    (z w : Fin 2 → ℝ) :
    RHSQueryHardness.sqDistance (RHSQueryHardness.preparationOracleMinus kappa z)
        (RHSQueryHardness.preparationOracleMinus kappa w) =
      RHSQueryHardness.sqDistance z w := by
  have hsub :
      RHSQueryHardness.preparationOracleMinus kappa z -
          RHSQueryHardness.preparationOracleMinus kappa w =
        RHSQueryHardness.preparationOracleMinus kappa (z - w) := by
    funext i
    fin_cases i <;>
      simp [RHSQueryHardness.preparationOracleMinus, RHSQueryHardness.fin2Zero,
        RHSQueryHardness.fin2One] <;>
      ring
  rw [RHSQueryHardness.sqDistance, hsub, canonicalPreparationOracleMinus_sqNorm,
    RHSQueryHardness.sqDistance]

theorem graphPreparationOraclePlus_on_image {G : WeightedGraph n m}
    (M : ExtremeLaplacianModes G) (kappa : ℝ) (z : Fin 2 → ℝ) :
    graphPreparationOraclePlus M kappa (graphPairEmbedding M z) =
      graphPairEmbedding M (RHSQueryHardness.preparationOraclePlus kappa z) := by
  rw [graphPreparationOraclePlus, graphPairCoordinates_embedding]

theorem graphPreparationOracleMinus_on_image {G : WeightedGraph n m}
    (M : ExtremeLaplacianModes G) (kappa : ℝ) (z : Fin 2 → ℝ) :
    graphPreparationOracleMinus M kappa (graphPairEmbedding M z) =
      graphPairEmbedding M (RHSQueryHardness.preparationOracleMinus kappa z) := by
  rw [graphPreparationOracleMinus, graphPairCoordinates_embedding]

/-- The transported plus oracle preserves squared norms on the graph pair image. -/
theorem graphPreparationOraclePlus_sqNorm_on_image {G : WeightedGraph n m}
    (M : ExtremeLaplacianModes G) (kappa : ℝ) (z : Fin 2 → ℝ) :
    RHSQueryHardness.sqNorm
        (graphPreparationOraclePlus M kappa (graphPairEmbedding M z)) =
      RHSQueryHardness.sqNorm (graphPairEmbedding M z) := by
  rw [graphPreparationOraclePlus_on_image, graphPairEmbedding_sqNorm,
    graphPairEmbedding_sqNorm, canonicalPreparationOraclePlus_sqNorm]

/-- The transported minus oracle preserves squared norms on the graph pair image. -/
theorem graphPreparationOracleMinus_sqNorm_on_image {G : WeightedGraph n m}
    (M : ExtremeLaplacianModes G) (kappa : ℝ) (z : Fin 2 → ℝ) :
    RHSQueryHardness.sqNorm
        (graphPreparationOracleMinus M kappa (graphPairEmbedding M z)) =
      RHSQueryHardness.sqNorm (graphPairEmbedding M z) := by
  rw [graphPreparationOracleMinus_on_image, graphPairEmbedding_sqNorm,
    graphPairEmbedding_sqNorm, canonicalPreparationOracleMinus_sqNorm]

/-- The transported plus oracle preserves squared distances on the graph pair image. -/
theorem graphPreparationOraclePlus_sqDistance_on_image {G : WeightedGraph n m}
    (M : ExtremeLaplacianModes G) (kappa : ℝ) (z w : Fin 2 → ℝ) :
    RHSQueryHardness.sqDistance
        (graphPreparationOraclePlus M kappa (graphPairEmbedding M z))
        (graphPreparationOraclePlus M kappa (graphPairEmbedding M w)) =
      RHSQueryHardness.sqDistance (graphPairEmbedding M z) (graphPairEmbedding M w) := by
  rw [graphPreparationOraclePlus_on_image, graphPreparationOraclePlus_on_image,
    graphPairEmbedding_sqDistance, graphPairEmbedding_sqDistance,
    canonicalPreparationOraclePlus_sqDistance]

/-- The transported minus oracle preserves squared distances on the graph pair image. -/
theorem graphPreparationOracleMinus_sqDistance_on_image {G : WeightedGraph n m}
    (M : ExtremeLaplacianModes G) (kappa : ℝ) (z w : Fin 2 → ℝ) :
    RHSQueryHardness.sqDistance
        (graphPreparationOracleMinus M kappa (graphPairEmbedding M z))
        (graphPreparationOracleMinus M kappa (graphPairEmbedding M w)) =
      RHSQueryHardness.sqDistance (graphPairEmbedding M z) (graphPairEmbedding M w) := by
  rw [graphPreparationOracleMinus_on_image, graphPreparationOracleMinus_on_image,
    graphPairEmbedding_sqDistance, graphPairEmbedding_sqDistance,
    canonicalPreparationOracleMinus_sqDistance]

/-- The transported plus oracle prepares the graph's plus hard right hand side. -/
theorem graphPreparationOraclePlus_prepares {G : WeightedGraph n m}
    (M : ExtremeLaplacianModes G) (kappa : ℝ) :
    graphPreparationOraclePlus M kappa
        (graphPairEmbedding M RHSQueryHardness.preparationBasis) =
      RHSQueryHardness.balancedPreparedPlus M.pair kappa := by
  rw [graphPreparationOraclePlus_on_image, RHSQueryHardness.preparationOraclePlus_prepares]
  rfl

/-- The transported minus oracle prepares the graph's minus hard right hand side. -/
theorem graphPreparationOracleMinus_prepares {G : WeightedGraph n m}
    (M : ExtremeLaplacianModes G) (kappa : ℝ) :
    graphPreparationOracleMinus M kappa
        (graphPairEmbedding M RHSQueryHardness.preparationBasis) =
      RHSQueryHardness.balancedPreparedMinus M.pair kappa := by
  rw [graphPreparationOracleMinus_on_image, RHSQueryHardness.preparationOracleMinus_prepares]
  rfl

/-- On the graph pair image, the transported plus oracle is inverse to the minus oracle. -/
theorem graphPreparationOraclePlus_comp_minus_on_image {G : WeightedGraph n m}
    (M : ExtremeLaplacianModes G) (kappa : ℝ) (hkappa : 0 < kappa)
    (z : Fin 2 → ℝ) :
    graphPreparationOraclePlus M kappa
        (graphPreparationOracleMinus M kappa (graphPairEmbedding M z)) =
      graphPairEmbedding M z := by
  rw [graphPreparationOracleMinus_on_image, graphPreparationOraclePlus_on_image,
    RHSQueryHardness.preparationOraclePlus_comp_minus kappa hkappa]

/-- On the graph pair image, the transported minus oracle is inverse to the plus oracle. -/
theorem graphPreparationOracleMinus_comp_plus_on_image {G : WeightedGraph n m}
    (M : ExtremeLaplacianModes G) (kappa : ℝ) (hkappa : 0 < kappa)
    (z : Fin 2 → ℝ) :
    graphPreparationOracleMinus M kappa
        (graphPreparationOraclePlus M kappa (graphPairEmbedding M z)) =
      graphPairEmbedding M z := by
  rw [graphPreparationOraclePlus_on_image, graphPreparationOracleMinus_on_image,
    RHSQueryHardness.preparationOracleMinus_comp_plus kappa hkappa]

/-- The canonical oracle separation is preserved by the graph pair embedding. -/
theorem graphPreparationOracle_gap_sq_on_image {G : WeightedGraph n m}
    (M : ExtremeLaplacianModes G) (kappa : ℝ) (hkappa : 0 < kappa)
    (z : Fin 2 → ℝ) :
    RHSQueryHardness.sqDistance
        (graphPreparationOraclePlus M kappa (graphPairEmbedding M z))
        (graphPreparationOracleMinus M kappa (graphPairEmbedding M z)) =
      (4 / (kappa ^ 2 + 1)) * RHSQueryHardness.sqNorm z := by
  rw [graphPreparationOraclePlus_on_image, graphPreparationOracleMinus_on_image,
    graphPairEmbedding_sqDistance, RHSQueryHardness.preparationOracle_gap_sq kappa hkappa]

/-- Scale the exact balanced inverse so its gain on the fast mode is one. -/
def conditionScaledSolve (G : WeightedGraph n m)
    (hconn : G.CombinatoriallyConnected) (hn : 1 < n) :
    zeroSumSubspace n →ₗ[ℝ] zeroSumSubspace n :=
  laplacianEigenvalueMax G (fun _ ↦ 1) • balancedSolve G hconn (by omega)

theorem conditionScaledSolve_fast (G : WeightedGraph n m)
    (hconn : G.CombinatoriallyConnected) (hn : 1 < n)
    (M : ExtremeLaplacianModes G) :
    conditionScaledSolve G hconn hn
        (asZeroSumVector M.pair.fast M.pair.fast_balanced) =
      asZeroSumVector M.pair.fast M.pair.fast_balanced := by
  let fast := asZeroSumVector M.pair.fast M.pair.fast_balanced
  have hmax_pos := lambdaMax_pos_of_combinatoriallyConnected G hconn hn
  have hinv := balancedSolve_eigenvector G hconn (by omega) fast
    (laplacianEigenvalueMax G (fun _ ↦ 1)) hmax_pos.ne' M.fastEigen
  change laplacianEigenvalueMax G (fun _ ↦ 1) •
      balancedSolve G hconn (by omega) fast = fast
  rw [hinv, smul_smul]
  simp [hmax_pos.ne']

theorem conditionScaledSolve_slow (G : WeightedGraph n m)
    (hconn : G.CombinatoriallyConnected) (hn : 1 < n)
    (M : ExtremeLaplacianModes G) :
    conditionScaledSolve G hconn hn
        (asZeroSumVector M.pair.slow M.pair.slow_balanced) =
      effectiveConditionNumber G (fun _ ↦ 1) •
        asZeroSumVector M.pair.slow M.pair.slow_balanced := by
  let slow := asZeroSumVector M.pair.slow M.pair.slow_balanced
  have htwo_pos : 0 < laplacian_eigenvalue₂ G (fun _ ↦ 1) :=
    combinatoriallyConnected_implies_spectralConnected G hconn hn
  have hinv := balancedSolve_eigenvector G hconn (by omega) slow
    (laplacian_eigenvalue₂ G (fun _ ↦ 1)) htwo_pos.ne' M.slowEigen
  change laplacianEigenvalueMax G (fun _ ↦ 1) •
      balancedSolve G hconn (by omega) slow = _
  rw [hinv, smul_smul]
  unfold effectiveConditionNumber
  congr 1

/-- Embed two hard mode coefficients into the exact balanced bus subspace. -/
def embedZeroSum (P : RHSQueryHardness.BalancedModePair n) (z : Fin 2 → ℝ) :
    zeroSumSubspace n :=
  asZeroSumVector (P.embed z) (P.embed_balanced z)

theorem embedZeroSum_eq (P : RHSQueryHardness.BalancedModePair n) (z : Fin 2 → ℝ) :
    embedZeroSum P z =
      z 0 • asZeroSumVector P.fast P.fast_balanced +
        z 1 • asZeroSumVector P.slow P.slow_balanced := by
  apply Subtype.ext
  apply WithLp.ofLp_injective 2
  ext i
  simp [embedZeroSum, asZeroSumVector, RHSQueryHardness.BalancedModePair.embed]

/-- Exact balanced right hand side for the plus hard instance. -/
def preparedPlusVector (P : RHSQueryHardness.BalancedModePair n) (kappa : ℝ) :
    zeroSumSubspace n :=
  embedZeroSum P (RHSQueryHardness.preparedPlus kappa)

/-- Exact balanced right hand side for the minus hard instance. -/
def preparedMinusVector (P : RHSQueryHardness.BalancedModePair n) (kappa : ℝ) :
    zeroSumSubspace n :=
  embedZeroSum P (RHSQueryHardness.preparedMinus kappa)

/-- Exact normalized plus solution in the two extreme modes. -/
def solutionPlusVector (P : RHSQueryHardness.BalancedModePair n) : zeroSumSubspace n :=
  embedZeroSum P RHSQueryHardness.solutionPlus

/-- Exact normalized minus solution in the two extreme modes. -/
def solutionMinusVector (P : RHSQueryHardness.BalancedModePair n) : zeroSumSubspace n :=
  embedZeroSum P RHSQueryHardness.solutionMinus

theorem conditionScaledSolve_preparedPlus (G : WeightedGraph n m)
    (hconn : G.CombinatoriallyConnected) (hn : 1 < n)
    (M : ExtremeLaplacianModes G) :
    conditionScaledSolve G hconn hn
        (preparedPlusVector M.pair (effectiveConditionNumber G (fun _ ↦ 1))) =
      (effectiveConditionNumber G (fun _ ↦ 1) * Real.sqrt 2 /
          Real.sqrt (effectiveConditionNumber G (fun _ ↦ 1) ^ 2 + 1)) •
        solutionPlusVector M.pair := by
  have hsqrt2 : Real.sqrt 2 ≠ 0 := by positivity
  simp only [preparedPlusVector, solutionPlusVector, embedZeroSum_eq,
    LinearMap.map_add, LinearMap.map_smul, conditionScaledSolve_fast G hconn hn M,
    conditionScaledSolve_slow G hconn hn M]
  apply Subtype.ext
  apply WithLp.ofLp_injective 2
  ext i
  simp [RHSQueryHardness.preparedPlus, RHSQueryHardness.solutionPlus]
  field_simp [hsqrt2]

theorem conditionScaledSolve_preparedMinus (G : WeightedGraph n m)
    (hconn : G.CombinatoriallyConnected) (hn : 1 < n)
    (M : ExtremeLaplacianModes G) :
    conditionScaledSolve G hconn hn
        (preparedMinusVector M.pair (effectiveConditionNumber G (fun _ ↦ 1))) =
      (effectiveConditionNumber G (fun _ ↦ 1) * Real.sqrt 2 /
          Real.sqrt (effectiveConditionNumber G (fun _ ↦ 1) ^ 2 + 1)) •
        solutionMinusVector M.pair := by
  have hsqrt2 : Real.sqrt 2 ≠ 0 := by positivity
  simp only [preparedMinusVector, solutionMinusVector, embedZeroSum_eq,
    LinearMap.map_add, LinearMap.map_smul, conditionScaledSolve_fast G hconn hn M,
    conditionScaledSolve_slow G hconn hn M]
  apply Subtype.ext
  apply WithLp.ofLp_injective 2
  ext i
  simp [RHSQueryHardness.preparedMinus, RHSQueryHardness.solutionMinus]
  field_simp [hsqrt2]

/-- The effective condition number used by the graph derived hard pair. -/
def graphKappa (G : WeightedGraph n m) : ℝ :=
  effectiveConditionNumber G (fun _ ↦ 1)

/-- Equal positive extrema are exactly the degenerate condition number one branch. -/
theorem graphKappa_eq_one_of_extrema_eq (G : WeightedGraph n m)
    (hlambdaTwo : 0 < laplacian_eigenvalue₂ G (fun _ ↦ 1))
    (heq : laplacianEigenvalueMax G (fun _ ↦ 1) =
      laplacian_eigenvalue₂ G (fun _ ↦ 1)) :
    graphKappa G = 1 := by
  unfold graphKappa effectiveConditionNumber
  rw [heq, div_self hlambdaTwo.ne']

/-- For a connected graph with at least two vertices, the minimum balanced eigenvalue cannot
exceed the maximum balanced eigenvalue. -/
theorem lambda2_le_lambdaMax_of_combinatoriallyConnected (G : WeightedGraph n m)
    (hconn : G.CombinatoriallyConnected) (hn : 1 < n) :
    laplacian_eigenvalue₂ G (fun _ ↦ 1) ≤
      laplacianEigenvalueMax G (fun _ ↦ 1) := by
  letI := zeroSumSubspace_nontrivial hn
  have hex : ∃ x : zeroSumSubspace n, x ≠ 0 := exists_ne 0
  letI : Nonempty {x : zeroSumSubspace n // x ≠ 0} :=
    ⟨⟨Classical.choose hex, Classical.choose_spec hex⟩⟩
  calc
    laplacian_eigenvalue₂ G (fun _ ↦ 1) = restrictedEigenvalueMin G :=
      (restrictedEigenvalueMin_eq_lambda2 G hn).symm
    _ ≤ restrictedEigenvalueMax G :=
      ciInf_le_ciSup (restrictedRayleigh_bddBelow G) (restrictedRayleigh_bddAbove G)
    _ = laplacianEigenvalueMax G (fun _ ↦ 1) :=
      restrictedEigenvalueMax_eq_lambdaMax G hconn hn

/-- For a connected graph with at least two vertices, condition number one is equivalent to
coincident positive extreme eigenvalues. -/
theorem graphKappa_eq_one_iff_extrema_eq (G : WeightedGraph n m)
    (hconn : G.CombinatoriallyConnected) (hn : 1 < n) :
    graphKappa G = 1 ↔
      laplacianEigenvalueMax G (fun _ ↦ 1) =
        laplacian_eigenvalue₂ G (fun _ ↦ 1) := by
  have hlambdaTwo : 0 < laplacian_eigenvalue₂ G (fun _ ↦ 1) :=
    combinatoriallyConnected_implies_spectralConnected G hconn hn
  unfold graphKappa effectiveConditionNumber
  exact div_eq_one_iff_eq hlambdaTwo.ne'

/-- Every connected graph with at least two vertices lies in exactly the degenerate branch or
the distinct-extrema branch. -/
theorem graphKappa_degenerate_or_distinct (G : WeightedGraph n m)
    (hconn : G.CombinatoriallyConnected) (hn : 1 < n) :
    (graphKappa G = 1 ∧
        laplacianEigenvalueMax G (fun _ ↦ 1) =
          laplacian_eigenvalue₂ G (fun _ ↦ 1)) ∨
      (1 < graphKappa G ∧
        laplacian_eigenvalue₂ G (fun _ ↦ 1) <
          laplacianEigenvalueMax G (fun _ ↦ 1)) := by
  have hlambdaTwo : 0 < laplacian_eigenvalue₂ G (fun _ ↦ 1) :=
    combinatoriallyConnected_implies_spectralConnected G hconn hn
  rcases eq_or_lt_of_le (lambda2_le_lambdaMax_of_combinatoriallyConnected G hconn hn) with
    heq | hlt
  · left
    have heq' : laplacianEigenvalueMax G (fun _ ↦ 1) =
        laplacian_eigenvalue₂ G (fun _ ↦ 1) := heq.symm
    exact ⟨(graphKappa_eq_one_iff_extrema_eq G hconn hn).2 heq', heq'⟩
  · right
    refine ⟨?_, hlt⟩
    unfold graphKappa effectiveConditionNumber
    exact (one_lt_div hlambdaTwo).2 hlt

/-- A condition number lower bound strictly above one forces distinct extreme eigenvalues. -/
theorem strict_extrema_of_scaled_graphKappa_lowerBound (G : WeightedGraph n m)
    (hconn : G.CombinatoriallyConnected) (hn : 1 < n) (c : ℝ)
    (hone : 1 < c * (n : ℝ)) (hbound : c * (n : ℝ) ≤ graphKappa G) :
    laplacian_eigenvalue₂ G (fun _ ↦ 1) <
      laplacianEigenvalueMax G (fun _ ↦ 1) := by
  have hlambdaTwo : 0 < laplacian_eigenvalue₂ G (fun _ ↦ 1) :=
    combinatoriallyConnected_implies_spectralConnected G hconn hn
  have hkappa : 1 < graphKappa G := hone.trans_le hbound
  unfold graphKappa effectiveConditionNumber at hkappa
  have := (lt_div_iff₀ hlambdaTwo).mp hkappa
  simpa using this

/-- All algebraic facts needed to instantiate the two input right hand side hard family. -/
structure GraphHardPairCertificate (G : WeightedGraph n m)
    (hconn : G.CombinatoriallyConnected) (hn : 1 < n) where
  /-- The graph's normalized extreme balanced modes. -/
  modes : ExtremeLaplacianModes G
  kappa_pos : 0 < graphKappa G
  preparedPlus_normalized :
    RHSQueryHardness.sqNorm
      (RHSQueryHardness.balancedPreparedPlus modes.pair (graphKappa G)) = 1
  preparedMinus_normalized :
    RHSQueryHardness.sqNorm
      (RHSQueryHardness.balancedPreparedMinus modes.pair (graphKappa G)) = 1
  prepared_gap :
    RHSQueryHardness.sqDistance
        (RHSQueryHardness.balancedPreparedPlus modes.pair (graphKappa G))
        (RHSQueryHardness.balancedPreparedMinus modes.pair (graphKappa G)) =
      4 / (graphKappa G ^ 2 + 1)
  solutionPlus_normalized :
    RHSQueryHardness.sqNorm (RHSQueryHardness.balancedSolutionPlus modes.pair) = 1
  solutionMinus_normalized :
    RHSQueryHardness.sqNorm (RHSQueryHardness.balancedSolutionMinus modes.pair) = 1
  solution_gap :
    RHSQueryHardness.sqDistance
        (RHSQueryHardness.balancedSolutionPlus modes.pair)
        (RHSQueryHardness.balancedSolutionMinus modes.pair) = 2
  fastSolve :
    conditionScaledSolve G hconn hn
        (asZeroSumVector modes.pair.fast modes.pair.fast_balanced) =
      asZeroSumVector modes.pair.fast modes.pair.fast_balanced
  slowSolve :
    conditionScaledSolve G hconn hn
        (asZeroSumVector modes.pair.slow modes.pair.slow_balanced) =
      graphKappa G • asZeroSumVector modes.pair.slow modes.pair.slow_balanced
  solvePlus :
    conditionScaledSolve G hconn hn
        (preparedPlusVector modes.pair (graphKappa G)) =
      (graphKappa G * Real.sqrt 2 / Real.sqrt (graphKappa G ^ 2 + 1)) •
        solutionPlusVector modes.pair
  solveMinus :
    conditionScaledSolve G hconn hn
        (preparedMinusVector modes.pair (graphKappa G)) =
      (graphKappa G * Real.sqrt 2 / Real.sqrt (graphKappa G ^ 2 + 1)) •
        solutionMinusVector modes.pair

/-- An actual connected weighted graph with distinct extrema constructs the complete hard pair. -/
theorem graph_to_balancedHardPair (G : WeightedGraph n m)
    (hconn : G.CombinatoriallyConnected) (hn : 1 < n)
    (hextreme : laplacian_eigenvalue₂ G (fun _ ↦ 1) <
      laplacianEigenvalueMax G (fun _ ↦ 1)) :
    Nonempty (GraphHardPairCertificate G hconn hn) := by
  let M := extremeLaplacianModes G hconn hn hextreme
  have htwo_pos : 0 < laplacian_eigenvalue₂ G (fun _ ↦ 1) :=
    combinatoriallyConnected_implies_spectralConnected G hconn hn
  have hmax_pos := lambdaMax_pos_of_combinatoriallyConnected G hconn hn
  have hkappa : 0 < graphKappa G := by
    exact div_pos hmax_pos htwo_pos
  refine ⟨
    { modes := M
      kappa_pos := hkappa
      preparedPlus_normalized :=
        RHSQueryHardness.balancedPreparedPlus_normalized M.pair (graphKappa G)
      preparedMinus_normalized :=
        RHSQueryHardness.balancedPreparedMinus_normalized M.pair (graphKappa G)
      prepared_gap :=
        RHSQueryHardness.balancedPrepared_sqDistance M.pair (graphKappa G) hkappa
      solutionPlus_normalized :=
        RHSQueryHardness.balancedSolutionPlus_normalized M.pair
      solutionMinus_normalized :=
        RHSQueryHardness.balancedSolutionMinus_normalized M.pair
      solution_gap := RHSQueryHardness.balancedSolution_sqDistance M.pair
      fastSolve := conditionScaledSolve_fast G hconn hn M
      slowSolve := conditionScaledSolve_slow G hconn hn M
      solvePlus := conditionScaledSolve_preparedPlus G hconn hn M
      solveMinus := conditionScaledSolve_preparedMinus G hconn hn M }
  ⟩

/-- Coordinate form of the graph derived extreme balanced eigenmodes. -/
theorem exists_balancedModePair_coordinate (G : WeightedGraph n m)
    (hconn : G.CombinatoriallyConnected) (hn : 1 < n)
    (hextreme : laplacian_eigenvalue₂ G (fun _ ↦ 1) <
      laplacianEigenvalueMax G (fun _ ↦ 1)) :
    ∃ P : RHSQueryHardness.BalancedModePair n,
      (∀ i, ∑ j, G.laplacian (fun _ ↦ 1) i j * P.fast j =
        laplacianEigenvalueMax G (fun _ ↦ 1) * P.fast i) ∧
      (∀ i, ∑ j, G.laplacian (fun _ ↦ 1) i j * P.slow j =
        laplacian_eigenvalue₂ G (fun _ ↦ 1) * P.slow i) := by
  let M := extremeLaplacianModes G hconn hn hextreme
  refine ⟨M.pair, ?_, ?_⟩
  · intro i
    have h := congrArg (fun z : zeroSumSubspace n ↦
      (z : EuclideanSpace ℝ (Fin n))) M.fastEigen
    have h' := congrArg WithLp.ofLp h
    have hi := congrFun h' i
    simpa only [restrictedLaplacian_coe, laplacianOperator_apply, asZeroSumVector,
      WithLp.ofLp_toLp, PiLp.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct] using hi
  · intro i
    have h := congrArg (fun z : zeroSumSubspace n ↦
      (z : EuclideanSpace ℝ (Fin n))) M.slowEigen
    have h' := congrArg WithLp.ofLp h
    have hi := congrFun h' i
    simpa only [restrictedLaplacian_coe, laplacianOperator_apply, asZeroSumVector,
      WithLp.ofLp_toLp, PiLp.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct] using hi

/-- The condition scaled inverse on the span of an orthonormal hard mode pair. -/
def twoModeCoordinateSolve (P : RHSQueryHardness.BalancedModePair n) (kappa : ℝ) :
    (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) where
  toFun x :=
    dotProduct P.fast x • P.fast +
      (kappa * dotProduct P.slow x) • P.slow
  map_add' := by
    intro x y
    ext i
    simp only [dotProduct_add, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  map_smul' := by
    intro c x
    ext i
    simp only [RingHom.id_apply, dotProduct_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring

@[simp]
theorem twoModeCoordinateSolve_fast (P : RHSQueryHardness.BalancedModePair n) (kappa : ℝ) :
    twoModeCoordinateSolve P kappa P.fast = P.fast := by
  have hff : dotProduct P.fast P.fast = 1 := P.fast_normalized
  have hsf : dotProduct P.slow P.fast = 0 := P.slow_dot_fast
  ext i
  simp [twoModeCoordinateSolve, hff, hsf]

@[simp]
theorem twoModeCoordinateSolve_slow (P : RHSQueryHardness.BalancedModePair n) (kappa : ℝ) :
    twoModeCoordinateSolve P kappa P.slow = kappa • P.slow := by
  have hss : dotProduct P.slow P.slow = 1 := P.slow_normalized
  have hfs : dotProduct P.fast P.slow = 0 := P.orthogonal
  ext i
  simp [twoModeCoordinateSolve, hss, hfs]

theorem laplacian_embed_apply (G : WeightedGraph n m)
    (P : RHSQueryHardness.BalancedModePair n) (lambdaFast lambdaSlow : ℝ)
    (hfast : ∀ i, ∑ j, G.laplacian (fun _ ↦ 1) i j * P.fast j =
      lambdaFast * P.fast i)
    (hslow : ∀ i, ∑ j, G.laplacian (fun _ ↦ 1) i j * P.slow j =
      lambdaSlow * P.slow i)
    (z : Fin 2 → ℝ) (i : Fin n) :
    ∑ j, G.laplacian (fun _ ↦ 1) i j * P.embed z j =
      z 0 * lambdaFast * P.fast i + z 1 * lambdaSlow * P.slow i := by
  simp only [RHSQueryHardness.BalancedModePair.embed, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, mul_add, Finset.sum_add_distrib]
  rw [show ∑ j, G.laplacian (fun _ ↦ 1) i j * (z 0 * P.fast j) =
      z 0 * ∑ j, G.laplacian (fun _ ↦ 1) i j * P.fast j by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by ring]
  rw [show ∑ j, G.laplacian (fun _ ↦ 1) i j * (z 1 * P.slow j) =
      z 1 * ∑ j, G.laplacian (fun _ ↦ 1) i j * P.slow j by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by ring]
  rw [hfast i, hslow i]
  ring

/-- Coordinate Laplacian identities for both graph derived hard inputs and solutions. -/
theorem exists_balancedModePair_coordinate_inverse (G : WeightedGraph n m)
    (hconn : G.CombinatoriallyConnected) (hn : 1 < n)
    (hextreme : laplacian_eigenvalue₂ G (fun _ ↦ 1) <
      laplacianEigenvalueMax G (fun _ ↦ 1)) :
    ∃ P : RHSQueryHardness.BalancedModePair n,
      (∀ i, ∑ j, G.laplacian (fun _ ↦ 1) i j * P.fast j =
        laplacianEigenvalueMax G (fun _ ↦ 1) * P.fast i) ∧
      (∀ i, ∑ j, G.laplacian (fun _ ↦ 1) i j * P.slow j =
        laplacian_eigenvalue₂ G (fun _ ↦ 1) * P.slow i) ∧
      (∀ i, ∑ j, G.laplacian (fun _ ↦ 1) i j *
          ((effectiveConditionNumber G (fun _ ↦ 1) * Real.sqrt 2 /
            Real.sqrt (effectiveConditionNumber G (fun _ ↦ 1) ^ 2 + 1)) *
              RHSQueryHardness.balancedSolutionPlus P j) =
        laplacianEigenvalueMax G (fun _ ↦ 1) *
          RHSQueryHardness.balancedPreparedPlus P
            (effectiveConditionNumber G (fun _ ↦ 1)) i) ∧
      (∀ i, ∑ j, G.laplacian (fun _ ↦ 1) i j *
          ((effectiveConditionNumber G (fun _ ↦ 1) * Real.sqrt 2 /
            Real.sqrt (effectiveConditionNumber G (fun _ ↦ 1) ^ 2 + 1)) *
              RHSQueryHardness.balancedSolutionMinus P j) =
        laplacianEigenvalueMax G (fun _ ↦ 1) *
          RHSQueryHardness.balancedPreparedMinus P
            (effectiveConditionNumber G (fun _ ↦ 1)) i) := by
  obtain ⟨P, hfast, hslow⟩ := exists_balancedModePair_coordinate G hconn hn hextreme
  refine ⟨P, hfast, hslow, ?_, ?_⟩
  all_goals
    intro i
    let lambdaTwo := laplacian_eigenvalue₂ G (fun _ ↦ 1)
    let lambdaMax := laplacianEigenvalueMax G (fun _ ↦ 1)
    let kappa := effectiveConditionNumber G (fun _ ↦ 1)
    let c := kappa * Real.sqrt 2 / Real.sqrt (kappa ^ 2 + 1)
    have htwo_pos : 0 < lambdaTwo :=
      combinatoriallyConnected_implies_spectralConnected G hconn hn
    have hkappa : kappa = lambdaMax / lambdaTwo := rfl
    have hkappa_pos : 0 < kappa := by
      rw [hkappa]
      exact div_pos (lambdaMax_pos_of_combinatoriallyConnected G hconn hn) htwo_pos
    have hkappa_mul : kappa * lambdaTwo = lambdaMax := by
      rw [hkappa]
      field_simp
    have hsqrt2 : Real.sqrt 2 ≠ 0 := by positivity
    have hsqrtK : Real.sqrt (kappa ^ 2 + 1) ≠ 0 := by positivity
    change ∑ j, G.laplacian (fun _ ↦ 1) i j *
        (c * RHSQueryHardness.BalancedModePair.embed P _ j) =
      lambdaMax * RHSQueryHardness.BalancedModePair.embed P _ i
    rw [show ∑ j, G.laplacian (fun _ ↦ 1) i j *
        (c * RHSQueryHardness.BalancedModePair.embed P _ j) =
        c * ∑ j, G.laplacian (fun _ ↦ 1) i j *
          RHSQueryHardness.BalancedModePair.embed P _ j by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ ↦ by ring]
    rw [laplacian_embed_apply G P lambdaMax lambdaTwo hfast hslow]
    simp only [RHSQueryHardness.BalancedModePair.embed, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul]
    simp only [RHSQueryHardness.solutionPlus, RHSQueryHardness.solutionMinus, Fin.isValue,
      ↓reduceIte, one_div, one_ne_zero, RHSQueryHardness.preparedPlus,
      RHSQueryHardness.preparedMinus, c]
    rw [show effectiveConditionNumber G (fun _ ↦ 1) = kappa by rfl]
    field_simp [hsqrt2, hsqrtK, htwo_pos.ne']
    rw [← hkappa_mul]
    ring

/-- The full graph Laplacian, rather than the rank-two coordinate solve, maps each scaled
normalized hard solution back to `lambdaMax` times its prepared right hand side. -/
theorem exists_balancedModePair_laplacian_inverse (G : WeightedGraph n m)
    (hconn : G.CombinatoriallyConnected) (hn : 1 < n)
    (hextreme : laplacian_eigenvalue₂ G (fun _ ↦ 1) <
      laplacianEigenvalueMax G (fun _ ↦ 1)) :
    ∃ P : RHSQueryHardness.BalancedModePair n,
      (∀ i, ∑ j, G.laplacian (fun _ ↦ 1) i j * P.fast j =
        laplacianEigenvalueMax G (fun _ ↦ 1) * P.fast i) ∧
      (∀ i, ∑ j, G.laplacian (fun _ ↦ 1) i j * P.slow j =
        laplacian_eigenvalue₂ G (fun _ ↦ 1) * P.slow i) ∧
      G.laplacian (fun _ ↦ 1) *ᵥ
          ((effectiveConditionNumber G (fun _ ↦ 1) * Real.sqrt 2 /
              Real.sqrt (effectiveConditionNumber G (fun _ ↦ 1) ^ 2 + 1)) •
            RHSQueryHardness.balancedSolutionPlus P) =
        laplacianEigenvalueMax G (fun _ ↦ 1) •
          RHSQueryHardness.balancedPreparedPlus P
            (effectiveConditionNumber G (fun _ ↦ 1)) ∧
      G.laplacian (fun _ ↦ 1) *ᵥ
          ((effectiveConditionNumber G (fun _ ↦ 1) * Real.sqrt 2 /
              Real.sqrt (effectiveConditionNumber G (fun _ ↦ 1) ^ 2 + 1)) •
            RHSQueryHardness.balancedSolutionMinus P) =
        laplacianEigenvalueMax G (fun _ ↦ 1) •
          RHSQueryHardness.balancedPreparedMinus P
            (effectiveConditionNumber G (fun _ ↦ 1)) := by
  obtain ⟨P, hfast, hslow, hplus, hminus⟩ :=
    exists_balancedModePair_coordinate_inverse G hconn hn hextreme
  refine ⟨P, hfast, hslow, ?_, ?_⟩
  · funext i
    simpa only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] using hplus i
  · funext i
    simpa only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] using hminus i

/-- Coordinate only closure of the graph to hard pair construction and its exact solve action. -/
theorem exists_balancedModePair_with_solve (G : WeightedGraph n m)
    (hconn : G.CombinatoriallyConnected) (hn : 1 < n)
    (hextreme : laplacian_eigenvalue₂ G (fun _ ↦ 1) <
      laplacianEigenvalueMax G (fun _ ↦ 1)) :
    ∃ (P : RHSQueryHardness.BalancedModePair n)
      (solve : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)),
      (∀ i, ∑ j, G.laplacian (fun _ ↦ 1) i j * P.fast j =
        laplacianEigenvalueMax G (fun _ ↦ 1) * P.fast i) ∧
      (∀ i, ∑ j, G.laplacian (fun _ ↦ 1) i j * P.slow j =
        laplacian_eigenvalue₂ G (fun _ ↦ 1) * P.slow i) ∧
      0 < effectiveConditionNumber G (fun _ ↦ 1) ∧
      RHSQueryHardness.sqNorm
          (RHSQueryHardness.balancedPreparedPlus P
            (effectiveConditionNumber G (fun _ ↦ 1))) = 1 ∧
      RHSQueryHardness.sqNorm
          (RHSQueryHardness.balancedPreparedMinus P
            (effectiveConditionNumber G (fun _ ↦ 1))) = 1 ∧
      RHSQueryHardness.sqDistance
          (RHSQueryHardness.balancedPreparedPlus P
            (effectiveConditionNumber G (fun _ ↦ 1)))
          (RHSQueryHardness.balancedPreparedMinus P
            (effectiveConditionNumber G (fun _ ↦ 1))) =
        4 / (effectiveConditionNumber G (fun _ ↦ 1) ^ 2 + 1) ∧
      RHSQueryHardness.sqNorm (RHSQueryHardness.balancedSolutionPlus P) = 1 ∧
      RHSQueryHardness.sqNorm (RHSQueryHardness.balancedSolutionMinus P) = 1 ∧
      RHSQueryHardness.sqDistance
          (RHSQueryHardness.balancedSolutionPlus P)
          (RHSQueryHardness.balancedSolutionMinus P) = 2 ∧
      solve P.fast = P.fast ∧
      solve P.slow = effectiveConditionNumber G (fun _ ↦ 1) • P.slow ∧
      solve (RHSQueryHardness.balancedPreparedPlus P
          (effectiveConditionNumber G (fun _ ↦ 1))) =
        (effectiveConditionNumber G (fun _ ↦ 1) * Real.sqrt 2 /
            Real.sqrt (effectiveConditionNumber G (fun _ ↦ 1) ^ 2 + 1)) •
          RHSQueryHardness.balancedSolutionPlus P ∧
      solve (RHSQueryHardness.balancedPreparedMinus P
          (effectiveConditionNumber G (fun _ ↦ 1))) =
        (effectiveConditionNumber G (fun _ ↦ 1) * Real.sqrt 2 /
            Real.sqrt (effectiveConditionNumber G (fun _ ↦ 1) ^ 2 + 1)) •
          RHSQueryHardness.balancedSolutionMinus P := by
  obtain ⟨P, hfast, hslow⟩ := exists_balancedModePair_coordinate G hconn hn hextreme
  let kappa := effectiveConditionNumber G (fun _ ↦ 1)
  let solve := twoModeCoordinateSolve P kappa
  have htwo_pos : 0 < laplacian_eigenvalue₂ G (fun _ ↦ 1) :=
    combinatoriallyConnected_implies_spectralConnected G hconn hn
  have hmax_pos := lambdaMax_pos_of_combinatoriallyConnected G hconn hn
  have hkappa : 0 < kappa := div_pos hmax_pos htwo_pos
  have hsolve_fast : solve P.fast = P.fast := twoModeCoordinateSolve_fast P kappa
  have hsolve_slow : solve P.slow = kappa • P.slow :=
    twoModeCoordinateSolve_slow P kappa
  have hsolve_plus := RHSQueryHardness.solve_balancedPreparedPlus P kappa solve
    hsolve_fast hsolve_slow
  have hsolve_minus := RHSQueryHardness.solve_balancedPreparedMinus P kappa solve
    hsolve_fast hsolve_slow
  refine ⟨P, solve, hfast, hslow, hkappa, ?_, ?_, ?_, ?_, ?_, ?_, hsolve_fast,
    hsolve_slow, hsolve_plus, hsolve_minus⟩
  · exact RHSQueryHardness.balancedPreparedPlus_normalized P kappa
  · exact RHSQueryHardness.balancedPreparedMinus_normalized P kappa
  · exact RHSQueryHardness.balancedPrepared_sqDistance P kappa hkappa
  · exact RHSQueryHardness.balancedSolutionPlus_normalized P
  · exact RHSQueryHardness.balancedSolutionMinus_normalized P
  · exact RHSQueryHardness.balancedSolution_sqDistance P

end SpectralHardPair
