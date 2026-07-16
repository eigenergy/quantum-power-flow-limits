import Mathlib.Tactic
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Probability.Moments.SubGaussian

/-!
# Trusted statements for Comparator

This file intentionally imports only Mathlib. It repeats the project-specific
definitions needed to state the manuscript's claims, then gives those claims
with `sorry`. A reader can audit this file and use `comparator.json` to check
that `PowerFlowLimits` proves these exact statements with only the permitted
axioms.

Keep the definitions and theorem statements here synchronized with the
corresponding declarations in `PowerFlowLimits`.
-/

open Finset BigOperators
open scoped Matrix

noncomputable section

variable {n m : ℕ}

/-- A weighted graph with `n` nodes and `m` edges. -/
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

end WeightedGraph

def WeightedGraph.totalWeight (G : WeightedGraph n m) : ℝ :=
  ∑ e, G.weights e

def WeightedGraph.cutWeight (G : WeightedGraph n m) (S : Finset (Fin n)) : ℝ :=
  ∑ e, G.weights e *
    ((if G.posEndpoint e ∈ S then (1 : ℝ) else 0) -
     (if G.negEndpoint e ∈ S then (1 : ℝ) else 0)) ^ 2

def WeightedGraph.incidentEdges (G : WeightedGraph n m) (i : Fin n) : Finset (Fin m) :=
  Finset.univ.filter fun e => i = G.posEndpoint e ∨ i = G.negEndpoint e

def WeightedGraph.laplacian (G : WeightedGraph n m) (s : Fin m → ℝ)
    (i j : Fin n) : ℝ :=
  ∑ e, G.incidence i e * (G.weights e * s e) * G.incidence j e

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

def WeightedGraph.withWeights (G : WeightedGraph n m) (w : Fin m → ℝ)
    (hw : ∀ e, 0 < w e) : WeightedGraph n m :=
  { G with weights := w, weights_pos := hw }

/-- Lemma 1(i), trace form. -/
theorem two_totalWeight_div_le_lambdaMax (G : WeightedGraph n m) (hn : 1 < n) :
    2 * G.totalWeight / ((n : ℝ) - 1) ≤ laplacianEigenvalueMax G (fun _ => 1) := by
  sorry

/-- Lemma 1(i), edge form. -/
theorem two_mul_weight_le_lambdaMax (G : WeightedGraph n m) (e : Fin m) :
    2 * G.weights e ≤ laplacianEigenvalueMax G (fun _ => 1) := by
  sorry

/-- Lemma 1(ii), quotient form. -/
theorem lambda2_le_cut_div (G : WeightedGraph n m) (S : Finset (Fin n))
    (hne : S.Nonempty) (hproper : S ≠ Finset.univ) :
    laplacian_eigenvalue₂ G (fun _ => 1) ≤
      G.cutWeight S /
        (((S.card : ℝ) / n) * (1 - (S.card : ℝ) / n) * n) := by
  sorry

/-- Lemma 1(ii), denominator-free form. -/
theorem lambda2_mul_le_cut (G : WeightedGraph n m) (S : Finset (Fin n))
    (hne : S.Nonempty) (hproper : S ≠ Finset.univ) :
    laplacian_eigenvalue₂ G (fun _ => 1) * ((S.card : ℝ) * ((n : ℝ) - S.card)) ≤
      (n : ℝ) * G.cutWeight S := by
  sorry

/-- Lemma 1, equation (2), total-weight form. -/
theorem kappaPlus_ge_totalWeight (G : WeightedGraph n m) (S : Finset (Fin n))
    (hne : S.Nonempty) (hproper : S ≠ Finset.univ)
    (hconn : G.Connected (fun _ => 1)) :
    2 * ((S.card : ℝ) / n) * (1 - (S.card : ℝ) / n) * G.totalWeight /
        G.cutWeight S ≤
      effectiveConditionNumber G (fun _ => 1) := by
  sorry

/-- Lemma 1, equation (2), per-edge form. -/
theorem kappaPlus_ge_edge (G : WeightedGraph n m) (S : Finset (Fin n))
    (hne : S.Nonempty) (hproper : S ≠ Finset.univ)
    (hconn : G.Connected (fun _ => 1)) (e : Fin m) :
    2 * ((S.card : ℝ) / n) * (1 - (S.card : ℝ) / n) * ((n : ℝ) * G.weights e) /
        G.cutWeight S ≤
      effectiveConditionNumber G (fun _ => 1) := by
  sorry

/-- Theorem 1. -/
theorem separator_kappa_bound (G : WeightedGraph n m)
    (A X Bv : Finset (Fin n)) (s Δ bmax β : ℝ)
    (hcover : A ∪ X ∪ Bv = Finset.univ)
    (hdisj : Disjoint (A ∪ X) Bv)
    (hnoAB : ∀ e, ¬(G.posEndpoint e ∈ A ∧ G.negEndpoint e ∈ Bv) ∧
      ¬(G.posEndpoint e ∈ Bv ∧ G.negEndpoint e ∈ A))
    (hX : (X.card : ℝ) ≤ s)
    (hdeg : ∀ i, ((G.incidentEdges i).card : ℝ) ≤ Δ)
    (hbmax : ∀ e, G.weights e ≤ bmax)
    (hβ : 0 < β) (hβ' : β ≤ 1 / 2)
    (hA_size : β * n ≤ ((A ∪ X).card : ℝ)) (hB_size : β * n ≤ (Bv.card : ℝ))
    (hconn : G.Connected (fun _ => 1)) :
    2 * β * (1 - β) * G.totalWeight / (s * Δ * bmax) ≤
      effectiveConditionNumber G (fun _ => 1) := by
  sorry

/-- Corollary 1(i). -/
theorem treewidth_kappa_bound (G : WeightedGraph n m)
    (A X Bv : Finset (Fin n)) (τ Δ bmax : ℝ)
    (hcover : A ∪ X ∪ Bv = Finset.univ)
    (hdisj : Disjoint (A ∪ X) Bv)
    (hnoAB : ∀ e, ¬(G.posEndpoint e ∈ A ∧ G.negEndpoint e ∈ Bv) ∧
      ¬(G.posEndpoint e ∈ Bv ∧ G.negEndpoint e ∈ A))
    (hX : (X.card : ℝ) ≤ τ + 1)
    (hdeg : ∀ i, ((G.incidentEdges i).card : ℝ) ≤ Δ)
    (hbmax : ∀ e, G.weights e ≤ bmax)
    (hA_size : (n : ℝ) / 4 ≤ ((A ∪ X).card : ℝ))
    (hB_size : (n : ℝ) / 4 ≤ (Bv.card : ℝ))
    (hconn : G.Connected (fun _ => 1)) :
    3 / 8 * G.totalWeight / ((τ + 1) * Δ * bmax) ≤
      effectiveConditionNumber G (fun _ => 1) := by
  sorry

/-- Corollary 1(ii). -/
theorem planar_kappa_bound (G : WeightedGraph n m)
    (A X Bv : Finset (Fin n)) (Δ bmax : ℝ)
    (hcover : A ∪ X ∪ Bv = Finset.univ)
    (hdisj : Disjoint (A ∪ X) Bv)
    (hnoAB : ∀ e, ¬(G.posEndpoint e ∈ A ∧ G.negEndpoint e ∈ Bv) ∧
      ¬(G.posEndpoint e ∈ Bv ∧ G.negEndpoint e ∈ A))
    (hX : (X.card : ℝ) ≤ Real.sqrt (8 * n))
    (hdeg : ∀ i, ((G.incidentEdges i).card : ℝ) ≤ Δ)
    (hbmax : ∀ e, G.weights e ≤ bmax)
    (hA_size : (n : ℝ) / 6 ≤ ((A ∪ X).card : ℝ))
    (hB_size : (n : ℝ) / 6 ≤ (Bv.card : ℝ))
    (hconn : G.Connected (fun _ => 1)) :
    5 / 18 * G.totalWeight / (Real.sqrt (8 * n) * Δ * bmax) ≤
      effectiveConditionNumber G (fun _ => 1) := by
  sorry

/-- Near-planar extension of Corollary 1(ii). -/
theorem near_planar_kappa_bound (G : WeightedGraph n m)
    (A X Bv : Finset (Fin n)) (Δ bmax c : ℝ) (_hc : 0 ≤ c)
    (hcover : A ∪ X ∪ Bv = Finset.univ)
    (hdisj : Disjoint (A ∪ X) Bv)
    (hnoAB : ∀ e, ¬(G.posEndpoint e ∈ A ∧ G.negEndpoint e ∈ Bv) ∧
      ¬(G.posEndpoint e ∈ Bv ∧ G.negEndpoint e ∈ A))
    (hX : (X.card : ℝ) ≤ 2 * Real.sqrt (8 * ((n : ℝ) + c)))
    (hdeg : ∀ i, ((G.incidentEdges i).card : ℝ) ≤ Δ)
    (hbmax : ∀ e, G.weights e ≤ bmax)
    (hA_size : (n : ℝ) / 6 ≤ ((A ∪ X).card : ℝ))
    (hB_size : (n : ℝ) / 6 ≤ (Bv.card : ℝ))
    (hconn : G.Connected (fun _ => 1)) :
    5 / 36 * G.totalWeight / (Real.sqrt (8 * ((n : ℝ) + c)) * Δ * bmax) ≤
      effectiveConditionNumber G (fun _ => 1) := by
  sorry

/-- Proposition 1. -/
theorem corridor_kappa_bound (G : WeightedGraph n m)
    (VS VT : Finset (Fin n)) (ℓ : ℕ) (hl : 2 ≤ ℓ)
    (p : Fin ℓ → Fin n) (EP : Finset (Fin m)) (β : ℝ)
    (hp_inj : Function.Injective p)
    (hdisjS : ∀ i, p i ∉ VS) (hdisjT : ∀ i, p i ∉ VT)
    (hST : Disjoint VS VT)
    (hpath : ∀ e ∈ EP, ∃ i : Fin ℓ, ∃ h : i.val + 1 < ℓ,
      (G.posEndpoint e = p i ∧ G.negEndpoint e = p ⟨i.val + 1, h⟩) ∨
      (G.posEndpoint e = p ⟨i.val + 1, h⟩ ∧ G.negEndpoint e = p i))
    (hnonpath : ∀ e ∉ EP,
      ((G.posEndpoint e ∈ VS ∨ G.posEndpoint e = p ⟨0, by omega⟩) ∧
       (G.negEndpoint e ∈ VS ∨ G.negEndpoint e = p ⟨0, by omega⟩)) ∨
      ((G.posEndpoint e ∈ VT ∨ G.posEndpoint e = p ⟨ℓ - 1, by omega⟩) ∧
       (G.negEndpoint e ∈ VT ∨ G.negEndpoint e = p ⟨ℓ - 1, by omega⟩)))
    (hβ : 0 < β)
    (hVS_size : β * n ≤ (VS.card : ℝ)) (hVT_size : β * n ≤ (VT.card : ℝ))
    (hconn : G.Connected (fun _ => 1)) :
    2 * β ^ 2 * ((ℓ : ℝ) - 1) ^ 2 * G.totalWeight / (∑ e ∈ EP, G.weights e) ≤
      effectiveConditionNumber G (fun _ => 1) := by
  sorry

/-- Proposition 2. -/
theorem random_kappa_bound {Ωs : Type*} [MeasurableSpace Ωs]
    (μ : MeasureTheory.Measure Ωs) [MeasureTheory.IsProbabilityMeasure μ]
    (G : WeightedGraph n m) (hm : 0 < m)
    (w : Fin m → Ωs → ℝ)
    (hw_meas : ∀ e, Measurable (w e))
    (hw_indep : ProbabilityTheory.iIndepFun w μ)
    (bmax : ℝ) (hw_mem : ∀ ω, ∀ e, w e ω ∈ Set.Ioc 0 bmax)
    (A X Bv : Finset (Fin n)) (s Δ β ε : ℝ)
    (hcover : A ∪ X ∪ Bv = Finset.univ)
    (hdisj : Disjoint (A ∪ X) Bv)
    (hnoAB : ∀ e, ¬(G.posEndpoint e ∈ A ∧ G.negEndpoint e ∈ Bv) ∧
      ¬(G.posEndpoint e ∈ Bv ∧ G.negEndpoint e ∈ A))
    (hX : (X.card : ℝ) ≤ s)
    (hdeg : ∀ i, ((G.incidentEdges i).card : ℝ) ≤ Δ)
    (hβ : 0 < β) (hβ' : β ≤ 1 / 2)
    (hA_size : β * n ≤ ((A ∪ X).card : ℝ)) (hB_size : β * n ≤ (Bv.card : ℝ))
    (hden : 0 < s * Δ * bmax)
    (hε : 0 < ε) (_hε' : ε < 1)
    (hconn : ∀ ω, (G.withWeights (fun e => w e ω)
      (fun e => (hw_mem ω e).1)).Connected (fun _ => 1)) :
    1 - Real.exp (-2 * ε ^ 2 * (∑ e, ∫ ω, w e ω ∂μ) ^ 2 / (m * bmax ^ 2)) ≤
      μ.real {ω | 2 * β * (1 - β) * ((1 - ε) * (∑ e, ∫ ω', w e ω' ∂μ)) /
        (s * Δ * bmax) ≤
        effectiveConditionNumber
          (G.withWeights (fun e => w e ω) (fun e => (hw_mem ω e).1))
          (fun _ => 1)} := by
  sorry

/-- Proposition 3(i), abstract form. -/
theorem e2e_query_lower_bound (nn q ε κ preps costPerPrep total c₁ c₂ c₃ : ℝ)
    (hn : 0 < nn) (hq : 0 < q) (hε : 0 < ε)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃)
    (hκ : c₃ * q ≤ κ)
    (hpreps : c₂ * (nn / ε) ≤ preps)
    (hcost : c₁ * κ ≤ costPerPrep)
    (htotal : preps * costPerPrep ≤ total) :
    c₁ * c₂ * c₃ * (nn * q) / ε ≤ total := by
  sorry

/-- Proposition 3(i), grid specialization. -/
theorem e2e_query_lower_bound_grid (nn ε κ preps costPerPrep total c₁ c₂ c₃ : ℝ)
    (hn : 0 < nn) (hε : 0 < ε)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃)
    (hκ : c₃ * nn ≤ κ)
    (hpreps : c₂ * (nn / ε) ≤ preps)
    (hcost : c₁ * κ ≤ costPerPrep)
    (htotal : preps * costPerPrep ≤ total) :
    c₁ * c₂ * c₃ * nn ^ 2 / ε ≤ total := by
  sorry

/-- Proposition 3(i), corridor specialization. -/
theorem e2e_query_lower_bound_corridor
    (nn ε κ preps costPerPrep total c₁ c₂ c₃ : ℝ)
    (hn : 0 < nn) (hε : 0 < ε)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃)
    (hκ : c₃ * nn ^ 2 ≤ κ)
    (hpreps : c₂ * (nn / ε) ≤ preps)
    (hcost : c₁ * κ ≤ costPerPrep)
    (htotal : preps * costPerPrep ≤ total) :
    c₁ * c₂ * c₃ * nn ^ 3 / ε ≤ total := by
  sorry

/-- Proposition 3(ii). -/
theorem e2e_observable_lower_bound (nn κ cost c₁ c₃ : ℝ)
    (hc₁ : 0 < c₁) (hκ : c₃ * nn ≤ κ) (hcost : c₁ * κ ≤ cost) :
    c₁ * (c₃ * nn) ≤ cost := by
  sorry

end
