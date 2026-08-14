/-
Copyright (c) 2026 Cameron Khanpour and Samuel Talkington. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Cameron Khanpour, Samuel Talkington
-/
import PowerFlowLimits.QueryHardness

/-!
# Proposition 3 (prop:e2e): end-to-end query lower bounds, chaining the cited facts (F1), (F2)

Part of the Lean 4 formalization of
"The Limits of Quantum Computers for Power Flow" (Khanpour and Talkington).
-/

open Finset BigOperators

noncomputable section

variable {n m : ℕ}

/-- Proposition 3 (prop:e2e), part (i), as a cost composition lemma. Its explicit
    hypotheses give a tomography preparation lower bound, a per-preparation QLS cost,
    and a structural condition-number bound. The recovered worst case theorem below,
    `clean_qls_worst_case_product`, derives the shared per-preparation cost from the
    balanced hard pair before choosing the tomography hard input. -/
theorem e2e_query_lower_bound (nn q ε κ preps costPerPrep total c₁ c₂ c₃ : ℝ)
    (hn : 0 < nn) (hq : 0 < q) (hε : 0 < ε)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃)
    (hκ : c₃ * q ≤ κ)
    (hpreps : c₂ * (nn / ε) ≤ preps)
    (hcost : c₁ * κ ≤ costPerPrep)
    (htotal : preps * costPerPrep ≤ total) :
    c₁ * c₂ * c₃ * (nn * q) / ε ≤ total := by
  have hp_pos : (0 : ℝ) < c₂ * (nn / ε) := by positivity
  have hpreps_nn : 0 ≤ preps := le_trans hp_pos.le hpreps
  calc c₁ * c₂ * c₃ * (nn * q) / ε
      = (c₂ * (nn / ε)) * (c₁ * (c₃ * q)) := by field_simp
    _ ≤ preps * (c₁ * (c₃ * q)) :=
        mul_le_mul_of_nonneg_right hpreps (by positivity)
    _ ≤ preps * (c₁ * κ) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hκ hc₁.le) hpreps_nn
    _ ≤ preps * costPerPrep := mul_le_mul_of_nonneg_left hcost hpreps_nn
    _ ≤ total := htotal

/-- Proposition 3 (prop:e2e), part (i) on grid families: κ ≥ c₃·n gives
    query cost ≥ c₁c₂c₃·n²/ε. -/
theorem e2e_query_lower_bound_grid (nn ε κ preps costPerPrep total c₁ c₂ c₃ : ℝ)
    (hn : 0 < nn) (hε : 0 < ε)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃)
    (hκ : c₃ * nn ≤ κ)
    (hpreps : c₂ * (nn / ε) ≤ preps)
    (hcost : c₁ * κ ≤ costPerPrep)
    (htotal : preps * costPerPrep ≤ total) :
    c₁ * c₂ * c₃ * nn ^ 2 / ε ≤ total := by
  calc c₁ * c₂ * c₃ * nn ^ 2 / ε = c₁ * c₂ * c₃ * (nn * nn) / ε := by ring
    _ ≤ total := e2e_query_lower_bound nn nn ε κ preps costPerPrep total c₁ c₂ c₃
      hn hn hε hc₁ hc₂ hc₃ hκ hpreps hcost htotal

/-- Proposition 3 (prop:e2e), part (i) on corridor families: κ ≥ c₃·n² gives
    query cost ≥ c₁c₂c₃·n³/ε. -/
theorem e2e_query_lower_bound_corridor
    (nn ε κ preps costPerPrep total c₁ c₂ c₃ : ℝ)
    (hn : 0 < nn) (hε : 0 < ε)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃)
    (hκ : c₃ * nn ^ 2 ≤ κ)
    (hpreps : c₂ * (nn / ε) ≤ preps)
    (hcost : c₁ * κ ≤ costPerPrep)
    (htotal : preps * costPerPrep ≤ total) :
    c₁ * c₂ * c₃ * nn ^ 3 / ε ≤ total := by
  calc c₁ * c₂ * c₃ * nn ^ 3 / ε = c₁ * c₂ * c₃ * (nn * nn ^ 2) / ε := by ring
    _ ≤ total := e2e_query_lower_bound nn (nn ^ 2) ε κ preps costPerPrep total
      c₁ c₂ c₃ hn (by positivity) hε hc₁ hc₂ hc₃ hκ hpreps hcost htotal

/-- Proposition 3 (prop:e2e), part (ii): estimating even one observable pays
    the full solve cost, ≥ c₁·κ ≥ c₁c₃·n queries — already the price of the
    classical solution. -/
theorem e2e_observable_lower_bound (nn κ cost c₁ c₃ : ℝ)
    (hc₁ : 0 < c₁) (hκ : c₃ * nn ≤ κ) (hcost : c₁ * κ ≤ cost) :
    c₁ * (c₃ * nn) ≤ cost :=
  le_trans (mul_le_mul_of_nonneg_left hκ hc₁.le) hcost

/-- Joint hard-family form of Proposition 3.  A code of dimension proportional to `nn` is
embedded in slow balanced Laplacian modes.  The right hand side oracle exposes that code with
phase `phase`; `horacle` is the fractional-phase direct-sum lower bound, and `hattenuation`
records suppression by the fast/slow inverse gain ratio `gain`.  Unlike a multiplication of two
independent worst-case statements, all premises concern the same coded family. -/
theorem joint_hard_family_readout_lower_bound
    (nn ε κ gain code phase queries cD cQ cE cG : ℝ)
    (hn : 0 < nn) (hε : 0 < ε) (hgain : 0 < gain)
    (hcD : 0 < cD) (hcQ : 0 < cQ) (hcE : 0 < cE) (hcG : 0 < cG)
    (hqueries : 0 ≤ queries)
    (hcode : cD * nn ≤ code)
    (horacle : cQ * code ≤ queries * phase)
    (hattenuation : phase ≤ cE * ε / gain)
    (hcondition : κ ≤ cG * gain) :
    cQ * cD * (nn * κ) / (cE * cG * ε) ≤ queries := by
  have hcode' : cQ * (cD * nn) ≤ cQ * code :=
    mul_le_mul_of_nonneg_left hcode hcQ.le
  have hphase' : queries * phase ≤ queries * (cE * ε / gain) :=
    mul_le_mul_of_nonneg_left hattenuation hqueries
  have hbase : cQ * cD * nn ≤ queries * (cE * ε / gain) := by
    calc
      cQ * cD * nn = cQ * (cD * nn) := by ring
      _ ≤ cQ * code := hcode'
      _ ≤ queries * phase := horacle
      _ ≤ queries * (cE * ε / gain) := hphase'
  have hbase_gain : cQ * cD * nn * gain ≤ queries * (cE * ε) := by
    have h := mul_le_mul_of_nonneg_right hbase hgain.le
    calc
      cQ * cD * nn * gain ≤ queries * (cE * ε / gain) * gain := h
      _ = queries * (cE * ε) := by field_simp
  have hcondition' : cQ * cD * nn * κ ≤ (cQ * cD * nn * gain) * cG := by
    have hleft : 0 ≤ cQ * cD * nn := by positivity
    have h := mul_le_mul_of_nonneg_left hcondition hleft
    nlinarith
  have hproduct : cQ * cD * (nn * κ) ≤ (cE * cG * ε) * queries := by
    calc
      cQ * cD * (nn * κ) = cQ * cD * nn * κ := by ring
      _ ≤ (cQ * cD * nn * gain) * cG := hcondition'
      _ ≤ (queries * (cE * ε)) * cG :=
        mul_le_mul_of_nonneg_right hbase_gain hcG.le
      _ = (cE * cG * ε) * queries := by ring
  apply (div_le_iff₀ (by positivity : 0 < cE * cG * ε)).2
  simpa [mul_comm, mul_left_comm, mul_assoc] using hproduct

/-- If the same joint family has `κ = Ω(nn)`, its full readout query lower bound is
`Ω(nn²/ε)`. -/
theorem joint_hard_family_grid_lower_bound
    (nn ε κ gain code phase queries cD cQ cE cG cK : ℝ)
    (hn : 0 < nn) (hε : 0 < ε) (hgain : 0 < gain)
    (hcD : 0 < cD) (hcQ : 0 < cQ) (hcE : 0 < cE) (hcG : 0 < cG)
    (hqueries : 0 ≤ queries)
    (hcode : cD * nn ≤ code)
    (horacle : cQ * code ≤ queries * phase)
    (hattenuation : phase ≤ cE * ε / gain)
    (hcondition : κ ≤ cG * gain)
    (hkappaLinear : cK * nn ≤ κ) :
    cQ * cD * cK * nn ^ 2 / (cE * cG * ε) ≤ queries := by
  have h := joint_hard_family_readout_lower_bound nn ε κ gain code phase queries
    cD cQ cE cG hn hε hgain hcD hcQ hcE hcG hqueries hcode horacle
    hattenuation hcondition
  apply le_trans ?_ h
  have hnum : cQ * cD * cK * nn ^ 2 ≤ cQ * cD * (nn * κ) := by
    have hnonneg : 0 ≤ cQ * cD * nn := by positivity
    have hmul := mul_le_mul_of_nonneg_left hkappaLinear hnonneg
    nlinarith
  exact div_le_div_of_nonneg_right hnum (by positivity)

/-- If the same joint family has `κ = Ω(nn²)`, its full readout query lower bound is
`Ω(nn³/ε)`. -/
theorem joint_hard_family_corridor_lower_bound
    (nn ε κ gain code phase queries cD cQ cE cG cK : ℝ)
    (hn : 0 < nn) (hε : 0 < ε) (hgain : 0 < gain)
    (hcD : 0 < cD) (hcQ : 0 < cQ) (hcE : 0 < cE) (hcG : 0 < cG)
    (hqueries : 0 ≤ queries)
    (hcode : cD * nn ≤ code)
    (horacle : cQ * code ≤ queries * phase)
    (hattenuation : phase ≤ cE * ε / gain)
    (hcondition : κ ≤ cG * gain)
    (hkappaQuadratic : cK * nn ^ 2 ≤ κ) :
    cQ * cD * cK * nn ^ 3 / (cE * cG * ε) ≤ queries := by
  have h := joint_hard_family_readout_lower_bound nn ε κ gain code phase queries
    cD cQ cE cG hn hε hgain hcD hcQ hcE hcG hqueries hcode horacle
    hattenuation hcondition
  apply le_trans ?_ h
  have hnum : cQ * cD * cK * nn ^ 3 ≤ cQ * cD * (nn * κ) := by
    have hnonneg : 0 ≤ cQ * cD * nn := by positivity
    have hmul := mul_le_mul_of_nonneg_left hkappaQuadratic hnonneg
    nlinarith
  exact div_le_div_of_nonneg_right hnum (by positivity)

/-- A joint `Ω(nn·κ/ε)` query lower bound exceeds a nearly linear classical upper bound once
the condition number is above the displayed constant and logarithmic threshold. -/
theorem joint_product_exceeds_classical
    (nn ε κ queries classicalTime lowerConstant C logFactor : ℝ)
    (hn : 0 < nn) (hε : 0 < ε)
    (hquantum : lowerConstant * (nn * κ) / ε ≤ queries)
    (hclassical : classicalTime ≤ C * nn * logFactor)
    (hthreshold : C * logFactor * ε < lowerConstant * κ) :
    classicalTime < queries := by
  have hlinear : C * nn * logFactor < lowerConstant * (nn * κ) / ε := by
    apply (lt_div_iff₀ hε).2
    have h := mul_lt_mul_of_pos_left hthreshold hn
    nlinarith
  exact lt_of_le_of_lt hclassical (lt_of_lt_of_le hlinear hquantum)

/-- Separate full readout and two-state right hand side bounds. This diagnostic theorem does not
use the coded joint family above. -/
theorem qls_state_readout_lower_bound
    (nn ε κ fullReadout rhsReadout total cT cR : ℝ)
    (hfull : cT * (nn / ε) ≤ fullReadout)
    (hrhs : cR * κ ≤ rhsReadout)
    (hfullTotal : fullReadout ≤ total)
    (hrhsTotal : rhsReadout ≤ total) :
    max (cT * (nn / ε)) (cR * κ) ≤ total :=
  max_le (le_trans hfull hfullTotal) (le_trans hrhs hrhsTotal)

/-- Separate-bound diagnostic on sparse separator grid families. -/
theorem qls_state_readout_grid_lower_bound
    (nn ε κ fullReadout rhsReadout total cT cR cK : ℝ)
    (hcR : 0 ≤ cR)
    (hκ : cK * nn ≤ κ)
    (hfull : cT * (nn / ε) ≤ fullReadout)
    (hrhs : cR * κ ≤ rhsReadout)
    (hfullTotal : fullReadout ≤ total)
    (hrhsTotal : rhsReadout ≤ total) :
    max (cT * (nn / ε)) (cR * (cK * nn)) ≤ total :=
  max_le (le_trans hfull hfullTotal)
    (le_trans (mul_le_mul_of_nonneg_left hκ hcR) (le_trans hrhs hrhsTotal))

/-- Separate-bound diagnostic on macroscopic corridor families. -/
theorem qls_state_readout_corridor_lower_bound
    (nn ε κ fullReadout rhsReadout total cT cR cK : ℝ)
    (hcR : 0 ≤ cR)
    (hκ : cK * nn ^ 2 ≤ κ)
    (hfull : cT * (nn / ε) ≤ fullReadout)
    (hrhs : cR * κ ≤ rhsReadout)
    (hfullTotal : fullReadout ≤ total)
    (hrhsTotal : rhsReadout ≤ total) :
    max (cT * (nn / ε)) (cR * (cK * nn ^ 2)) ≤ total :=
  max_le (le_trans hfull hfullTotal)
    (le_trans (mul_le_mul_of_nonneg_left hκ hcR) (le_trans hrhs hrhsTotal))

/-- On a corridor family, a quadratic right hand side oracle lower bound exceeds a linear
explicit-input classical upper bound once the displayed constant/polylog threshold holds. -/
theorem corridor_rhs_oracle_exceeds_classical
    (nn κ rhsReadout total classicalTime cR cK C logFactor : ℝ)
    (hn : 0 < nn)
    (hcR : 0 < cR)
    (hκ : cK * nn ^ 2 ≤ κ)
    (hrhs : cR * κ ≤ rhsReadout)
    (hrhsTotal : rhsReadout ≤ total)
    (hclassical : classicalTime ≤ C * nn * logFactor)
    (hthreshold : C * logFactor < cR * cK * nn) :
    classicalTime < total := by
  have hquadratic : cR * (cK * nn ^ 2) ≤ total :=
    le_trans (mul_le_mul_of_nonneg_left hκ hcR.le) (le_trans hrhs hrhsTotal)
  have hlinear : C * nn * logFactor < cR * (cK * nn ^ 2) := by
    calc
      C * nn * logFactor = nn * (C * logFactor) := by ring
      _ < nn * (cR * cK * nn) := mul_lt_mul_of_pos_left hthreshold hn
      _ = cR * (cK * nn ^ 2) := by ring
  exact lt_of_le_of_lt hclassical (lt_of_lt_of_le hlinear hquadratic)

/-- Direct worst case recovery of Proposition 3 on corridor families.  The balanced hard pair
supplies constant output separation and per-query progress at most `hybridConstant / κ`; the
corridor condition supplies `κ = Ω(nn²)`.  The resulting right hand side query lower bound
strictly exceeds the nearly linear classical upper bound after the displayed threshold. -/
theorem worst_case_corridor_qls_exceeds_classical
    (q : ℕ)
    (nn κ distance gap hybridConstant cK classicalTime classicalConstant logFactor : ℝ)
    (hn : 0 < nn) (hκpos : 0 < κ) (hgap : 0 < gap) (hhybrid : 0 < hybridConstant)
    (hκ : cK * nn ^ 2 ≤ κ)
    (hseparate : gap ≤ distance)
    (hprogress : κ * distance ≤ hybridConstant * q)
    (hclassical : classicalTime ≤ classicalConstant * nn * logFactor)
    (hthreshold : classicalConstant * logFactor <
      (gap / hybridConstant) * cK * nn) :
    classicalTime < q := by
  have hq : gap * κ / hybridConstant ≤ (q : ℝ) :=
    RHSQueryHardness.rhs_query_lower_bound q distance gap hybridConstant κ
      hκpos hhybrid hseparate hprogress
  have hq' : (gap / hybridConstant) * κ ≤ (q : ℝ) := by
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hq
  exact corridor_rhs_oracle_exceeds_classical nn κ q q classicalTime
    (gap / hybridConstant) cK classicalConstant logFactor hn (by positivity) hκ hq'
    le_rfl hclassical hthreshold

/-- On the invertible balanced subspace, every nonzero target direction is the normalized
solution direction of a normalized right hand side.  Instantiate `B` with the positive weighted
Laplacian restricted to `span(1)^perp`.  This is the reachability step that transfers a real pure
state tomography hard target to a lossless DCPF injection. -/
theorem normalized_rhs_reaches_every_target
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (B : V ≃ₗ[ℝ] V) (theta : V) (htheta : theta ≠ 0) :
    ∃ (p : V) (c : ℝ), ‖p‖ = 1 ∧ 0 < c ∧ B.symm p = c • theta := by
  have hBtheta : B theta ≠ 0 := by
    intro hzero
    apply htheta
    apply B.injective
    simpa using hzero
  have hnorm : ‖B theta‖ ≠ 0 := norm_ne_zero_iff.mpr hBtheta
  have hc : 0 < ‖B theta‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr hBtheta)
  refine ⟨‖B theta‖⁻¹ • B theta, ‖B theta‖⁻¹, ?_, hc, ?_⟩
  · simp [norm_smul, hnorm]
  · simp

/-- Worst case product lower bound with the input quantifier made explicit.

For an input `p`, let `U_p` prepare its right hand side and let `W_p` prepare its normalized
solution. `qSolve` counts the `U_p` and `U_p†` calls in one fixed coherent implementation of
`W_p` or `W_p†`. `calls p` counts tomography's calls to `W_p` and `W_p†`. `total p` counts the
resulting internal `U_p` and `U_p†` calls. The two-state hybrid premises force
`qSolve = Omega(κ)`. Tomography can select a different hard input, but every call on that input
pays the same fixed schedule. Thus both factors hold on the input selected by `htomography`; no
independently witnessed input costs are multiplied. -/
theorem clean_qls_worst_case_product
    {ι : Type*}
    (qSolve : ℕ) (calls total : ι → ℝ)
    (nn ε κ solverDistance solverGap hybridConstant tomographyConstant : ℝ)
    (hn : 0 < nn) (hε : 0 < ε) (hκ : 0 < κ)
    (hgap : 0 < solverGap) (hhybrid : 0 < hybridConstant)
    (htomographyConstant : 0 < tomographyConstant)
    (hsolverSeparate : solverGap ≤ solverDistance)
    (hsolverProgress : κ * solverDistance ≤ hybridConstant * qSolve)
    (htomography : ∃ p, tomographyConstant * (nn / ε) ≤ calls p)
    (htotal : ∀ p, calls p * qSolve ≤ total p) :
    ∃ p, tomographyConstant * solverGap * (nn * κ) / (hybridConstant * ε) ≤ total p := by
  obtain ⟨p, hp⟩ := htomography
  have hsolve : solverGap * κ / hybridConstant ≤ (qSolve : ℝ) :=
    RHSQueryHardness.rhs_query_lower_bound qSolve solverDistance solverGap hybridConstant κ
      hκ hhybrid hsolverSeparate hsolverProgress
  have hcalls : 0 ≤ calls p := le_trans (by positivity) hp
  refine ⟨p, ?_⟩
  calc
    tomographyConstant * solverGap * (nn * κ) / (hybridConstant * ε) =
        (tomographyConstant * (nn / ε)) * (solverGap * κ / hybridConstant) := by
          field_simp
    _ ≤ calls p * (solverGap * κ / hybridConstant) :=
      mul_le_mul_of_nonneg_right hp (by positivity)
    _ ≤ calls p * qSolve := mul_le_mul_of_nonneg_left hsolve hcalls
    _ ≤ total p := htotal p

/-- On a family with `κ = Omega(nn)`, the clean QLS readout product is
`Omega(nn² / ε)` on one worst case input. -/
theorem clean_qls_worst_case_grid_product
    {ι : Type*}
    (qSolve : ℕ) (calls total : ι → ℝ)
    (nn ε κ solverDistance solverGap hybridConstant tomographyConstant cK : ℝ)
    (hn : 0 < nn) (hε : 0 < ε) (hκ : 0 < κ)
    (hgap : 0 < solverGap) (hhybrid : 0 < hybridConstant)
    (htomographyConstant : 0 < tomographyConstant)
    (hsolverSeparate : solverGap ≤ solverDistance)
    (hsolverProgress : κ * solverDistance ≤ hybridConstant * qSolve)
    (htomography : ∃ p, tomographyConstant * (nn / ε) ≤ calls p)
    (htotal : ∀ p, calls p * qSolve ≤ total p)
    (hkappaLinear : cK * nn ≤ κ) :
    ∃ p, tomographyConstant * solverGap * cK * nn ^ 2 /
      (hybridConstant * ε) ≤ total p := by
  obtain ⟨p, hp⟩ := clean_qls_worst_case_product qSolve calls total nn ε κ solverDistance
    solverGap hybridConstant tomographyConstant hn hε hκ hgap hhybrid htomographyConstant
    hsolverSeparate hsolverProgress htomography htotal
  refine ⟨p, le_trans ?_ hp⟩
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hmul := mul_le_mul_of_nonneg_left hkappaLinear
    (show 0 ≤ tomographyConstant * solverGap * nn by positivity)
  nlinarith

/-- On a family with `κ = Omega(nn²)`, the same clean QLS readout product is
`Omega(nn³ / ε)` on one worst case input. -/
theorem clean_qls_worst_case_corridor_product
    {ι : Type*}
    (qSolve : ℕ) (calls total : ι → ℝ)
    (nn ε κ solverDistance solverGap hybridConstant tomographyConstant cK : ℝ)
    (hn : 0 < nn) (hε : 0 < ε) (hκ : 0 < κ)
    (hgap : 0 < solverGap) (hhybrid : 0 < hybridConstant)
    (htomographyConstant : 0 < tomographyConstant)
    (hsolverSeparate : solverGap ≤ solverDistance)
    (hsolverProgress : κ * solverDistance ≤ hybridConstant * qSolve)
    (htomography : ∃ p, tomographyConstant * (nn / ε) ≤ calls p)
    (htotal : ∀ p, calls p * qSolve ≤ total p)
    (hkappaQuadratic : cK * nn ^ 2 ≤ κ) :
    ∃ p, tomographyConstant * solverGap * cK * nn ^ 3 /
      (hybridConstant * ε) ≤ total p := by
  obtain ⟨p, hp⟩ := clean_qls_worst_case_product qSolve calls total nn ε κ solverDistance
    solverGap hybridConstant tomographyConstant hn hε hκ hgap hhybrid htomographyConstant
    hsolverSeparate hsolverProgress htomography htotal
  refine ⟨p, le_trans ?_ hp⟩
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hmul := mul_le_mul_of_nonneg_left hkappaQuadratic
    (show 0 ≤ tomographyConstant * solverGap * nn by positivity)
  nlinarith

/-- The clean QLS grid product exceeds a nearly linear classical upper bound on the same input.
`mm ≤ sparseConstant * nn` is the sparse-family assumption. -/
theorem clean_qls_grid_product_exceeds_nearly_linear
    {ι : Type*}
    (qSolve : ℕ) (calls total classicalTime : ι → ℝ)
    (nn mm ε κ solverDistance solverGap hybridConstant tomographyConstant cK
      classicalConstant sparseConstant logFactor : ℝ)
    (hn : 0 < nn) (hε : 0 < ε) (hκ : 0 < κ)
    (hgap : 0 < solverGap) (hhybrid : 0 < hybridConstant)
    (htomographyConstant : 0 < tomographyConstant)
    (hclassicalConstant : 0 ≤ classicalConstant) (hlogFactor : 0 ≤ logFactor)
    (hsolverSeparate : solverGap ≤ solverDistance)
    (hsolverProgress : κ * solverDistance ≤ hybridConstant * qSolve)
    (htomography : ∃ p, tomographyConstant * (nn / ε) ≤ calls p)
    (htotal : ∀ p, calls p * qSolve ≤ total p)
    (hkappaLinear : cK * nn ≤ κ)
    (hsparse : mm ≤ sparseConstant * nn)
    (hclassical : ∀ p, classicalTime p ≤ classicalConstant * mm * logFactor)
    (hthreshold : classicalConstant * sparseConstant * logFactor <
      tomographyConstant * solverGap * cK * nn / (hybridConstant * ε)) :
    ∃ p, classicalTime p < total p := by
  obtain ⟨p, hp⟩ := clean_qls_worst_case_grid_product qSolve calls total nn ε κ
    solverDistance solverGap hybridConstant tomographyConstant cK hn hε hκ hgap hhybrid
    htomographyConstant hsolverSeparate hsolverProgress htomography htotal hkappaLinear
  have hsparseTime :
      classicalConstant * mm * logFactor ≤
        classicalConstant * (sparseConstant * nn) * logFactor :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsparse hclassicalConstant) hlogFactor
  have hstrict :
      classicalConstant * (sparseConstant * nn) * logFactor <
        tomographyConstant * solverGap * cK * nn ^ 2 /
          (hybridConstant * ε) := by
    calc
      classicalConstant * (sparseConstant * nn) * logFactor =
          nn * (classicalConstant * sparseConstant * logFactor) := by ring
      _ < nn * (tomographyConstant * solverGap * cK * nn /
          (hybridConstant * ε)) := mul_lt_mul_of_pos_left hthreshold hn
      _ = tomographyConstant * solverGap * cK * nn ^ 2 /
          (hybridConstant * ε) := by ring
  refine ⟨p, ?_⟩
  exact lt_of_le_of_lt (hclassical p)
    (lt_of_le_of_lt hsparseTime (lt_of_lt_of_le hstrict hp))

end
