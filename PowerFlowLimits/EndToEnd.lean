import Mathlib.Tactic

/-!
# Proposition 3 (prop:e2e): end-to-end query lower bounds, chaining the cited facts (F1), (F2)

Part of the Lean 4 formalization of
"The Limits of Quantum Computers for Power Flow" (Khanpour and Talkington).
-/

open Finset BigOperators

noncomputable section

variable {n m : ℕ}

/-- Proposition 3 (prop:e2e), part (i), formalized as the arithmetic chaining
    in its proof. The quantum-information inputs are the cited facts and enter
    as hypotheses: (F1) every QLS solve on a κ-conditioned system costs at
    least c₁·κ queries [hhl2009]; (F2) recovering a classical ε-approximation
    needs at least c₂·n/ε state preparations, each a fresh solve since
    measurement destroys the state [apeldoorn2023]. Given the structural bound
    κ ≥ c₃·q — with q = n from `separator_kappa_bound`/Corollary 1, or q = n²
    from `corridor_kappa_bound` — the end-to-end query cost is at least
    c₁c₂c₃·n·q/ε, i.e. Ω(n²/ε) on grid families and Ω(n³/ε) on corridor
    families. -/
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
  have h := e2e_query_lower_bound nn nn ε κ preps costPerPrep total c₁ c₂ c₃
    hn hn hε hc₁ hc₂ hc₃ hκ hpreps hcost htotal
  calc c₁ * c₂ * c₃ * nn ^ 2 / ε = c₁ * c₂ * c₃ * (nn * nn) / ε := by ring
    _ ≤ total := h

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
  have h := e2e_query_lower_bound nn (nn ^ 2) ε κ preps costPerPrep total
    c₁ c₂ c₃ hn (by positivity) hε hc₁ hc₂ hc₃ hκ hpreps hcost htotal
  calc c₁ * c₂ * c₃ * nn ^ 3 / ε = c₁ * c₂ * c₃ * (nn * nn ^ 2) / ε := by ring
    _ ≤ total := h

/-- Proposition 3 (prop:e2e), part (ii): estimating even one observable pays
    the full solve cost, ≥ c₁·κ ≥ c₁c₃·n queries — already the price of the
    classical solution. -/
theorem e2e_observable_lower_bound (nn κ cost c₁ c₃ : ℝ)
    (hc₁ : 0 < c₁) (hκ : c₃ * nn ≤ κ) (hcost : c₁ * κ ≤ cost) :
    c₁ * (c₃ * nn) ≤ cost :=
  le_trans (mul_le_mul_of_nonneg_left hκ hc₁.le) hcost

end
