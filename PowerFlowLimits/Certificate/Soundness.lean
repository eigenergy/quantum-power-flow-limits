import PowerFlowLimits.Certificate.Core
import PowerFlowLimits.CutBounds

/-!
# Spectral soundness of the computable cut certificate

The correspondence hypotheses are the boundary between PowerIO's trusted extraction and the Lean
model. Once the extracted totals, cut, and bus count denote a `WeightedGraph`, the executable
formula is exactly the condition number lower bound already proved in `CutBounds`.
-/

open Finset

namespace PowerFlowLimits.Certificate

noncomputable section

variable {n m : ℕ}

theorem cutLowerBound_le_condition (model : Model) (witness : CutWitness)
    (G : WeightedGraph n m) (S : Finset (Fin n)) (lower : Rat)
    (hbound : cutLowerBound model witness = some lower)
    (hbuses : model.buses = n)
    (hside : sideCard witness ≤ model.buses)
    (hcard : (sideCard witness : ℝ) = S.card)
    (htotal : ((totalWeight model : Rat) : ℝ) = G.totalWeight)
    (hcut : ((cutWeight model witness : Rat) : ℝ) = G.cutWeight S)
    (hSnonempty : S.Nonempty) (hSproper : S ≠ Finset.univ)
    (hconnected : G.CombinatoriallyConnected) :
    ((lower : Rat) : ℝ) ≤ effectiveConditionNumber G (fun _ ↦ 1) := by
  have hspectral := kappaPlus_ge_totalWeight G S hSnonempty hSproper hconnected
  have hlower : lower =
      2 * (sideCard witness : Rat) * (model.buses - sideCard witness : Nat) *
        totalWeight model /
          ((model.buses : Rat) ^ 2 * cutWeight model witness) := by
    unfold cutLowerBound at hbound
    split at hbound <;> simp_all
  rw [hlower]
  push_cast
  have hsideN : sideCard witness ≤ n := by simpa [hbuses] using hside
  have hsub : ((n - sideCard witness : Nat) : ℝ) = n - S.card := by
    rw [Nat.cast_sub hsideN, hcard]
  rw [hbuses, hcard, hsub, htotal, hcut]
  have hn : (0 : ℝ) < n := by
    have hnNat : 0 < n := Fin.pos_iff_nonempty.mpr hconnected.nonempty
    exact_mod_cast hnNat
  convert hspectral using 1
  field_simp

theorem accepted_no_advantage_sound (model : Model) (policy : Policy)
    (witness : CutWitness) (G : WeightedGraph n m) (S : Finset (Fin n))
    (accepted : checkNoAdvantage model policy witness = true)
    (hbuses : model.buses = n)
    (hside : sideCard witness ≤ model.buses)
    (hcard : (sideCard witness : ℝ) = S.card)
    (htotal : ((totalWeight model : Rat) : ℝ) = G.totalWeight)
    (hcut : ((cutWeight model witness : Rat) : ℝ) = G.cutWeight S)
    (hSnonempty : S.Nonempty) (hSproper : S ≠ Finset.univ)
    (hconnected : G.CombinatoriallyConnected) :
    ∃ lower : Rat,
      ((lower : Rat) : ℝ) ≤ effectiveConditionNumber G (fun _ ↦ 1) ∧
      classicalCost model policy < quantumCostLower model policy lower := by
  obtain ⟨lower, _, hlower, hcost⟩ := checkNoAdvantage_sound accepted
  exact ⟨lower,
    cutLowerBound_le_condition model witness G S lower hlower hbuses hside hcard htotal hcut
      hSnonempty hSproper hconnected,
    hcost⟩

/-- End to end interpretation of acceptance. The two external complexity results enter as
premises: the classical implementation is no slower than the policy bound, and the declared QLS
plus full readout workflow is no faster than the policy lower bound whenever `lower` is a valid
condition number lower bound. -/
theorem accepted_cost_separation (model : Model) (policy : Policy)
    (witness : CutWitness) (G : WeightedGraph n m) (S : Finset (Fin n))
    (classicalTime quantumTime : Rat)
    (accepted : checkNoAdvantage model policy witness = true)
    (hbuses : model.buses = n) (hside : sideCard witness ≤ model.buses)
    (hcard : (sideCard witness : ℝ) = S.card)
    (htotal : ((totalWeight model : Rat) : ℝ) = G.totalWeight)
    (hcut : ((cutWeight model witness : Rat) : ℝ) = G.cutWeight S)
    (hSnonempty : S.Nonempty) (hSproper : S ≠ Finset.univ)
    (hconnected : G.CombinatoriallyConnected)
    (hclassical : classicalTime ≤ classicalCost model policy)
    (hquantum : ∀ lower : Rat,
      ((lower : Rat) : ℝ) ≤ effectiveConditionNumber G (fun _ ↦ 1) →
      quantumCostLower model policy lower ≤ quantumTime) :
    classicalTime < quantumTime := by
  obtain ⟨lower, hlower, hcost⟩ := accepted_no_advantage_sound model policy witness G S accepted
    hbuses hside hcard htotal hcut hSnonempty hSproper hconnected
  exact hclassical.trans_lt (hcost.trans_le (hquantum lower hlower))

end

end PowerFlowLimits.Certificate
