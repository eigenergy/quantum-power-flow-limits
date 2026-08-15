/-
Copyright (c) 2026 Cameron Khanpour and Samuel Talkington. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Cameron Khanpour, Samuel Talkington
-/

/-!
# Computable quantum advantage obstruction certificates

The executable kernel uses exact rational arithmetic. An accepted certificate is one sided: it
establishes that the policy's quantum lower bound is strictly larger than its classical upper
bound. Rejection makes no claim about quantum advantage.
-/

namespace PowerFlowLimits.Certificate

/-- One positive weighted branch in a dense zero based bus index space. -/
structure Branch where
  /-- Zero based index of one endpoint bus. -/
  source : Nat
  /-- Zero based index of the other endpoint bus. -/
  target : Nat
  /-- Series susceptance weight of the branch. Valid branches have positive weight. -/
  weight : Rat
deriving BEq

/-- The canonical positive weighted DC model supplied by PowerIO. -/
structure Model where
  /-- Number of buses. Bus indices run from `0` to `buses - 1`. -/
  buses : Nat
  /-- All branches of the model. -/
  branches : List Branch
deriving BEq

/-- A cut is represented by one Boolean membership value per bus. -/
structure CutWitness where
  /-- `side[i] = true` when bus `i` belongs to the cut side `S`. -/
  side : List Bool
deriving BEq

/-- Explicit finite cost model for full angle vector readout. -/
structure Policy where
  /-- Readout accuracy target. Divides the quantum cost lower bound. Must be positive. -/
  error : Rat
  /-- Constant factor of the tomography term in the quantum cost lower bound. Must be positive. -/
  tomographyConstant : Rat
  /-- Constant factor for the solver queries per tomography repetition. Must be positive. -/
  solverGap : Rat
  /-- Divisor that discounts the quantum cost lower bound for hybrid schemes. Must be positive. -/
  hybridConstant : Rat
  /-- Constant factor of the classical cost upper bound. Must be nonnegative. -/
  classicalConstant : Rat
  /-- Logarithmic factor of the classical cost upper bound. Must be nonnegative. -/
  classicalLogFactor : Rat
deriving BEq

/-- A branch is valid for an `n` bus model when both endpoints are distinct indices below `n`
and the weight is positive. -/
def Branch.valid (n : Nat) (e : Branch) : Bool :=
  e.source < n && e.target < n && e.source != e.target && 0 < e.weight

private def adjacency (model : Model) : Array (List Nat) :=
  model.branches.foldl
    (fun adj branch ↦
      let adj := adj.modify branch.source (branch.target :: ·)
      adj.modify branch.target (branch.source :: ·))
    (Array.replicate model.buses [])

/-- Breadth first traversal. A bus is marked when it is enqueued, so every bus is dequeued at
most once and `model.buses` steps of fuel visit the whole component. -/
private def bfsVisit (adj : Array (List Nat)) :
    Nat → List Nat → Array Bool → Array Bool
  | 0, _, visited => visited
  | _ + 1, [], visited => visited
  | fuel + 1, bus :: queue, visited =>
      let (visited, fresh) := (adj.getD bus []).foldl
        (fun (state : Array Bool × List Nat) next ↦
          if state.1.getD next false then state
          else (state.1.setIfInBounds next true, next :: state.2))
        (visited, [])
      bfsVisit adj fuel (fresh ++ queue) visited

/-- Decide whether every bus is reachable from bus `0` along branches. -/
def Model.connected (model : Model) : Bool :=
  match model.buses with
  | 0 => true
  | _ + 1 =>
      let start := (Array.replicate model.buses false).setIfInBounds 0 true
      let visited := bfsVisit (adjacency model) model.buses [0] start
      (List.range model.buses).all (fun bus ↦ visited.getD bus false)

/-- A model is valid when it has at least two buses, every branch is valid, and the branch
graph is connected. -/
def Model.valid (model : Model) : Bool :=
  2 ≤ model.buses && model.branches.all (Branch.valid model.buses) && model.connected

/-- Sign checks for the policy constants. -/
def Policy.valid (policy : Policy) : Bool :=
  0 < policy.error && 0 < policy.tomographyConstant && 0 < policy.solverGap &&
    0 < policy.hybridConstant && 0 ≤ policy.classicalConstant &&
    0 ≤ policy.classicalLogFactor

/-- Total branch weight `b(E)`. -/
def totalWeight (model : Model) : Rat :=
  model.branches.foldl (fun total branch ↦ total + branch.weight) 0

/-- Total weight of the branches whose endpoints lie on opposite sides of the cut, `b(∂S)`. -/
def cutWeight (model : Model) (witness : CutWitness) : Rat :=
  let side := witness.side.toArray
  model.branches.foldl
    (fun total branch ↦
      if side.getD branch.source false != side.getD branch.target false then
        total + branch.weight
      else total)
    0

/-- Number of buses on the cut side `S`. -/
def sideCard (witness : CutWitness) : Nat :=
  witness.side.foldl (fun count inside ↦ if inside then count + 1 else count) 0

/-- Exact Lemma 1 cut expression. Soundness as a condition number lower bound is established in
the mathlib layer after the model is related to a connected `WeightedGraph`. -/
def cutLowerBound (model : Model) (witness : CutWitness) : Option Rat :=
  if !model.valid || witness.side.length != model.buses then none
  else
    let a := sideCard witness
    let cut := cutWeight model witness
    if a = 0 || a = model.buses || cut ≤ 0 then none
    else
      some (2 * (a : Rat) * (model.buses - a : Nat) * totalWeight model /
        ((model.buses : Rat) ^ 2 * cut))

/-- Classical cost upper bound `classicalConstant * m * classicalLogFactor`. -/
def classicalCost (model : Model) (policy : Policy) : Rat :=
  policy.classicalConstant * model.branches.length * policy.classicalLogFactor

/-- Quantum cost lower bound obtained from the certified condition number lower bound. -/
def quantumCostLower (model : Model) (policy : Policy) (conditionLower : Rat) : Rat :=
  policy.tomographyConstant / 2 * policy.solverGap * model.buses * conditionLower /
    (policy.hybridConstant * policy.error)

/-- The one sided verdict. -/
def checkNoAdvantage (model : Model) (policy : Policy) (witness : CutWitness) : Bool :=
  if policy.valid then
    match cutLowerBound model witness with
    | none => false
    | some conditionLower =>
        classicalCost model policy < quantumCostLower model policy conditionLower
  else false

theorem checkNoAdvantage_sound {model : Model} {policy : Policy} {witness : CutWitness}
    (accepted : checkNoAdvantage model policy witness = true) :
    ∃ conditionLower,
      policy.valid = true ∧
      cutLowerBound model witness = some conditionLower ∧
      classicalCost model policy < quantumCostLower model policy conditionLower := by
  unfold checkNoAdvantage at accepted
  split at accepted
  next hvalid =>
    split at accepted
    next hbound => simp_all
    next conditionLower hbound =>
      exact ⟨conditionLower, hvalid, hbound, by simpa using accepted⟩
  next => simp_all

/-- Composition boundary for the spectral proof. Once the checked cut expression is known to
lower bound the true condition number, acceptance gives the strict finite cost comparison. -/
theorem checkNoAdvantage_of_condition_bound {model : Model} {policy : Policy}
    {witness : CutWitness} {condition : Rat}
    (accepted : checkNoAdvantage model policy witness = true)
    (bound : ∀ lower, cutLowerBound model witness = some lower → lower ≤ condition) :
    ∃ lower,
      lower ≤ condition ∧
      classicalCost model policy < quantumCostLower model policy lower := by
  obtain ⟨lower, _, hlower, hcost⟩ := checkNoAdvantage_sound accepted
  exact ⟨lower, bound lower hlower, hcost⟩

end PowerFlowLimits.Certificate
