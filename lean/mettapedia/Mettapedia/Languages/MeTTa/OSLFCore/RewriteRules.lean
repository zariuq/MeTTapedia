import Mettapedia.Languages.MeTTa.OSLFCore.State
import Mettapedia.Languages.MeTTa.OSLFCore.MinimalOps

/-!
# MeTTaCore Rewrite Rules

The core rewrite rules from the Meta-MeTTa paper. These rules define how
the interpreter state transitions during evaluation.

## Main Definitions

* `ruleQuery` - Match term against knowledge
* `ruleTransform` - Apply equation to workspace term
* `ruleAddAtom` - Add atom to knowledge
* `ruleRemAtom` - Remove atom from knowledge
* `ruleOutput` - Move insensitive term to output
* `applyRewriteRules` - Apply all applicable rules

## References

* Meta-MeTTa paper (Meredith, Goertzel, Warrell, Vandervorst)
* Section on rewrite semantics
-/

namespace Mettapedia.Languages.MeTTa.OSLFCore

/-! ## State Transition Result -/

/-- Result of applying rewrite rules: a multiset of possible next states -/
abbrev StateTransitions := Multiset MeTTaState

/-! ## Core Rewrite Rules -/

/-- Query rule: For each term in workspace, try to match against equations in knowledge.
    If a match is found, replace the term with the RHS of the equation (with bindings applied).

    From Meta-MeTTa: This is the fundamental evaluation mechanism. -/
def ruleQuery (state : MeTTaState) : StateTransitions :=
  -- For each term in workspace
  state.workspace.bind fun t =>
    -- Query equations in knowledge
    let eqResults := state.knowledge.queryEquations t
    if eqResults.card == 0 then
      -- No matches: return state unchanged (as a possible continuation)
      {state}
    else
      -- For each match, create a new state with the term replaced
      eqResults.map fun (rhs, bindings) =>
        { state with
          workspace := (state.workspace.erase t) + {bindings.apply rhs} }

/-- Transform rule: Apply a single equation transformation to a workspace term.
    Similar to Query but more explicit about the transformation step.

    This is essentially the same as ruleQuery but conceptually distinct in Meta-MeTTa. -/
def ruleTransform (state : MeTTaState) : StateTransitions :=
  ruleQuery state  -- Implementation is identical

/-- AddAtom rule: Handle `(add-atom space atom)` expressions in workspace.
    Adds the atom to the knowledge base.

    From Meta-MeTTa: This modifies the knowledge component of state. -/
def ruleAddAtom (state : MeTTaState) : StateTransitions :=
  -- Look for (add-atom ...) expressions in workspace
  state.workspace.filterMap fun t =>
    match t with
    | .expression [.symbol "add-atom", _, atom] =>
        some { state with
          workspace := state.workspace.erase t
          knowledge := state.knowledge.add atom }
    | _ => none

/-- RemAtom rule: Handle `(remove-atom space atom)` expressions in workspace.
    Removes the atom from the knowledge base.

    From Meta-MeTTa: This modifies the knowledge component of state. -/
def ruleRemAtom (state : MeTTaState) : StateTransitions :=
  -- Look for (remove-atom ...) expressions in workspace
  state.workspace.filterMap fun t =>
    match t with
    | .expression [.symbol "remove-atom", _, atom] =>
        some { state with
          workspace := state.workspace.erase t
          knowledge := state.knowledge.remove atom }
    | _ => none

/-- Output rule: Move insensitive terms from workspace to output.
    A term is insensitive if no equation in knowledge can match it.

    From Meta-MeTTa: Insensitive terms are "fully reduced" and go to output. -/
def ruleOutput (state : MeTTaState) : StateTransitions :=
  -- Find insensitive terms in workspace
  let insensitiveTerms := state.workspace.filter fun t =>
    state.knowledge.insensitive t
  if insensitiveTerms.card == 0 then
    ∅  -- No insensitive terms
  else
    -- Move each insensitive term to output
    insensitiveTerms.map fun t =>
      state.workspaceToOutput t

/-! ## Input Processing -/

/-- Input rule: Move terms from input to workspace for processing.
    This is how new terms enter the evaluation pipeline.

    From Meta-MeTTa: The input register feeds the workspace. -/
def ruleInput (state : MeTTaState) : StateTransitions :=
  -- Move each input term to workspace
  state.input.map fun t =>
    state.inputToWorkspace t

/-! ## Combined Rule Application -/

/-- Apply all rewrite rules non-deterministically.
    Returns all possible next states from any applicable rule.

    The multiset union captures that any rule can fire. -/
def applyRewriteRules (state : MeTTaState) : StateTransitions :=
  ruleInput state + ruleQuery state + ruleAddAtom state +
  ruleRemAtom state + ruleOutput state

/-- Apply a single step of rewrite rules, preferring certain rules.
    Priority: Input > Query > AddAtom/RemAtom > Output

    This is a deterministic version for simpler reasoning. -/
noncomputable def stepOnce (state : MeTTaState) : Option MeTTaState :=
  -- Priority 1: Process input
  if state.input.card > 0 then
    -- Take first input term
    match state.input.toList.head? with
    | some t => some (state.inputToWorkspace t)
    | none => none
  -- Priority 2: Apply equations
  else if let some t := state.workspace.toList.head? then
    let eqResults := state.knowledge.queryEquations t
    match eqResults.toList.head? with
    | some (rhs, bindings) =>
        some { state with
          workspace := (state.workspace.erase t) + {bindings.apply rhs} }
    | none =>
        -- No match: move to output if insensitive
        if state.knowledge.insensitive t then
          some (state.workspaceToOutput t)
        else
          none
  else
    none

/-! ## Evaluation with Fuel -/

/-- Evaluate state until done or out of fuel.
    Uses the combined rewrite rules non-deterministically. -/
def evalWithFuel (fuel : Nat) (state : MeTTaState) : StateTransitions :=
  match fuel with
  | 0 => {state}  -- Out of fuel
  | n + 1 =>
    if state.isDone then
      {state}  -- Done: return final state
    else
      let nextStates := applyRewriteRules state
      if nextStates.card == 0 then
        {state}  -- Stuck: return current state
      else
        nextStates.bind fun s => evalWithFuel n s

/-- Evaluate a term to completion (with fuel bound). -/
def evaluate (fuel : Nat) (knowledge : Atomspace) (term : Atom) : Multiset Atom :=
  let initial := MeTTaState.initial term knowledge
  let finals := evalWithFuel fuel initial
  finals.bind fun s => s.output

/-! ## Theorems -/

/-- Empty state is done -/
theorem empty_is_done : MeTTaState.empty.isDone = true := rfl

/-- Initial state has term in workspace -/
theorem initial_has_workspace (a : Atom) :
    (MeTTaState.initial a).workspace = {a} := rfl

/-- Initial state is not done (has work) - concrete example -/
theorem initial_not_done_example :
    (MeTTaState.initial (.symbol "x")).isDone = false := by decide

/-- Output rule doesn't add to workspace.

    Council insights:
    - Mario Carneiro: Use Multiset.mem_map to decompose membership
    - Terrence Tao: The key is Multiset.card_erase_le
    - Kevin Buzzard: Handle the if-then-else by case splitting -/
theorem output_workspace_card (state : MeTTaState) :
    ∀ s' ∈ ruleOutput state, s'.workspace.card ≤ state.workspace.card := by
  intro s' h
  -- Unfold ruleOutput definition
  simp only [ruleOutput] at h
  -- Case split on whether there are insensitive terms
  split_ifs at h with hcond
  · -- Case: no insensitive terms, result is empty
    -- h : s' ∈ ∅, which is false (∅ = 0 for Multiset)
    exact absurd h (Multiset.notMem_zero s')
  · -- Case: some insensitive terms exist
    -- s' is in the map, so extract the source term
    rw [Multiset.mem_map] at h
    obtain ⟨t, ht_filter, ht_eq⟩ := h
    -- t is in the filtered workspace, so t ∈ workspace
    rw [Multiset.mem_filter] at ht_filter
    obtain ⟨ht_ws, _⟩ := ht_filter
    -- s' = state.workspaceToOutput t, so s'.workspace = state.workspace.erase t
    rw [← ht_eq]
    simp only [MeTTaState.workspaceToOutput]
    -- card of erase is ≤ original card
    exact Multiset.card_erase_le

/-! ## Unit Tests -/

section Tests

-- Empty state
example : MeTTaState.empty.isDone = true := rfl

-- Initial state with symbol (workspace not empty)
example : (MeTTaState.initial (.symbol "x")).workspaceEmpty = false := by decide

-- Initial state has one term in workspace
example : (MeTTaState.initial (.symbol "x")).workspace.card = 1 := rfl

end Tests

end Mettapedia.Languages.MeTTa.OSLFCore
