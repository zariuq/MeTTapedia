import Mettapedia.TypeTheory.ContextualDependentSequencing
import Mettapedia.GSLT.Dynamics.ContextualStrategyQualification

/-!
# Qualified use of first-class contextual computations

A thunk here is an existing contextual `Program` held as an answer value,
not a new source constructor or a memo cell. Selecting such a value does not
execute it. Forcing sequences its existing code in the selected world.
An indexed thunk retains its selected index beside the resulting fibre value.

Read-only qualification of each actually selected thunk permits recomputation
to be replaced by result reuse, or an unused force to be discarded. The outer
selection and the continuation may still choose, write and emit intents. The
equalities retain the handler's ordered worlds, states, paths and intents;
they do not assert work equality, divergence preservation or an implementation
by the owned Need machine. Native mathematical terms are not classified as
CBPV values by these semantic interfaces.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualThunkStrategy

open Mettapedia.GSLT.Dynamics.ContextualEffectHandlers
open Mettapedia.GSLT.Dynamics.ContextualStrategyQualification
open Mettapedia.TypeTheory.ContextualDependentSequencing
open Mettapedia.TypeTheory.ContextualComputationKleisli.Program (bindSigma)

universe u

variable {State Intent Index : Type u} {Family Result : Index → Type u}

/-- Select an index and retain the continuation as a first-class value,
without executing that continuation. -/
def delaySelected (indices : Program State Index Intent)
    (next : (index : Index) → Program State (Family index) Intent) :
    Program State (Sigma fun index => Program State (Family index) Intent) Intent :=
  Program.map (fun index => ⟨index, next index⟩) indices

/-- Force the selected program in its current world and retain its index.
No cell is allocated and no result is memoized. -/
def forceSelected
    (thunks : Program State (Sigma fun index => Program State (Family index) Intent) Intent) :
    Program State (Sigma Family) Intent :=
  thunks.bind fun selected => Program.map (Sigma.mk selected.1) selected.2

/-- Delaying the dependent continuation and then forcing it gives the
existing witness-retaining dependent sequencing operation. -/
theorem forceSelected_delaySelected (indices : Program State Index Intent)
    (next : (index : Index) → Program State (Family index) Intent) :
    forceSelected (delaySelected indices next) = bindSigma indices next := by
  unfold forceSelected delaySelected Program.map bindSigma
  rw [ContextualComputationKleisli.Program.bind_assoc]
  rfl

/-- Forcing retains each selected prefix and evaluates its stored program in
that prefix's state and branch, appending rather than replacing its intents. -/
theorem runWorldsAt_forceSelected
    (thunks : Program State (Sigma fun index => Program State (Family index) Intent) Intent)
    (state : State) (branch : BranchTrace) :
    runWorldsAt (forceSelected thunks) state branch =
      (runWorldsAt thunks state branch).flatMap fun prior =>
        (runWorldsAt prior.answer.2 prior.state prior.branch).map fun suffix =>
          WorldResult.prependIntents prior.intents
            (WorldResult.mapAnswer (Sigma.mk prior.answer.1) suffix) := by
  rw [forceSelected, runWorldsAt_bind]
  simp only [runWorldsAt_map, List.map_map, Function.comp_def]

/-- Execute a selected thunk twice before an index-dependent continuation. -/
def repeatSelectedThen
    (thunks : Program State (Sigma fun index => Program State (Family index) Intent) Intent)
    (next : (index : Index) → Family index → Family index → Program State (Result index) Intent) :
    Program State (Sigma Result) Intent :=
  thunks.bind fun selected =>
    Program.map (Sigma.mk selected.1) (repeatThen selected.2 (next selected.1))

/-- Execute a selected thunk once and reuse its answer, retaining its index.
This describes result reuse, not allocation of a memoized suspension. -/
def reuseSelectedThen
    (thunks : Program State (Sigma fun index => Program State (Family index) Intent) Intent)
    (next : (index : Index) → Family index → Family index → Program State (Result index) Intent) :
    Program State (Sigma Result) Intent :=
  thunks.bind fun selected =>
    Program.map (Sigma.mk selected.1) (reuseThen selected.2 (next selected.1))

/-- Only the programs actually selected at this entry observation must be
structurally read-only. Outer selection and later effects remain unrestricted. -/
theorem repeatSelected_eq_reuseSelected
    (thunks : Program State (Sigma fun index => Program State (Family index) Intent) Intent)
    (next : (index : Index) → Family index → Family index → Program State (Result index) Intent)
    (state : State) (branch : BranchTrace)
    (qualified : ∀ prior ∈ runWorldsAt thunks state branch, ReadOnly prior.answer.2) :
    runWorldsAt (repeatSelectedThen thunks next) state branch =
      runWorldsAt (reuseSelectedThen thunks next) state branch := by
  rw [repeatSelectedThen, reuseSelectedThen, runWorldsAt_bind, runWorldsAt_bind]
  apply List.flatMap_congr
  intro prior membership
  rw [runWorldsAt_map, runWorldsAt_map,
    repeat_eq_reuse prior.answer.2 (qualified prior membership) (next prior.answer.1)
      prior.state prior.branch]

/-- Run the stored program even though the continuation does not use its
answer. This differs from merely selecting and discarding the stored code. -/
def eagerDiscardSelected
    (thunks : Program State (Sigma fun index => Program State (Family index) Intent) Intent)
    (next : (index : Index) → Program State (Result index) Intent) :
    Program State (Sigma Result) Intent :=
  thunks.bind fun selected =>
    Program.map (Sigma.mk selected.1) (selected.2.bind fun _ => next selected.1)

/-- Select and discard a thunk value without forcing its body. -/
def discardSelected
    (thunks : Program State (Sigma fun index => Program State (Family index) Intent) Intent)
    (next : (index : Index) → Program State (Result index) Intent) :
    Program State (Sigma Result) Intent :=
  thunks.bind fun selected => Program.map (Sigma.mk selected.1) (next selected.1)

theorem eagerDiscardSelected_eq_discardSelected
    (thunks : Program State (Sigma fun index => Program State (Family index) Intent) Intent)
    (next : (index : Index) → Program State (Result index) Intent)
    (state : State) (branch : BranchTrace)
    (qualified : ∀ prior ∈ runWorldsAt thunks state branch, ReadOnly prior.answer.2) :
    runWorldsAt (eagerDiscardSelected thunks next) state branch =
      runWorldsAt (discardSelected thunks next) state branch := by
  rw [eagerDiscardSelected, discardSelected, runWorldsAt_bind, runWorldsAt_bind]
  apply List.flatMap_congr
  intro prior membership
  rw [runWorldsAt_map, runWorldsAt_map,
    discard_readOnly prior.answer.2 (qualified prior membership) (next prior.answer.1)
      prior.state prior.branch]

namespace Examples

open Mettapedia.TypeTheory.DependencyExtensionalityOrthogonality

/-- The false fibre is a singleton; the true fibre has two values. -/
def readOnlyThunk : (index : Bool) → Program Bool (varyingBoolFamily index) Nat
  | false => .read fun _ => .pure PUnit.unit
  | true => .read fun state => .pure state

theorem readOnlyThunk_qualified (index : Bool) : ReadOnly (readOnlyThunk index) := by
  cases index <;> exact .read _ fun _ => .pure _

/-- Selecting a thunk may itself choose, write state and retain intents. -/
def indices : Program Bool Bool Nat :=
  .choose (.intent 1 (.pure false)) (.write true (.intent 2 (.pure true)))

def selected : Program Bool (Sigma fun index => Program Bool (varyingBoolFamily index) Nat) Nat :=
  delaySelected indices readOnlyThunk

def pairNext (index : Bool) (first second : varyingBoolFamily index) :
    Program Bool (varyingBoolFamily index × varyingBoolFamily index) Nat :=
  .intent 3 (.pure (first, second))

theorem selected_qualified :
    ∀ prior ∈ runWorldsAt selected false [], ReadOnly prior.answer.2 := by
  intro prior membership
  simp only [selected, delaySelected, indices, Program.map, Program.bind, runWorldsAt,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at membership
  rcases membership with rfl | rfl
  · exact readOnlyThunk_qualified false
  · exact readOnlyThunk_qualified true

theorem selected_recomputation_equals_reuse :
    runWorldsAt (repeatSelectedThen selected pairNext) false [] =
      runWorldsAt (reuseSelectedThen selected pairNext) false [] :=
  repeatSelected_eq_reuseSelected selected pairNext false [] selected_qualified

/-- The index, selected state and chronological intents survive both uses. -/
theorem selected_dependent_observation :
    (runWorldsAt (reuseSelectedThen selected pairNext) false []).map
      (fun world => (world.answer.1, world.state, world.intents)) =
      [(false, false, [1, 3]), (true, true, [2, 3])] := rfl

theorem selected_family_not_uniform :
    ¬ ∃ Constant : Type, ∀ index, Nonempty (varyingBoolFamily index ≃ Constant) :=
  varyingBoolFamily_not_constant

/-- Selecting this value emits only the selection intent. Its stored code
emits another intent and makes a fresh Boolean choice whenever forced. -/
def effectfulThunk : Program Unit Bool Nat :=
  .intent 7 (.choose (.pure false) (.pure true))

def selectedEffectful : Program Unit (Sigma fun _ : Unit => Program Unit Bool Nat) Nat :=
  .intent 5 (.pure ⟨(), effectfulThunk⟩)

def pairBooleans (_ : Unit) (first second : Bool) : Program Unit (Bool × Bool) Nat :=
  .intent 9 (.pure (first, second))

theorem forced_twice_keeps_independent_choices_and_repeated_intents :
    (runWorldsAt (repeatSelectedThen selectedEffectful pairBooleans) () []).map
      (fun world => (world.answer.2, world.intents)) =
      [((false, false), [5, 7, 7, 9]), ((false, true), [5, 7, 7, 9]),
        ((true, false), [5, 7, 7, 9]), ((true, true), [5, 7, 7, 9])] := rfl

theorem reused_answer_keeps_correlated_choices_and_single_intent :
    (runWorldsAt (reuseSelectedThen selectedEffectful pairBooleans) () []).map
      (fun world => (world.answer.2, world.intents)) =
      [((false, false), [5, 7, 9]), ((true, true), [5, 7, 9])] := rfl

theorem first_class_thunk_does_not_memoize :
    runWorldsAt (repeatSelectedThen selectedEffectful pairBooleans) () [] ≠
      runWorldsAt (reuseSelectedThen selectedEffectful pairBooleans) () [] := by
  intro equal
  have lengths := congrArg List.length equal
  change 4 = 2 at lengths
  cases lengths

def ignoreAnswer (_ : Unit) : Program Unit Unit Nat := .intent 9 (.pure ())

theorem unused_thunk_does_not_emit_its_body_intent :
    (runWorldsAt (discardSelected selectedEffectful ignoreAnswer) () []).map
      WorldResult.intents = [[5, 9]] := rfl

theorem eager_force_of_unused_thunk_changes_intents_and_occurrences :
    (runWorldsAt (eagerDiscardSelected selectedEffectful ignoreAnswer) () []).map
      WorldResult.intents = [[5, 7, 9], [5, 7, 9]] := rfl

theorem unqualified_eager_discard_is_invalid :
    runWorldsAt (eagerDiscardSelected selectedEffectful ignoreAnswer) () [] ≠
      runWorldsAt (discardSelected selectedEffectful ignoreAnswer) () [] := by
  intro equal
  have lengths := congrArg List.length equal
  change 2 = 1 at lengths
  cases lengths

end Examples

#print axioms forceSelected_delaySelected
#print axioms runWorldsAt_forceSelected
#print axioms repeatSelected_eq_reuseSelected
#print axioms eagerDiscardSelected_eq_discardSelected
#print axioms Examples.selected_recomputation_equals_reuse
#print axioms Examples.selected_dependent_observation
#print axioms Examples.selected_family_not_uniform
#print axioms Examples.first_class_thunk_does_not_memoize
#print axioms Examples.unused_thunk_does_not_emit_its_body_intent
#print axioms Examples.eager_force_of_unused_thunk_changes_intents_and_occurrences
#print axioms Examples.unqualified_eager_discard_is_invalid

end Mettapedia.TypeTheory.ContextualThunkStrategy
