import Mettapedia.Languages.MeTTa.ContextualTransform.HEReturnAndSpaces

/-!
# Stateful source controls with named stores

This explicit model host implements list-valued stores, first-occurrence take,
append, inspection and a failing destination. It supplies primitive outcomes
to the independent HE source judgments; it receives no evaluator continuation.
The controls distinguish source sequencing from rollback and space labels from
their host representations. They are not conformance proofs for CeTTa natives.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.ContextualTransform.HEWorldControls

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed Spec.Eval.Completed.Stateful
open HEStatefulContexts HEReturnAndSpaces

abbrev World := Bool → List Atom

def failure (destination : Atom) : Atom :=
  .expression [.symbol "Error", destination, .symbol "BadDestination"]

/-- An independent primitive service, with ordered physical occurrences. -/
def execute (label : Bool) (world : World) (command argument : Atom) : List Atom × World :=
  if command = .symbol "put" then
    ([.expression []], Function.update world label (world label ++ [argument]))
  else if command = .symbol "take" then
    if argument ∈ world label then
      ([argument], Function.update world label ((world label).erase argument))
    else ([], world)
  else if command = .symbol "silent-put" then
    ([], Function.update world label (world label ++ [argument]))
  else if command = .symbol "read" then (world label, world)
  else ([failure argument], world)

def services : WorldServices Bool World where
  contextPayload label := .int (if label then 1 else 0)
  nativeCall label before name command argument frame results after :=
    name = .symbol "model-store" ∧
      results = (execute label before command argument).1.map
        (fun value => (Entry.Value.ofAtom value, frame)) ∧
      after = (execute label before command argument).2

def environment : WorldEnvironment Bool World where
  view world label := ⟨world label⟩
  services := services
  dispatch := { executable := fun _ => False, outcome := fun _ _ _ => False }
  lookup := rawLookup

def command (name : String) (argument : Atom) : Entry.Value :=
  native (.symbol "model-store") (.symbol name) (Entry.Value.ofAtom argument)

theorem command_exact (label : Bool) (before : World) (name : String) (argument : Atom)
    (live : List Atom) (scope : List String) (caller : Option Atom) (policy : Policy)
    (frame : Frame) (results : List Result) (after : World) :
    MinimalRel environment label before live scope caller (command name argument)
        frame results after (policy := policy) ↔
      results = (execute label before (.symbol name) argument).1.map
        (fun value => (Entry.Value.ofAtom value, frame)) ∧
      after = (execute label before (.symbol name) argument).2 := by
  rw [command, native_exact]
  simp [environment, services, Entry.Value.erase]

/-- Changing one named store leaves the other store intact. -/
theorem execute_other_space (label other : Bool) (different : other ≠ label)
    (world : World) (name argument : Atom) :
    (execute label world name argument).2 other = world other := by
  unfold execute
  split_ifs <;> simp [Function.update_of_ne different]

theorem handles_distinct : Function.Injective services.contextPayload := by
  intro first second same
  cases first <;> cases second <;> simp_all [services]

private theorem substitute_command (policy : Policy) (binder : String) (value : Entry.Value)
    (name argument : String) :
    substituteBinder policy binder value (command name (.symbol argument)) =
      command name (.symbol argument) := by
  cases rebuild : policy.rebuilding <;>
    simp [command, native, substituteBinder, Entry.Value.ofAtom,
      Entry.Value.substitute, Entry.Value.rebuildStatus, rebuild]

def takeThenFail (item destination : String) : Entry.Value :=
  chain (command "take" (.symbol item)) "claimed" (command "bad" (.symbol destination))

/-- A later destination error does not undo a successful earlier take. Both
directions exclude a success count, a missing error, or a restored source row. -/
theorem take_then_fail_exact (label : Bool) (before : World) (item destination : String)
    (present : Atom.symbol item ∈ before label)
    (live : List Atom) (scope : List String) (caller : Option Atom) (policy : Policy)
    (frame : Frame) (results : List Result) (after : World) :
    MinimalRel environment label before live scope caller (takeThenFail item destination)
        frame results after (policy := policy) ↔
      results = [(Entry.Value.ofAtom (failure (.symbol destination)), frame)] ∧
      after = Function.update before label ((before label).erase (.symbol item)) := by
  rw [takeThenFail, chain_exact]
  constructor
  · rintro ⟨middle, selected, taken, continued⟩
    have takenExact := (command_exact _ _ _ _ _ _ _ _ _ _ _).mp taken
    simp [execute, present] at takenExact
    rcases takenExact with ⟨rfl, rfl⟩
    have one := BoundaryBatchRel.single_iff.mp continued
    cases one with
    | chain resumed =>
        rw [substitute_command] at resumed
        have result := (command_exact _ _ _ _ _ _ _ _ _ _ _).mp resumed
        simpa [execute] using result
  · rintro ⟨rfl, rfl⟩
    refine ⟨Function.update before label ((before label).erase (.symbol item)),
      [(Entry.Value.ofAtom (.symbol item), frame)], ?_, ?_⟩
    · apply (command_exact _ _ _ _ _ _ _ _ _ _ _).mpr
      simp [execute, present]
    · apply BoundaryBatchRel.single_iff.mpr
      apply Stateful.BoundaryRel.chain
      rw [substitute_command]
      apply (command_exact _ _ _ _ _ _ _ _ _ _ _).mpr
      simp [execute]

/-- An effectful operand that emits no answers suppresses the continuation,
but its store update survives. This holds for every continuation template. -/
theorem answerless_effect_exact (label : Bool) (before : World) (item : Atom)
    (binder : String) (template : Entry.Value)
    (live : List Atom) (scope : List String) (caller : Option Atom) (policy : Policy)
    (frame : Frame) (results : List Result) (after : World) :
    MinimalRel environment label before live scope caller
        (chain (command "silent-put" item) binder template)
        frame results after (policy := policy) ↔
      results = [] ∧ after = Function.update before label (before label ++ [item]) := by
  rw [chain_exact]
  constructor
  · rintro ⟨middle, selected, produced, continued⟩
    have producedExact := (command_exact _ _ _ _ _ _ _ _ _ _ _).mp produced
    simp [execute] at producedExact
    rcases producedExact with ⟨rfl, rfl⟩
    cases continued
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    refine ⟨_, [], ?_, .nil⟩
    apply (command_exact _ _ _ _ _ _ _ _ _ _ _).mpr
    simp [execute]

/-- Completed outcomes cannot claim that the source was rolled back. -/
theorem answerless_is_not_rollback (label : Bool) (before : World) (item : Atom)
    (template : Entry.Value) (policy : Policy) :
    ¬MinimalRel environment label before [] [] none
      (chain (command "silent-put" item) "unused" template)
      Frame.empty [] before (policy := policy) := by
  intro run
  have same := ((answerless_effect_exact _ _ _ _ _ _ _ _ _ _ _ _).mp run).2
  have atLabel := congrFun same label
  have lengths := congrArg List.length atLabel
  simp at lengths

def aliasedEnvironment : WorldEnvironment Bool World :=
  { environment with services := { services with contextPayload := fun _ => .int 0 } }

def twoStores : World := fun label => if label then [.symbol "right"] else [.symbol "left"]

private theorem aliased_read (child : Bool) (policy : Policy) :
    MinimalRel aliasedEnvironment false twoStores [] [] none
      (inSpace (command "read" (.symbol "ignored")) (.int 0)) Frame.empty
      ((twoStores child).map (fun value => (Entry.Value.ofAtom value, Frame.empty)))
      twoStores (policy := policy) := by
  apply in_space_exact.mpr
  refine ⟨child, rfl, ?_⟩
  apply Stateful.InvocationRel.embedded
  · simp [Minimal.HostCall, command, native, Entry.Value.erase, aliasedEnvironment, environment]
  · simp [command, native, Entry.Value.erase, Minimal.embeddedInstruction]
  · rw [Frame.read_empty]
    apply native_exact.mpr
    simp [aliasedEnvironment, services, execute, Entry.Value.erase]

/-- Equal host handles do not distinguish worlds: identical source syntax
admits both stores' answers. Injectivity is a real premise of named-space
identification, not something syntax alone provides. -/
theorem aliased_handles_have_distinct_answers (policy : Policy) :
    MinimalRel aliasedEnvironment false twoStores [] [] none
        (inSpace (command "read" (.symbol "ignored")) (.int 0)) Frame.empty
        [(.symbol "left", Frame.empty)] twoStores (policy := policy) ∧
    MinimalRel aliasedEnvironment false twoStores [] [] none
        (inSpace (command "read" (.symbol "ignored")) (.int 0)) Frame.empty
        [(.symbol "right", Frame.empty)] twoStores (policy := policy) ∧
      (Entry.Value.symbol "left" ≠ Entry.Value.symbol "right") := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [twoStores, Entry.Value.ofAtom] using aliased_read false policy
  · simpa [twoStores, Entry.Value.ofAtom] using aliased_read true policy
  · intro same
    have erased := congrArg Entry.Value.erase same
    simp [Entry.Value.erase] at erased

end Mettapedia.Languages.MeTTa.ContextualTransform.HEWorldControls
