import Mettapedia.Languages.MeTTa.ContextualTransform.HEStatefulContexts

/-!
# HE completion, typed re-entry and named-space contexts

Completed native values and emitted code are different producer contracts.
Only the former has a pure return/type gate. These exact source laws retain
the reached world and make space-handle identification explicit. They do not
assert that every operation named transform is a completed-value producer.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.ContextualTransform.HEReturnAndSpaces

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Spec.Type Spec.Eval Spec.Eval.Completed Spec.Eval.Completed.Stateful

variable {Context World : Type}

theorem completed_return_exact
    {environment : WorldEnvironment Context World} {label : Context}
    {live : List Atom} {scope : List String} {caller : Option Atom} {policy : Policy}
    {original value : Entry.Value} {expected : Atom} {frame : Frame}
    {before after : World} {results : List Result} :
    BoundaryRel environment label before live scope caller
        (.native original (some expected) .completed) value frame results after
        (policy := policy) ↔
      after = before ∧ NativeCompletedReturnRel (environment.view before label)
        (environment.lookup (invocationTypeScope scope live original.erase expected frame.bindings)
          (environment.view before label)) policy value expected frame results := by
  constructor
  · intro run
    cases run with
    | nativeCompletedReturn typed => exact ⟨rfl, typed⟩
  · rintro ⟨rfl, typed⟩
    exact .nativeCompletedReturn typed

theorem completed_keep_exact
    {environment : WorldEnvironment Context World} {label : Context}
    {live : List Atom} {scope : List String} {caller : Option Atom} {policy : Policy}
    {original value : Entry.Value} {expected : Atom} {frame : Frame}
    {before after : World} {results : List Result}
    (held : CompletedNativeKeepRel value.erase expected) :
    BoundaryRel environment label before live scope caller
        (.native original (some expected) .completed) value frame results after
        (policy := policy) ↔ results = [(value, frame)] ∧ after = before := by
  rw [completed_return_exact]
  constructor
  · rintro ⟨same, returned⟩
    cases returned with
    | keep => exact ⟨rfl, same⟩
    | cast cannotKeep _ _ => exact (cannotKeep held).elim
  · rintro ⟨rfl, rfl⟩
    exact ⟨rfl, .keep held⟩

/-- Undefined demand is not a request to execute a producer-completed value. -/
theorem completed_undefined_exact
    {environment : WorldEnvironment Context World} {label : Context}
    {live : List Atom} {scope : List String} {caller : Option Atom} {policy : Policy}
    {original value : Entry.Value} {frame : Frame}
    {before after : World} {results : List Result} :
    BoundaryRel environment label before live scope caller
        (.native original (some Atom.undefinedType) .completed) value frame results after
        (policy := policy) ↔ results = [(value, frame)] ∧ after = before :=
  completed_keep_exact (Or.inr (Or.inl rfl))

/-- The concrete cast is performed against the reached named space. It can
refine answer frames or emit structured errors, but it cannot change a world. -/
theorem completed_cast_exact
    {environment : WorldEnvironment Context World} {label : Context}
    {live : List Atom} {scope : List String} {caller : Option Atom} {policy : Policy}
    {original value : Entry.Value} {expected : Atom} {frame : Frame}
    {before after : World} {results : List Result}
    (notHeld : ¬CompletedNativeKeepRel value.erase expected) :
    BoundaryRel environment label before live scope caller
        (.native original (some expected) .completed) value frame results after
        (policy := policy) ↔
      after = before ∧ ∃ raw,
        TypeCastBatchRel (environment.view before label) value.erase expected frame.bindings raw
          (lookup := environment.lookup
            (invocationTypeScope scope live original.erase expected frame.bindings)
            (environment.view before label)) (matching := policy.matching.Rel) ∧
        List.Forall₂ (CastResultRel policy (environment.lookup
            (invocationTypeScope scope live original.erase expected frame.bindings)
            (environment.view before label)) frame value expected) raw results := by
  rw [completed_return_exact]
  constructor
  · rintro ⟨same, returned⟩
    cases returned with
    | keep kept => exact (notHeld kept).elim
    | cast _ cast mapped => exact ⟨same, _, cast, mapped⟩
  · rintro ⟨same, raw, cast, mapped⟩
    exact ⟨same, .cast notHeld cast mapped⟩

/-- Ordinary emitted code uses its producer boundary first, then the typed
caller continuation. These are allowed to execute and retain further effects. -/
theorem emitted_return_exact
    {environment : WorldEnvironment Context World} {label : Context}
    {live : List Atom} {scope : List String} {caller : Option Atom} {policy : Policy}
    {original value : Entry.Value} {expected : Atom} {frame : Frame}
    {before after : World} {results : List Result} :
    BoundaryRel environment label before live scope caller
        (.native original (some expected) .emitted) value frame results after
        (policy := policy) ↔
      ∃ middle produced,
        BoundaryRel environment label before (expected :: live) scope (some original.erase)
          .producer value frame produced middle (policy := policy) ∧
        BoundaryBatchRel environment label middle live scope caller (.returned original expected)
          produced results after (policy := policy) := by
  constructor
  · intro run
    cases run with
    | nativeEmittedReturn produced resumed => exact ⟨_, _, produced, resumed⟩
  · rintro ⟨middle, produced, evaluated, resumed⟩
    exact .nativeEmittedReturn evaluated resumed

def native (name function arguments : Entry.Value) : Entry.Value :=
  .expression .active [.symbol "call-native", name, function, arguments]

theorem native_exact
    {environment : WorldEnvironment Context World} {label : Context}
    {live : List Atom} {scope : List String} {caller : Option Atom} {policy : Policy}
    {name function arguments : Entry.Value} {frame : Frame}
    {before after : World} {results : List Result} :
    MinimalRel environment label before live scope caller (native name function arguments)
        frame results after (policy := policy) ↔
      environment.services.nativeCall label before name.erase function.erase arguments.erase
        frame results after := by
  constructor
  · intro run
    generalize shaped : native name function arguments = term at run
    cases run <;> simp_all [native, Minimal.embeddedInstruction]
    subst term
    simp_all [Entry.Value.erase]
  · intro executed
    exact .native executed

/-- A native source inside any compiled chain context executes before its
saved continuations. Its effects and each result's frame survive that handoff. -/
theorem contextual_native_exact
    {environment : WorldEnvironment Context World} {label : Context}
    {live : List Atom} {scope : List String} {caller : Option Atom} {policy : Policy}
    (contexts : HEStatefulContexts.Contexts)
    {name function arguments : Entry.Value} {frame : Frame}
    {before after : World} {results : List Result} :
    MinimalRel environment label before live scope caller
        (HEStatefulContexts.plug contexts (native name function arguments)) frame results after
        (policy := policy) ↔
      ∃ middle produced,
        environment.services.nativeCall label before name.erase function.erase arguments.erase
          frame produced middle ∧
        HEStatefulContexts.Resume environment label scope policy
          (HEStatefulContexts.compile contexts (native name function arguments) live caller).stack
          middle produced results after := by
  rw [HEStatefulContexts.context_exact]
  simp only [native_exact]

def inSpace (operand : Entry.Value) (payload : GroundedValue) : Entry.Value :=
  .expression .active [.symbol "evalc", operand, .grounded payload]

/-- A payload may identify more than one label unless the host's handle
representation is injective. Preserve that distinction in the source law. -/
theorem in_space_exact
    {environment : WorldEnvironment Context World} {label : Context}
    {live : List Atom} {scope : List String} {caller : Option Atom} {policy : Policy}
    {operand : Entry.Value} {payload : GroundedValue} {frame : Frame}
    {before after : World} {results : List Result} :
    MinimalRel environment label before live scope caller (inSpace operand payload)
        frame results after (policy := policy) ↔
      ∃ child, environment.services.contextPayload child = payload ∧
        InvocationRel environment child before live scope caller (frame.read policy operand)
          frame results after (policy := policy) := by
  constructor
  · intro run
    generalize shaped : inSpace operand payload = term at run
    cases run <;> simp_all [inSpace, Minimal.embeddedInstruction]
    · subst term
      simp_all [Entry.Value.erase]
    · exact ⟨_, rfl, by assumption⟩
  · rintro ⟨child, rfl, executed⟩
    exact .evalc executed

theorem in_named_space_exact
    {environment : WorldEnvironment Context World} {label child : Context}
    {live : List Atom} {scope : List String} {caller : Option Atom} {policy : Policy}
    {operand : Entry.Value} {frame : Frame} {before after : World} {results : List Result}
    (distinct : Function.Injective environment.services.contextPayload) :
    MinimalRel environment label before live scope caller
        (inSpace operand (environment.services.contextPayload child)) frame results after
        (policy := policy) ↔
      InvocationRel environment child before live scope caller (frame.read policy operand)
        frame results after (policy := policy) := by
  rw [in_space_exact]
  constructor
  · rintro ⟨other, same, executed⟩
    have equal := distinct same
    subst other
    exact executed
  · intro executed
    exact ⟨child, rfl, executed⟩

def typedInSpace (operand : Entry.Value) (expected : Atom)
    (payload : GroundedValue) : Entry.Value :=
  .expression .active [.symbol "metta", operand, Entry.Value.ofAtom expected, .grounded payload]

theorem typed_in_space_exact
    {environment : WorldEnvironment Context World} {label : Context}
    {live : List Atom} {scope : List String} {caller : Option Atom} {policy : Policy}
    {operand : Entry.Value} {expected : Atom} {payload : GroundedValue} {frame : Frame}
    {before after : World} {results : List Result} :
    MinimalRel environment label before live scope caller (typedInSpace operand expected payload)
        frame results after (policy := policy) ↔
      ∃ child, environment.services.contextPayload child = payload ∧
        AtomRel environment child before live scope operand expected frame results after
          (policy := policy) := by
  constructor
  · intro run
    generalize shaped : typedInSpace operand expected payload = term at run
    cases run <;> simp_all [typedInSpace, Minimal.embeddedInstruction]
    · subst term
      simp_all [Entry.Value.erase]
    · rcases shaped with ⟨rfl, rfl, rfl, rfl⟩
      simp_all only [Entry.Value.erase_ofAtom]
      exact ⟨_, rfl, by assumption⟩
  · rintro ⟨child, rfl, executed⟩
    exact .metta (by simpa only [Entry.Value.erase_ofAtom] using executed)

end Mettapedia.Languages.MeTTa.ContextualTransform.HEReturnAndSpaces
