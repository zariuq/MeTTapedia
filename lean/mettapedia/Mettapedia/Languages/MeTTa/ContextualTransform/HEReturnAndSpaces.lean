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
open Spec.Eval.Steps (EquationWork EquationFrontierRel)
open Spec.Bindings.ScopeObservation (specBindingVars)
open Spec.Type.Presentation (TypeSubst)

variable {Context World : Type}

/-- Install a genuinely fresh rule key in the existing contextual readout. The stored
operand is the materialized, annotated operand, not a reconstruction from its erasure. -/
def assignFresh (policy : Policy) (frame : Frame) (key : String) (value : Entry.Value)
    (fresh : key ∉ specBindingVars frame.bindings) (avoids : key ∉ TypeSubst.typeVars value.erase) : Frame :=
  ⟨frame.bindings.assign key value.erase, Entry.Value.bind policy.rebuilding frame.environment key value, by
    rw [Entry.Value.erase_bind]
    exact frame.certified.fresh_assignment key value.erase fresh avoids⟩

theorem assignFresh_reads (policy : Policy) (frame : Frame) (key : String) (value : Entry.Value)
    (fresh : key ∉ specBindingVars frame.bindings) (avoids : key ∉ TypeSubst.typeVars value.erase) :
    (assignFresh policy frame key value fresh avoids).read policy (.var key) = frame.read policy value := by
  apply Entry.Value.assigned_value_exact
  simp [assignFresh, Entry.Value.bind, Frame.read]

/-- Contextual unification against the fresh pattern variable performs exactly this
binding, preserving the annotation of the operand it read. Aliases use their own case. -/
theorem assignFresh_unifies (policy : Policy) (frame : Frame) (key : String) (value : Entry.Value)
    (fresh : key ∉ specBindingVars frame.bindings) (avoids : key ∉ TypeSubst.typeVars value.erase)
    (nonvariable : ∀ name, (frame.read policy value).erase ≠ .var name) :
    Entry.Value.UnifyRel policy.rebuilding frame.environment value (.var key)
      (assignFresh policy frame key value fresh avoids).environment := by
  have absent : key ∉ (Entry.Value.eraseEnvironment frame.environment).keys := by
    apply frame.certified.normal.apply_variable_not_key (.var key) key
    simp [TypeSubst.apply, TypeSubst.typeVars, frame.certified.lookup_none_of_outside fresh]
  have pending : (frame.read policy (.var key)) = .var key := by
    simp [Frame.read, Entry.Value.substitute,
      Entry.Value.resolve_of_not_mem_keys frame.environment key absent]
  have acyclic : key ∉ TypeSubst.typeVars (frame.read policy value).erase := by
    rw [Frame.read, Entry.Value.erase_substitute_environment]
    exact frame.certified.avoids_outside fresh value.erase avoids
  have stable : Entry.Value.bind policy.rebuilding frame.environment key (frame.read policy value) =
      (assignFresh policy frame key value fresh avoids).environment := by
    have twice := frame.read_idempotent policy value
    simp only [Frame.read] at twice
    simp only [assignFresh, Entry.Value.bind, twice, Frame.read]
  apply Entry.Value.UnifyRel.ordinary
  change Entry.Value.AppliedUnifyRel policy.rebuilding frame.environment (frame.read policy value)
    (frame.read policy (.var key)) (assignFresh policy frame key value fresh avoids).environment
  rw [pending, ← stable]
  exact .bindRight nonvariable acyclic

/-- A shared unary head adds no binding. Materializing the two child values again
preserves their full annotations in the same certified frame. -/
theorem unary_unifies (policy : Policy) (frame : Frame) (head : String)
    {left right : Entry.Value} {reached : Entry.Value.Environment}
    (child : Entry.Value.UnifyRel policy.rebuilding frame.environment left right reached) :
    Entry.Value.UnifyRel policy.rebuilding frame.environment
      (.expression .active [.symbol head, left]) (.expression .active [.symbol head, right]) reached := by
  have children : Entry.Value.UnifyRel policy.rebuilding frame.environment
      (frame.read policy left) (frame.read policy right) reached := by
    cases child with
    | ordinary applied =>
      apply Entry.Value.UnifyRel.ordinary
      change Entry.Value.AppliedUnifyRel policy.rebuilding frame.environment
        (frame.read policy (frame.read policy left)) (frame.read policy (frame.read policy right)) reached
      change Entry.Value.AppliedUnifyRel policy.rebuilding frame.environment (frame.read policy left)
        (frame.read policy right) reached at applied
      simpa only [frame.read_idempotent] using applied
  apply Entry.Value.UnifyRel.ordinary
  have readExpression (value : Entry.Value) :
      frame.read policy (.expression .active [.symbol head, value]) =
        .expression .active [.symbol head, frame.read policy value] := by
    cases rebuilder : policy.rebuilding <;>
      simp [Frame.read, Entry.Value.substitute, Entry.Value.rebuildStatus, rebuilder]
  change Entry.Value.AppliedUnifyRel policy.rebuilding frame.environment
    (frame.read policy (.expression .active [.symbol head, left]))
    (frame.read policy (.expression .active [.symbol head, right])) reached
  rw [readExpression, readExpression]
  exact .expression (.cons (.ordinary (.identical rfl)) (.cons children (.nil _)))

/-- `NotReducible` is a return instruction, not the payload of the call. The caller gets
the syntax of the call, with the reached binding frame and no new world change. -/
theorem returned_not_reducible_exact
    {environment : WorldEnvironment Context World} {label : Context}
    {live : List Atom} {scope : List String} {caller : Option Atom} {policy : Policy}
    {original value : Entry.Value} {expected : Atom} {frame : Frame}
    {before after : World} {results : List Result}
    (marker : value.erase = Atom.notReducible) :
    BoundaryRel environment label before live scope caller (.returned original expected)
        value frame results after (policy := policy) ↔
      results = [(original, frame)] ∧ after = before := by
  constructor
  · intro run
    cases run with
    | returned returned =>
        cases returned with
        | notReducible => exact ⟨rfl, rfl⟩
        | stopped failed => simp [marker, Atom.notReducible, IsEmptyOrErrorRel, IsErrorRel, Atom.empty] at failed
        | evaluate ordinary _ _ => exact (ordinary marker).elim
  · rintro ⟨rfl, rfl⟩
    exact .returned (.notReducible marker)

/-- An ordinary equation body can return code. Its evaluation is in the reached world and
under the expected type of the caller, unlike a producer-completed native value. -/
theorem returned_code_exact
    {environment : WorldEnvironment Context World} {label : Context}
    {live : List Atom} {scope : List String} {caller : Option Atom} {policy : Policy}
    {original value : Entry.Value} {expected : Atom} {frame : Frame}
    {before after : World} {results : List Result}
    (ordinary : value.erase ≠ Atom.notReducible)
    (clean : ¬IsEmptyOrErrorRel value.erase) :
    BoundaryRel environment label before live scope caller (.returned original expected)
        value frame results after (policy := policy) ↔
      AtomRel environment label before live scope value expected frame results after
        (policy := policy) := by
  constructor
  · intro run
    cases run with
    | returned returned =>
        cases returned with
        | notReducible marker => exact (ordinary marker).elim
        | stopped stopped => exact (clean stopped).elim
        | evaluate _ _ entered => exact entered
  · exact fun entered => .returned (.evaluate ordinary clean entered)

/-- A complete one-row marker frontier restores the prepared call using a frame certified
by the actual contextual unification. The incoming frame need not be empty or ground. -/
theorem marker_equation_call
    {environment : WorldEnvironment Context World} {label : Context}
    {live : List Atom} {scope : List String} {policy : Policy}
    {call : Entry.Value} {expected : Atom} {frame : Frame} {world : World} {work : EquationWork}
    (clean : ¬IsErrorRel call.erase) (equational : NonGroundedCallRel environment.dispatch call.erase)
    (frontier : EquationFrontierRel (environment.view world label) (expected :: live)
      call.erase frame.bindings [work])
    (marker : work.body = Atom.notReducible) :
    ∃ reached : Frame, reached.bindings = work.bindings ∧
      CallRel environment label world live scope call expected frame [(call, reached)] world
        (policy := policy) := by
  obtain ⟨tables, paired⟩ := Entry.Value.UnifyRel.equation_frontier
    (policy := policy.rebuilding) frame.certified frontier
  cases paired with
  | @cons _ reached _ _ proof rest =>
      cases rest
      let next : Frame := ⟨work.bindings, reached, proof.2⟩
      refine ⟨next, rfl, ?_⟩
      have read : next.read policy (Entry.Value.ofAtom work.body) = .symbol "NotReducible" := by
        simp [marker, Atom.notReducible, Entry.Value.ofAtom, Frame.read, Entry.Value.substitute]
      have producer : BoundaryRel environment label world (expected :: live) scope
          (some call.erase) .producer (next.read policy (Entry.Value.ofAtom work.body)) next
          [(.symbol "NotReducible", next)] world (policy := policy) := by
        rw [read]
        exact .producerRaw (by simp [FunctionPending, Minimal.IsFunction, Entry.Value.erase])
      have returned : BoundaryRel environment label world live scope none (.returned call expected)
          (.symbol "NotReducible") next [(call, next)] world (policy := policy) :=
        (returned_not_reducible_exact (by simp [Atom.notReducible, Entry.Value.erase])).mpr ⟨rfl, rfl⟩
      apply Stateful.CallRel.equations clean equational frontier (by simp)
      simpa only [List.append_nil] using Stateful.EquationBodiesRel.cons
        (rfl : next.bindings = work.bindings) proof.1 producer
        (Stateful.BoundaryBatchRel.single_iff.mpr returned) Stateful.EquationBodiesRel.nil

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

/-- Collection first finishes the actual operand in its reached world. It then
stores one complete binding snapshot per surviving occurrence. A saved prefix
or an unfinished operand cannot be substituted for the completed child. -/
theorem collapse_bind_exact
    {environment : WorldEnvironment Context World} {label : Context}
    {live : List Atom} {scope : List String} {caller : Option Atom} {policy : Policy}
    {operand : Entry.Value} {readiness : Entry.Status} {frame : Frame}
    {before after : World} {results : List Result} :
    MinimalRel environment label before live scope caller
        (.expression readiness [.symbol "collapse-bind", operand]) frame results after (policy := policy) ↔
      ∃ (snapshots : SnapshotServices Context World) (reached : World) (rows : List Result) (packed : Entry.Value),
        environment.services.snapshots = some snapshots ∧
        MinimalRel environment label before live scope caller operand frame rows reached (policy := policy) ∧
        CaptureRowsRel snapshots label reached rows [] packed after ∧ results = [(packed, frame)] := by
  constructor
  · intro source
    generalize shaped : (Entry.Value.expression readiness [.symbol "collapse-bind", operand]) = value at source
    cases source with
    | data terminal =>
      subst value
      simp [Entry.Value.erase, Minimal.embeddedInstruction] at terminal
    | collapseBind provided completed captured =>
      simp at shaped
      obtain ⟨rfl, rfl⟩ := shaped
      exact ⟨_, _, _, _, provided, completed, captured, rfl⟩
    | _ => simp at shaped
  · rintro ⟨_, _, _, _, provided, completed, captured, rfl⟩
    exact .collapseBind provided completed captured

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
