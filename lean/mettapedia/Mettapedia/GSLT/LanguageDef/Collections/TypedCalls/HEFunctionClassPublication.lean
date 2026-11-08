import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEScopedFunctionPublication
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEClosedAliasRetirement
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEFormalOperatorPublication

/-!
# Source operator completion joined to scoped type-class publication

The first type constraint and actual symbol operator cast construct the
selected class, including a freshly queried second name. The resulting raw
record and marked environment feed the executable class-local projection.
The complete pending argument packet is substituted coherently afterwards.

The source symbol query uses the explicitly named scoped declaration-reader
profile. Whole native stack projection additionally needs its caller-retention
invariant and unresolved-class cases; neither is inferred from the freshness
scope. No complete expression-run equality is supplied as an assumption.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEFunctionClassPublication

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Spec.Eval Spec.Eval.Completed Spec.Type.Presentation Spec.Bindings.ScopeObservation
open HEOperatorAliasPublication (arrow)
open HEClosedAliasRetirement

/-- The operator run earns the source class used by projection. The
projected frame's certificate is constructed, not assumed as a boundary
premise, and the full marked payload action is derived from that same class. -/
theorem source_operator_publication {Context World : Type} (environment : WorldEnvironment Context World)
    (lookup : environment.lookup = scopedLookup) (policy : Policy)
    (label : Context) (world : World) (live : List Atom) (scope retained : List String)
    (caller : Frame) (head original left : String) (front suffix : List String)
    (value : Atom) (closed : TypeSubst.typeVars value = [])
    (notUndefined : value ≠ Atom.undefinedType) (notAtom : value ≠ Atom.atomType)
    (notEmpty : head ≠ "Empty") (leftFresh : left ∉ specBindingVars caller.bindings)
    (declared : getAtomTypes (environment.view world label) (.symbol head) = [arrow front suffix original]) :
    ∃ (right : String) (selected completed published : Frame),
      Frame.TypeRenewRel policy (.var left) value caller selected ∧
      Stateful.AtomRel environment label world live scope (.symbol head) (arrow front suffix left) selected
        [(.symbol head, completed)] world (policy := policy) ∧
      completed.bindings = (HEFreshRangeFrame.extend caller.bindings left value).addEquality left right ∧
      completed.environment = (right, Entry.Value.ofAtom value) :: (left, Entry.Value.ofAtom value) :: caller.environment ∧
      projectBindings retained left right completed.bindings = some published.bindings ∧
      projectEnvironment retained left right completed.environment = published.environment ∧
      (∀ payload, expose retained left right completed payload =
        Entry.Value.substitute .preserve (classValuation retained left right (Entry.Value.ofAtom value)) payload) ∧
      right ≠ left ∧ right ∉ specBindingVars caller.bindings := by
  obtain ⟨right, selected, completed, renewed, selectedBindings, _, run, bindings, annotated, allocated⟩ :=
    HEFormalOperatorPublication.formal_scoped_source environment lookup policy label world live scope
      caller head original left front suffix value closed notUndefined notAtom notEmpty leftFresh declared
  have notSelected : right ∉ specBindingVars selected.bindings := by
    intro present
    exact allocated (by simp [invocationTypeScope, present])
  have rightFresh : right ∉ specBindingVars caller.bindings := by
    intro present
    apply notSelected
    rw [selectedBindings]
    simp only [HEFreshRangeFrame.extend, specBindingVars, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at present ⊢
    tauto
  have different : right ≠ left := by
    intro same
    apply notSelected
    rw [same, selectedBindings]
    simp [HEFreshRangeFrame.extend, specBindingVars]
  have valueClosed : TypeSubst.typeVars (Entry.Value.ofAtom value).erase = [] := by simpa using closed
  obtain ⟨published, raw, marked⟩ := projected_frame retained caller completed left right
    (Entry.Value.ofAtom value) valueClosed leftFresh rightFresh (by simpa using bindings) annotated
  exact ⟨right, selected, completed, published, renewed, run, bindings, annotated, raw, marked,
    expose_class retained completed left right (Entry.Value.ofAtom value) caller.environment
      (Ne.symm different) annotated, different, rightFresh⟩

/-- Publication is one coherent operation on the actual pending packet.
Administrative instruction names must survive its partial class action. -/
theorem pending_packet (retained : List String) (completed : Frame) (left right : String)
    (value : Entry.Value) (rest : Entry.Value.Environment) (different : left ≠ right)
    (environment : completed.environment = (right, value) :: (left, value) :: rest)
    (callback : GroundedValue) (subject : Entry.Value) (arguments parameterAndRange : List Entry.Value)
    (expected context operator : Entry.Value) (answers unpacked result : String)
    (answersLeft : answers ≠ left) (answersRight : answers ≠ right)
    (unpackedLeft : unpacked ≠ left) (unpackedRight : unpacked ≠ right)
    (resultLeft : result ≠ left) (resultRight : result ≠ right) :
    expose retained left right completed
      (HEScopedFunctionPublication.pending callback subject arguments parameterAndRange expected context operator
        answers unpacked result) =
      let read := Entry.Value.substitute .preserve (classValuation retained left right value)
      HEScopedFunctionPublication.pending callback (read subject) (arguments.map read)
        (parameterAndRange.map read) (read expected) (read context) (read operator) answers unpacked result := by
  rw [expose_class retained completed left right value rest different environment]
  exact HEScopedFunctionPublication.substitute_pending _ callback subject arguments parameterAndRange
    expected context operator answers unpacked result
    (classValuation_fixes_outside retained left right answers value answersLeft answersRight)
    (classValuation_fixes_outside retained left right unpacked value unpackedLeft unpackedRight)
    (classValuation_fixes_outside retained left right result value resultLeft resultRight)

/-- Expression demand enters through delivery regardless of the operand's
existing mark. The frame read remains the real annotated source read. -/
theorem expression_argument {Context World : Type} (environment : WorldEnvironment Context World)
    (policy : Policy) (label : Context) (world : World) (live : List Atom) (scope : List String)
    (before : Frame) (status : Entry.Status) (children : List Entry.Value) :
    Stateful.AtomRel environment label world live scope (.expression status children) Atom.expressionType before
      [(before.read policy (.expression status children), before)] world (policy := policy) := by
  apply Stateful.AtomRel.delivered
  by_cases stopped : IsEmptyOrErrorRel (before.read policy (.expression status children)).erase
  · exact .stopped stopped
  · apply Entry.Rel.pass stopped
    · simp only [Frame.read, Entry.Value.substitute, Entry.Value.erase]
      exact .expression _
    · exact Or.inr (Or.inl rfl)

/-- Both published Expression formals deliver their original operands.
The reads are a binding condition, not an assumption about a child run. -/
theorem expression_arguments {Context World : Type} (environment : WorldEnvironment Context World)
    (policy : Policy) (label : Context) (world : World) (live : List Atom) (scope : List String)
    (before : Frame) (firstStatus secondStatus : Entry.Status) (first second : List Entry.Value)
    (firstFixed : before.read policy (.expression firstStatus first) = .expression firstStatus first)
    (secondFixed : before.read policy (.expression secondStatus second) = .expression secondStatus second) :
    Stateful.ArgumentsRel environment label world live scope
      [(.expression firstStatus first, Atom.expressionType), (.expression secondStatus second, Atom.expressionType)]
      before [(Entry.Value.argumentPacket [.expression firstStatus first, .expression secondStatus second], before)]
      world (policy := policy) := by
  have firstRun := expression_argument environment policy label world
    (argumentScope [(.expression secondStatus second, Atom.expressionType)] ++ live) scope before firstStatus first
  have secondRun := expression_argument environment policy label world
    (argumentScope [] ++ (Entry.Value.expression firstStatus first).erase :: live) scope before secondStatus second
  rw [firstFixed] at firstRun
  rw [secondFixed] at secondRun
  have tail : Stateful.ArgumentsRel environment label world ((Entry.Value.expression firstStatus first).erase :: live)
      scope [(.expression secondStatus second, Atom.expressionType)] before
      [(Entry.Value.argumentPacket [.expression secondStatus second], before)] world (policy := policy) := by
    apply Stateful.ArgumentsRel.cons secondRun
    simpa only [List.map_cons, List.map_nil, List.append_nil, argumentPrepend_packet] using
      (Stateful.ArgumentBranchesRel.continuing (head := (.expression secondStatus second, before))
        (by simp [ArgumentStopped]) (Stateful.ArgumentsRel.nil (frame := before)) Stateful.ArgumentBranchesRel.nil)
  apply Stateful.ArgumentsRel.cons firstRun
  simpa only [List.map_cons, List.map_nil, List.append_nil, argumentPrepend_packet] using
    (Stateful.ArgumentBranchesRel.continuing (head := (.expression firstStatus first, before))
      (by simp [ArgumentStopped]) tail Stateful.ArgumentBranchesRel.nil)

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEFunctionClassPublication
