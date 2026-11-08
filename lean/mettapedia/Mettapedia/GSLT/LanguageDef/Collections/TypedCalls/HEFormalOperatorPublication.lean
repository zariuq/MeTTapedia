import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEOperatorAliasPublication
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEExpectedPrivateTypePublication

/-!
# Authored formal applicability followed by the operator alias cast

The first comparison has the authored variable on the expected side. Its
source-derived frame feeds the actual fresh operator query and repeated-slot
arrow match. This keeps formal applicability distinct from range selection
while delivering the exact annotated packet required by scoped publication.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEFormalOperatorPublication

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open Spec.Eval Spec.Eval.Completed Spec.Type.Presentation Spec.Bindings.ScopeObservation
open HEOperatorAliasPublication (arrow)

theorem formal_packet (policy : Policy) (caller : Frame) (front suffix : List String)
    (left right : String) (value : Atom) (closed : TypeSubst.typeVars value = [])
    (notUndefined : value ≠ Atom.undefinedType) (notAtom : value ≠ Atom.atomType)
    (leftFresh : left ∉ specBindingVars caller.bindings)
    (rightFresh : right ∉ specBindingVars caller.bindings) (different : right ≠ left) :
    ∃ selected after : Frame,
      Frame.TypeRenewRel policy (.var left) value caller selected ∧
      selected.bindings = HEFreshRangeFrame.extend caller.bindings left value ∧
      selected.environment = (left, Entry.Value.ofAtom value) :: caller.environment ∧
      after.bindings = (HEFreshRangeFrame.extend caller.bindings left value).addEquality left right ∧
      after.environment = (right, Entry.Value.ofAtom value) :: (left, Entry.Value.ofAtom value) :: caller.environment ∧
      policy.matching.Rel (arrow front suffix left) (arrow front suffix right)
        selected.bindings after.bindings ∧
      Entry.Value.UnifyRel policy.rebuilding selected.environment
        (Entry.Value.ofAtom (arrow front suffix left)) (Entry.Value.ofAtom (arrow front suffix right))
        after.environment := by
  obtain ⟨selected, renewed, bindings, annotated, _, _⟩ :=
    HEExpectedPrivateTypePublication.fresh_formal policy caller left value closed notUndefined notAtom leftFresh
  have read : selected.read policy (.var left) = Entry.Value.ofAtom value := by
    simp [Frame.read, Entry.Value.substitute, annotated, Entry.Value.resolve]
  have isolated : left ∉ selected.bindings.eqVarsInOrder := by
    rw [bindings]
    exact (HEFreshRangeAlias.extended_private_facts caller.bindings left value leftFresh).2
  have assigned : selected.bindings.lookup left = some (Entry.Value.ofAtom value).erase := by
    rw [bindings, Entry.Value.erase_ofAtom]
    exact (HEFreshRangeAlias.extended_private_facts caller.bindings left value leftFresh).1
  have fresh : right ∉ specBindingVars selected.bindings := by
    rw [bindings]
    simpa [HEFreshRangeFrame.extend, specBindingVars, closed, and_assoc, and_left_comm, and_comm]
      using And.intro rightFresh different
  obtain ⟨after, afterBindings, afterAnnotated, matched, contextual⟩ :=
    HEOperatorAliasPublication.alias_frame policy selected front suffix left right (Entry.Value.ofAtom value)
      (by simpa using closed) read isolated assigned fresh
  refine ⟨selected, after, renewed, bindings, annotated, ?_, ?_, matched, contextual⟩
  · exact afterBindings.trans (congrArg (fun b => b.addEquality left right) bindings)
  · rw [afterAnnotated, annotated]

/-- Actual scoped symbol lookup allocates one fresh name for both repeated
occurrences. The result is a source operator run, not only table algebra. -/
theorem formal_scoped_source {Context World : Type} (environment : WorldEnvironment Context World)
    (lookup : environment.lookup = scopedLookup) (policy : Policy)
    (label : Context) (world : World) (live : List Atom) (scope : List String)
    (caller : Frame) (head original left : String) (front suffix : List String)
    (value : Atom) (closed : TypeSubst.typeVars value = [])
    (notUndefined : value ≠ Atom.undefinedType) (notAtom : value ≠ Atom.atomType)
    (notEmpty : head ≠ "Empty") (leftFresh : left ∉ specBindingVars caller.bindings)
    (declared : getAtomTypes (environment.view world label) (.symbol head) = [arrow front suffix original]) :
    ∃ (right : String) (selected after : Frame),
      Frame.TypeRenewRel policy (.var left) value caller selected ∧
      selected.bindings = HEFreshRangeFrame.extend caller.bindings left value ∧
      selected.environment = (left, Entry.Value.ofAtom value) :: caller.environment ∧
      Stateful.AtomRel environment label world live scope (.symbol head) (arrow front suffix left) selected
        [(.symbol head, after)] world (policy := policy) ∧
      after.bindings = (HEFreshRangeFrame.extend caller.bindings left value).addEquality left right ∧
      after.environment = (right, Entry.Value.ofAtom value) :: (left, Entry.Value.ofAtom value) :: caller.environment ∧
      right ∉ invocationTypeScope
        (invocationTypeScope scope live (.symbol head) (arrow front suffix left) selected.bindings)
        [] (.symbol head) (arrow front suffix left) selected.bindings := by
  obtain ⟨selected, renewed, bindings, annotated, _, _⟩ :=
    HEExpectedPrivateTypePublication.fresh_formal policy caller left value closed notUndefined notAtom leftFresh
  let names := invocationTypeScope scope live (.symbol head) (arrow front suffix left) selected.bindings
  let avoid := invocationTypeScope names [] (.symbol head) (arrow front suffix left) selected.bindings
  let right := instanceName avoid [original] 0 original
  have fresh : right ∉ avoid := instanceName_not_mem avoid [original] 0 original
  have bindingFresh : right ∉ specBindingVars selected.bindings := by
    intro present
    exact fresh (by simp [avoid, invocationTypeScope, present])
  have queried : environment.lookup names (environment.view world label) selected.bindings
      (.symbol head) (arrow front suffix left) [arrow front suffix right] := by
    rw [lookup]
    exact HEOperatorAliasPublication.scoped_query _ selected names head original right front suffix _ declared fresh
  have read : selected.read policy (.var left) = Entry.Value.ofAtom value := by
    simp [Frame.read, Entry.Value.substitute, annotated, Entry.Value.resolve]
  have isolated : left ∉ selected.bindings.eqVarsInOrder := by
    rw [bindings]
    exact (HEFreshRangeAlias.extended_private_facts caller.bindings left value leftFresh).2
  have assigned : selected.bindings.lookup left = some (Entry.Value.ofAtom value).erase := by
    rw [bindings, Entry.Value.erase_ofAtom]
    exact (HEFreshRangeAlias.extended_private_facts caller.bindings left value leftFresh).1
  obtain ⟨after, run, finalBindings, finalEnvironment⟩ :=
    HEOperatorAliasPublication.source_operator environment policy label world live scope
      selected head left right front suffix (Entry.Value.ofAtom value) notEmpty (by simpa using closed)
      read isolated assigned bindingFresh queried
  refine ⟨right, selected, after, renewed, bindings, annotated, run, ?_, ?_, fresh⟩
  · exact finalBindings.trans (congrArg (fun b => b.addEquality left right) bindings)
  · rw [finalEnvironment, annotated]

namespace Controls

theorem expression_formal_packet (policy : Policy) (caller : Frame) (suffix : List String)
    (left right : String) (leftFresh : left ∉ specBindingVars caller.bindings)
    (rightFresh : right ∉ specBindingVars caller.bindings) (different : right ≠ left) :
    ∃ selected after : Frame,
      Frame.TypeRenewRel policy (.var left) Atom.expressionType caller selected ∧
      after.bindings = (HEFreshRangeFrame.extend caller.bindings left Atom.expressionType).addEquality left right ∧
      after.environment = (right, .symbol "Expression") :: (left, .symbol "Expression") :: caller.environment ∧
      Entry.Value.UnifyRel policy.rebuilding selected.environment
        (Entry.Value.ofAtom (arrow ["->"] suffix left))
        (Entry.Value.ofAtom (arrow ["->"] suffix right)) after.environment := by
  obtain ⟨selected, after, renewed, _, _, bindings, annotated, _, contextual⟩ :=
    formal_packet policy caller ["->"] suffix left right Atom.expressionType rfl (by decide) (by decide)
      leftFresh rightFresh different
  exact ⟨selected, after, renewed, bindings,
    by simpa only [Atom.expressionType, Entry.Value.ofAtom] using annotated, contextual⟩

/-- The actual formal matcher does not bind a fresh variable when the
observed type is Undefined. This excluded case is a genuine semantic cut. -/
theorem undefined_does_not_allocate_a_formal_instance :
    matchTypes (.var "t") Atom.undefinedType Bindings.empty 8 = [Bindings.empty] ∧
      Bindings.empty ≠ HEFreshRangeFrame.extend Bindings.empty "t" Atom.undefinedType := by decide +kernel

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEFormalOperatorPublication
