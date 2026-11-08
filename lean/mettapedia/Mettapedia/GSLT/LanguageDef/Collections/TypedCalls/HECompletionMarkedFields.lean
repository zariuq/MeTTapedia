import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECompletionEntry
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEOpenSyntaxBinding

/-!
# Source capture and return of fields admitted by the marked-ready gate

The native gate checks every marked expression node before it treats a ready
argument as a value. Its selected nonempty expression fields are therefore
held too. A certified caller's actual materialization earns read stability,
even with free variables; fresh source capture then retains the field and
returns it without a second query. This is the marked-ready branch, not the
unmarked constructor-normal-form or whole source-analysis theorem.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECompletionMarkedFields

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open Spec.Eval Spec.Eval.Completed Spec.Type.Presentation Spec.Bindings.ScopeObservation
open HECompletionEntry

theorem marked_field {fields : List Entry.Value} {index : Nat} {field : Entry.Value}
    (checked : markedThroughout (.expression .held fields) = true)
    (selected : fields[index]? = some field) : markedThroughout field = true := by
  have nonempty : fields ≠ [] := by intro empty; subst fields; simp at selected
  have all : markedFields fields = true := by cases fields <;> simp_all [markedThroughout]
  exact List.all_eq_true.mp (by simpa only [markedFields_all] using all) field (List.mem_of_getElem? selected)

theorem selected_nonempty_is_held {fields : List Entry.Value} {index : Nat}
    {status : Entry.Status} {head : Entry.Value} {tail : List Entry.Value}
    (checked : markedThroughout (.expression .held fields) = true)
    (selected : fields[index]? = some (.expression status (head :: tail))) : status = .held := by
  have field := marked_field checked selected
  cases status <;> simp_all [markedThroughout]

/-- This is derived from the certified caller's materialization, not from a
groundness premise or a separately assumed field-read equality. -/
theorem materialized_field_unassigned (policy : Policy) (frame : Frame) (input : Entry.Value)
    (status : Entry.Status) (fields : List Entry.Value) (index : Nat) (field : Entry.Value)
    (materialized : frame.read policy input = .expression status fields)
    (selected : fields[index]? = some field) : FrameUnassignedOn frame field.erase := by
  have parent := FrameUnassignedOn.after_read policy frame input
  rw [materialized] at parent
  intro name occurs
  apply parent name
  simp only [Entry.Value.erase, TypeSubst.typeVars]
  exact Freshness.typeVars_mem_typeVarsList_of_mem
    (List.mem_map.mpr ⟨field, List.mem_of_getElem? selected, rfl⟩) name occurs

theorem held_entry (policy : Policy) (reuse : policy.reentry = .reuse)
    (fields : List Entry.Value) (expected : Atom) :
    Entry.Rel policy.reentry .held (Entry.Value.expression .held fields).erase expected .deliver := by
  rw [reuse]
  obtain ⟨action, entry⟩ := Entry.total .reuse .held (.expression (fields.map Entry.Value.erase)) expected
  have same := Entry.held_expression_exact entry
  subst action
  simpa only [Entry.Value.erase] using entry

/-- An actual source binder captures an admitted, materialized held field.
The body variable is then delivered under the reached source frame. -/
theorem held_capture_source {Context World : Type} (environment : WorldEnvironment Context World)
    (label : Context) (world : World) (policy : Policy) (reuse : policy.reentry = .reuse)
    (live : List Atom) (scope : List String) (before : Frame) (fields : List Entry.Value)
    (unassigned : FrameUnassignedOn before (Entry.Value.expression .held fields).erase)
    (name : String) (fresh : name ∉ specBindingVars before.bindings)
    (absent : name ∉ TypeSubst.typeVars (Entry.Value.expression .held fields).erase) (expected : Atom) :
    ∃ after : Frame,
      Entry.Value.UnifyRel policy.rebuilding before.environment (.expression .held fields) (.var name) after.environment ∧
      after.read policy (.var name) = .expression .held fields ∧
      Stateful.AtomRel environment label world live scope (.var name) expected after
        [(.expression .held fields, after)] world (policy := policy) := by
  let value : Entry.Value := .expression .held fields
  let after := HEFreshSyntaxBinding.bindFrame policy before name value fresh absent
  have fixed : before.read policy value = value := unassigned.read_eq policy
  have bound := HEOpenSyntaxBinding.source_fixed_nonvariable policy before name value fresh absent fixed
    (by intro other impossible; simp [value, Entry.Value.erase] at impossible)
  have read := HEOpenSyntaxBinding.bound_read_fixed policy policy before name value fresh absent fixed
  have readAfter : after.read policy (.var name) = value := read
  have entered : Entry.Rel policy.reentry (after.read policy (.var name)).status
      (after.read policy (.var name)).erase expected .deliver := by
    rw [readAfter]
    exact held_entry policy reuse fields expected
  have delivered := Stateful.AtomRel.delivered (environment := environment) (label := label) (world0 := world)
    (live := live) (scope := scope) (value := .var name) (expected := expected) (frame := after) (policy := policy) entered
  exact ⟨after, bound, readAfter, by simpa only [readAfter] using delivered⟩

/-- The source-ready input gate earns the status used by capture; parent
readiness or a nominal whole-value type alone is not used. -/
theorem admitted_marked_field_capture {Context World : Type} (environment : WorldEnvironment Context World)
    (label : Context) (world : World) (policy : Policy) (reuse : policy.reentry = .reuse)
    (live : List Atom) (scope : List String) (before : Frame) (input : Entry.Value)
    (symbolAllowed : String → Bool) (normalForm : Entry.Value → Bool)
    (fields : List Entry.Value) (index : Nat) (status : Entry.Status) (head : Entry.Value) (tail : List Entry.Value)
    (materialized : before.read policy input = .expression .held fields)
    (admitted : readyOperand symbolAllowed normalForm (.expression .held fields) = value)
    (selected : fields[index]? = some (.expression status (head :: tail)))
    (name : String) (fresh : name ∉ specBindingVars before.bindings)
    (absent : name ∉ TypeSubst.typeVars (Entry.Value.expression status (head :: tail)).erase) (expected : Atom) :
    ∃ after : Frame,
      Entry.Value.UnifyRel policy.rebuilding before.environment (.expression status (head :: tail)) (.var name) after.environment ∧
      after.read policy (.var name) = .expression status (head :: tail) ∧
      Stateful.AtomRel environment label world live scope (.var name) expected after
        [(.expression status (head :: tail), after)] world (policy := policy) := by
  have checked : markedThroughout (.expression .held fields) = true := by
    simp only [readyOperand] at admitted
    split at admitted
    next checked => exact checked
    next => cases admitted
  have held := selected_nonempty_is_held checked selected
  subst status
  apply held_capture_source environment label world policy reuse live scope before (head :: tail)
  · exact materialized_field_unassigned policy before input .held fields index _ materialized selected
  · exact fresh
  · exact absent

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECompletionMarkedFields
