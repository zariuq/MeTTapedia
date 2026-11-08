import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEOpenSyntaxBinding

/-!
# Publishing an isolated private type assignment

An isolated fresh assignment is a concrete fragment of scoped publication:
the removed name is substituted into emitted code, then removed from the
binding record. The old caller may contain arbitrary aliases and annotated
values. Its complete support excludes the new name, which makes the final
substitution through retained cells an identity, including every readiness
mark.

The fragment does not drop a member of a shared alias class. General native
class projection and unresolved-alias retargeting require their own laws.
This module proves a boundary operation, not that evaluation commutes with
unrestricted materialization.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEPrivateTypePublication

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed Spec.Type.Presentation Spec.Type.RuntimeRefinement
open Spec.Type.Presentation.BindingTheory Spec.Bindings.ScopeObservation
open HEFreshSyntaxBinding
open private lookup_eq_some_of_mem_of_nodup
  from Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.Theory

/-- Complete source freshness excludes the name from both stored keys and
the complete annotated values of the certified caller environment. -/
theorem environment_avoids (before : Frame) (name : String)
    (fresh : name ∉ specBindingVars before.bindings)
    (row : String × Entry.Value) (stored : row ∈ before.environment) :
    row.1 ≠ name ∧ name ∉ TypeSubst.typeVars row.2.erase := by
  have erased : (row.1, row.2.erase) ∈ Entry.Value.eraseEnvironment before.environment :=
    List.mem_map.mpr ⟨row, stored, rfl⟩
  have selected := lookup_eq_some_of_mem_of_nodup before.certified.normal.1 erased
  have different : row.1 ≠ name := by
    intro same
    rw [same, before.certified.lookup_none_of_outside fresh] at selected
    contradiction
  refine ⟨different, ?_⟩
  have absent := before.certified.avoids_outside fresh (.var row.1)
    (by simpa only [TypeSubst.typeVars, List.mem_singleton] using Ne.symm different)
  simpa only [TypeSubst.apply, selected, Option.getD_some] using absent

theorem substitute_one_away (rebuilding : Entry.RebuildPolicy) (name : String)
    (replacement value : Entry.Value) (absent : name ∉ TypeSubst.typeVars value.erase) :
    Entry.Value.substitute rebuilding (Entry.Value.resolve [(name, replacement)]) value = value := by
  apply Entry.Value.substitute_of_fixed_variables
  intro other member
  have different : other ≠ name := by intro same; exact absent (same ▸ member)
  simp only [Entry.Value.resolve, List.lookup_cons, beq_eq_false_iff_ne.mpr different,
    List.lookup_nil, Option.getD_none]

/-- A genuinely fresh closed assignment adds one annotated row without
rewriting the caller's keys, aliases, values or readiness marks. -/
theorem fresh_environment (policy : Policy) (before : Frame) (name : String)
    (value : Entry.Value) (fresh : name ∉ specBindingVars before.bindings)
    (closed : TypeSubst.typeVars value.erase = []) :
    Entry.Value.bind policy.rebuilding before.environment name value =
      (name, value) :: before.environment := by
  unfold Entry.Value.bind
  rw [ground_substitution policy.rebuilding _ value closed]
  dsimp only
  have filtered : before.environment.filter (fun row => row.1 != name) = before.environment := by
    apply List.filter_eq_self.mpr
    intro row member
    simpa using (environment_avoids before name fresh row member).1
  rw [filtered]
  apply congrArg (List.cons (name, value))
  conv_rhs => rw [← List.map_id before.environment]
  apply List.map_congr_left
  intro row member
  exact congrArg (Prod.mk row.1)
    (substitute_one_away policy.rebuilding name value row.2
      (environment_avoids before name fresh row member).2)

/-- Remove one isolated assignment. The fresh-source theorem below, rather
than this operation alone, justifies leaving the equality authority intact. -/
def dropAssignment (name : String) (bindings : Bindings) : Bindings :=
  { bindings with assignments := bindings.assignments.filter (fun row => row.1 != name) }

def dropEnvironment (name : String) (environment : Entry.Value.Environment) : Entry.Value.Environment :=
  environment.filter (fun row => row.1 != name)

/-- The direct payload traversal substitutes only the departing name and
preserves the original expression and nested readiness marks. -/
def exposeName (name : String) (frame : Frame) (payload : Entry.Value) : Entry.Value :=
  Entry.Value.substitute .preserve
    (fun other => if other = name then frame.read Policy.ready (.var name) else .var other) payload

theorem drop_fresh_assignment (before : Bindings) (name : String) (value : Atom)
    (fresh : name ∉ specBindingVars before) :
    dropAssignment name (HEFreshRangeFrame.extend before name value) = before := by
  have filtered : before.assignments.filter (fun row => row.1 != name) = before.assignments := by
    apply List.filter_eq_self.mpr
    intro row stored
    have different : row.1 ≠ name := by
      intro same
      apply fresh
      simp only [specBindingVars, List.mem_append, List.mem_flatMap]
      exact Or.inl ⟨row, stored, by simp [same]⟩
    simpa using different
  simp [dropAssignment, HEFreshRangeFrame.extend, List.filter_append, filtered]

theorem drop_fresh_environment (before : Frame) (name : String) (value : Entry.Value)
    (fresh : name ∉ specBindingVars before.bindings) :
    dropEnvironment name ((name, value) :: before.environment) = before.environment := by
  simp only [dropEnvironment, List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  apply List.filter_eq_self.mpr
  intro row member
  simpa using (environment_avoids before name fresh row member).1

/-- The final traversal through retained annotated cells is also an
identity. This is stronger than equality after erasing their marks. -/
theorem retained_cells_unchanged (before : Frame) (name : String) (replacement : Entry.Value)
    (fresh : name ∉ specBindingVars before.bindings) (rebuilding : Entry.RebuildPolicy) :
    before.environment.map (fun row =>
      (row.1, Entry.Value.substitute rebuilding (Entry.Value.resolve [(name, replacement)]) row.2)) =
      before.environment := by
  conv_rhs => rw [← List.map_id before.environment]
  apply List.map_congr_left
  intro row member
  exact congrArg (Prod.mk row.1)
    (substitute_one_away rebuilding name replacement row.2
      (environment_avoids before name fresh row member).2)

theorem exposed_fresh_binding (policy : Policy) (before : Frame) (name : String)
    (value payload : Entry.Value) (fresh : name ∉ specBindingVars before.bindings)
    (closed : TypeSubst.typeVars value.erase = []) :
    exposeName name (bindFrame policy before name value fresh (by simp [closed])) payload =
      Entry.Value.substitute .preserve (Entry.Value.resolve [(name, value)]) payload := by
  unfold exposeName
  rw [bound_read policy before name value fresh closed Policy.ready]
  congr 1
  funext other
  by_cases same : other = name
  · simp [same, Entry.Value.resolve]
  · simp only [if_neg same, Entry.Value.resolve, List.lookup_cons,
      beq_eq_false_iff_ne.mpr same, List.lookup_nil, Option.getD_none]

/-- Source matching earns the actual type instance and annotated frame.
Publishing this isolated instance recovers the exact caller record and
environment. No evaluated expression result is assumed. -/
theorem fresh_closed_type_publication (policy : Policy) (before : Frame) (name : String)
    (actual : Atom) (closed : TypeSubst.typeVars actual = [])
    (notUndefined : actual ≠ Atom.undefinedType) (notAtom : actual ≠ Atom.atomType)
    (fresh : name ∉ specBindingVars before.bindings) :
    ∃ selected : Frame,
      Frame.TypeRenewRel policy actual (.var name) before selected ∧
      selected.bindings = HEFreshRangeFrame.extend before.bindings name actual ∧
      selected.environment = (name, Entry.Value.ofAtom actual) :: before.environment ∧
      dropAssignment name selected.bindings = before.bindings ∧
      dropEnvironment name selected.environment = before.environment ∧
      (∀ payload, exposeName name selected payload =
        Entry.Value.substitute .preserve (Entry.Value.resolve [(name, Entry.Value.ofAtom actual)]) payload) := by
  have valueClosed : TypeSubst.typeVars (Entry.Value.ofAtom actual).erase = [] := by
    simpa using closed
  let selected := bindFrame policy before name (Entry.Value.ofAtom actual) fresh (by simp [closed])
  have exactBindings : selected.bindings = HEFreshRangeFrame.extend before.bindings name actual := by
    simpa only [Entry.Value.erase_ofAtom] using
      binding_keeps_caller policy before name (Entry.Value.ofAtom actual) fresh (by simp [closed])
  have source := HEFreshRangeFrame.source_match before.bindings name actual closed notUndefined notAtom fresh
  have matched : policy.matching.Rel actual (.var name) before.bindings selected.bindings := by
    rw [exactBindings]
    cases policy.matching with
    | raw => exact source
    | finite => exact ⟨source, HEFreshRangeFrame.extended_model before name actual closed fresh⟩
  refine ⟨selected, .unified matched ?_, exactBindings, ?_, ?_, ?_, ?_⟩
  · simpa only [Entry.Value.ofAtom, Entry.Value.erase_ofAtom] using
      source_binding policy before name (Entry.Value.ofAtom actual) fresh valueClosed
  · exact fresh_environment policy before name (Entry.Value.ofAtom actual) fresh valueClosed
  · rw [exactBindings]
    exact drop_fresh_assignment before.bindings name actual fresh
  · change dropEnvironment name (Entry.Value.bind policy.rebuilding before.environment name (Entry.Value.ofAtom actual)) = _
    rw [fresh_environment policy before name (Entry.Value.ofAtom actual) fresh valueClosed]
    exact drop_fresh_environment before name (Entry.Value.ofAtom actual) fresh
  · intro payload
    exact exposed_fresh_binding policy before name (Entry.Value.ofAtom actual) payload fresh valueClosed

namespace Controls

theorem arbitrary_caller_expression_instance (policy : Policy) (before : Frame) (name : String)
    (fresh : name ∉ specBindingVars before.bindings) :
    ∃ selected : Frame,
      Frame.TypeRenewRel policy Atom.expressionType (.var name) before selected ∧
      dropAssignment name selected.bindings = before.bindings ∧
      dropEnvironment name selected.environment = before.environment ∧
      exposeName name selected (.expression .held [.var name, .expression .held [.var name]]) =
        .expression .held [.symbol "Expression", .expression .held [.symbol "Expression"]] := by
  obtain ⟨selected, renewed, _, _, bindings, environment, payload⟩ :=
    fresh_closed_type_publication policy before name Atom.expressionType rfl (by decide) (by decide) fresh
  refine ⟨selected, renewed, bindings, environment, ?_⟩
  rw [payload]
  simp [Entry.Value.substitute, Entry.Value.resolve, Entry.Value.ofAtom,
    Entry.Value.rebuildStatus, Atom.expressionType]

/-- Removing a value row while keeping its alias loses a real constraint.
The isolated-name theorem cannot be extended by ignoring equality classes. -/
theorem alias_assignment_cannot_be_dropped :
    let bindings : Bindings := ⟨[("private", Atom.expressionType)], [("kept", "private")]⟩
    TypeBindingSatisfied (fun _ => .symbol "String") (dropAssignment "private" bindings) ∧
      ¬ TypeBindingSatisfied (fun _ => .symbol "String") bindings := by
  constructor
  · simp [dropAssignment, TypeBindingSatisfied]
  · intro model
    have equation := model.1 "private" Atom.expressionType (by simp)
    simp [applyTypeValuation, Atom.expressionType] at equation

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEPrivateTypePublication
