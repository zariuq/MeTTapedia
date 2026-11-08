import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEPrivateTypePublication

/-!
# Retiring names from a fresh resolved two-name class

This is the closed-value fragment of name-wise scope projection. Both names
may disappear, either name may survive, or both may survive. In particular,
removing the assignment's original name while retaining its alias moves the
value to that retained name; deleting only the old assignment would be wrong.

The operations below are checked on an isolated fresh class over an arbitrary
caller. They do not implement unresolved-alias retargeting, nor projection of
an arbitrary native binding graph. The contextual source operator-cast witness
is supplied by the separate source-match construction, not by these filters.
Caller authority is left untouched by this class-local operation. Equality
with a whole-scope name filter additionally requires a caller-retention law;
freshness alone does not establish that law.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEClosedAliasRetirement

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed Spec.Type.Presentation Spec.Bindings.ScopeObservation
open HEPrivateTypePublication

def outsidePair (left right name : String) : Bool := name != left && name != right

def removePair (left right : String) (bindings : Bindings) : Bindings where
  assignments := bindings.assignments.filter (fun row => outsidePair left right row.1)
  equalities := bindings.equalities.filter (fun row =>
    outsidePair left right row.1 && outsidePair left right row.2)

/-- Read the assigned class value before removing either name. An absent
assignment is outside this fragment, not an invented closed type instance. -/
def projectBindings (retained : List String) (left right : String) (bindings : Bindings) : Option Bindings :=
  (bindings.lookup left).map fun value =>
    let rest := removePair left right bindings
    if left ∈ retained then
      let saved := HEFreshRangeFrame.extend rest left value
      if right ∈ retained then saved.addEquality left right else saved
    else if right ∈ retained then HEFreshRangeFrame.extend rest right value else rest

def projectEnvironment (retained : List String) (left right : String)
    (environment : Entry.Value.Environment) : Entry.Value.Environment :=
  environment.filter (fun row => outsidePair left right row.1 || retained.contains row.1)

def expose (retained : List String) (left right : String) (frame : Frame)
    (payload : Entry.Value) : Entry.Value :=
  Entry.Value.substitute .preserve (fun name =>
    if outsidePair left right name || retained.contains name then .var name
    else frame.read Policy.ready (.var name)) payload

theorem outsidePair_of_fresh_row (before : Bindings) (left right : String)
    (leftFresh : left ∉ specBindingVars before) (rightFresh : right ∉ specBindingVars before)
    (row : String × Atom) (stored : row ∈ before.assignments) : outsidePair left right row.1 = true := by
  have freshKey (name : String) (fresh : name ∉ specBindingVars before) : row.1 ≠ name := by
    intro same
    apply fresh
    exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨row, stored, by simp [same]⟩)
  simp [outsidePair, freshKey left leftFresh, freshKey right rightFresh]

theorem outsidePair_of_fresh_equality (before : Bindings) (left right : String)
    (leftFresh : left ∉ specBindingVars before) (rightFresh : right ∉ specBindingVars before)
    (row : String × String) (stored : row ∈ before.equalities) :
    outsidePair left right row.1 = true ∧ outsidePair left right row.2 = true := by
  have absent (name : String) (fresh : name ∉ specBindingVars before) : row.1 ≠ name ∧ row.2 ≠ name := by
    constructor
    · intro same
      apply fresh
      exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨row, stored, by simp [same]⟩)
    · intro same
      apply fresh
      exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨row, stored, by simp [same]⟩)
  simp [outsidePair, (absent left leftFresh).1, (absent left leftFresh).2,
    (absent right rightFresh).1, (absent right rightFresh).2]

theorem removePair_fresh_class (before : Bindings) (left right : String) (value : Atom)
    (leftFresh : left ∉ specBindingVars before) (rightFresh : right ∉ specBindingVars before) :
    removePair left right ((HEFreshRangeFrame.extend before left value).addEquality left right) = before := by
  have assignments : before.assignments.filter (fun row => outsidePair left right row.1) = before.assignments := by
    apply List.filter_eq_self.mpr
    exact outsidePair_of_fresh_row before left right leftFresh rightFresh
  have equalities : before.equalities.filter (fun row =>
      outsidePair left right row.1 && outsidePair left right row.2) = before.equalities := by
    apply List.filter_eq_self.mpr
    intro row member
    simp only [outsidePair_of_fresh_equality before left right leftFresh rightFresh row member,
      Bool.and_self]
  simp only [removePair, HEFreshRangeFrame.extend, Bindings.addEquality, List.filter_append,
    assignments, equalities]
  simp [outsidePair]

/-- The result is computed from the actual incoming record. The four
branches express name-wise retention, rather than keeping whole classes. -/
theorem project_fresh_class (retained : List String) (before : Bindings)
    (left right : String) (value : Atom)
    (leftFresh : left ∉ specBindingVars before) (rightFresh : right ∉ specBindingVars before) :
    projectBindings retained left right
      ((HEFreshRangeFrame.extend before left value).addEquality left right) =
    some (if left ∈ retained then
      if right ∈ retained then (HEFreshRangeFrame.extend before left value).addEquality left right
      else HEFreshRangeFrame.extend before left value
      else if right ∈ retained then HEFreshRangeFrame.extend before right value else before) := by
  have lookup : ((HEFreshRangeFrame.extend before left value).addEquality left right).lookup left = some value := by
    simp only [Bindings.addEquality, HEFreshRangeFrame.extend, Bindings.lookup, List.lookup_append]
    rw [show before.assignments.lookup left = none from HEFreshRangeFrame.fresh_lookup before left leftFresh]
    simp
  unfold projectBindings
  rw [lookup]
  simp only [Option.map_some, removePair_fresh_class before left right value leftFresh rightFresh]

theorem project_fresh_environment (retained : List String) (before : Frame)
    (left right : String) (value : Entry.Value)
    (leftFresh : left ∉ specBindingVars before.bindings) (rightFresh : right ∉ specBindingVars before.bindings) :
    projectEnvironment retained left right ((right, value) :: (left, value) :: before.environment) =
      (if right ∈ retained then [(right, value)] else []) ++
        (if left ∈ retained then [(left, value)] else []) ++ before.environment := by
  have fixed : before.environment.filter (fun row => outsidePair left right row.1 || retained.contains row.1) =
      before.environment := by
    apply List.filter_eq_self.mpr
    intro row stored
    simp [outsidePair, (environment_avoids before left leftFresh row stored).1,
      (environment_avoids before right rightFresh row stored).1]
  simp only [projectEnvironment, List.filter_cons, fixed]
  by_cases leftKept : left ∈ retained <;> by_cases rightKept : right ∈ retained <;>
    simp [outsidePair, leftKept, rightKept]

theorem expose_kept (retained : List String) (left right : String) (frame : Frame)
    (name : String) (kept : name ∈ retained) :
    expose retained left right frame (.var name) = .var name := by
  simp [expose, Entry.Value.substitute, kept]

theorem expose_removed_left (retained : List String) (left right : String) (frame : Frame)
    (removed : left ∉ retained) :
    expose retained left right frame (.var left) = frame.read Policy.ready (.var left) := by
  simp [expose, Entry.Value.substitute, outsidePair, removed]

theorem expose_removed_right (retained : List String) (left right : String) (frame : Frame)
    (removed : right ∉ retained) :
    expose retained left right frame (.var right) = frame.read Policy.ready (.var right) := by
  simp [expose, Entry.Value.substitute, outsidePair, removed]

/-- If the authored variable stays live and its private operator-query alias
does not occur in pending code, publishing that code does not read the
authored variable even when its class has a closed assigned value. -/
theorem retained_left_packet_unchanged (retained : List String) (left right : String)
    (frame : Frame) (payload : Entry.Value) (leftKept : left ∈ retained)
    (rightAbsent : right ∉ TypeSubst.typeVars payload.erase) :
    expose retained left right frame payload = payload := by
  apply Entry.Value.substitute_of_fixed_variables
  intro name member
  have notRight : name ≠ right := by intro same; exact rightAbsent (same ▸ member)
  by_cases same : name = left
  · simp [same, leftKept]
  · simp [outsidePair, same, notRight]

/-- Computed projection has a certified annotated output in every retention
case. The source match supplies the input packet; this theorem constructs
the output certificate rather than asking a caller to assume one. -/
theorem projected_frame (retained : List String) (before selected : Frame)
    (left right : String) (value : Entry.Value) (closed : TypeSubst.typeVars value.erase = [])
    (leftFresh : left ∉ specBindingVars before.bindings) (rightFresh : right ∉ specBindingVars before.bindings)
    (bindings : selected.bindings = (HEFreshRangeFrame.extend before.bindings left value.erase).addEquality left right)
    (environment : selected.environment = (right, value) :: (left, value) :: before.environment) :
    ∃ after : Frame,
      projectBindings retained left right selected.bindings = some after.bindings ∧
      projectEnvironment retained left right selected.environment = after.environment := by
  have raw := project_fresh_class retained before.bindings left right value.erase leftFresh rightFresh
  have marked := project_fresh_environment retained before left right value leftFresh rightFresh
  rw [← bindings] at raw
  rw [← environment] at marked
  by_cases leftKept : left ∈ retained
  · by_cases rightKept : right ∈ retained
    · refine ⟨selected, ?_, ?_⟩
      · simpa only [if_pos leftKept, if_pos rightKept, bindings] using raw
      · simpa only [if_pos leftKept, if_pos rightKept, List.singleton_append,
          List.cons_append, List.nil_append, environment] using marked
    · let after := HEFreshSyntaxBinding.bindFrame Policy.ready before left value leftFresh (by simp [closed])
      refine ⟨after, ?_, ?_⟩
      · have same := HEFreshSyntaxBinding.binding_keeps_caller Policy.ready before left value leftFresh (by simp [closed])
        simpa only [if_pos leftKept, if_neg rightKept, after, same] using raw
      · have same := fresh_environment Policy.ready before left value leftFresh closed
        simpa only [if_pos leftKept, if_neg rightKept, List.nil_append, List.singleton_append,
          after, HEFreshSyntaxBinding.bindFrame, same] using marked
  · by_cases rightKept : right ∈ retained
    · let after := HEFreshSyntaxBinding.bindFrame Policy.ready before right value rightFresh (by simp [closed])
      refine ⟨after, ?_, ?_⟩
      · have same := HEFreshSyntaxBinding.binding_keeps_caller Policy.ready before right value rightFresh (by simp [closed])
        simpa only [if_neg leftKept, if_pos rightKept, after, same] using raw
      · have same := fresh_environment Policy.ready before right value rightFresh closed
        simpa only [if_neg leftKept, if_pos rightKept, List.nil_append, List.singleton_append,
          after, HEFreshSyntaxBinding.bindFrame, same] using marked
    · exact ⟨before, by simpa only [if_neg leftKept, if_neg rightKept] using raw,
        by simpa only [if_neg leftKept, if_neg rightKept, List.nil_append] using marked⟩

def classValuation (retained : List String) (left right : String) (value : Entry.Value) : String → Entry.Value :=
  fun name => if outsidePair left right name || retained.contains name then .var name else value

theorem class_read (selected : Frame) (left right : String) (value : Entry.Value)
    (rest : Entry.Value.Environment) (different : left ≠ right)
    (environment : selected.environment = (right, value) :: (left, value) :: rest)
    (policy : Policy) :
    selected.read policy (.var left) = value ∧ selected.read policy (.var right) = value := by
  simp only [Frame.read, Entry.Value.substitute, environment, Entry.Value.resolve,
    List.lookup_cons, beq_eq_false_iff_ne.mpr different, beq_self_eq_true, Option.getD_some]
  exact ⟨True.intro, True.intro⟩

/-- The payload action reads only the disappearing members. This equation
holds for the full annotated packet, not just its syntactic erasure. -/
theorem expose_class (retained : List String) (selected : Frame) (left right : String)
    (value : Entry.Value) (rest : Entry.Value.Environment) (different : left ≠ right)
    (environment : selected.environment = (right, value) :: (left, value) :: rest)
    (payload : Entry.Value) :
    expose retained left right selected payload =
      Entry.Value.substitute .preserve (classValuation retained left right value) payload := by
  obtain ⟨leftRead, rightRead⟩ := class_read selected left right value rest different environment Policy.ready
  unfold expose
  congr 1
  funext name
  unfold classValuation
  by_cases kept : (outsidePair left right name || retained.contains name) = true
  · simp only [kept, ↓reduceIte]
  · simp only [kept]
    have same : name = left ∨ name = right := by
      by_contra missing
      have outside : outsidePair left right name = true := by
        simp [outsidePair, not_or.mp missing |>.1, not_or.mp missing |>.2]
      simp [outside] at kept
    rcases same with rfl | rfl
    · exact leftRead
    · exact rightRead

theorem classValuation_fixes_outside (retained : List String) (left right name : String)
    (value : Entry.Value) (notLeft : name ≠ left) (notRight : name ≠ right) :
    classValuation retained left right value name = .var name := by
  simp [classValuation, outsidePair, notLeft, notRight]

theorem classValuation_fixes_payload (retained : List String) (left right : String)
    (value payload : Entry.Value)
    (notLeft : left ∉ TypeSubst.typeVars payload.erase) (notRight : right ∉ TypeSubst.typeVars payload.erase) :
    Entry.Value.substitute .preserve (classValuation retained left right value) payload = payload := by
  apply Entry.Value.substitute_of_fixed_variables
  intro name occurs
  exact classValuation_fixes_outside retained left right name value
    (by intro same; exact notLeft (same ▸ occurs)) (by intro same; exact notRight (same ▸ occurs))

/-- The additional scope premise needed to equate class-local retirement
with filtering the complete reached annotated record. This premise is
separate from fresh allocation of the two type variables. -/
theorem complete_environment_filter (retained : List String) (before : Frame)
    (left right : String) (value : Entry.Value)
    (leftFresh : left ∉ specBindingVars before.bindings) (rightFresh : right ∉ specBindingVars before.bindings)
    (callerRetained : ∀ name ∈ specBindingVars before.bindings, name ∈ retained) :
    projectEnvironment retained left right ((right, value) :: (left, value) :: before.environment) =
      ((right, value) :: (left, value) :: before.environment).filter (fun row => retained.contains row.1) := by
  have oldKept : before.environment.filter (fun row => retained.contains row.1) = before.environment := by
    apply List.filter_eq_self.mpr
    intro row member
    have inSupport : row.1 ∈ specBindingVars before.bindings := by
      by_contra absent
      exact (environment_avoids before row.1 absent row member).1 rfl
    simpa using callerRetained row.1 inSupport
  rw [project_fresh_environment retained before left right value leftFresh rightFresh]
  simp only [List.filter_cons, oldKept]
  by_cases leftKept : left ∈ retained <;> by_cases rightKept : right ∈ retained <;>
    simp [leftKept, rightKept]

namespace Controls

theorem retained_alias_gets_value (before : Bindings) (left right : String) (value : Atom)
    (different : left ≠ right) (leftFresh : left ∉ specBindingVars before)
    (rightFresh : right ∉ specBindingVars before) :
    projectBindings [right] left right ((HEFreshRangeFrame.extend before left value).addEquality left right) =
      some (HEFreshRangeFrame.extend before right value) := by
  rw [project_fresh_class [right] before left right value leftFresh rightFresh]
  simp [different]

theorem both_private_restore_caller (before : Bindings) (left right : String) (value : Atom)
    (leftFresh : left ∉ specBindingVars before) (rightFresh : right ∉ specBindingVars before) :
    projectBindings [] left right ((HEFreshRangeFrame.extend before left value).addEquality left right) = some before := by
  rw [project_fresh_class [] before left right value leftFresh rightFresh]
  simp

theorem unresolved_class_is_not_closed_publication :
    projectBindings ["kept"] "private" "kept" (Bindings.empty.addEquality "private" "kept") = none := rfl

/-- With an unrelated old binding outside the kept scope, a whole native
name filter is not the class-local operation proved in this module. -/
theorem omitted_caller_changes_full_filter :
    projectEnvironment [] "left" "right" [("caller", .grounded (.int 7))] =
        [("caller", .grounded (.int 7))] ∧
      ([("caller", .grounded (.int 7))] : Entry.Value.Environment).filter
        (fun row => ([] : List String).contains row.1) = [] := by constructor <;> rfl

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEClosedAliasRetirement
