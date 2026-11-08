import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEPrivateTypePublication

/-! A fresh authored formal is the expected side of an applicability check.
This orientation is proved from its actual var/nonvariable match and local
merge; the opposite, range-style orientation is not used as a substitute. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEExpectedPrivateTypePublication

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed Spec.Type Spec.Type.Presentation Spec.Type.RuntimeRefinement
open Spec.Bindings.ScopeObservation Spec.Match.Merge Spec.Eval.Steps
open HEPrivateTypePublication

theorem source_match (before : Bindings) (name : String) (actual : Atom)
    (closed : TypeSubst.typeVars actual = [])
    (notUndefined : actual ≠ Atom.undefinedType) (notAtom : actual ≠ Atom.atomType)
    (fresh : name ∉ specBindingVars before) :
    TypeMatchRel (.var name) actual before (HEFreshRangeFrame.extend before name actual) := by
  have single : MatchRel equalityGroundedSemantic (.var name) actual (Bindings.empty.assign name actual) := by
    apply MatchRel.varNonVar (HEFreshRangeFrame.closed_nonvariable actual closed)
    apply semanticLoopFree_single_assignment
    intro occurs
    have member := atomOccurs_mem_typeVars occurs
    simp [closed] at member
  have merged : MergeRel equalityGroundedSemantic before (Bindings.empty.assign name actual)
      (HEFreshRangeFrame.extend before name actual) := by
    apply MergeRel.mk (order := [.value name actual])
    · simp [constraints, Bindings.empty, Bindings.assign, Bindings.isBound, Bindings.lookup, List.eraseDups_cons]
    · exact FreshPrivateMerge.closed_constraints_source [(name, actual)] (by simp)
        (by intro key value member; cases List.mem_singleton.mp member; exact closed) before
        (by
          intro key member
          have same : key = name := by simpa using member
          simpa [same] using fresh)
  exact .structural (by simp [Atom.undefinedType]) (by simp [Atom.atomType]) notUndefined notAtom single merged

theorem fresh_formal (policy : Policy) (before : Frame) (name : String) (actual : Atom)
    (closed : TypeSubst.typeVars actual = [])
    (notUndefined : actual ≠ Atom.undefinedType) (notAtom : actual ≠ Atom.atomType)
    (fresh : name ∉ specBindingVars before.bindings) :
    ∃ selected : Frame,
      Frame.TypeRenewRel policy (.var name) actual before selected ∧
      selected.bindings = HEFreshRangeFrame.extend before.bindings name actual ∧
      selected.environment = (name, Entry.Value.ofAtom actual) :: before.environment ∧
      dropAssignment name selected.bindings = before.bindings ∧
      dropEnvironment name selected.environment = before.environment := by
  obtain ⟨selected, _, bindings, environment, rawDrop, markedDrop, _⟩ :=
    fresh_closed_type_publication policy before name actual closed notUndefined notAtom fresh
  have matched : policy.matching.Rel (.var name) actual before.bindings selected.bindings := by
    rw [bindings]
    cases policy.matching with
    | raw => exact source_match before.bindings name actual closed notUndefined notAtom fresh
    | finite => exact ⟨source_match before.bindings name actual closed notUndefined notAtom fresh,
        HEFreshRangeFrame.extended_model before name actual closed fresh⟩
  have valueClosed : TypeSubst.typeVars (Entry.Value.ofAtom actual).erase = [] := by simpa using closed
  have unified : Entry.Value.UnifyRel policy.rebuilding before.environment
      (Entry.Value.ofAtom (.var name)) (Entry.Value.ofAtom actual) selected.environment := by
    rw [environment, ← fresh_environment policy before name (Entry.Value.ofAtom actual) fresh valueClosed]
    apply Entry.Value.UnifyRel.ordinary
    simp only [Entry.Value.ofAtom, Entry.Value.substitute, HEFreshSyntaxBinding.resolve_fresh before name fresh]
    rw [HEFreshSyntaxBinding.ground_substitution policy.rebuilding _ (Entry.Value.ofAtom actual) valueClosed]
    exact .bindLeft (by simp [closed])
  exact ⟨selected, .unified matched unified, bindings, environment, rawDrop, markedDrop⟩

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEExpectedPrivateTypePublication
