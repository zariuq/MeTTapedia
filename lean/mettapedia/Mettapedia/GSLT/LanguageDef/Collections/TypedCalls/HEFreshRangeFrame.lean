import Mettapedia.Languages.MeTTa.HE.Spec.Eval
import Mettapedia.Languages.MeTTa.HE.QueryBindingProjection

/-!
# A fresh schematic result range under an arbitrary caller frame

Matching a closed expected type with a genuinely fresh result variable
constructs the actual source type constraint and its selected contextual
frame. The caller's assignments and equality occurrences are retained exactly.
The arrow's result remains schematic until this match; no ground-arrow
restriction or empty-caller assumption is used.

Only `Atom` and `%Undefined%` are excluded here: they are the wildcard types
whose matching rules deliberately add no constraint. Entry/evaluation gates
may impose their own additional metatype exclusions.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEFreshRangeFrame

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open Spec.Type Spec.Type.Presentation Spec.Type.RuntimeRefinement
open Spec.Type.Presentation.BindingTheory
open Spec.Bindings.ScopeObservation
open Spec.Match.Merge
open Spec.Eval Spec.Eval.Completed Spec.Eval.Steps

def extend (before : Bindings) (name : String) (expected : Atom) : Bindings :=
  ⟨before.assignments ++ [(name, expected)], before.equalities⟩

theorem fresh_lookup (before : Bindings) (name : String) (fresh : name ∉ specBindingVars before) :
    before.lookup name = none :=
  (FreshPrivateMerge.readFrame_of_fresh (keys := fun other => other = name)
    (fun _ same => same ▸ fresh)).reads name rfl

theorem assign_eq_extend (before : Bindings) (name : String) (expected : Atom)
    (fresh : name ∉ specBindingVars before) : before.assign name expected = extend before name expected := by
  simp [Bindings.assign, Bindings.isBound, fresh_lookup before name fresh, extend]

theorem closed_nonvariable (expected : Atom) (closed : TypeSubst.typeVars expected = []) :
    isVariableB expected = false := by
  cases expected <;> simp_all [isVariableB, TypeSubst.typeVars]

/-- The private one-row source match is built, then the actual independent
merge appends that row without reconciling away the old caller constraints. -/
theorem source_match (before : Bindings) (name : String) (expected : Atom)
    (closed : TypeSubst.typeVars expected = [])
    (notUndefined : expected ≠ Atom.undefinedType) (notAtom : expected ≠ Atom.atomType)
    (fresh : name ∉ specBindingVars before) :
    TypeMatchRel expected (.var name) before (extend before name expected) := by
  have single : MatchRel equalityGroundedSemantic expected (.var name)
      (Bindings.empty.assign name expected) := by
    apply MatchRel.nonVarVar (closed_nonvariable expected closed)
    apply semanticLoopFree_single_assignment
    intro occurs
    have present := atomOccurs_mem_typeVars occurs
    simp [closed] at present
  have merged : MergeRel equalityGroundedSemantic before (Bindings.empty.assign name expected)
      (extend before name expected) := by
    apply MergeRel.mk (order := [.value name expected])
    · simp [constraints, Bindings.empty, Bindings.assign, Bindings.isBound, Bindings.lookup, List.eraseDups_cons]
    · exact FreshPrivateMerge.closed_constraints_source [(name, expected)] (by simp)
        (by intro key value member; cases List.mem_singleton.mp member; exact closed) before
        (by
          intro key member
          have same : key = name := by simpa using member
          simpa [same] using fresh)
  exact .structural notUndefined notAtom (by simp [Atom.undefinedType]) (by simp [Atom.atomType]) single merged

/-- The model is earned from the incoming frame certificate, not supplied
as an assumption about the desired output frame. -/
theorem extended_model (before : Frame) (name : String) (expected : Atom)
    (closed : TypeSubst.typeVars expected = []) (fresh : name ∉ specBindingVars before.bindings) :
    ∃ valuation, TypeBindingSatisfied valuation (extend before.bindings name expected) := by
  have absent : name ∉ TypeSubst.typeVars expected := by simp [closed]
  have certificate := before.certified.fresh_assignment name expected fresh absent
  simpa [assign_eq_extend before.bindings name expected fresh] using certificate.satisfiable

theorem old_constraints_retained (before : Bindings) (name : String) (expected : Atom)
    (valuation : String → Atom)
    (model : TypeBindingSatisfied valuation (extend before name expected)) :
    TypeBindingSatisfied valuation before :=
  (appendPrivatePresentation_solutions valuation before [(name, expected)]).mp model |>.1

theorem forced_range_read (after : Frame) (before : Bindings) (name : String) (expected : Atom)
    (closed : TypeSubst.typeVars expected = [])
    (bindings : after.bindings = extend before name expected) (policy : Policy) :
    (after.read policy (.var name)).erase = expected := by
  have forced := after.certified.forced_read (.var name) expected (by
    intro valuation model
    rw [bindings] at model
    have assigned := model.1 name expected (List.mem_append_right _ (by simp))
    simpa [applyTypeValuation, applyTypeValuation_of_typeVars_eq_nil _ _ closed] using assigned)
  simpa only [Frame.read, Entry.Value.erase_substitute_environment, Entry.Value.erase] using forced

/-- The fresh result binding, actual policy-specific source match, selected
frame and its range observation are derived together. -/
theorem fresh_range_frame (policy : Policy) (before : Frame) (name : String) (expected : Atom)
    (closed : TypeSubst.typeVars expected = [])
    (notUndefined : expected ≠ Atom.undefinedType) (notAtom : expected ≠ Atom.atomType)
    (fresh : name ∉ specBindingVars before.bindings) :
    ∃ after : Frame,
      after.bindings = extend before.bindings name expected ∧
      Frame.TypeRenewRel policy expected (.var name) before after ∧
      ∀ readingPolicy : Policy, (after.read readingPolicy (.var name)).erase = expected := by
  have source := source_match before.bindings name expected closed notUndefined notAtom fresh
  have model := extended_model before name expected closed fresh
  have selected : policy.matching.Rel expected (.var name) before.bindings (extend before.bindings name expected) := by
    cases chosen : policy.matching with
    | raw => exact source
    | finite => exact ⟨source, model⟩
  obtain ⟨after, bindings, renewed⟩ := Frame.TypeRenewRel.of_modelled_match before selected model
  exact ⟨after, bindings, renewed, forced_range_read after before.bindings name expected closed bindings⟩

theorem symbol_of_erase (value : Entry.Value) (name : String) (erased : value.erase = .symbol name) :
    value = .symbol name := by cases value <;> simp_all [Entry.Value.erase]

/-- The concrete expected type used by the ndcol range/if source. Its
annotated readback is exact, not only equality after erasure. -/
theorem number_range_frame (policy : Policy) (before : Frame) (name : String)
    (fresh : name ∉ specBindingVars before.bindings) :
    ∃ after : Frame,
      after.bindings = extend before.bindings name (.symbol "Number") ∧
      Frame.TypeRenewRel policy (.symbol "Number") (.var name) before after ∧
      ∀ readingPolicy : Policy, after.read readingPolicy (.var name) = .symbol "Number" := by
  obtain ⟨after, bindings, renewed, read⟩ := fresh_range_frame policy before name (.symbol "Number")
    rfl (by decide) (by decide) fresh
  exact ⟨after, bindings, renewed, fun readingPolicy => symbol_of_erase _ _ (read readingPolicy)⟩

namespace Controls

theorem old_aliases_survive (policy : Policy) :
    ∃ after : Frame,
      after.bindings.assignments = [("if-range", .symbol "Number")] ∧
      after.bindings.equalities = [("y", "x")] ∧
      Frame.TypeRenewRel policy (.symbol "Number") (.var "if-range")
        Spec.Eval.Completed.Controls.representedAliasFrame after ∧
      ∀ readingPolicy : Policy, after.read readingPolicy (.var "if-range") = .symbol "Number" := by
  obtain ⟨after, bindings, renewed, read⟩ := number_range_frame policy
    Spec.Eval.Completed.Controls.representedAliasFrame "if-range" (by decide)
  refine ⟨after, ?_, ?_, renewed, read⟩ <;> rw [bindings] <;> rfl

theorem unbound_alias_is_not_fresh :
    let bindings : Bindings := ⟨[], [("saved", "range")]⟩
    bindings.lookup "range" = none ∧ "range" ∈ specBindingVars bindings := by decide

theorem wildcard_cannot_establish_range (before : Bindings) (name : String) :
    ¬ TypeMatchRel Atom.atomType (.var name) before (extend before name Atom.atomType) := by
  intro matched
  have unchanged := matched.wildcard_output (Or.inr (Or.inl rfl))
  have lengths := congrArg (fun bindings => bindings.assignments.length) unchanged
  simp [extend] at lengths

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEFreshRangeFrame
