import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEAliasExplicitFrames
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEAssignedRangeReturn

/-!
# Source casts at a semantically retained numeric range

A range read is justified by the entire constraint record, not necessarily a
direct assignment or a singleton equality class. Alias-explicit equation
publication earns the non-variable assignment invariant used below. The raw
source matcher may append a redundant constraint; its complete theory and
annotated environment are preserved rather than asserting raw record identity.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEForcedRangeReturn

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open Spec.Type Spec.Type.Presentation Spec.Type.Presentation.BindingTheory
open Spec.Type.RuntimeRefinement Spec.Bindings.ScopeObservation
open Spec.Match.Merge Spec.Match.ModelTheory Spec.Match.SolutionTheory
open Spec.Eval Spec.Eval.Completed Spec.Eval.Steps

theorem read_forces (frame : Frame) (policy : Policy) (name : String)
    (read : (frame.read policy (.var name)).erase = .symbol "Number") :
    ∀ valuation, TypeBindingSatisfied valuation frame.bindings → valuation name = .symbol "Number" := by
  have tableRead : (Entry.Value.eraseEnvironment frame.environment).apply (.var name) = .symbol "Number" := by
    simpa only [Frame.read, Entry.Value.erase_substitute_environment, Entry.Value.erase] using read
  intro valuation model
  have preserved := frame.certified.preserves_model valuation model (.var name)
  rw [tableRead] at preserved
  simpa only [applyTypeValuation] using preserved.symm

theorem read_supported (frame : Frame) (policy : Policy) (name : String)
    (read : (frame.read policy (.var name)).erase = .symbol "Number") :
    name ∈ specBindingVars frame.bindings := by
  by_contra absent
  have noLookup := frame.certified.lookup_none_of_outside absent
  have tableRead : (Entry.Value.eraseEnvironment frame.environment).apply (.var name) = .symbol "Number" := by
    simpa only [Frame.read, Entry.Value.erase_substitute_environment, Entry.Value.erase] using read
  simp [TypeSubst.apply, noLookup] at tableRead

theorem class_value_model {bindings : Bindings} {valuation : String → Atom}
    (model : TypeBindingSatisfied valuation bindings) {name : String} {value : Atom}
    (member : value ∈ bindings.classValues name) : valuation name = applyTypeValuation valuation value := by
  have encoded := (ModelTransport.heBindingSatisfied_of_specTypeBindingSatisfied model).eq_applyClassSolution_of_mem_classValues member
  rw [← ModelTransport.encodeModelAtom_applyTypeValuation] at encoded
  exact encodeModelAtom_injective encoded

theorem class_value_nonvariable {bindings : Bindings} (shape : AssignmentsNonVariable bindings)
    {name : String} {value : Atom} (member : value ∈ bindings.classValues name) : isVariableB value = false := by
  obtain ⟨key, _, assigned⟩ := List.mem_filterMap.mp member
  obtain ⟨pre, post, layout, _⟩ := List.lookup_eq_some_iff.mp assigned
  exact shape key value (by rw [layout]; simp)

theorem class_values_number {bindings : Bindings} (shape : AssignmentsNonVariable bindings)
    {valuation : String → Atom} (model : TypeBindingSatisfied valuation bindings)
    {name : String} (forced : valuation name = .symbol "Number") :
    ∀ value ∈ bindings.classValues name, value = .symbol "Number" := by
  intro value member
  have interpreted := (class_value_model model member).symm.trans forced
  have nonvariable := class_value_nonvariable shape member
  cases value <;> simp_all [isVariableB, applyTypeValuation]

theorem number_values_agree (values : List Atom)
    (allNumber : ∀ value ∈ values, value = .symbol "Number") : ValuesAgree values := by
  cases values with
  | nil => trivial
  | cons first rest =>
      intro value member
      exact (allNumber value (List.mem_cons_of_mem _ member)).trans (allNumber first (by simp)).symm

theorem append_forced_agreement (frame : Frame) (policy : Policy) (name : String)
    (read : (frame.read policy (.var name)).erase = .symbol "Number") :
    BindingSourceAgreement frame.bindings
      (HEFreshRangeFrame.extend frame.bindings name (.symbol "Number")) := by
  constructor
  · intro valuation
    constructor
    · intro model
      refine ⟨?_, model.2⟩
      intro key value member
      rcases List.mem_append.mp member with old | added
      · exact model.1 key value old
      · cases List.mem_singleton.mp added
        simpa only [applyTypeValuation] using read_forces frame policy name read valuation model
    · exact HEFreshRangeFrame.old_constraints_retained frame.bindings name (.symbol "Number") valuation
  · intro key
    have present := read_supported frame policy name read
    simp only [specBindingVars, HEFreshRangeFrame.extend, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, TypeSubst.typeVars, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false]
    constructor
    · rintro (h | h)
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
    · rintro ((h | same) | h)
      · exact Or.inl h
      · subst key; exact List.mem_append.mp present
      · exact Or.inr h

/-- The raw source match is derived from a semantic range observation. Its
output presentation may differ, but no model or supported name changes. -/
theorem source_match (frame : Frame) (policy : Policy) (name : String)
    (shape : AssignmentsNonVariable frame.bindings)
    (read : (frame.read policy (.var name)).erase = .symbol "Number") :
    ∃ output, TypeMatchRel (.var name) (.symbol "Number") frame.bindings output ∧
      BindingSourceAgreement frame.bindings output ∧ AssignmentsNonVariable output := by
  obtain ⟨valuation, model⟩ := frame.certified.satisfiable
  have values := class_values_number shape model (read_forces frame policy name read valuation model)
  cases classes : frame.bindings.classValues name with
  | nil =>
      have unbound := EqualityClosure.isBound_eq_false_of_classValues_nil classes
      have layout : frame.bindings.assign name (.symbol "Number") =
          HEFreshRangeFrame.extend frame.bindings name (.symbol "Number") := by
        simp [Bindings.assign, unbound, HEFreshRangeFrame.extend]
      refine ⟨frame.bindings.assign name (.symbol "Number"), ?_, ?_, ?_⟩
      · apply TypeMatchRel.structural (matched := Bindings.empty.assign name (.symbol "Number"))
          (by simp [Atom.undefinedType]) (by simp [Atom.atomType]) (by decide) (by decide)
        · exact .varNonVar rfl (semanticLoopFree_single_assignment (by intro impossible; cases impossible))
        · apply MergeRel.mk (order := [.value name (.symbol "Number")])
          · simp [constraints, Bindings.empty, Bindings.assign, Bindings.isBound, Bindings.lookup, List.eraseDups_cons]
          · exact .value (.fresh classes) .nil
      · rw [layout]; exact append_forced_agreement frame policy name read
      · rw [layout]
        intro key value member
        rcases List.mem_append.mp member with old | added
        · exact shape key value old
        · cases List.mem_singleton.mp added; rfl
  | cons first rest =>
      have firstNumber := values first (by rw [classes]; simp)
      subst first
      refine ⟨frame.bindings, ?_, .refl _, shape⟩
      apply HEAssignedRangeReturn.valued_class_match _ name (.symbol "Number") rest rfl
        (by decide) (by decide) classes
      exact number_values_agree _ (by simpa only [classes] using values)

/-- The selected source cast has a model-equivalent output with exactly the
same annotated environment. The expected operand remains a variable. -/
theorem renewed_frame (frame : Frame) (policy : Policy) (name : String)
    (shape : AssignmentsNonVariable frame.bindings)
    (read : (frame.read policy (.var name)).erase = .symbol "Number") :
    ∃ after : Frame,
      policy.matching.Rel (.var name) (.symbol "Number") frame.bindings after.bindings ∧
      Entry.Value.UnifyRel policy.rebuilding frame.environment (.var name) (.symbol "Number") after.environment ∧
      BindingSourceAgreement frame.bindings after.bindings ∧
      AssignmentsNonVariable after.bindings ∧ after.environment = frame.environment := by
  obtain ⟨output, matched, agreement, outputShape⟩ := source_match frame policy name shape read
  let after := frame.represent output agreement
  have model := after.certified.satisfiable
  have policyMatch : policy.matching.Rel (.var name) (.symbol "Number") frame.bindings output := by
    cases matching : policy.matching with
    | raw => exact matched
    | finite => exact ⟨matched, model⟩
  refine ⟨after, policyMatch, ?_, agreement, outputShape, rfl⟩
  apply Entry.Value.UnifyRel.ordinary
  apply Entry.Value.AppliedUnifyRel.identical
  simpa only [Frame.read, Entry.Value.substitute, Entry.Value.erase] using read

theorem number_at_range {Context World : Type} (environment : WorldEnvironment Context World)
    (lookup : environment.lookup = scopedLookup) (policy : Policy)
    (label : Context) (world : World) (live : List Atom) (scope : List String)
    (before : Frame) (name : String) (value : Int)
    (shape : AssignmentsNonVariable before.bindings)
    (read : (before.read policy (.var name)).erase = .symbol "Number") :
    ∃ after : Frame,
      Stateful.AtomRel environment label world live scope (.grounded (.int value)) (.var name) before
        [(.grounded (.int value), after)] world (policy := policy) ∧
      BindingSourceAgreement before.bindings after.bindings ∧
      AssignmentsNonVariable after.bindings ∧ after.environment = before.environment := by
  obtain ⟨after, matched, unified, agreement, outputShape, environmentSame⟩ :=
    renewed_frame before policy name shape read
  have queried := HEContextualArithmeticSource.scalar_lookup (environment.view world label)
    (invocationTypeScope scope live (.grounded (.int value)) (.var name) before.bindings)
    before (.int value) "Number" (.var name) rfl (by decide)
  have readValue : before.read policy (.grounded (.int value)) = .grounded (.int value) := by
    simp [Frame.read, Entry.Value.substitute]
  have renewed : Frame.CastRenewRel policy
      (scopedLookup
        (invocationTypeScope scope live (.grounded (.int value)) (.var name) before.bindings)
        (environment.view world label))
      (.grounded (.int value)) (.var name) before after :=
    .matched queried (earlier := []) (later := []) rfl (by simp) matched
      (by simpa only [Entry.Value.ofAtom] using unified)
  refine ⟨after, ?_, agreement, outputShape, environmentSame⟩
  apply Stateful.AtomRel.cast (raw := [(.grounded (.int value), after.bindings)])
  · rw [readValue]
    apply Entry.Rel.cast (metaType := Atom.groundedType)
    · simp [Entry.Value.erase, IsEmptyOrErrorRel, IsErrorRel, Atom.empty]
    · simpa only [Entry.Value.erase] using MetaTypeRel.grounded (.int value)
    · simp [Atom.atomType, Atom.groundedType, Atom.variableType]
    · exact Or.inr (Or.inl ⟨.int value, by simp [Entry.Value.erase]⟩)
    · simp [Entry.Value.erase, Atom.unit]
  · rw [lookup, readValue]
    simp only [Entry.Value.erase]
    exact TypeCastBatchRel.success (earlierTypes := []) (laterTypes := []) queried rfl (by simp) matched
  · rw [lookup, readValue]
    exact .cons ⟨by simp [Completed.rawResult, Entry.Value.erase],
      by simpa only [Entry.Value.erase] using renewed,
      by simp [Entry.Value.erase]⟩ .nil

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEForcedRangeReturn
