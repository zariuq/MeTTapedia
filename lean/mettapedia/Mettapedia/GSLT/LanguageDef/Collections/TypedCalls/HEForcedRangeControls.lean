import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEForcedRangeAlias
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEFreshRangeControls

/-! # Retained ranges beyond direct assignments and isolated alias classes -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEForcedRangeControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open Spec.Type Spec.Type.Presentation Spec.Type.RuntimeRefinement
open Spec.Match.Merge Spec.Match.ModelTheory Spec.Bindings.ScopeObservation
open Spec.Eval Spec.Eval.Completed

def box (value : Atom) : Atom := .expression [.symbol "Box", value]

def direct : Bindings := ⟨[("range", .symbol "Number"), ("packet", box (.symbol "Number"))], []⟩

/-- The range has no direct class value; it is forced by two equations for
the same enclosing constructor. Duplicate assignment occurrences matter. -/
def indirect : Bindings := ⟨[("packet", box (.symbol "Number")), ("packet", box (.var "range"))], []⟩

theorem indirect_agreement : BindingSourceAgreement direct indirect := by
  constructor
  · intro valuation
    constructor
    · intro model
      have rangeValue : valuation "range" = .symbol "Number" := by
        simpa only [applyTypeValuation] using model.1 "range" (.symbol "Number") (by decide)
      have packetValue := model.1 "packet" (box (.symbol "Number")) (by decide)
      refine ⟨?_, by simp [indirect]⟩
      intro key value member
      rcases List.mem_cons.mp member with same | rest
      · cases same; exact packetValue
      · cases List.mem_singleton.mp rest
        simpa [applyTypeValuation, box, rangeValue] using packetValue
    · intro model
      have first := model.1 "packet" (box (.symbol "Number")) (by decide)
      have second := model.1 "packet" (box (.var "range")) (by decide)
      have rangeValue : valuation "range" = .symbol "Number" := by
        simpa [applyTypeValuation, box] using second.symm.trans first
      refine ⟨?_, by simp [direct]⟩
      intro key value member
      rcases List.mem_cons.mp member with same | rest
      · cases same; simpa only [applyTypeValuation] using rangeValue
      · cases List.mem_singleton.mp rest; exact first
  · intro name
    simp [direct, indirect, specBindingVars, TypeSubst.typeVars, TypeSubst.typeVarsList, box, or_comm]

theorem indirect_shape : AssignmentsNonVariable indirect := by
  intro key value member
  rcases List.mem_cons.mp member with same | rest
  · cases same; rfl
  · cases List.mem_singleton.mp rest; rfl

theorem indirect_has_no_range_class_value : indirect.classValues "range" = [] := by decide

theorem indirect_raw_match_changes_record :
    TypeMatchRel (.var "range") (.symbol "Number") indirect
      (indirect.assign "range" (.symbol "Number")) ∧
    indirect.assign "range" (.symbol "Number") ≠ indirect := by
  constructor
  · apply TypeMatchRel.structural (matched := Bindings.empty.assign "range" (.symbol "Number"))
      (by decide) (by decide) (by decide) (by decide)
    · exact .varNonVar rfl (semanticLoopFree_single_assignment (by intro impossible; cases impossible))
    · apply MergeRel.mk (order := [.value "range" (.symbol "Number")])
      · decide
      · exact .value (.fresh indirect_has_no_range_class_value) .nil
  · decide

theorem indirect_frame (policy : Policy) :
    ∃ frame : Frame, frame.bindings = indirect ∧
      ∀ readingPolicy, frame.read readingPolicy (.var "range") = .symbol "Number" := by
  obtain ⟨first, firstBindings, _, _⟩ :=
    HEFreshRangeFrame.number_range_frame policy Frame.empty "range" (by decide)
  obtain ⟨second, secondBindings, _, _⟩ :=
    HEFreshRangeFrame.fresh_range_frame policy first "packet" (box (.symbol "Number"))
      rfl (by simp [box, Atom.undefinedType]) (by simp [box, Atom.atomType])
      (by rw [firstBindings]; decide)
  have directBindings : second.bindings = direct := by
    rw [secondBindings, firstBindings]; rfl
  have agreement : BindingSourceAgreement second.bindings indirect := by rw [directBindings]; exact indirect_agreement
  let frame := second.represent indirect agreement
  refine ⟨frame, rfl, ?_⟩
  intro readingPolicy
  apply HEFreshRangeFrame.symbol_of_erase
  have forced := frame.certified.forced_read (.var "range") (.symbol "Number") (by
    intro valuation model
    have previous := (indirect_agreement.solutions valuation).mpr model
    simpa only [applyTypeValuation] using previous.1 "range" (.symbol "Number") (by decide))
  simpa only [Frame.read, Entry.Value.erase_substitute_environment, Entry.Value.erase] using forced

/-- The generic return theorem covers a real source frame whose class is
empty. The resulting constraint record cannot stay identical. -/
theorem indirect_cast_is_actual_source {Context World : Type} (environment : WorldEnvironment Context World)
    (lookup : environment.lookup = scopedLookup) (policy : Policy)
    (label : Context) (world : World) (live : List Atom) (scope : List String) :
    ∃ before after : Frame,
      before.bindings.classValues "range" = [] ∧
      Stateful.AtomRel environment label world live scope (.grounded (.int 7)) (.var "range") before
        [(.grounded (.int 7), after)] world (policy := policy) ∧
      BindingSourceAgreement before.bindings after.bindings ∧ after.environment = before.environment := by
  obtain ⟨before, bindings, reads⟩ := indirect_frame policy
  obtain ⟨after, evaluated, agreement, _, environmentSame⟩ :=
    HEForcedRangeReturn.number_at_range environment lookup policy label world live scope before "range" 7
      (bindings ▸ indirect_shape) (by rw [reads policy]; simp [Entry.Value.erase])
  exact ⟨before, after, by rw [bindings]; exact indirect_has_no_range_class_value,
    evaluated, agreement, environmentSame⟩

/-- After two already-aliased private names, another recursive range joins
the existing class through an actual source renewal. -/
theorem third_private_range (policy : Policy) :
    ∃ before after : Frame,
      "range" ∈ before.bindings.eqVarsInOrder ∧
      Frame.TypeRenewRel policy (.var "range") (.var "recursive-range") before after ∧
      after.bindings.equalities = [("range", "query"), ("range", "recursive-range")] ∧
      ∀ readingPolicy,
        after.read readingPolicy (.var "range") = .symbol "Number" ∧
        after.read readingPolicy (.var "recursive-range") = .symbol "Number" := by
  obtain ⟨_, before, _, _, bindings, _, reads⟩ :=
    HEFreshRangeControls.if_range_and_operator_frames policy Frame.empty "range" "query" (by decide) (by decide)
  have shape : AssignmentsNonVariable before.bindings := by
    rw [bindings]
    intro key value member
    cases List.mem_singleton.mp member; rfl
  obtain ⟨after, afterBindings, renewed, _, afterReads⟩ :=
    HEForcedRangeAlias.fresh_range_frame before policy "range" "recursive-range" shape
      (by rw [(reads policy).1]; simp [Entry.Value.erase]) (by rw [bindings]; decide)
  refine ⟨before, after, ?_, renewed, ?_, afterReads⟩
  · rw [bindings]; decide
  · rw [afterBindings, bindings]; rfl

/-- An empty class is not permission to skip range checking: only the
complete record's certified observation establishes the owed type. -/
theorem empty_class_does_not_force_number :
    Bindings.empty.classValues "range" = [] ∧
    ¬ (∀ valuation, TypeBindingSatisfied valuation Bindings.empty → valuation "range" = .symbol "Number") := by
  refine ⟨rfl, ?_⟩
  intro forced
  have impossible := forced (fun _ => .symbol "String") (by simp [TypeBindingSatisfied, Bindings.empty])
  exact (by decide : (Atom.symbol "String") ≠ .symbol "Number") impossible

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEForcedRangeControls
