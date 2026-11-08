import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEForcedRangeReturn

/-!
# Fresh ranges join an already constrained private class

Recursive calls may retain many aliases of the caller's result variable. A
new range instance joins that class by the actual source merge, without an
isolated-left or direct-assignment premise. The existing observation and
finite model earn agreement of every value in the enlarged class.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEForcedRangeAlias

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open Spec.Type Spec.Type.Presentation Spec.Type.Presentation.BindingTheory
open Spec.Type.RuntimeRefinement Spec.Bindings.ScopeObservation
open Spec.Match.Merge Spec.Match.ModelTheory
open Spec.Eval Spec.Eval.Completed

theorem old_model {bindings : Bindings} {left right : String} {valuation : String → Atom}
    (model : TypeBindingSatisfied valuation (bindings.addEquality left right)) :
    TypeBindingSatisfied valuation bindings :=
  ⟨model.1, fun a b member => model.2 a b (List.mem_append_left _ member)⟩

theorem alias_shape {bindings : Bindings} (shape : AssignmentsNonVariable bindings)
    (left right : String) : AssignmentsNonVariable (bindings.addEquality left right) := shape

theorem source_merge (frame : Frame) (policy : Policy) (left right : String)
    (shape : AssignmentsNonVariable frame.bindings)
    (read : (frame.read policy (.var left)).erase = .symbol "Number")
    (fresh : right ∉ specBindingVars frame.bindings) :
    MergeRel equalityGroundedSemantic frame.bindings (Bindings.empty.addEquality left right)
      (frame.bindings.addEquality left right) := by
  obtain ⟨valuation, model⟩ := HEFreshRangeAlias.alias_model frame left right fresh
  have forced := HEForcedRangeReturn.read_forces frame policy left read valuation (old_model model)
  have values := HEForcedRangeReturn.class_values_number (alias_shape shape left right) model forced
  apply MergeRel.mk (order := [.equality left right])
  · simp [constraints, Bindings.empty, Bindings.addEquality, List.eraseDups_cons]
  · exact .equality (.consistent rfl (HEForcedRangeReturn.number_values_agree _ values)) .nil

theorem source_match (frame : Frame) (policy : Policy) (left right : String)
    (shape : AssignmentsNonVariable frame.bindings)
    (read : (frame.read policy (.var left)).erase = .symbol "Number")
    (fresh : right ∉ specBindingVars frame.bindings) :
    TypeMatchRel (.var left) (.var right) frame.bindings (frame.bindings.addEquality left right) :=
  .structural (by simp [Atom.undefinedType]) (by simp [Atom.atomType])
    (by simp [Atom.undefinedType]) (by simp [Atom.atomType])
    (.varVar left right (semanticLoopFree_of_assignments_nil rfl))
    (source_merge frame policy left right shape read fresh)

theorem arrow_source_match (frame : Frame) (policy : Policy) (spine : List String) (left right : String)
    (shape : AssignmentsNonVariable frame.bindings)
    (read : (frame.read policy (.var left)).erase = .symbol "Number")
    (fresh : right ∉ specBindingVars frame.bindings) :
    TypeMatchRel (HEFreshRangeAlias.arrowWith spine left) (HEFreshRangeAlias.arrowWith spine right)
      frame.bindings (frame.bindings.addEquality left right) :=
  .structural (by simp [HEFreshRangeAlias.arrowWith, Atom.undefinedType])
    (by simp [HEFreshRangeAlias.arrowWith, Atom.atomType])
    (by simp [HEFreshRangeAlias.arrowWith, Atom.undefinedType])
    (by simp [HEFreshRangeAlias.arrowWith, Atom.atomType])
    (HEFreshRangeAlias.arrow_match spine left right)
    (source_merge frame policy left right shape read fresh)

theorem retained_reads (before after : Frame) (policy : Policy) (left right : String)
    (read : (before.read policy (.var left)).erase = .symbol "Number")
    (bindings : after.bindings = before.bindings.addEquality left right) :
    ∀ readingPolicy,
      after.read readingPolicy (.var left) = .symbol "Number" ∧
      after.read readingPolicy (.var right) = .symbol "Number" := by
  have forced (name : String) (side : name = left ∨ name = right) :
      (Entry.Value.eraseEnvironment after.environment).apply (.var name) = .symbol "Number" := by
    apply after.certified.forced_read
    intro valuation model
    rw [bindings] at model
    have leftNumber := HEForcedRangeReturn.read_forces before policy left read valuation (old_model model)
    have linked := model.2 left right (List.mem_append_right _ (by simp))
    rcases side with rfl | rfl
    · simpa only [applyTypeValuation] using leftNumber
    · simpa only [applyTypeValuation] using linked.symm.trans leftNumber
  intro readingPolicy
  constructor
  · apply HEFreshRangeFrame.symbol_of_erase
    simpa only [Frame.read, Entry.Value.erase_substitute_environment, Entry.Value.erase] using forced left (Or.inl rfl)
  · apply HEFreshRangeFrame.symbol_of_erase
    simpa only [Frame.read, Entry.Value.erase_substitute_environment, Entry.Value.erase] using forced right (Or.inr rfl)

theorem fresh_range_frame (before : Frame) (policy : Policy) (left right : String)
    (shape : AssignmentsNonVariable before.bindings)
    (read : (before.read policy (.var left)).erase = .symbol "Number")
    (fresh : right ∉ specBindingVars before.bindings) :
    ∃ after : Frame,
      after.bindings = before.bindings.addEquality left right ∧
      Frame.TypeRenewRel policy (.var left) (.var right) before after ∧
      AssignmentsNonVariable after.bindings ∧
      ∀ readingPolicy,
        after.read readingPolicy (.var left) = .symbol "Number" ∧
        after.read readingPolicy (.var right) = .symbol "Number" := by
  have sourceMatch := source_match before policy left right shape read fresh
  have model := HEFreshRangeAlias.alias_model before left right fresh
  have policyMatch : policy.matching.Rel (.var left) (.var right) before.bindings
      (before.bindings.addEquality left right) := by
    cases matching : policy.matching with
    | raw => exact sourceMatch
    | finite => exact ⟨sourceMatch, model⟩
  obtain ⟨after, bindings, renewed⟩ := Frame.TypeRenewRel.of_modelled_match before policyMatch model
  exact ⟨after, bindings, renewed, bindings ▸ alias_shape shape left right,
    retained_reads before after policy left right read bindings⟩

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEForcedRangeAlias
