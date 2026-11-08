import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEFreshRangeAlias

/-! # Composed fresh-range entry and operator-cast controls -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEFreshRangeControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open Spec.Type Spec.Type.Presentation Spec.Type.RuntimeRefinement
open Spec.Bindings.ScopeObservation Spec.Eval Spec.Eval.Completed
open HEFreshRangeFrame HEFreshRangeAlias

/-- Both frames are earned while retaining the arbitrary initial caller.
The second freshness requirement is on the actual first output record. -/
theorem if_range_and_operator_frames (policy : Policy) (before : Frame) (rangeName queryName : String)
    (rangeFresh : rangeName ∉ specBindingVars before.bindings)
    (queryFresh : queryName ∉ specBindingVars (extend before.bindings rangeName (.symbol "Number"))) :
    ∃ selected after : Frame,
      selected.bindings = extend before.bindings rangeName (.symbol "Number") ∧
      Frame.TypeRenewRel policy (.symbol "Number") (.var rangeName) before selected ∧
      after.bindings =
        ⟨before.bindings.assignments ++ [(rangeName, .symbol "Number")],
          before.bindings.equalities ++ [(rangeName, queryName)]⟩ ∧
      Frame.TypeRenewRel policy (arrowWith ["->", "Bool", "Atom", "Atom"] rangeName)
        (arrowWith ["->", "Bool", "Atom", "Atom"] queryName) selected after ∧
      ∀ readingPolicy : Policy,
        after.read readingPolicy (.var rangeName) = .symbol "Number" ∧
        after.read readingPolicy (.var queryName) = .symbol "Number" := by
  obtain ⟨selected, selectedBindings, renewed, _⟩ := number_range_frame policy before rangeName rangeFresh
  have privateFacts := extended_private_facts before.bindings rangeName (.symbol "Number") rangeFresh
  have assigned : selected.bindings.lookup rangeName = some (.symbol "Number") := by
    simpa [selectedBindings] using privateFacts.1
  have isolated : rangeName ∉ selected.bindings.eqVarsInOrder := by
    simpa [selectedBindings] using privateFacts.2
  have fresh : queryName ∉ specBindingVars selected.bindings := by simpa [selectedBindings] using queryFresh
  obtain ⟨after, finalBindings, operatorRenewed, reads⟩ :=
    if_number_alias_frame policy selected rangeName queryName isolated assigned fresh
  refine ⟨selected, after, selectedBindings, renewed, ?_, operatorRenewed, reads⟩
  simpa [selectedBindings, extend, Bindings.addEquality] using finalBindings

theorem aliased_caller_survives_both_steps (policy : Policy) :
    ∃ selected after : Frame,
      Frame.TypeRenewRel policy (.symbol "Number") (.var "if-range")
        Spec.Eval.Completed.Controls.representedAliasFrame selected ∧
      after.bindings.assignments = [("if-range", .symbol "Number")] ∧
      after.bindings.equalities = [("y", "x"), ("if-range", "if-query")] ∧
      ∀ readingPolicy : Policy,
        after.read readingPolicy (.var "if-range") = .symbol "Number" ∧
        after.read readingPolicy (.var "if-query") = .symbol "Number" := by
  obtain ⟨selected, after, _, renewed, bindings, _, reads⟩ :=
    if_range_and_operator_frames policy Spec.Eval.Completed.Controls.representedAliasFrame
      "if-range" "if-query" (by decide) (by decide)
  refine ⟨selected, after, renewed, ?_, ?_, reads⟩ <;> rw [bindings] <;> rfl

def conflicting : Bindings := ⟨[("range", .symbol "Number"), ("query", .symbol "String")], []⟩

/-- Distinct names alone do not justify a fresh range instance: an existing
incompatible type binding cannot be discarded when the two names are linked. -/
theorem conflicting_alias_has_no_model :
    ¬ ∃ valuation, TypeBindingSatisfied valuation (conflicting.addEquality "range" "query") := by
  rintro ⟨valuation, model⟩
  have left := model.1 "range" (.symbol "Number") (by decide)
  have right := model.1 "query" (.symbol "String") (by decide)
  have aliasEq := model.2 "range" "query" (by decide)
  simp only [applyTypeValuation] at left right
  have impossible : (Atom.symbol "Number") = .symbol "String" := left.symm.trans (aliasEq.trans right)
  exact (by decide : (Atom.symbol "Number") ≠ .symbol "String") impossible

theorem distinct_is_not_fresh :
    "range" ≠ "query" ∧ "query" ∈ specBindingVars conflicting := by decide

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEFreshRangeControls
