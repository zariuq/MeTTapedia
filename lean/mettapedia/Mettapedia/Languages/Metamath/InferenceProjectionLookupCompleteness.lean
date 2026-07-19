import Mettapedia.Languages.Metamath.InferenceProjectionFidelity

/-!
# Lookup completeness of the Metamath prefix projection

The fidelity layer proves that every projected assertion came from the live
runtime database.  This file proves the converse needed by whole-proof fold
reflection: every assertion object in a successfully projected database has a
corresponding projected `AssertionView` with the exact runtime payload.

The assertion list is deterministically sorted by label before projection,
but no chronological meaning is assigned to that order.  Chronology remains
the responsibility of the parser's pre-insertion database boundary.
-/

namespace Mettapedia.Languages.Metamath.InferenceProjectionLookupCompleteness

open Mettapedia.Languages.Metamath.MMLean4Bridge
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.InferenceProjection
open Mettapedia.Languages.Metamath.InferenceProjectionParserBridge
open Mettapedia.Languages.Metamath.InferenceProjectionFidelity

/-! ## Completeness of the assertion traversal -/

/-- Every assertion entry in an input list occurs in the output of a
successful assertion traversal, represented by the exact partial decoder
result at that entry. -/
private theorem projectAssertionsFromEntries?_complete
    (db : RuntimeDB)
    (entries : List (String × Metamath.Verify.Object))
    (assertions : List AssertionView)
    (label embeddedLabel : String)
    (runtimeFormula : RuntimeFormula) (frame : RuntimeFrame)
    (hproject :
      projectAssertionsFromEntries? db entries = some assertions)
    (hentry :
      (label, .assert runtimeFormula frame embeddedLabel) ∈ entries) :
    ∃ assertion,
      assertion ∈ assertions ∧
      projectAssertion? db label runtimeFormula frame embeddedLabel =
        some assertion := by
  induction entries generalizing assertions with
  | nil =>
      simp at hentry
  | cons entry entries ih =>
      rcases entry with ⟨sourceLabel, object⟩
      cases object with
      | const name =>
          simp only [projectAssertionsFromEntries?] at hproject
          have htail :
              (label, .assert runtimeFormula frame embeddedLabel) ∈ entries := by
            simpa using hentry
          exact ih assertions hproject htail
      | var name =>
          simp only [projectAssertionsFromEntries?] at hproject
          have htail :
              (label, .assert runtimeFormula frame embeddedLabel) ∈ entries := by
            simpa using hentry
          exact ih assertions hproject htail
      | hyp essential formula origin =>
          simp only [projectAssertionsFromEntries?] at hproject
          have htail :
              (label, .assert runtimeFormula frame embeddedLabel) ∈ entries := by
            simpa using hentry
          exact ih assertions hproject htail
      | assert sourceFormula sourceFrame sourceEmbeddedLabel =>
          cases hhead :
              projectAssertion? db sourceLabel sourceFormula sourceFrame
                sourceEmbeddedLabel with
          | none =>
              simp [projectAssertionsFromEntries?, hhead] at hproject
          | some headAssertion =>
              cases htailProject :
                  projectAssertionsFromEntries? db entries with
              | none =>
                  simp [projectAssertionsFromEntries?, hhead, htailProject]
                    at hproject
              | some tailAssertions =>
                  simp [projectAssertionsFromEntries?, hhead, htailProject]
                    at hproject
                  subst assertions
                  simp only [List.mem_cons] at hentry
                  rcases hentry with hsame | htail
                  · injection hsame with hlabel hobject
                    injection hobject with hformula hframe hembedded
                    subst sourceLabel
                    subst sourceFormula
                    subst sourceFrame
                    subst sourceEmbeddedLabel
                    exact ⟨headAssertion, by simp, hhead⟩
                  · obtain ⟨assertion, hmember, hdecode⟩ :=
                      ih tailAssertions htailProject htail
                    exact ⟨assertion, by simp [hmember], hdecode⟩

/-! ## Reverse lookup theorem -/

/-- Every live assertion lookup is represented in a successful prefix
projection.  The witness retains the exact lookup label, decoded runtime
formula, frame, and embedded label.

This is extensional completeness for one already supplied pre-insertion
database.  It neither infers chronology from the projection's sorted order nor
proves that a runtime database is a parser prefix. -/
theorem projectedAssertion_of_runtime_lookup
    (db : RuntimeDB) (projection : PrefixProjection)
    (label embeddedLabel : String)
    (runtimeFormula : RuntimeFormula) (frame : RuntimeFrame)
    (hproject : projectPrefix? db = some projection)
    (hfind : db.find? label =
      some (.assert runtimeFormula frame embeddedLabel)) :
    ∃ assertion,
      assertion ∈ projection.assertions ∧
      assertion.label = label ∧
      runtimeFormula = assertion.formula.toRuntime ∧
      frame = assertion.frame ∧
      embeddedLabel = label := by
  have hentry :
      (label, .assert runtimeFormula frame embeddedLabel) ∈
        objectEntries db :=
    (objectEntries_exact db label
      (.assert runtimeFormula frame embeddedLabel)).mpr hfind
  have hassertions :
      projectAssertionsFromEntries? db (objectEntries db) =
        some projection.assertions :=
    (projectPrefix?_eq_some_fields db projection hproject).2.2.2.2
  obtain ⟨assertion, hmember, hdecode⟩ :=
    projectAssertionsFromEntries?_complete db (objectEntries db)
      projection.assertions label embeddedLabel runtimeFormula frame
      hassertions hentry
  obtain ⟨hembedded, hformula, _hhypotheses, hlabel, hframe⟩ :=
    projectAssertion?_eq_some_fidelity db label embeddedLabel
      runtimeFormula frame assertion hdecode
  have hruntime : runtimeFormula = assertion.formula.toRuntime :=
    (ConstantHeadedFormula.ofRuntime?_eq_some_iff
      runtimeFormula assertion.formula).mp hformula
  exact ⟨assertion, hmember, hlabel, hruntime, hframe.symm, hembedded⟩

/-! ## Absence boundary -/

/-- A successful projection cannot fabricate an assertion view at a label
which is absent from the runtime database. -/
theorem projectedAssertion_label_ne_of_runtime_absent
    (db : RuntimeDB) (projection : PrefixProjection) (label : String)
    (hproject : projectPrefix? db = some projection)
    (habsent : db.find? label = none)
    (assertion : AssertionView)
    (hmember : assertion ∈ projection.assertions) :
    assertion.label ≠ label := by
  intro heq
  have hfidelity :=
    projectedAssertion_database_fidelity
      db projection assertion hproject hmember
  rw [heq, habsent] at hfidelity
  cases hfidelity.1

/-! ## Executable boundary -/

/-- A concrete traversal skips declarations on both sides of an assertion yet
retains that assertion with its exact decoder witness. -/
private def traversalBoundaryFormula : ConstantHeadedFormula :=
  ⟨"|-", []⟩

private def traversalBoundaryFrame : RuntimeFrame :=
  ⟨#[], #[]⟩

private def traversalBoundaryAssertion : AssertionView :=
  { label := "ax-T"
    formula := traversalBoundaryFormula
    frame := traversalBoundaryFrame
    hypotheses := [] }

example :
    ∃ assertion,
      assertion ∈ [traversalBoundaryAssertion] ∧
      projectAssertion? (default : RuntimeDB) "ax-T"
          traversalBoundaryFormula.toRuntime traversalBoundaryFrame "ax-T" =
        some assertion := by
  exact projectAssertionsFromEntries?_complete
    (default : RuntimeDB)
    [ ("|-", .const "|-")
    , ("ax-T", .assert traversalBoundaryFormula.toRuntime
        traversalBoundaryFrame "ax-T")
    , ("x", .var "x") ]
    [traversalBoundaryAssertion]
    "ax-T" "ax-T" traversalBoundaryFormula.toRuntime
    traversalBoundaryFrame (by rfl) (by simp)

end Mettapedia.Languages.Metamath.InferenceProjectionLookupCompleteness
