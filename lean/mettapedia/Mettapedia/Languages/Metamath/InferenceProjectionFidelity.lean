import Mettapedia.Languages.Metamath.InferenceProjectionParserBridge

/-!
# Database fidelity of the Metamath inference projection

This file proves that projected assertion and active-hypothesis views are
faithful to the live runtime database from which `projectPrefix?` reads them.
The result is extensional fidelity to the current object map.  It does not
assert that the database is a chronological parser prefix.
-/

namespace Mettapedia.Languages.Metamath.InferenceProjectionFidelity

open Mettapedia.Languages.Metamath.MMLean4Bridge
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.InferenceProjection
open Mettapedia.Languages.Metamath.InferenceProjectionParserBridge

/-! ## Fidelity of the partial decoders -/

private theorem proposition_of_guard_success {proposition : Prop}
    [Decidable proposition]
    (hsuccess : ∃ value, _root_.guard proposition = some value) :
    proposition := by
  obtain ⟨value, hvalue⟩ := hsuccess
  by_contra hfalse
  simp [_root_.guard, hfalse] at hvalue

/-- The runtime hypothesis discriminator represented by a projected view. -/
def hypothesisEssentialBit : HypothesisView → Bool
  | .floating _ _ _ => false
  | .essential _ _ => true

/-- A successful hypothesis view comes from an exact live hypothesis object;
its embedded label and decoded formula are not reconstructed independently. -/
theorem projectHypothesis?_eq_some_fidelity
    (db : RuntimeDB) (label : String) (hypothesis : HypothesisView)
    (hproject : projectHypothesis? db label = some hypothesis) :
    ∃ runtimeFormula,
      db.find? label =
        some (.hyp (hypothesisEssentialBit hypothesis) runtimeFormula label) ∧
      ConstantHeadedFormula.ofRuntime? runtimeFormula =
        some hypothesis.formula ∧
      hypothesis.label = label := by
  unfold projectHypothesis? at hproject
  simp only [bind] at hproject
  simp only [Option.bind_eq_some_iff] at hproject
  obtain ⟨object, hfind, hdecode⟩ := hproject
  cases object with
  | const name => simp at hdecode
  | var name => simp at hdecode
  | assert formula frame embeddedLabel => simp at hdecode
  | hyp essential runtimeFormula embeddedLabel =>
      cases essential with
      | false =>
          cases hformula : ConstantHeadedFormula.ofRuntime? runtimeFormula with
          | none => simp [hformula] at hdecode
          | some formula =>
              cases formula with
              | mk typecode body =>
                  cases body with
                  | nil => simp [hformula] at hdecode
                  | cons symbol tail =>
                      cases tail with
                      | cons next rest => simp [hformula] at hdecode
                      | nil =>
                          cases symbol with
                          | const name => simp [hformula] at hdecode
                          | var variableName =>
                              simp [hformula] at hdecode
                              obtain ⟨hembedded, hview⟩ := hdecode
                              have heq : embeddedLabel = label :=
                                proposition_of_guard_success hembedded
                              subst embeddedLabel
                              subst hypothesis
                              exact ⟨runtimeFormula, hfind, hformula, rfl⟩
      | true =>
          cases hformula : ConstantHeadedFormula.ofRuntime? runtimeFormula with
          | none => simp [hformula] at hdecode
          | some formula =>
              simp [hformula] at hdecode
              obtain ⟨hembedded, hview⟩ := hdecode
              have heq : embeddedLabel = label :=
                proposition_of_guard_success hembedded
              subst embeddedLabel
              subst hypothesis
              exact ⟨runtimeFormula, hfind, hformula, rfl⟩

/-- Successful list projection preserves the label order pointwise. -/
theorem projectHypotheses?_forall₂
    (db : RuntimeDB) (labels : List String)
    (hypotheses : List HypothesisView)
    (hproject : projectHypotheses? db labels = some hypotheses) :
    List.Forall₂
      (fun label hypothesis =>
        projectHypothesis? db label = some hypothesis)
      labels hypotheses := by
  induction labels generalizing hypotheses with
  | nil =>
      simp [projectHypotheses?] at hproject
      subst hypotheses
      exact .nil
  | cons label labels ih =>
      cases hhead : projectHypothesis? db label with
      | none => simp [projectHypotheses?, hhead] at hproject
      | some headHypothesis =>
          simp [projectHypotheses?, hhead] at hproject
          obtain ⟨tailHypotheses, htail, hresult⟩ := hproject
          have htail' :
              projectHypotheses? db labels = some tailHypotheses := by
            exact htail
          cases hresult
          exact .cons hhead (ih tailHypotheses htail')

/-- The projected views expose exactly the source frame's hypothesis labels,
in the same order. -/
theorem projectHypotheses?_labels
    (db : RuntimeDB) (labels : List String)
    (hypotheses : List HypothesisView)
    (hproject : projectHypotheses? db labels = some hypotheses) :
    hypotheses.map HypothesisView.label = labels := by
  have hordered := projectHypotheses?_forall₂ db labels hypotheses hproject
  clear hproject
  induction hordered with
  | nil => rfl
  | cons hhead _htail ih =>
      obtain ⟨_runtimeFormula, _hfind, _hdecode, hlabel⟩ :=
        projectHypothesis?_eq_some_fidelity _ _ _ hhead
      simp only [List.map_cons, hlabel, ih]

/-- Successful assertion decoding retains the source label, formula, frame,
and mandatory-hypothesis order exactly. -/
theorem projectAssertion?_eq_some_fidelity
    (db : RuntimeDB) (label embeddedLabel : String)
    (runtimeFormula : RuntimeFormula) (frame : RuntimeFrame)
    (assertion : AssertionView)
    (hproject :
      projectAssertion? db label runtimeFormula frame embeddedLabel =
        some assertion) :
    embeddedLabel = label ∧
      ConstantHeadedFormula.ofRuntime? runtimeFormula =
        some assertion.formula ∧
      projectHypotheses? db frame.hyps.toList = some assertion.hypotheses ∧
      assertion.label = label ∧ assertion.frame = frame := by
  simp [projectAssertion?] at hproject
  obtain ⟨⟨guardValue, hembedded⟩, formula, hformula, hypotheses,
    hhypotheses, _hframe, _hformulaFrame, hassertion⟩ := hproject
  subst assertion
  have heq : embeddedLabel = label := by
    by_contra hne
    simp [_root_.guard, hne] at hembedded
  exact ⟨heq, hformula, hhypotheses, rfl, rfl⟩

/-- Every assertion emitted by the entry traversal came from an assertion
entry in that exact input list and succeeded in the assertion decoder. -/
theorem projectAssertionsFromEntries?_member
    (db : RuntimeDB) (entries : List (String × Metamath.Verify.Object))
    (assertions : List AssertionView) (assertion : AssertionView)
    (hproject : projectAssertionsFromEntries? db entries = some assertions)
    (hmember : assertion ∈ assertions) :
    ∃ label runtimeFormula frame embeddedLabel,
      (label, .assert runtimeFormula frame embeddedLabel) ∈ entries ∧
      projectAssertion? db label runtimeFormula frame embeddedLabel =
        some assertion := by
  induction entries generalizing assertions with
  | nil =>
      simp [projectAssertionsFromEntries?] at hproject
      subst assertions
      simp at hmember
  | cons entry entries ih =>
      rcases entry with ⟨label, object⟩
      cases object with
      | const name =>
          simp only [projectAssertionsFromEntries?] at hproject
          obtain ⟨sourceLabel, sourceFormula, sourceFrame,
                sourceEmbeddedLabel, hsourceMember, hsourceProject⟩ :=
            ih assertions hproject hmember
          exact ⟨sourceLabel, sourceFormula, sourceFrame, sourceEmbeddedLabel,
            by exact List.mem_cons_of_mem _ hsourceMember, hsourceProject⟩
      | var name =>
          simp only [projectAssertionsFromEntries?] at hproject
          obtain ⟨sourceLabel, sourceFormula, sourceFrame,
                sourceEmbeddedLabel, hsourceMember, hsourceProject⟩ :=
            ih assertions hproject hmember
          exact ⟨sourceLabel, sourceFormula, sourceFrame, sourceEmbeddedLabel,
            by exact List.mem_cons_of_mem _ hsourceMember, hsourceProject⟩
      | hyp essential formula embeddedLabel =>
          simp only [projectAssertionsFromEntries?] at hproject
          obtain ⟨sourceLabel, sourceFormula, sourceFrame,
                sourceEmbeddedLabel, hsourceMember, hsourceProject⟩ :=
            ih assertions hproject hmember
          exact ⟨sourceLabel, sourceFormula, sourceFrame, sourceEmbeddedLabel,
            by exact List.mem_cons_of_mem _ hsourceMember, hsourceProject⟩
      | assert runtimeFormula frame embeddedLabel =>
          cases hhead : projectAssertion? db label runtimeFormula frame embeddedLabel with
          | none => simp [projectAssertionsFromEntries?, hhead] at hproject
          | some headAssertion =>
            cases htail : projectAssertionsFromEntries? db entries with
            | none => simp [projectAssertionsFromEntries?, hhead, htail] at hproject
            | some tailAssertions =>
              simp [projectAssertionsFromEntries?, hhead, htail] at hproject
              subst assertions
              simp only [List.mem_cons] at hmember
              rcases hmember with rfl | htailMember
              · exact ⟨label, runtimeFormula, frame, embeddedLabel,
                  by simp, hhead⟩
              · obtain ⟨sourceLabel, sourceFormula, sourceFrame,
                    sourceEmbeddedLabel, hsourceMember, hsourceProject⟩ :=
                  ih tailAssertions htail htailMember
                exact ⟨sourceLabel, sourceFormula, sourceFrame,
                  sourceEmbeddedLabel, by simp [hsourceMember], hsourceProject⟩

/-! ## Fidelity of a successful prefix projection -/

/-- The inspectable projection fields are the exact values computed from the
live database; in particular, neither declaration lists nor source views are
independently supplied data. -/
theorem projectPrefix?_eq_some_fields
    (db : RuntimeDB) (projection : PrefixProjection)
    (hproject : projectPrefix? db = some projection) :
    projection.declaredConstants =
        declaredConstantNames (objectEntries db) ∧
      projection.declaredVariables =
        declaredVariableNames (objectEntries db) ∧
      projection.callerFrame = proofFacingCallerFrame db ∧
      projectHypotheses? db db.frame.hyps.toList =
        some projection.activeHypotheses ∧
      projectAssertionsFromEntries? db (objectEntries db) =
        some projection.assertions := by
  unfold projectPrefix? at hproject
  simp only [bind] at hproject
  simp only [Option.bind_eq_some_iff] at hproject
  obtain ⟨_guardError, _herror, _guardWellFormed, _hwellFormed,
    _guardDV, _hdv, _guardRawDV, _hrawDV, _guardEmbedded, _hembedded,
    _guardDeclarations,
    _hdeclarations, activeHypotheses, hactive, _guardFrame, _hframe,
    assertions, hassertions, _guardProjection, _hprojectionValid,
    hprojection⟩ := hproject
  cases hprojection
  exact ⟨rfl, rfl, rfl, hactive, hassertions⟩

/-- Membership in the projected assertion list entails an exact live database
lookup.  The lookup includes the decoded runtime formula, source frame, and
embedded label; the remaining conclusions retain the hypothesis order and the
projection fields used to construct the snapshot. -/
theorem projectedAssertion_database_fidelity
    (db : RuntimeDB) (projection : PrefixProjection)
    (assertion : AssertionView)
    (hproject : projectPrefix? db = some projection)
    (hmember : assertion ∈ projection.assertions) :
    db.find? assertion.label =
        some (.assert assertion.formula.toRuntime assertion.frame
          assertion.label) ∧
      projectHypotheses? db assertion.frame.hyps.toList =
        some assertion.hypotheses ∧
      assertion.hypotheses.map HypothesisView.label =
        assertion.frame.hyps.toList ∧
      projection.declaredConstants =
        declaredConstantNames (objectEntries db) ∧
      projection.declaredVariables =
        declaredVariableNames (objectEntries db) ∧
      projection.callerFrame = proofFacingCallerFrame db ∧
      projectHypotheses? db db.frame.hyps.toList =
        some projection.activeHypotheses := by
  obtain ⟨hconstants, hvariables, hcaller, hactive, hassertions⟩ :=
    projectPrefix?_eq_some_fields db projection hproject
  obtain ⟨sourceLabel, runtimeFormula, sourceFrame, embeddedLabel,
      hentry, hsourceProject⟩ :=
    projectAssertionsFromEntries?_member db (objectEntries db)
      projection.assertions assertion hassertions hmember
  have hfind :
      db.find? sourceLabel =
        some (.assert runtimeFormula sourceFrame embeddedLabel) :=
    (objectEntries_exact db sourceLabel
      (.assert runtimeFormula sourceFrame embeddedLabel)).mp hentry
  obtain ⟨hembedded, hdecode, hhypotheses, hlabel, hframe⟩ :=
    projectAssertion?_eq_some_fidelity db sourceLabel embeddedLabel
      runtimeFormula sourceFrame assertion hsourceProject
  have hruntime : runtimeFormula = assertion.formula.toRuntime :=
    (ConstantHeadedFormula.ofRuntime?_eq_some_iff
      runtimeFormula assertion.formula).mp hdecode
  subst runtimeFormula
  subst sourceLabel
  subst sourceFrame
  subst embeddedLabel
  have hlabels :=
    projectHypotheses?_labels db assertion.frame.hyps.toList
      assertion.hypotheses hhypotheses
  exact ⟨hfind, hhypotheses, hlabels, hconstants, hvariables,
    hcaller, hactive⟩

/-- The whole active-hypothesis list is pointwise faithful to the current
runtime frame, retaining order as a `Forall₂` relation. -/
theorem projectedActiveHypotheses_ordered_fidelity
    (db : RuntimeDB) (projection : PrefixProjection)
    (hproject : projectPrefix? db = some projection) :
    List.Forall₂
      (fun label hypothesis =>
        projectHypothesis? db label = some hypothesis)
      db.frame.hyps.toList projection.activeHypotheses := by
  have hfields := projectPrefix?_eq_some_fields db projection hproject
  exact projectHypotheses?_forall₂ db db.frame.hyps.toList
    projection.activeHypotheses hfields.2.2.2.1

private theorem exists_left_of_forall₂_right_member
    {leftType rightType : Type} {relation : leftType → rightType → Prop}
    {left : List leftType} {right : List rightType}
    (hordered : List.Forall₂ relation left right)
    {target : rightType} (hmember : target ∈ right) :
    ∃ source, source ∈ left ∧ relation source target := by
  induction hordered with
  | nil => simp at hmember
  | cons hhead _htail ih =>
      simp only [List.mem_cons] at hmember
      rcases hmember with rfl | htailMember
      · exact ⟨_, by simp, hhead⟩
      · obtain ⟨source, hsourceMember, hsource⟩ := ih htailMember
        exact ⟨source, by simp [hsourceMember], hsource⟩

/-- An individual active view therefore has an exact live hypothesis lookup,
including its essential/floating bit, decoded formula, and embedded label. -/
theorem projectedActiveHypothesis_database_fidelity
    (db : RuntimeDB) (projection : PrefixProjection)
    (hypothesis : HypothesisView)
    (hproject : projectPrefix? db = some projection)
    (hmember : hypothesis ∈ projection.activeHypotheses) :
    hypothesis.label ∈ db.frame.hyps.toList ∧
      db.find? hypothesis.label =
        some (.hyp (hypothesisEssentialBit hypothesis)
          hypothesis.formula.toRuntime hypothesis.label) := by
  have hordered :=
    projectedActiveHypotheses_ordered_fidelity db projection hproject
  obtain ⟨label, hlabelMember, hlabelProject⟩ :=
    exists_left_of_forall₂_right_member hordered hmember
  obtain ⟨runtimeFormula, hfind, hdecode, hlabel⟩ :=
    projectHypothesis?_eq_some_fidelity db label hypothesis hlabelProject
  have hruntime : runtimeFormula = hypothesis.formula.toRuntime :=
    (ConstantHeadedFormula.ofRuntime?_eq_some_iff
      runtimeFormula hypothesis.formula).mp hdecode
  subst runtimeFormula
  subst label
  exact ⟨hlabelMember, hfind⟩

/-! ## Executable decoder boundaries -/

private def boundaryFormula : ConstantHeadedFormula :=
  ⟨"|-", [.const "T"]⟩

private def boundaryFrame : RuntimeFrame :=
  ⟨#[], #[]⟩

private def boundaryAssertion : AssertionView :=
  { label := "ax-T"
    formula := boundaryFormula
    frame := boundaryFrame
    hypotheses := [] }

/-- Positive boundary: an empty mandatory frame retains all assertion data. -/
example :
    projectAssertion? (default : RuntimeDB) "ax-T"
      boundaryFormula.toRuntime boundaryFrame "ax-T" =
        some boundaryAssertion := by
  rfl

/-- Negative boundary: a mismatched embedded label cannot yield a view. -/
example :
    projectAssertion? (default : RuntimeDB) "ax-T"
      boundaryFormula.toRuntime boundaryFrame "different-label" = none := by
  rfl

/-- Non-assertion entries are skipped rather than fabricated as assertions. -/
example (db : RuntimeDB) :
    projectAssertionsFromEntries? db [("T", .const "T")] = some [] := by
  rfl

end Mettapedia.Languages.Metamath.InferenceProjectionFidelity
