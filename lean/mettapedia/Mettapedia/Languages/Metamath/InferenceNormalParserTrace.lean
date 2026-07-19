import Mettapedia.Languages.Metamath.MMLean4Bridge
import Metamath.ParserAnyModeEquivalence

/-!
# Exact extraction of normal Metamath parser traces

This module retains the submitted normal-proof tokens and both complete
runtime proof states.  A successful parser trace is reflected to the exact
left-to-right `stepNormal` fold over the labels decoded from those tokens.
The fold runs against the pre-insertion database used by `feedProof`.

The initial state is the result of `DB.mkProofState` with the theorem's
trimmed target frame.  It is deliberately not required to use `db.frame`.
Successful `finishProof` then supplies target-label freshness and the exact
post-state insertion, so the submitted labels cannot refer to the theorem
being proved.

This is a normal-mode trace theorem.  It does not cover compressed tokens and
does not infer a trace from a final database or from stack-only reachability.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.InferenceNormalParserTrace

open Mettapedia.Languages.Metamath.MMLean4Bridge
open Metamath.Verify
open Metamath.PrefixProvenance
  (NormalTokensOK goNormal_extracts_stepNormal
    finishProof_prefix_characterization stepNormal_preserves_label
    stepNormal_preserves_ptp)
open Metamath.PrefixTraceCompressed (feedProof_success_go_ok)
open Metamath.ParserAnyModeEquivalence (finishProof_success_stack_conditions)

/-- Exact source order of labels submitted in a normal proof. -/
def submittedNormalLabels (firstToken : ByteSlice)
    (remainingTokens : List ByteSlice) : List String :=
  (firstToken :: remainingTokens).map fun token => (toLabel token).2

/-- An array with one element and the expected value at index zero is the
corresponding singleton. -/
private theorem array_eq_singleton_of_size_getElem?
    {α : Type} (array : Array α) (value : α)
    (hsize : array.size = 1) (hvalue : array[0]? = some value) :
    array = #[value] := by
  obtain ⟨hindex, heq⟩ := Array.getElem_of_getElem? hvalue
  apply Array.ext'
  have hlength : array.toList.length = 1 := by
    rwa [Array.length_toList]
  rw [List.eq_getElem_of_length_eq_one array.toList hlength]
  simp
  exact heq

/-- A parser-origin normal trace with its canonical initial state, exact first
transition, remaining token trace, and complete final proof state.  The target
frame is the trimmed frame supplied to `mkProofState`, not the ambient frame of
the prefix database. -/
structure ExactNormalParserTrace
    (s : ParserState) (pos : Pos) (targetLabel : String)
    (targetFormula : RuntimeFormula) (targetFrame : RuntimeFrame)
    (firstToken : ByteSlice) (remainingTokens : List ByteSlice)
    (initial afterFirst final : RuntimeProofState) : Prop where
  initial_eq :
    initial = s.db.mkProofState pos targetLabel targetFormula targetFrame
  first_success : (s.feedProof firstToken initial).db.error? = none
  first_not_open : ¬ firstToken.eqArray "(".toAscii
  first_not_unknown : ¬ firstToken.eqArray "?".toAscii
  first_result : (s.feedProof firstToken initial).tokp = .proof afterFirst
  remaining : NormalTokensOK s afterFirst remainingTokens final

/-- `resumeThm` installs exactly the `mkProofState` produced from the supplied
trimmed target frame and leaves the prefix database unchanged. -/
@[simp] theorem resumeThm_exact
    (s : ParserState) (pos : Pos) (targetLabel : String)
    (targetFormula : RuntimeFormula) (targetFrame : RuntimeFrame) :
    (s.resumeThm pos targetLabel targetFormula targetFrame).db = s.db ∧
      (s.resumeThm pos targetLabel targetFormula targetFrame).tokp =
        .proof (s.db.mkProofState pos targetLabel targetFormula targetFrame) := by
  simp [ParserState.resumeThm]

private theorem normalFeedProof_extracts_step
    (s : ParserState) (token : ByteSlice) (initial final : RuntimeProofState)
    (hsuccess : (s.feedProof token initial).db.error? = none)
    (hresult : (s.feedProof token initial).tokp = .proof final)
    (hnormal : initial.ptp = .normal)
    (hnotUnknown : ¬ token.eqArray "?".toAscii) :
    s.db.stepNormal initial (toLabel token).2 = .ok final := by
  obtain ⟨actual, hgo, hactual⟩ :=
    feedProof_success_go_ok s token initial hsuccess
  have hactualEq : final = actual := by
    rw [hresult] at hactual
    exact TokenParser.proof.inj hactual
  subst actual
  have hgoNormal :
      ParserState.feedProof.goNormal s token initial = .ok final := by
    unfold ParserState.feedProof.go at hgo
    simpa [hnormal] using hgo
  exact goNormal_extracts_stepNormal s token initial final hgoNormal hnotUnknown

private theorem ExactNormalParserTrace.first_stepNormal
    {s : ParserState} {pos : Pos} {targetLabel : String}
    {targetFormula : RuntimeFormula} {targetFrame : RuntimeFrame}
    {firstToken : ByteSlice} {remainingTokens : List ByteSlice}
    {initial afterFirst final : RuntimeProofState}
    (trace : ExactNormalParserTrace s pos targetLabel targetFormula targetFrame
      firstToken remainingTokens initial afterFirst final) :
    s.db.stepNormal {initial with ptp := .normal} (toLabel firstToken).2 =
      .ok afterFirst := by
  have hstart : initial.ptp = .start := by
    simp [trace.initial_eq, DB.mkProofState]
  obtain ⟨actual, hgo, hactual⟩ :=
    feedProof_success_go_ok s firstToken initial trace.first_success
  have hactualEq : afterFirst = actual := by
    rw [trace.first_result] at hactual
    exact TokenParser.proof.inj hactual
  subst actual
  have hgoNormal :
      ParserState.feedProof.goNormal s firstToken
        {initial with ptp := .normal} = .ok afterFirst := by
    unfold ParserState.feedProof.go at hgo
    simpa [hstart, trace.first_not_open] using hgo
  exact goNormal_extracts_stepNormal s firstToken {initial with ptp := .normal}
    afterFirst hgoNormal trace.first_not_unknown

/-- The existing recursive parser trace reflects to the exact fold over the
submitted labels.  No ghost state or existential replacement label list is
introduced. -/
theorem normalTokensOK_extracts_exact_fold
    (s : ParserState) (tokens : List ByteSlice)
    (initial final : RuntimeProofState)
    (htrace : NormalTokensOK s initial tokens final) :
    (tokens.map fun token => (toLabel token).2).foldlM
        (DB.stepNormal s.db) initial = .ok final := by
  induction tokens generalizing initial with
  | nil =>
      unfold NormalTokensOK at htrace
      subst final
      rfl
  | cons token rest ih =>
      unfold NormalTokensOK at htrace
      obtain ⟨middle, hsuccess, hresult, hnormal, hnotUnknown, hrest⟩ := htrace
      have hstep :
          s.db.stepNormal initial (toLabel token).2 = .ok middle :=
        normalFeedProof_extracts_step s token initial middle
          hsuccess hresult hnormal hnotUnknown
      have htail := ih middle hrest
      simp only [List.map_cons, List.foldlM_cons, hstep, bind,
        Except.bind, htail]

/-- Every exact submitted label in a successful normal token trace resolves in
the same pre-insertion database. -/
theorem normalTokensOK_labels_resolve
    (s : ParserState) (tokens : List ByteSlice)
    (initial final : RuntimeProofState)
    (htrace : NormalTokensOK s initial tokens final) :
    ∀ label ∈ tokens.map (fun token => (toLabel token).2),
      ∃ object, s.db.find? label = some object := by
  induction tokens generalizing initial with
  | nil => simp
  | cons token rest ih =>
      unfold NormalTokensOK at htrace
      obtain ⟨middle, hsuccess, hresult, hnormal, hnotUnknown, hrest⟩ := htrace
      have hstep :
          s.db.stepNormal initial (toLabel token).2 = .ok middle :=
        normalFeedProof_extracts_step s token initial middle
          hsuccess hresult hnormal hnotUnknown
      have hlookup : ∃ object, s.db.find? (toLabel token).2 = some object := by
        cases hfind : s.db.find? (toLabel token).2 with
        | none =>
            simp [DB.stepNormal, hfind] at hstep
        | some object => exact ⟨object, rfl⟩
      intro label hlabel
      simp only [List.map_cons, List.mem_cons] at hlabel
      rcases hlabel with hlabel | hlabel
      · subst label
        exact hlookup
      · exact ih middle hrest label hlabel

private theorem normalTokensOK_preserves_core
    (s : ParserState) (tokens : List ByteSlice)
    (initial final : RuntimeProofState)
    (htrace : NormalTokensOK s initial tokens final) :
    final.label = initial.label ∧
      final.fmla = initial.fmla ∧
      final.frame = initial.frame ∧
      final.ptp = initial.ptp := by
  induction tokens generalizing initial with
  | nil =>
      unfold NormalTokensOK at htrace
      subst final
      exact ⟨rfl, rfl, rfl, rfl⟩
  | cons token rest ih =>
      unfold NormalTokensOK at htrace
      obtain ⟨middle, hsuccess, hresult, hnormal, hnotUnknown, hrest⟩ := htrace
      have hstep :
          s.db.stepNormal initial (toLabel token).2 = .ok middle :=
        normalFeedProof_extracts_step s token initial middle
          hsuccess hresult hnormal hnotUnknown
      have hheadLabel :=
        stepNormal_preserves_label s.db initial middle (toLabel token).2 hstep
      have hheadCore :=
        Metamath.ParserOps.stepNormal_ok_preserves_core
          s.db initial middle (toLabel token).2 hstep
      have hheadMode :=
        stepNormal_preserves_ptp s.db initial middle (toLabel token).2 hstep
      obtain ⟨htailLabel, htailFormula, htailFrame, htailMode⟩ :=
        ih middle hrest
      exact ⟨htailLabel.trans hheadLabel,
        htailFormula.trans hheadCore.1,
        htailFrame.trans hheadCore.2,
        htailMode.trans hheadMode⟩

/-- Exact extraction for a complete parser-origin trace.  The left-to-right
token order is observable in `submittedNormalLabels`, and both fold endpoints
are the original complete proof states. -/
theorem ExactNormalParserTrace.extracts_exact_fold
    {s : ParserState} {pos : Pos} {targetLabel : String}
    {targetFormula : RuntimeFormula} {targetFrame : RuntimeFrame}
    {firstToken : ByteSlice} {remainingTokens : List ByteSlice}
    {initial afterFirst final : RuntimeProofState}
    (trace : ExactNormalParserTrace s pos targetLabel targetFormula targetFrame
      firstToken remainingTokens initial afterFirst final) :
    (submittedNormalLabels firstToken remainingTokens).foldlM
        (DB.stepNormal s.db) {initial with ptp := .normal} = .ok final := by
  have hremaining := normalTokensOK_extracts_exact_fold
    s remainingTokens afterFirst final trace.remaining
  simp only [submittedNormalLabels, List.map_cons, List.foldlM_cons,
    trace.first_stepNormal, bind, Except.bind, hremaining]

/-- Every label retained by a complete trace resolves in its pre-insertion
database, in the exact submitted order. -/
theorem ExactNormalParserTrace.labels_resolve
    {s : ParserState} {pos : Pos} {targetLabel : String}
    {targetFormula : RuntimeFormula} {targetFrame : RuntimeFrame}
    {firstToken : ByteSlice} {remainingTokens : List ByteSlice}
    {initial afterFirst final : RuntimeProofState}
    (trace : ExactNormalParserTrace s pos targetLabel targetFormula targetFrame
      firstToken remainingTokens initial afterFirst final) :
    ∀ label ∈ submittedNormalLabels firstToken remainingTokens,
      ∃ object, s.db.find? label = some object := by
  have hfirstLookup : ∃ object, s.db.find? (toLabel firstToken).2 = some object := by
    cases hfind : s.db.find? (toLabel firstToken).2 with
    | none =>
        have hfirstStep := trace.first_stepNormal
        simp [DB.stepNormal, hfind] at hfirstStep
    | some object => exact ⟨object, rfl⟩
  intro label hlabel
  simp only [submittedNormalLabels, List.map_cons, List.mem_cons] at hlabel
  rcases hlabel with hlabel | hlabel
  · subst label
    exact hfirstLookup
  · exact normalTokensOK_labels_resolve s remainingTokens afterFirst final
      trace.remaining label hlabel

/-- Normal execution preserves the theorem identity, its trimmed target frame,
and normal mode from the canonical parser state to the retained final state. -/
theorem ExactNormalParserTrace.final_target_core
    {s : ParserState} {pos : Pos} {targetLabel : String}
    {targetFormula : RuntimeFormula} {targetFrame : RuntimeFrame}
    {firstToken : ByteSlice} {remainingTokens : List ByteSlice}
    {initial afterFirst final : RuntimeProofState}
    (trace : ExactNormalParserTrace s pos targetLabel targetFormula targetFrame
      firstToken remainingTokens initial afterFirst final) :
    final.label = targetLabel ∧
      final.fmla = targetFormula ∧
      final.frame = targetFrame ∧
      final.ptp = .normal := by
  have hfirstLabel := stepNormal_preserves_label s.db
    {initial with ptp := .normal} afterFirst (toLabel firstToken).2
      trace.first_stepNormal
  have hfirstCore := Metamath.ParserOps.stepNormal_ok_preserves_core s.db
    {initial with ptp := .normal} afterFirst (toLabel firstToken).2
      trace.first_stepNormal
  have hfirstMode := stepNormal_preserves_ptp s.db
    {initial with ptp := .normal} afterFirst (toLabel firstToken).2
      trace.first_stepNormal
  obtain ⟨hrestLabel, hrestFormula, hrestFrame, hrestMode⟩ :=
    normalTokensOK_preserves_core s remainingTokens afterFirst final trace.remaining
  constructor
  · rw [hrestLabel, hfirstLabel, trace.initial_eq]
    rfl
  constructor
  · rw [hrestFormula, hfirstCore.1, trace.initial_eq]
    rfl
  constructor
  · rw [hrestFrame, hfirstCore.2, trace.initial_eq]
    rfl
  · rw [hrestMode, hfirstMode]

/-- A successful normal `finishProof` leaves exactly the claimed theorem
formula as the singleton runtime stack. -/
theorem ExactNormalParserTrace.final_stack_eq_singleton
    {s : ParserState} {pos : Pos} {targetLabel : String}
    {targetFormula : RuntimeFormula} {targetFrame : RuntimeFrame}
    {firstToken : ByteSlice} {remainingTokens : List ByteSlice}
    {initial afterFirst final : RuntimeProofState}
    (trace : ExactNormalParserTrace s pos targetLabel targetFormula targetFrame
      firstToken remainingTokens initial afterFirst final)
    (hfinish : (s.finishProof final).db.error? = none) :
    final.stack = #[targetFormula] := by
  obtain ⟨hstackSize, hstackValue, _⟩ :=
    finishProof_success_stack_conditions s final hfinish
  apply array_eq_singleton_of_size_getElem? final.stack targetFormula hstackSize
  simpa [trace.final_target_core.2.1] using hstackValue

/-- Successful `finishProof` closes the prefix boundary for the exact trace.
The conclusion records the exact fold, target fields, exact post-insert DB,
freshness in the pre-insertion DB, and explicit absence of self-reference from
the submitted labels. -/
theorem ExactNormalParserTrace.accepted_prefix_boundary
    {s : ParserState} {pos : Pos} {targetLabel : String}
    {targetFormula : RuntimeFormula} {targetFrame : RuntimeFrame}
    {firstToken : ByteSlice} {remainingTokens : List ByteSlice}
    {initial afterFirst final : RuntimeProofState}
    (trace : ExactNormalParserTrace s pos targetLabel targetFormula targetFrame
      firstToken remainingTokens initial afterFirst final)
    (hfinish : (s.finishProof final).db.error? = none) :
    (submittedNormalLabels firstToken remainingTokens).foldlM
        (DB.stepNormal s.db) {initial with ptp := .normal} = .ok final ∧
      final.label = targetLabel ∧
      final.fmla = targetFormula ∧
      final.frame = targetFrame ∧
      final.ptp = .normal ∧
      final.stack = #[targetFormula] ∧
      (s.finishProof final).db =
        s.db.insert final.pos targetLabel (.assert targetFormula targetFrame) ∧
      s.db.find? targetLabel = none ∧
      targetLabel ∉ submittedNormalLabels firstToken remainingTokens := by
  obtain ⟨hfinalLabel, hfinalFormula, hfinalFrame, hfinalMode⟩ :=
    trace.final_target_core
  have hfinalStack := trace.final_stack_eq_singleton hfinish
  have hprefix : s.db.error? = none := by
    have hdb := Metamath.ParserOps.feedProof_success_db
      s firstToken initial trace.first_success
    rw [← hdb]
    exact trace.first_success
  obtain ⟨hinsert, _, hfreshFinal⟩ :=
    finishProof_prefix_characterization s final hfinish hprefix
  have hfresh : s.db.find? targetLabel = none := by
    simpa [hfinalLabel] using hfreshFinal
  have hpost :
      (s.finishProof final).db =
        s.db.insert final.pos targetLabel (.assert targetFormula targetFrame) := by
    simpa [hfinalLabel, hfinalFormula, hfinalFrame] using hinsert
  have hnoSelf : targetLabel ∉
      submittedNormalLabels firstToken remainingTokens := by
    intro hmember
    obtain ⟨object, hlookup⟩ := trace.labels_resolve targetLabel hmember
    rw [hfresh] at hlookup
    contradiction
  exact ⟨trace.extracts_exact_fold, hfinalLabel, hfinalFormula, hfinalFrame,
    hfinalMode, hfinalStack, hpost, hfresh, hnoSelf⟩

/-! ## Positive and negative interface boundaries -/

example
    {s : ParserState} {pos : Pos} {targetLabel : String}
    {targetFormula : RuntimeFormula} {targetFrame : RuntimeFrame}
    {firstToken : ByteSlice} {remainingTokens : List ByteSlice}
    {initial afterFirst final : RuntimeProofState}
    (trace : ExactNormalParserTrace s pos targetLabel targetFormula targetFrame
      firstToken remainingTokens initial afterFirst final)
    (hfinish : (s.finishProof final).db.error? = none) :
    targetLabel ∉ submittedNormalLabels firstToken remainingTokens := by
  exact (trace.accepted_prefix_boundary hfinish).2.2.2.2.2.2.2.2

/-- A trimmed theorem frame distinct from the ambient database frame remains
distinct in the canonical initial proof state. -/
example
    {s : ParserState} {pos : Pos} {targetLabel : String}
    {targetFormula : RuntimeFormula} {targetFrame : RuntimeFrame}
    {firstToken : ByteSlice} {remainingTokens : List ByteSlice}
    {initial afterFirst final : RuntimeProofState}
    (trace : ExactNormalParserTrace s pos targetLabel targetFormula targetFrame
      firstToken remainingTokens initial afterFirst final)
    (hframes : targetFrame ≠ s.db.frame) :
    initial.frame ≠ s.db.frame := by
  simpa [trace.initial_eq, DB.mkProofState] using hframes

/-- A candidate trace whose exact source-ordered fold does not reach the
retained final state cannot inhabit the parser-trace interface. -/
example
    {s : ParserState} {pos : Pos} {targetLabel : String}
    {targetFormula : RuntimeFormula} {targetFrame : RuntimeFrame}
    {firstToken : ByteSlice} {remainingTokens : List ByteSlice}
    {initial afterFirst final : RuntimeProofState}
    (hwrong :
      (submittedNormalLabels firstToken remainingTokens).foldlM
          (DB.stepNormal s.db) {initial with ptp := .normal} ≠ .ok final) :
    ¬ ExactNormalParserTrace s pos targetLabel targetFormula targetFrame
      firstToken remainingTokens initial afterFirst final := by
  intro trace
  exact hwrong trace.extracts_exact_fold

end Mettapedia.Languages.Metamath.InferenceNormalParserTrace
