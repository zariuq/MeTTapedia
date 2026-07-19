import Metamath.Verify

/-!
# Relational graph of a live Metamath assertion step

This module exposes the successful assertion branch of the runtime checker as
an explicit relation.  Its witnesses record the selected database object, the
consumed stack window, the substitution recovered from the hypotheses, the
disjoint-variable check, the substituted conclusion, and the exact resulting
proof state.

The relation describes only the live `mm-lean4` runtime.  It does not identify
runtime steps with any generated inference calculus.
-/

namespace Mettapedia.Languages.Metamath.InferenceRuntimeAssertionGraph

open Std (HashMap)
open Metamath.Verify

/-- Component-wise graph of a successful assertion-label `DB.stepNormal`.

`stackPrefix` and `window` expose the exact stack boundary used by `checkHyp`.
The final equality is an equality of complete `ProofState`s, so fields other
than `stack` are preserved rather than merely related componentwise. -/
structure AssertionLabelStepWitness
    (db : DB) (pr : ProofState) (label : String) (result : ProofState) : Type where
  assertionFormula : Formula
  assertionFrame : Frame
  embeddedLabel : String
  lookup :
    db.find? label =
      some (.assert assertionFormula assertionFrame embeddedLabel)
  stackEnough : assertionFrame.hyps.size ≤ pr.stack.size
  assertionHasConstantHead : assertionFormula.hasConstHead = true
  assertionSymbolsRespectFrame :
    DB.formulaSymsRespectFrame db assertionFormula assertionFrame = true
  offset : Nat
  offset_eq : offset + assertionFrame.hyps.size = pr.stack.size
  offset_canonical :
    offset = pr.stack.size - assertionFrame.hyps.size
  stackPrefix : Array Formula
  stackPrefix_eq : stackPrefix = pr.stack.shrink offset
  window : Array Formula
  window_eq : window = pr.stack.extract offset pr.stack.size
  window_size : window.size = assertionFrame.hyps.size
  substitution : HashMap String Formula
  checkHyp_ok :
    DB.checkHyp db assertionFrame.hyps pr.stack
        ⟨offset, offset_eq⟩ 0 ∅ =
      Except.ok substitution
  callerVariables : List String
  callerVariables_eq : callerVariables = DB.frameFloatVars db db.frame
  dvCheck_ok :
    DB.dvCheck callerVariables db.frame.dj assertionFrame.dj substitution =
      Except.ok ()
  conclusion : Formula
  formula_subst_ok :
    assertionFormula.subst substitution = Except.ok conclusion
  result_eq : result = { pr with stack := stackPrefix.push conclusion }

/-- Relational graph: a step is related to a result exactly when its complete
component witness is inhabited. -/
def AssertionLabelStepGraph
    (db : DB) (pr : ProofState) (label : String) (result : ProofState) : Prop :=
  Nonempty (AssertionLabelStepWitness db pr label result)

/-- The label resolves to a stored assertion, as opposed to a hypothesis or a
data declaration.  The embedded label is retained because `Object.assert`
stores it even though `stepNormal` dispatches by the lookup key. -/
def IsAssertionLabel (db : DB) (label : String) : Prop :=
  ∃ formula frame embeddedLabel,
    db.find? label = some (.assert formula frame embeddedLabel)

private theorem extractWindow_size
    {stack : Array Formula} {offset hypothesisCount : Nat}
    (hoffset : offset + hypothesisCount = stack.size) :
    (stack.extract offset stack.size).size = hypothesisCount := by
  rw [Array.size_extract, Nat.min_self, ← hoffset]
  exact Nat.add_sub_cancel_left offset hypothesisCount

/-- Reassemble the executable assertion branch from its explicit component
witness. -/
theorem AssertionLabelStepWitness.stepNormal_ok
    {db : DB} {pr result : ProofState} {label : String}
    (witness : AssertionLabelStepWitness db pr label result) :
    db.stepNormal pr label = Except.ok result := by
  rcases witness with
    ⟨formula, frame, embeddedLabel, hlookup, hstack, hhead, hsymbols,
      offset, hoffset, hcanonical, stackPrefix, hprefix, window, hwindow,
      hwindowSize,
      substitution, hcheckHyp, callerVariables, hcallerVariables, hdv,
      conclusion, hsubst, hresult⟩
  subst offset
  unfold DB.stepNormal
  rw [hlookup]
  unfold DB.stepAssert
  simp only [hstack, ↓reduceDIte, hhead, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte, hsymbols]
  simp only [bind, Except.bind]
  simp only [hcheckHyp]
  simp only [← hcallerVariables, hdv]
  simp only [hsubst]
  simpa [pure, Except.pure, hprefix] using hresult.symm

/-- A live assertion-label step succeeds with `result` exactly when the label
really selects an assertion and the component-wise relational graph is
inhabited.  The assertion-label conjunct is necessary: hypothesis labels also
have successful `stepNormal` branches. -/
theorem assertionLabelStepGraph_iff_stepNormal_ok
    (db : DB) (pr result : ProofState) (label : String) :
    AssertionLabelStepGraph db pr label result ↔
      IsAssertionLabel db label ∧
        db.stepNormal pr label = Except.ok result := by
  constructor
  · rintro ⟨witness⟩
    exact
      ⟨⟨witness.assertionFormula, witness.assertionFrame,
          witness.embeddedLabel, witness.lookup⟩,
        witness.stepNormal_ok⟩
  · rintro ⟨⟨formula, frame, embeddedLabel, hlookup⟩, hstep⟩
    unfold DB.stepNormal at hstep
    simp only [hlookup] at hstep
    simp only [DB.stepAssert] at hstep
    have hstack : frame.hyps.size ≤ pr.stack.size := by
      by_cases hvalue : frame.hyps.size ≤ pr.stack.size
      · exact hvalue
      · rw [dif_neg hvalue] at hstep
        simp at hstep
    rw [dif_pos hstack] at hstep
    have hhead : formula.hasConstHead = true := by
      cases hvalue : formula.hasConstHead with
      | false => simp [hvalue] at hstep
      | true => rfl
    simp only [hhead, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hstep
    have hsymbols :
        DB.formulaSymsRespectFrame db formula frame = true := by
      cases hvalue : DB.formulaSymsRespectFrame db formula frame with
      | false => simp [hvalue] at hstep
      | true => rfl
    simp only [hsymbols, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hstep
    simp only [bind, Except.bind] at hstep
    let offset := pr.stack.size - frame.hyps.size
    have hoffset : offset + frame.hyps.size = pr.stack.size := by
      exact Nat.sub_add_cancel hstack
    cases hcheckHyp :
        DB.checkHyp db frame.hyps pr.stack ⟨offset, hoffset⟩ 0 ∅ with
    | error error =>
        simp [offset, hcheckHyp] at hstep
    | ok substitution =>
        simp only [offset, hcheckHyp] at hstep
        let callerVariables := DB.frameFloatVars db db.frame
        cases hdv :
            DB.dvCheck callerVariables db.frame.dj frame.dj substitution with
        | error error =>
            simp [callerVariables, hdv] at hstep
        | ok unitResult =>
            simp only [callerVariables, hdv] at hstep
            cases hsubst : formula.subst substitution with
            | error error =>
                simp [hsubst] at hstep
            | ok conclusion =>
                simp only [hsubst, pure, Except.pure, Except.ok.injEq] at hstep
                let stackPrefix := pr.stack.shrink offset
                let window := pr.stack.extract offset pr.stack.size
                refine ⟨⟨
                  formula,
                  frame,
                  embeddedLabel,
                  hlookup,
                  hstack,
                  hhead,
                  hsymbols,
                  offset,
                  hoffset,
                  rfl,
                  stackPrefix,
                  rfl,
                  window,
                  rfl,
                  extractWindow_size hoffset,
                  substitution,
                  ?_,
                  callerVariables,
                  rfl,
                  ?_,
                  conclusion,
                  hsubst,
                  ?_
                ⟩⟩
                · exact hcheckHyp
                · simpa [callerVariables] using hdv
                · simpa [stackPrefix, offset] using hstep.symm

/-- Direct checker equivalence once the lookup is known to select the stated
assertion object. -/
theorem assertionLabelStepGraph_iff_stepNormal_ok_of_lookup
    (db : DB) (pr result : ProofState) (label : String)
    (formula : Formula) (frame : Frame) (embeddedLabel : String)
    (hlookup : db.find? label = some (.assert formula frame embeddedLabel)) :
    AssertionLabelStepGraph db pr label result ↔
      db.stepNormal pr label = Except.ok result := by
  rw [assertionLabelStepGraph_iff_stepNormal_ok]
  constructor
  · exact And.right
  · intro hstep
    exact ⟨⟨formula, frame, embeddedLabel, hlookup⟩, hstep⟩

/-- The exact update shape carried by the graph; no non-stack field is
abstracted away. -/
theorem AssertionLabelStepGraph.result_shape
    {db : DB} {pr result : ProofState} {label : String}
    (hgraph : AssertionLabelStepGraph db pr label result) :
    ∃ (stackPrefix : Array Formula) (conclusion : Formula),
      result = { pr with stack := stackPrefix.push conclusion } := by
  rcases hgraph with ⟨witness⟩
  exact ⟨witness.stackPrefix, witness.conclusion, witness.result_eq⟩

/-- Every field outside the proof stack is preserved by exact equality. -/
theorem AssertionLabelStepGraph.preserves_nonstack_fields
    {db : DB} {pr result : ProofState} {label : String}
    (hgraph : AssertionLabelStepGraph db pr label result) :
    result.pos = pr.pos ∧
      result.label = pr.label ∧
      result.fmla = pr.fmla ∧
      result.frame = pr.frame ∧
      result.heap = pr.heap ∧
      result.ptp = pr.ptp := by
  rcases hgraph with ⟨witness⟩
  rw [witness.result_eq]
  cases pr
  simp

/-! ## Executable boundaries -/

private def constantBoundaryFormula : Formula :=
  #[.const "T"]

private def emptyBoundaryFrame : Frame :=
  ⟨#[], #[]⟩

/-- Positive boundary: a constant assertion with no hypotheses has an explicit
graph witness for every pre-existing stack. -/
theorem emptyFrame_constantAssertion_graph
    (db : DB) (pr : ProofState) (label embeddedLabel : String)
    (hlookup :
      db.find? label =
        some (.assert constantBoundaryFormula emptyBoundaryFrame embeddedLabel)) :
    AssertionLabelStepGraph db pr label
      { pr with
        stack := (pr.stack.shrink pr.stack.size).push constantBoundaryFormula } := by
  let offset := pr.stack.size
  have hoffset : offset + emptyBoundaryFrame.hyps.size = pr.stack.size := by
    simp [offset, emptyBoundaryFrame]
  let stackPrefix := pr.stack.shrink offset
  let window := pr.stack.extract offset pr.stack.size
  let callerVariables := DB.frameFloatVars db db.frame
  refine ⟨{
    assertionFormula := constantBoundaryFormula
    assertionFrame := emptyBoundaryFrame
    embeddedLabel := embeddedLabel
    lookup := hlookup
    stackEnough := by simp [emptyBoundaryFrame]
    assertionHasConstantHead := by rfl
    assertionSymbolsRespectFrame := by
      simp [DB.formulaSymsRespectFrame, constantBoundaryFormula,
        emptyBoundaryFrame]
    offset := offset
    offset_eq := hoffset
    offset_canonical := by simp [offset, emptyBoundaryFrame]
    stackPrefix := stackPrefix
    stackPrefix_eq := rfl
    window := window
    window_eq := rfl
    window_size := extractWindow_size hoffset
    substitution := ∅
    checkHyp_ok := by
      simp [DB.checkHyp, emptyBoundaryFrame, pure, Except.pure]
    callerVariables := callerVariables
    callerVariables_eq := rfl
    dvCheck_ok := by
      simp [DB.dvCheck, DB.dvCheckBool, emptyBoundaryFrame]
      intro left right
      intro hmem
      cases hmem
    conclusion := constantBoundaryFormula
    formula_subst_ok := by
      rfl
    result_eq := by
      rfl
  }⟩

/-- Negative boundary: a hypothesis object can never inhabit the assertion
graph, even when its own `stepNormal` branch would succeed. -/
theorem not_graph_of_hypothesis_lookup
    (db : DB) (pr result : ProofState) (label storedLabel : String)
    (essential : Bool) (formula : Formula)
    (hlookup : db.find? label = some (.hyp essential formula storedLabel)) :
    ¬ AssertionLabelStepGraph db pr label result := by
  rintro ⟨witness⟩
  have himpossible := witness.lookup
  rw [hlookup] at himpossible
  simp at himpossible

/-- Negative boundary: an absent database label cannot inhabit the assertion
graph. -/
theorem not_graph_of_missing_label
    (db : DB) (pr result : ProofState) (label : String)
    (hlookup : db.find? label = none) :
    ¬ AssertionLabelStepGraph db pr label result := by
  rintro ⟨witness⟩
  have himpossible := witness.lookup
  rw [hlookup] at himpossible
  simp at himpossible

end Mettapedia.Languages.Metamath.InferenceRuntimeAssertionGraph
