import Mettapedia.Languages.Metamath.InferenceOperationalSpecStepSoundness

/-!
# Exact inversion of singleton Metamath operational steps

The operational specification stores proof steps in reverse execution order:
the outer constructor contributes the head of the step list.  For a singleton
step, its recursive premise therefore has no steps and must leave the initial
stack unchanged.  The equivalences below expose precisely the remaining
constructor data.

This is inversion internal to `Metamath.Spec.ProofValidFrom`.  In particular,
the assertion equivalence does not reify an arbitrary operational frame,
substitution, or expression into the projected generated calculus.
-/

namespace Mettapedia.Languages.Metamath.InferenceOperationalSpecStepInversion

/-! ## Hypothesis steps -/

/-- The exact expression pushed by an upstream hypothesis step. -/
def pushedHypothesisExpr : Metamath.Spec.Hyp → Metamath.Spec.Expr
  | .essential expression => expression
  | .floating typecode variableName =>
      { typecode := typecode, syms := [variableName.v] }

@[simp] theorem pushedHypothesisExpr_essential
    (expression : Metamath.Spec.Expr) :
    pushedHypothesisExpr (.essential expression) = expression := rfl

@[simp] theorem pushedHypothesisExpr_floating
    (typecode : Metamath.Spec.Constant)
    (variableName : Metamath.Spec.Variable) :
    pushedHypothesisExpr (.floating typecode variableName) =
      ({ typecode := typecode, syms := [variableName.v] } :
        Metamath.Spec.Expr) := rfl

/-- A singleton upstream hypothesis proof is exactly membership in the caller
frame followed by the hypothesis expression pushed onto the unchanged initial
stack. -/
theorem proofValidFrom_single_useHyp_iff
    (database : Metamath.Spec.Database) (frame : Metamath.Spec.Frame)
    (initial final : List Metamath.Spec.Expr)
    (hypothesis : Metamath.Spec.Hyp) :
    Metamath.Spec.ProofValidFrom database frame initial final
        [Metamath.Spec.ProofStep.useHyp hypothesis] ↔
      hypothesis ∈ frame.hyps ∧
        final = pushedHypothesisExpr hypothesis :: initial := by
  constructor
  · intro valid
    cases valid with
    | useEssential stack steps expression hmember previous =>
        cases previous
        exact ⟨hmember, rfl⟩
    | useFloating stack steps typecode variableName hmember previous =>
        cases previous
        exact ⟨hmember, rfl⟩
  · rintro ⟨hmember, hfinal⟩
    rw [hfinal]
    cases hypothesis with
    | essential expression =>
        exact Metamath.Spec.ProofValidFrom.useEssential
          frame initial initial [] expression hmember
            (Metamath.Spec.ProofValidFrom.nil frame initial)
    | floating typecode variableName =>
        exact Metamath.Spec.ProofValidFrom.useFloating
          frame initial initial [] typecode variableName hmember
            (Metamath.Spec.ProofValidFrom.nil frame initial)

/-! ## Assertion steps -/

/-- A singleton upstream assertion proof contains exactly one successful
database lookup, the assertion's DV and floating-typing obligations, its
authored mandatory-hypothesis vector, one reversal of that vector at the head
of the initial stack, and the substituted assertion at the head of the
remaining suffix. -/
theorem proofValidFrom_single_useAssertion_iff
    (database : Metamath.Spec.Database) (frame : Metamath.Spec.Frame)
    (initial final : List Metamath.Spec.Expr)
    (label : Metamath.Spec.Label) (substitution : Metamath.Spec.Subst) :
    Metamath.Spec.ProofValidFrom database frame initial final
        [Metamath.Spec.ProofStep.useAssertion label substitution] ↔
      ∃ assertionFrame assertion needed remaining,
        database label = some (assertionFrame, assertion) ∧
        Metamath.Spec.dvOK frame.vars assertionFrame.dv frame.dv
          substitution ∧
        (∀ typecode variableName,
          Metamath.Spec.Hyp.floating typecode variableName ∈
              assertionFrame.hyps →
            (substitution variableName).typecode = typecode) ∧
        needed = assertionFrame.hyps.map (fun hypothesis =>
          match hypothesis with
          | .essential expression =>
              Metamath.Spec.applySubst assertionFrame.vars substitution
                expression
          | .floating _ variableName => substitution variableName) ∧
        initial = needed.reverse ++ remaining ∧
        final =
          Metamath.Spec.applySubst assertionFrame.vars substitution assertion ::
            remaining := by
  constructor
  · intro valid
    cases valid with
    | useAxiom stack steps stepLabel assertionFrame assertion stepSubstitution
        hlookup hdv htyped previous needed hneeded remaining hstack =>
        cases previous
        exact ⟨assertionFrame, assertion, needed, remaining,
          hlookup, hdv, htyped, hneeded, hstack, rfl⟩
  · rintro ⟨assertionFrame, assertion, needed, remaining,
      hlookup, hdv, htyped, hneeded, hinitial, hfinal⟩
    rw [hfinal]
    exact Metamath.Spec.ProofValidFrom.useAxiom
      frame initial initial [] label assertionFrame assertion substitution
        hlookup hdv htyped
          (Metamath.Spec.ProofValidFrom.nil frame initial)
            needed hneeded remaining hinitial

/-! ## Consequences exercising both directions -/

/-- Positive singleton hypothesis construction through the equivalence. -/
theorem proofValidFrom_single_useHyp_of_mem
    (database : Metamath.Spec.Database) (frame : Metamath.Spec.Frame)
    (initial : List Metamath.Spec.Expr)
    (hypothesis : Metamath.Spec.Hyp)
    (hmember : hypothesis ∈ frame.hyps) :
    Metamath.Spec.ProofValidFrom database frame initial
      (pushedHypothesisExpr hypothesis :: initial)
      [Metamath.Spec.ProofStep.useHyp hypothesis] := by
  exact (proofValidFrom_single_useHyp_iff database frame initial
    (pushedHypothesisExpr hypothesis :: initial) hypothesis).2
      ⟨hmember, rfl⟩

/-- Missing caller-frame membership rules out a singleton hypothesis step. -/
theorem not_proofValidFrom_single_useHyp_of_not_mem
    (database : Metamath.Spec.Database) (frame : Metamath.Spec.Frame)
    (initial final : List Metamath.Spec.Expr)
    (hypothesis : Metamath.Spec.Hyp)
    (hnotMember : hypothesis ∉ frame.hyps) :
    ¬Metamath.Spec.ProofValidFrom database frame initial final
      [Metamath.Spec.ProofStep.useHyp hypothesis] := by
  intro valid
  exact hnotMember
    ((proofValidFrom_single_useHyp_iff database frame initial final
      hypothesis).1 valid).1

/-- Even a member hypothesis cannot produce a different singleton-step stack. -/
theorem not_proofValidFrom_single_useHyp_of_wrong_final
    (database : Metamath.Spec.Database) (frame : Metamath.Spec.Frame)
    (initial final : List Metamath.Spec.Expr)
    (hypothesis : Metamath.Spec.Hyp)
    (hwrong : final ≠ pushedHypothesisExpr hypothesis :: initial) :
    ¬Metamath.Spec.ProofValidFrom database frame initial final
      [Metamath.Spec.ProofStep.useHyp hypothesis] := by
  intro valid
  exact hwrong
    ((proofValidFrom_single_useHyp_iff database frame initial final
      hypothesis).1 valid).2

/-- Positive singleton assertion construction through the exact equivalence. -/
theorem proofValidFrom_single_useAssertion_of_exact
    (database : Metamath.Spec.Database) (frame : Metamath.Spec.Frame)
    (label : Metamath.Spec.Label) (substitution : Metamath.Spec.Subst)
    (assertionFrame : Metamath.Spec.Frame)
    (assertion : Metamath.Spec.Expr)
    (needed remaining : List Metamath.Spec.Expr)
    (hlookup : database label = some (assertionFrame, assertion))
    (hdv : Metamath.Spec.dvOK frame.vars assertionFrame.dv frame.dv
      substitution)
    (htyped : ∀ typecode variableName,
      Metamath.Spec.Hyp.floating typecode variableName ∈ assertionFrame.hyps →
        (substitution variableName).typecode = typecode)
    (hneeded : needed = assertionFrame.hyps.map (fun hypothesis =>
      match hypothesis with
      | .essential expression =>
          Metamath.Spec.applySubst assertionFrame.vars substitution expression
      | .floating _ variableName => substitution variableName)) :
    Metamath.Spec.ProofValidFrom database frame
      (needed.reverse ++ remaining)
      (Metamath.Spec.applySubst assertionFrame.vars substitution assertion ::
        remaining)
      [Metamath.Spec.ProofStep.useAssertion label substitution] := by
  exact (proofValidFrom_single_useAssertion_iff database frame
    (needed.reverse ++ remaining)
    (Metamath.Spec.applySubst assertionFrame.vars substitution assertion ::
      remaining) label substitution).2
    ⟨assertionFrame, assertion, needed, remaining, hlookup, hdv, htyped,
      hneeded, rfl, rfl⟩

/-- A missing database label rules out every singleton assertion result. -/
theorem not_proofValidFrom_single_useAssertion_of_missing_lookup
    (database : Metamath.Spec.Database) (frame : Metamath.Spec.Frame)
    (initial final : List Metamath.Spec.Expr)
    (label : Metamath.Spec.Label) (substitution : Metamath.Spec.Subst)
    (hmissing : database label = none) :
    ¬Metamath.Spec.ProofValidFrom database frame initial final
      [Metamath.Spec.ProofStep.useAssertion label substitution] := by
  intro valid
  rcases (proofValidFrom_single_useAssertion_iff database frame initial final
    label substitution).1 valid with
    ⟨assertionFrame, assertion, needed, remaining, hlookup, _hdv, _htyped,
      _hneeded, _hinitial, _hfinal⟩
  rw [hmissing] at hlookup
  contradiction

/-- A stack without the reversed authored hypothesis vector as a prefix cannot
be the input of the singleton assertion step selected by a successful lookup. -/
theorem not_proofValidFrom_single_useAssertion_of_missing_prefix
    (database : Metamath.Spec.Database) (frame : Metamath.Spec.Frame)
    (initial final : List Metamath.Spec.Expr)
    (label : Metamath.Spec.Label) (substitution : Metamath.Spec.Subst)
    (assertionFrame : Metamath.Spec.Frame)
    (assertion : Metamath.Spec.Expr)
    (hlookup : database label = some (assertionFrame, assertion))
    (hmissingPrefix : ¬∃ remaining,
      initial =
        (assertionFrame.hyps.map (fun hypothesis =>
          match hypothesis with
          | .essential expression =>
              Metamath.Spec.applySubst assertionFrame.vars substitution
                expression
          | .floating _ variableName => substitution variableName)).reverse ++
          remaining) :
    ¬Metamath.Spec.ProofValidFrom database frame initial final
      [Metamath.Spec.ProofStep.useAssertion label substitution] := by
  intro valid
  rcases (proofValidFrom_single_useAssertion_iff database frame initial final
    label substitution).1 valid with
    ⟨otherFrame, otherAssertion, needed, remaining, otherLookup, _hdv,
      _htyped, hneeded, hinitial, _hfinal⟩
  have hsame : (otherFrame, otherAssertion) =
      (assertionFrame, assertion) := by
    exact Option.some.inj (otherLookup.symm.trans hlookup)
  cases hsame
  apply hmissingPrefix
  refine ⟨remaining, ?_⟩
  simpa [hneeded] using hinitial

end Mettapedia.Languages.Metamath.InferenceOperationalSpecStepInversion
