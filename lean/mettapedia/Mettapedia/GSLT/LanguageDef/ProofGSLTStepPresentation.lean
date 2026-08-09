import Mettapedia.GSLT.LanguageDef.ProofGSLTStepPresentability

/-!
# The generated trace presentation of a language

`stepPresentation` turns a proof-carrying `DirectTraceLanguage` into a
proof-theoretic presentation of its step relation: each authored rewrite
rule becomes a `Step` schema
whose premises are the rule's authored congruence premises read as `Step`
judgments, and `Steps` carries reflexive-transitive trace closure.  The
generic inference checker applied to a generated presentation is the trace
checker of that language — uniformly, with zero authored inference rules.

Faithfulness note.  MeTTaIL's declarative reduction grants **no free
congruence**: contextual authority comes only from authored
`Premise.congruence` premises inside rewrite rules
(`Mettapedia/OSLF/MeTTaIL/ContextualStep.lean`).  An earlier version of this
generator emitted one congruence schema per constructor argument position;
that derives steps the language does not have, and is refuted by the
compiled counterexample `congruence_is_not_free` in
`ProofGSLTStepPresentationCanary`.  The generator therefore translates
exactly the authored premises.

Direct fragment.  The translation covers rules whose premises are all
congruence premises, whose metavariables live at ambient depth, and whose
patterns are collection-rest free.  `DirectTraceLanguage` carries the
premise-shape gate, so unsupported premises cannot be silently discarded;
admission of the generated presentation (`Presentation.isValidV2`) checks
the remaining depth, pattern, and judgment conditions.

The source rewrite and equation declarations are consumed into the generated
schemas (the generated language carries no residual rewrite or equation
declarations), so the step relation keeps exactly one presentation
authority.

The full proof checker strictly exceeds this uniform family: every generated
presentation declares exactly the binary `Step` and `Steps` judgments, so
any admitted presentation with a different judgment signature is provably
outside the image of every language.  The compiled witness lives in
`ProofGSLTStepPresentationCanary`.
-/

namespace Mettapedia.GSLT.LanguageDef.ProofGSLT

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker

/-- The premise-shape gate of the direct fragment: every authored premise is
a congruence premise. -/
def RewriteRule.directTracePresentable (rule : RewriteRule) : Bool :=
  rule.premises.all fun premise =>
    match premise with
    | .congruence _ _ => true
    | _ => false

/-- The premise fragment accepted by the direct trace translation. -/
def LanguageDef.directTracePresentable (language : LanguageDef) : Bool :=
  language.rewrites.all RewriteRule.directTracePresentable

/-- A language together with machine-checked evidence that the direct trace
translation accounts for every authored rewrite premise.  This carrier is
deliberately weaker than generated-presentation validity: depth discipline,
collection-rest freedom, and judgment validation remain the responsibility
of `Presentation.isValidV2`. -/
structure DirectTraceLanguage where
  language : LanguageDef
  premisesSupported : LanguageDef.directTracePresentable language = true

namespace DirectTraceLanguage

/-- Recover support for any authored rule from the carrier evidence. -/
theorem rule_supported (source : DirectTraceLanguage) {rule : RewriteRule}
    (member : rule ∈ source.language.rewrites) :
    RewriteRule.directTracePresentable rule = true :=
  List.all_eq_true.mp source.premisesSupported rule member

/-- Executable, fail-closed admission into the direct trace fragment. -/
def ofLanguage? (language : LanguageDef) : Option DirectTraceLanguage :=
  if supported : LanguageDef.directTracePresentable language = true then
    some ⟨language, supported⟩
  else
    none

@[simp] theorem ofLanguage?_eq_some (source : DirectTraceLanguage) :
    ofLanguage? source.language = some source := by
  simp [ofLanguage?, source.premisesSupported]

theorem ofLanguage?_eq_none_of_unsupported {language : LanguageDef}
    (unsupported : LanguageDef.directTracePresentable language = false) :
    ofLanguage? language = none := by
  simp [ofLanguage?, unsupported]

end DirectTraceLanguage

/-- Read authored congruence premises as `Step` premise judgments, in authored
order.  `DirectTraceLanguage` guarantees that this function is only used on
rule tables for which the otherwise-ignored cases cannot occur. -/
def rewritePremiseJudgments : List Premise → List Pattern
  | [] => []
  | .congruence source target :: rest =>
      .apply "Step" [source, target] :: rewritePremiseJudgments rest
  | _ :: rest => rewritePremiseJudgments rest

/-- One `Step` schema per authored rewrite rule: the rule's typed context as
ambient-depth metavariables, its congruence premises as `Step` premises, and
its rewrite as the conclusion. -/
def rewriteStepRule (rule : RewriteRule) : RuleSchema :=
  { id := ⟨"step-rewrite-" ++ rule.name⟩
    metavariables := rule.typeContext.map fun binding => (binding.1, 0)
    premises := rewritePremiseJudgments rule.premises
    conclusion := .apply "Step" [rule.left, rule.right] }

/-- Reflexivity of the trace judgment. -/
def stepReflRule : RuleSchema :=
  { id := ⟨"steps-refl"⟩
    metavariables := [("stepPoint", 0)]
    premises := []
    conclusion := .apply "Steps" [.fvar "stepPoint", .fvar "stepPoint"] }

/-- One-step extension of the trace judgment. -/
def stepTransRule : RuleSchema :=
  { id := ⟨"steps-trans"⟩
    metavariables := [("stepSource", 0), ("stepMiddle", 0), ("stepTarget", 0)]
    premises := [.apply "Step" [.fvar "stepSource", .fvar "stepMiddle"],
      .apply "Steps" [.fvar "stepMiddle", .fvar "stepTarget"]]
    conclusion := .apply "Steps" [.fvar "stepSource", .fvar "stepTarget"] }

/-- The generated trace presentation of a language: its rewrite rules as
`Step` schemas with their authored congruence premises, and
reflexive-transitive `Steps` traces. -/
def stepPresentation (source : DirectTraceLanguage) : Presentation :=
  { language :=
      { source.language with
        equations := []
        rewrites := [] }
    calculus :=
      { judgments :=
          [{ head := "Step", arity := 2 }, { head := "Steps", arity := 2 }]
        rules :=
          source.language.rewrites.map rewriteStepRule ++
            [stepReflRule, stepTransRule] } }

/-! ## The image of the generator is pinned by its judgment signature -/

@[simp] theorem stepPresentation_judgments (source : DirectTraceLanguage) :
    (stepPresentation source).judgments =
      [{ head := "Step", arity := 2 }, { head := "Steps", arity := 2 }] :=
  rfl

/-- The golden difference, general form: an admitted presentation whose
judgment signature differs from the trace signature is not the generated
step presentation of any language.  Full proof judgments strictly exceed
uniform trace checking. -/
theorem not_stepPresentation_of_judgments {presentation : Presentation}
    (different : presentation.judgments ≠
      [{ head := "Step", arity := 2 }, { head := "Steps", arity := 2 }]) :
    ∀ source : DirectTraceLanguage,
      stepPresentation source ≠ presentation := by
  intro source equal
  apply different
  rw [← equal]
  rfl

end Mettapedia.GSLT.LanguageDef.ProofGSLT
