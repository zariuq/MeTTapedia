import Mettapedia.GSLT.LanguageDef.TypedScopedStepPremise
import Mettapedia.OSLF.MeTTaIL.ContextualStep

/-!
# Elaboration of authored premises into a scoped rule interface

The surface `congruence` form omits its endpoint sort. Its canonical image
opens no local binders and is admitted only when the authored declarations
give exactly one checked base sort. The explicit `scopedStep` form carries its
local binders and sort and is checked directly. Distinct rule-premise forms
remain distinct, including their order under collection quantification.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CanonicalScopedPremise

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.TypedScopedStepPremise

/-- The elaborated rule premise always gives each step its local context and
endpoint sort. Collection quantification remains a separate constructor. -/
inductive CanonicalPremise where
  | freshness : FreshnessCondition → CanonicalPremise
  | step : ScopedStepPremise → CanonicalPremise
  | relationQuery : String → List Pattern → CanonicalPremise
  | forAll : String → String → CanonicalPremise → CanonicalPremise
deriving Repr, DecidableEq

/-- Erasing elaboration annotations yields an explicitly scoped authored
premise, so the local context and sort survive serialization. -/
def CanonicalPremise.toAuthored : CanonicalPremise → Premise
  | .freshness condition => .freshness condition
  | .step payload => .scopedStep payload
  | .relationQuery relation arguments => .relationQuery relation arguments
  | .forAll collection parameter body =>
      .forAll collection parameter body.toAuthored

/-- The only sorts inferred for bare root notation are declared base sorts.
Authors can use `scopedStep` for a compound or otherwise underdetermined sort. -/
def rootSortCandidates (language : LanguageDef) : List TypeExpr :=
  language.types.map fun declaration => .base declaration.name

/-- Infer a root step's sort only when exactly one declared base sort checks
both endpoints in the supplied rule context. -/
def inferRootSort? (language : LanguageDef) (free : FreeTypeContext)
    (ambient : List TypeExpr) (source target : Pattern) : Option TypeExpr :=
  match (rootSortCandidates language).filter fun resultType =>
      check language free ambient
        (ScopedStepPremise.root resultType source target) with
  | [resultType] => some resultType
  | _ => none

/-- Inference returns only a sort at which both endpoints passed the actual
authored checker. Uniqueness is enforced by the singleton result shape. -/
theorem inferRootSort?_sound
    {language : LanguageDef} {free : FreeTypeContext}
    {ambient : List TypeExpr} {source target : Pattern}
    {resultType : TypeExpr}
    (inferred : inferRootSort? language free ambient source target =
      some resultType) :
    check language free ambient
      (ScopedStepPremise.root resultType source target) = true := by
  have hselected :
      (rootSortCandidates language).filter (fun candidate =>
        check language free ambient
          (ScopedStepPremise.root candidate source target)) =
      [resultType] := by
    unfold inferRootSort? at inferred
    cases hchoices : (rootSortCandidates language).filter (fun candidate =>
        check language free ambient
          (ScopedStepPremise.root candidate source target)) with
    | nil => simp [hchoices] at inferred
    | cons candidate rest =>
        cases rest with
        | nil =>
            have equal : candidate = resultType := by
              simpa [hchoices] using inferred
            simp [equal]
        | cons next tail => simp [hchoices] at inferred
  have member : resultType ∈ (rootSortCandidates language).filter (fun candidate =>
      check language free ambient
        (ScopedStepPremise.root candidate source target)) := by
    rw [hselected]
    simp
  exact (List.mem_filter.mp member).2

/-- Compile one surface premise into the checked scoped interface. -/
def compile? (language : LanguageDef) (free : FreeTypeContext)
    (ambient : List TypeExpr) : Premise → Option CanonicalPremise
  | .freshness condition => some (.freshness condition)
  | .congruence source target => do
      let resultType ← inferRootSort? language free ambient source target
      pure (.step (ScopedStepPremise.root resultType source target))
  | .scopedStep step =>
      if check language free ambient step then some (.step step) else none
  | .relationQuery relation arguments =>
      some (.relationQuery relation arguments)
  | .forAll collection parameter body => do
      let elementType ← match free collection with
        | some (.collection _ elementType) => some elementType
        | _ => none
      let localFree : FreeTypeContext :=
        fun name => if name == parameter then some elementType else free name
      let compiled ← compile? language localFree ambient body
      pure (.forAll collection parameter compiled)

/-- Elaborate an ordered premise list without reordering or collapsing its
entries. Each element is checked in the same ambient rule context. -/
def compileList? (language : LanguageDef) (free : FreeTypeContext)
    (ambient : List TypeExpr) : List Premise → Option (List CanonicalPremise)
  | [] => some []
  | premise :: rest => do
      let first ← compile? language free ambient premise
      let later ← compileList? language free ambient rest
      pure (first :: later)

/-- A successful list compilation retains its exact number of premises. -/
theorem compileList?_length
    {language : LanguageDef} {free : FreeTypeContext}
    {ambient : List TypeExpr} {premises : List Premise}
    {compiled : List CanonicalPremise}
    (h : compileList? language free ambient premises = some compiled) :
    compiled.length = premises.length := by
  induction premises generalizing compiled with
  | nil =>
      simp [compileList?] at h
      cases h
      rfl
  | cons premise rest ih =>
      simp only [compileList?] at h
      cases hfirst : compile? language free ambient premise with
      | none => simp [hfirst] at h
      | some first =>
          cases hlater : compileList? language free ambient rest with
          | none => simp [hfirst, hlater] at h
          | some later =>
              simp [hfirst, hlater] at h
              cases h
              simpa using congrArg Nat.succ (ih hlater)

/-- The finite rule context assigns each named schema variable its declared
sort. A duplicate name is rejected by the rule-level compiler below. -/
def freeFromRuleContext (context : List (String × TypeExpr)) :
    FreeTypeContext :=
  fun name => (context.find? fun entry => entry.1 == name).map Prod.snd

/-- Compile every ordered premise of one actual authored rewrite. Duplicate
schema-variable declarations are ambiguous and therefore rejected. -/
def compileRulePremises? (language : LanguageDef) (rule : RewriteRule) :
    Option (List CanonicalPremise) :=
  if (rule.typeContext.map Prod.fst).Nodup then
    compileList? language (freeFromRuleContext rule.typeContext) [] rule.premises
  else none

/-- Compiling a rule cannot invent or discard premise positions. -/
theorem compileRulePremises?_length
    {language : LanguageDef} {rule : RewriteRule}
    {compiled : List CanonicalPremise}
    (h : compileRulePremises? language rule = some compiled) :
    compiled.length = rule.premises.length := by
  unfold compileRulePremises? at h
  split at h
  · exact compileList?_length h
  · cases h

/-- A checked explicit step elaborates without losing its binders or sort. -/
theorem compile_scopedStep_of_check
    (language : LanguageDef) (free : FreeTypeContext)
    (ambient : List TypeExpr) (step : ScopedStepPremise)
    (checked : check language free ambient step = true) :
    compile? language free ambient (.scopedStep step) = some (.step step) := by
  simp [compile?, checked]

/-- An explicit step that fails the sorted admission check is not compiled. -/
theorem compile_scopedStep_of_rejected
    (language : LanguageDef) (free : FreeTypeContext)
    (ambient : List TypeExpr) (step : ScopedStepPremise)
    (rejected : check language free ambient step = false) :
    compile? language free ambient (.scopedStep step) = none := by
  simp [compile?, rejected]

/-- Every successful explicit-step compilation carries a typed premise. -/
theorem compile_scopedStep_typed
    {language : LanguageDef} {free : FreeTypeContext}
    {ambient : List TypeExpr} {step : ScopedStepPremise}
    (compiled : compile? language free ambient (.scopedStep step) =
      some (.step step)) :
    HasType language free ambient step := by
  by_cases checked : check language free ambient step = true
  · exact check_sound checked
  · have rejected : check language free ambient step = false :=
      Bool.eq_false_iff.mpr checked
    simp [compile?, rejected] at compiled

/-- A successfully elaborated bare congruence is exactly a typed root step. -/
theorem compile_congruence_typed
    {language : LanguageDef} {free : FreeTypeContext}
    {ambient : List TypeExpr} {source target : Pattern}
    {payload : ScopedStepPremise}
    (compiled : compile? language free ambient (.congruence source target) =
      some (.step payload)) :
    ∃ resultType,
      payload = ScopedStepPremise.root resultType source target ∧
        HasType language free ambient payload := by
  cases inferred : inferRootSort? language free ambient source target with
  | none => simp [compile?, inferred] at compiled
  | some resultType =>
      simp [compile?, inferred] at compiled
      cases compiled
      exact ⟨resultType, rfl, check_sound (inferRootSort?_sound inferred)⟩

/-- The explicit root representation has exactly the old root evaluator
behavior, for every recursive step function and binding assignment. -/
theorem scoped_root_execution_eq_congruence
    (base : Mettapedia.OSLF.MeTTaIL.ContextualStep.BasePremiseEvaluator)
    (language : LanguageDef) (recursiveStep : Pattern → List Pattern)
    (bindings : Mettapedia.OSLF.MeTTaIL.Match.Bindings)
    (resultType : TypeExpr) (source target : Pattern) :
    Mettapedia.OSLF.MeTTaIL.ContextualStep.premiseStepUsing
      base language recursiveStep bindings
      (.scopedStep (ScopedStepPremise.root resultType source target)) =
    Mettapedia.OSLF.MeTTaIL.ContextualStep.premiseStepUsing
      base language recursiveStep bindings (.congruence source target) := by
  rfl

private def term : TypeExpr := .base "Term"

private def lambdaFree : FreeTypeContext :=
  fun name => if name == "source" || name == "target" then some term else none

/-- The old root form elaborates when its two variables have one sort. -/
example : inferRootSort?
    Mettapedia.OSLF.Framework.LambdaInstance.lambdaCalc lambdaFree []
    (.fvar "source") (.fvar "target") = some term := by decide

/-- A missing sort declaration never gets guessed from the first occurrence. -/
example : inferRootSort?
    Mettapedia.OSLF.Framework.LambdaInstance.lambdaCalc FreeTypeContext.empty []
    (.fvar "source") (.fvar "target") = none := by decide

/-- Lambda congruence under its local binder uses the explicit form. -/
example : compile?
    Mettapedia.OSLF.Framework.LambdaInstance.lambdaCalc
    FreeTypeContext.empty []
    (.scopedStep TypedScopedStepPremise.lambdaBodyStep) =
      some (.step TypedScopedStepPremise.lambdaBodyStep) := by decide

/-- An escaping local variable fails canonical elaboration. -/
example : compile?
    Mettapedia.OSLF.Framework.LambdaInstance.lambdaCalc
    FreeTypeContext.empty []
    (.scopedStep { TypedScopedStepPremise.lambdaBodyStep with target := .bvar 1 }) =
      none := by decide

/-- The existing rho ParCong premise becomes unambiguous once its missing
schema declarations are supplied, including the collection rest. -/
private def sortedParCong : RewriteRule :=
  { rhoParCongRewrite with
    typeContext :=
      [("S", .base "Proc"), ("T", .base "Proc"),
       ("rest", .collection .hashBag (.base "Proc"))] }

example : compileRulePremises? rhoCalc sortedParCong =
    some [.step (ScopedStepPremise.root (.base "Proc")
      (.fvar "S") (.fvar "T"))] := by decide

/-- The shipped declaration is a negative control: its empty context cannot
justify either premise variable's sort. -/
example : compileRulePremises? rhoCalc rhoParCongRewrite = none := by decide

/-- Duplicate schema-variable declarations do not select the first row. -/
example : compileRulePremises? rhoCalc
    { sortedParCong with
      typeContext := ("S", .base "Proc") :: sortedParCong.typeContext } =
    none := by decide

end Mettapedia.GSLT.LanguageDef.CanonicalScopedPremise
