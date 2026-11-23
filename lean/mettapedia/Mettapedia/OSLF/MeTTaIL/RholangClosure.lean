import Mettapedia.OSLF.MeTTaIL.RholangReaching
import Mettapedia.OSLF.MeTTaIL.ContextRuleExtension

/-!
# Rholang's core with the closure view

CMTT's closure keeps the eliminated binder's value as explicit context. Declared on
Rholang's core, the closure view stores `@{κ(@42)!(0)}!(1)` for the example
`for(@v <- @"in"){ @{@v!(0)}!(1) } | @"in"!(42)`: the received name reaches the quoted
channel as the context `κ(@42)`.

The context constructor `κ` lies outside the signature, as CMTT's `clo(u, σ)` lies outside
its object language; the validator keeps it out, and compilation keeps the authored
signature. The example asks for the extension explicitly
(`GeneralExecutionAdmission.compileWithContextRules`): there `κ(v)` is a name whenever
`v` is (`Reflection.contextRule`), and the extended plan types, tables and emits `κ`.

* `context_typed`: the typing rule, from the profile's `closure "Ctx"` declaration.
* `comm_keeps_context`, `comm_closureView`: COMM stores `@{κ(@42)!(0)}!(1)` through the
  declared closure view.
* `stored_sorted`, `plan_sorted`: the result lies in the carrier of the extended language,
  and the extended plan's language types it.
* `stored_outside_signature`, `apply_rejects_context`, `apply_plan_rejects_context`,
  `contextPayload_apply_rejected`: the signature alone does not type `κ`, and neither does the
  apply presentation, which declares no closure.
* `compile_keeps_authored`, `authored_plan_rejects_context`, `duplicate_context_refused`,
  `extension_reentry_refused`: the extension is never implicit, and it is validated as a
  whole.
* `erase_closure_eq_apply`: on the signature's terms, erasing the context of the closure
  view gives the apply view (`apply = erase ∘ closure`); `erase_stored`,
  `erase_comm_eq_apply_comm` are the example.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.Rholang.Closure

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax Reflection ReflectiveSubstitution ReflectiveContextualQuote
open Mettapedia.GSLT.LanguageDef Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.ReflectiveWellSorted
open RuleBinding

/-! ## Terms of a signature are free of a label it does not declare -/

mutual
  theorem labelFresh_of_hasType {language : LanguageDef} {label : String}
      (fresh : ∀ rule ∈ language.terms, rule.label ≠ label) {free : FreeTypeContext}
      {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
      (typed : HasType language free bound pattern type) : labelFresh label pattern = true :=
    match typed with
    | .bvar _ => rfl
    | .fvar _ => rfl
    | .constructor declared _ arguments => by
        simp only [labelFresh, Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨fresh _ declared, labelFreshList_of_arguments fresh arguments⟩
    | .lambda body => by simpa only [labelFresh] using labelFresh_of_hasType fresh body
    | .multiLambda body => by simpa only [labelFresh] using labelFresh_of_hasType fresh body
    | .subst body replacement => by
        simp only [labelFresh, Bool.and_eq_true]
        exact ⟨labelFresh_of_hasType fresh body, labelFresh_of_hasType fresh replacement⟩
    | .collection elements => by
        simpa only [labelFresh] using labelFreshList_of_elements fresh elements
    | .collectionConstructor _ _ elements => by
        simpa only [labelFresh] using labelFreshList_of_elements fresh elements

  theorem labelFreshList_of_arguments {language : LanguageDef} {label : String}
      (fresh : ∀ rule ∈ language.terms, rule.label ≠ label) {free : FreeTypeContext}
      {bound : List TypeExpr} {arguments : List Pattern} {parameters : List TermParam}
      (typed : ArgumentsHaveTypes language free bound arguments parameters) :
      labelFreshList label arguments = true :=
    match typed with
    | .nil => rfl
    | .cons _ _ head tail => by
        simp only [labelFreshList, Bool.and_eq_true]
        exact ⟨labelFresh_of_hasType fresh head, labelFreshList_of_arguments fresh tail⟩

  theorem labelFreshList_of_elements {language : LanguageDef} {label : String}
      (fresh : ∀ rule ∈ language.terms, rule.label ≠ label) {free : FreeTypeContext}
      {bound : List TypeExpr} {elements : List Pattern} {type : TypeExpr}
      (typed : ElementsHaveType language free bound elements type) :
      labelFreshList label elements = true :=
    match typed with
    | .nil _ _ => rfl
    | .cons head tail => by
        simp only [labelFreshList, Bool.and_eq_true]
        exact ⟨labelFresh_of_hasType fresh head, labelFreshList_of_elements fresh tail⟩
end

/-! ## The presentation -/

/-- Rholang's core, with the received name kept as explicit context `Ctx` inside
quotations. -/
def presentation : ReflectivePresentationDecl :=
  { Rholang.presentation with
    name := "RholangClosure"
    -- Reaching (closure "Ctx"): the received name is kept as explicit context.
    quoteScope := .reaching (.closure "Ctx") }

def profile : ReflectionProfile :=
  { presentations := [presentation],
    rules := [{ reflectiveRule with
      matchingPresentation := presentation.name
      substitutionPresentation := presentation.name }] }

/-- The validator accepts the closure view: `Ctx` is fresh for the signature. -/
theorem profile_valid : Reflection.validate language profile = [] := by decide +kernel

theorem ctx_not_declared : ∀ rule ∈ language.terms, rule.label ≠ "Ctx" := by decide

/-- The profile declares one context rule: `Ctx(v) : Name` for `v : Name`. -/
theorem contextRules_eq : profile.contextRules =
    [{ label := "Ctx", category := "Name", params := [.simple "value" (.base "Name")],
       syntaxPattern := [.terminal "Ctx", .terminal "(", .nonTerminal "value", .terminal ")"] }] := rfl

/-- **The typing rule of the context constructor**, from the profile's declaration. -/
theorem context_typed {free : FreeTypeContext} {bound : List TypeExpr} {value : Pattern}
    (typed : HasType (profile.extendLanguage language) free bound value (.base "Name")) :
    HasType (profile.extendLanguage language) free bound (.apply "Ctx" [value]) (.base "Name") :=
  ReflectionProfile.context_hasType (presentation := presentation) (List.mem_singleton_self _) rfl typed

/-! ## The example -/

/-- `@{κ(@42)!(0)}!(1)`. -/
def stored : Pattern :=
  .apply "POutput" [.apply "NQuote" [.apply "POutput" [.apply "Ctx" [.apply "NQuote" [int42]], int0]], int1]

/-- **COMM keeps the received name as context inside the quoted channel.** -/
theorem comm_keeps_context :
    applyBindingsForRuleUsing profile GeneralRho.comm bindings = .collection .hashBag [stored] none := by
  decide +kernel

/-- COMM goes through the declared closure view. -/
theorem comm_closureView :
    applyBindingsForRuleUsing profile GeneralRho.comm bindings =
      .collection .hashBag [closureView presentation "Ctx" 0 (.apply "NQuote" [int42]) body] none := by
  decide +kernel

/-! ## The carrier -/

/-- **The result lies in the carrier** of the extended language. -/
theorem stored_sorted :
    checkOpenPatternWellSorted profile (profile.extendLanguage language) FreeTypeContext.empty [] (.base "Proc")
      stored = true := by
  decide +kernel

theorem source_sorted :
    checkOpenPatternWellSorted profile (profile.extendLanguage language) FreeTypeContext.empty [] (.base "Proc")
      source = true := by
  decide +kernel

/-- The signature alone does not type the context constructor. -/
theorem stored_outside_signature :
    checkOpenPatternWellSorted profile language FreeTypeContext.empty [] (.base "Proc") stored = false := by
  decide +kernel

/-- **Negative control.** The apply presentation declares no closure, so it proposes no
context rule and its carrier rejects `κ`. -/
theorem apply_contextless : Rholang.profile.contextRules = [] := rfl

theorem apply_rejects_context :
    checkOpenPatternWellSorted Rholang.profile (Rholang.profile.extendLanguage language) FreeTypeContext.empty []
      (.base "Proc") stored = false := by
  decide +kernel

/-! ## The plan -/

/-- Rho's standard reduction contexts and COMM, under the closure profile. -/
def permissions : GeneralExecutionAdmission.Permissions :=
  { GeneralRho.Standard.permissions with reflection := profile }

def plan : GeneralExecutionAdmission.Plan :=
  GeneralExecutionAdmission.compileWithContextRules snapshot permissions

/-- The extended plan's language is the signature with the context rule. -/
theorem plan_language :
    (GeneralPlanEnvironment.environment plan).language.terms = profile.contextRules ++ language.terms := rfl

theorem selected_rules :
    GeneralExecutionAdmission.selectedRules snapshot permissions = [(GeneralRho.comm, 0)] := rfl

theorem compiled_rules : plan.rules = [GeneralRho.declaration] := by
  unfold plan GeneralExecutionAdmission.compileWithContextRules GeneralExecutionAdmission.compile
    GeneralExecutionAdmission.rules
  simp only [selected_rules, List.filterMap_cons, rule_plan_compiled, List.filterMap_nil]

/-- The authored compilation is complete. -/
theorem authored_compilation_complete :
    (GeneralExecutionAdmission.compile snapshot permissions).complete = true := by
  have strata : GeneralPremise.checkStepStratification
      (GeneralExecutionAdmission.executionLanguage snapshot permissions) = true := by
    change GeneralPremise.checkStepStratification
      { language with rewrites := plan.rules.map GeneralExecutionAdmission.RulePlan.rule } = true
    rw [compiled_rules]
    rfl
  have ruleChecks : (GeneralExecutionAdmission.selectedRules snapshot permissions).flatMap
      (fun (rule, index) => GeneralExecutionAdmission.ruleObligations snapshot index rule) = [] := by
    rw [selected_rules]
    simp only [List.flatMap_cons, List.flatMap_nil, GeneralExecutionAdmission.ruleObligations,
      show snapshot.language = language from rfl, binding_compiled,
      show GeneralRho.declaration.binding.elaborate GeneralRho.comm = GeneralRho.comm from rfl,
      show GeneralRho.declaration.binding.spec = Mettapedia.GSLT.Examples.ScopedRhoBinding.scopedCommBindingSpec
        from rfl, premises_admitted,
      GeneralRho.canonical_comm, GeneralRho.canonical_spines, Bool.and_self,
      ↓reduceIte, List.nil_append]
  have equationSelection : GeneralExecutionAdmission.selectedEquations snapshot permissions = [] := rfl
  have freeChecked : GeneralExecutionAdmission.checkFreeContext snapshot = true := rfl
  have providerChecked : GeneralPremise.checkProviderClosed snapshot.language snapshot.free
      snapshot.provider = true := rfl
  have missingRules : GeneralExecutionAdmission.missing permissions.ruleIndices
      snapshot.language.rewrites.length = [] := rfl
  have missingEquations : GeneralExecutionAdmission.missing permissions.equationIndices
      snapshot.language.equations.length = [] := rfl
  have setChecked : GeneralExecutionAdmission.setDecompositionFree snapshot permissions = true := rfl
  apply List.isEmpty_iff.mpr
  dsimp only [GeneralExecutionAdmission.compile]
  rw [show snapshot.language.validate = [] from language_valid, freeChecked, providerChecked,
    show Reflection.validate snapshot.language permissions.reflection = [] from profile_valid,
    missingRules, missingEquations, ruleChecks, equationSelection, strata, setChecked]
  rfl

/-- The signature the extended plan executes over is valid. -/
theorem extended_language_valid : (snapshot.extendContexts profile).language.validate = [] := by
  simp [GeneralExecutionAdmission.Snapshot.extendContexts, ReflectionProfile.extendLanguage,
    contextRules_eq, snapshot, LanguageDef.validate, language, ground, GeneralRho.language, GeneralRho.comm, rhoCalc,
    rhoCommRewrite, rhoParCongRewrite, Mettapedia.GSLT.Examples.ScopedRhoBinding.scopedParCongRewrite,
    Mettapedia.GSLT.Examples.RestAwareTyping.declaredParCongRewrite,
    LanguageDef.duplicateErrors, LanguageDef.duplicateErrorsAux,
    LanguageDef.validateTypeExpr_eq_nil_iff,
    LanguageDef.validateEquation, LanguageDef.validateRewrite,
    LanguageDef.validatePatternConstructors,
    LanguageDef.validateRulePatterns,
    LanguageDef.typeNames, TypeDecl.plain, TypeExpr.baseType, TypeExpr.proc,
    TypeExpr.name, TypeExpr.funType, TypeExpr.bag, TypeExpr.baseNames,
    TermParam.bodyName, TermParam.binderNames, TermParam.typeExpr,
    LanguageDef.patternFvarNames, LanguageDef.patternBinderNames,
    LanguageDef.premiseProducedFvarNames, LanguageDef.premisePatterns,
    LanguageDef.premiseFvarNames, LanguageDef.premiseForAllParams,
    LanguageDef.premiseStepTypeExprs, LanguageDef.premiseLocallyScoped,
    Pattern.constructorRefs, Pattern.constructorRefsList,
    Pattern.freeFvarNames, Pattern.isWellScoped, Pattern.isWellScopedAt,
    Pattern.isWellScopedListAt]

/-- **One extension is accepted.** -/
theorem compilation_complete : plan.complete = true :=
  GeneralExecutionAdmission.compileWithContextRules_complete_iff.mpr
    ⟨extended_language_valid, authored_compilation_complete⟩

/-- **The plan's language types the closure result.** -/
theorem plan_sorted :
    checkOpenPatternWellSorted (GeneralPlanEnvironment.environment plan).language FreeTypeContext.empty []
      (.base "Proc") stored = true := by
  decide +kernel

/-- **Negative control.** The apply plan's language does not type the closure result. -/
theorem apply_plan_rejects_context :
    checkOpenPatternWellSorted (GeneralPlanEnvironment.environment Rholang.plan).language FreeTypeContext.empty []
      (.base "Proc") stored = false := by
  decide +kernel

/-- `for(@v <- @"in"){ v } | @"in"!(*κ(@42))`: a source whose payload already holds a context. -/
def contextPayload : Pattern :=
  .collection .hashBag [.apply "PInput" [inChannel, .lambda none (.apply "PDrop" [.bvar 0])],
    .apply "POutput" [inChannel, .apply "PDrop" [.apply "Ctx" [.apply "NQuote" [int42]]]]] none

/-- The closure plan sorts a source that holds a context. -/
theorem contextPayload_plan_sorted :
    checkOpenPatternWellSorted (GeneralPlanEnvironment.environment plan).language FreeTypeContext.empty []
      (.base "Proc") contextPayload = true := by
  decide +kernel

/-- **Negative control.** The apply plan does not sort it, so no rule job starts there. -/
theorem contextPayload_apply_rejected :
    checkOpenPatternWellSorted (GeneralPlanEnvironment.environment Rholang.plan).language FreeTypeContext.empty []
      (.base "Proc") contextPayload = false := by
  decide +kernel

/-! ## The extension is explicit

Compilation keeps the authored signature. The extension is asked for by name, and
its target is validated as a whole. -/

/-- Ordinary compilation keeps the authored snapshot, also under the closure profile. -/
theorem compile_keeps_authored :
    (GeneralExecutionAdmission.compile snapshot permissions).snapshot = snapshot := rfl

/-- **Negative control.** The ordinary plan does not type the closure result. -/
theorem authored_plan_rejects_context :
    checkOpenPatternWellSorted
      (GeneralPlanEnvironment.environment (GeneralExecutionAdmission.compile snapshot permissions)).language
      FreeTypeContext.empty [] (.base "Proc") stored = false := by
  decide +kernel

/-- Two presentations that propose one context constructor. -/
def collidingProfile : ReflectionProfile :=
  { profile with presentations := [presentation, { presentation with name := "OtherClosure" }] }

/-- Against the authored signature each proposal is fresh, so the profile alone validates. -/
theorem collidingProfile_valid : Reflection.validate language collidingProfile = [] := by decide +kernel

/-- **Negative control.** The extension refuses the collision, which validation against
the authored signature cannot see. -/
theorem duplicate_context_refused :
    (GeneralExecutionAdmission.compileWithContextRules snapshot
      { permissions with reflection := collidingProfile }).complete = false := by
  apply Bool.eq_false_iff.mpr
  intro complete
  have valid := (GeneralExecutionAdmission.compileWithContextRules_complete_iff.mp complete).1
  have distinct := LanguageDef.constructorLabels_nodup_of_validate_eq_nil _ valid
  change (("Ctx" : String) :: "Ctx" :: language.terms.map (·.label)).Nodup at distinct
  exact (List.nodup_cons.mp distinct).1 (List.mem_cons_self ..)

/-- **Negative control.** An extended signature cannot be extended by the same profile again. -/
theorem extension_reentry_refused :
    (GeneralExecutionAdmission.compileWithContextRules plan.snapshot permissions).complete = false := by
  apply Bool.eq_false_iff.mpr
  intro complete
  have valid := (GeneralExecutionAdmission.compileWithContextRules_complete_iff.mp complete).1
  have distinct := LanguageDef.constructorLabels_nodup_of_validate_eq_nil _ valid
  change (("Ctx" : String) :: "Ctx" :: language.terms.map (·.label)).Nodup at distinct
  exact (List.nodup_cons.mp distinct).1 (List.mem_cons_self ..)

/-! ## Apply is erasure of the closure -/

/-- **`apply = erase ∘ closure`** on the signature's terms: erasing the context of the
closure view gives the apply view, at every depth, for every body and replacement typed
in the signature. -/
theorem erase_closure_eq_apply {free : FreeTypeContext} {bound bound' : List TypeExpr}
    {depth : Nat} {replacement body : Pattern} {type type' : TypeExpr}
    (bodyTyped : HasType language free bound body type)
    (replacementTyped : HasType language free bound' replacement type') :
    erase presentation "Ctx"
        (substituteUnder presentation presentation.quoteScope depth replacement body) =
      substituteUnder presentation (.reaching .apply) depth replacement body := by
  rw [show presentation.quoteScope = .reaching (.closure "Ctx") from rfl, substituteUnder_closure,
    substituteUnder_apply]
  exact erase_closureView depth (by decide) (by decide) (labelFresh_of_hasType ctx_not_declared bodyTyped)
    (labelFresh_of_hasType ctx_not_declared replacementTyped)

/-- The example: erasing the context of the stored closure gives Rholang's result. -/
theorem erase_stored : erase presentation "Ctx" stored = Rholang.stored := by decide +kernel

/-- COMM under the closure profile, erased, is COMM under Rholang's apply profile. -/
theorem erase_comm_eq_apply_comm :
    erase presentation "Ctx" (applyBindingsForRuleUsing profile GeneralRho.comm bindings) =
      applyBindingsForRuleUsing Rholang.profile GeneralRho.comm bindings := by
  decide +kernel

end Mettapedia.OSLF.MeTTaIL.Rholang.Closure
