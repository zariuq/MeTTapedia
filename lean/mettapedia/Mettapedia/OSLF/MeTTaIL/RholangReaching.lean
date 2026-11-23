import Mettapedia.OSLF.MeTTaIL.GeneralRhoStandardSites
import Mettapedia.OSLF.MeTTaIL.ReflectiveContextualQuote
import Mettapedia.GSLT.LanguageDef.ReflectiveWellSortedChecker

/-!
# Rholang: a reflective presentation whose binders reach into quotations

Rholang as deployed substitutes through quoted channels: the interpreter's
substitution of normalized processes recurses into a quotation like into any
other constructor. Its reflective presentation therefore declares the apply
view, `quoteScope := .reaching .apply`, over rho's constructors, its COMM rule
and its quote-drop equation. Ground processes for the integers `0`, `1`, `42`
and the string `"in"` complete the core used below.

The example `for(@v <- @"in"){ @{@v!(0)}!(1) } | @"in"!(42)` receives `42` and
leaves `@{@42!(0)}!(1)`: the received process reaches into the quoted channel
`@{@v!(0)}`. In rho's locally nameless core the receiver binds a name `y` with
`v = *y`, so `@v` is `@*y`, which the quote-drop equation identifies with `y`.

* `comm_stores_received`: COMM, through the declared substitution and so
  through the apply view, gives `@{@42!(0)}!(1)`.
* `source_sorted`, `target_sorted`: the source and the result lie in the
  reflective carrier of the Rholang profile, which asks ordinary scope.
* `source_not_rho_sorted`, `rho_quotation_not_admitted`,
  `rho_comm_leaves_dangling_index`: rho's closed declaration rejects the same
  term, and its opaque substitution would leave the received name dangling
  inside the quotation.
* `comm_respects`, `comm_scoped`, `scopeSafe_iff`: the declared substitution
  respects the declared equations and keeps ordinary scope, which is all the
  presentation asks.

The closure view on the same core is `RholangClosure`.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.Rholang

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax Reflection ReflectiveSubstitution ScopedPattern
open Mettapedia.GSLT.LanguageDef Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.ReflectiveWellSorted
open Mettapedia.GSLT.LanguageDef.ReflectionExtension (rhoReflectionProfile)
open RuleBinding

/-! ## The presentation -/

/-- Rholang's reflective presentation: rho's constructors and quote-drop
equation, with binders reaching into quotations through the apply view. -/
def presentation : ReflectivePresentationDecl :=
  { rhoReflectivePresentation.toReflectivePresentationDecl with
    name := "RholangCommSubstitution"
    -- Reaching (apply): Rholang's substitution recurses into quoted channels.
    quoteScope := .reaching .apply }

/-- COMM selects the Rholang presentation for matching and substitution. -/
def reflectiveRule : ReflectiveRuleDecl where
  name := "RholangCommReflective"
  rewriteRule := "Comm"
  matchingPresentation := presentation.name
  substitutionPresentation := presentation.name

def profile : ReflectionProfile :=
  { presentations := [presentation], rules := [reflectiveRule] }

/-- A ground process with no arguments. -/
def ground (label spelling : String) : GrammarRule :=
  { label, category := "Proc", params := [], syntaxPattern := [.terminal spelling] }

/-- Rho's grammar, equation and COMM, with the ground processes of the example. -/
def language : LanguageDef :=
  { GeneralRho.language with
    name := "RholangCore"
    terms := rhoCalc.terms ++
      [ground "Int0" "int0", ground "Int1" "int1", ground "Int42" "int42", ground "StrIn" "str_in"] }

theorem language_valid : language.validate = [] := by
  simp [LanguageDef.validate, language, ground, GeneralRho.language, GeneralRho.comm, rhoCalc,
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

theorem profile_valid : Reflection.validate language profile = [] := by decide +kernel

theorem presentation_quoteScope : presentation.quoteScope = .reaching .apply := rfl

/-- The Rholang profile selects its own presentation for COMM. -/
theorem comm_selects : substitutionPresentationForRule? profile GeneralRho.comm = some presentation := by
  decide +kernel

/-! ## The example -/

def int0 : Pattern := .apply "Int0" []
def int1 : Pattern := .apply "Int1" []
def int42 : Pattern := .apply "Int42" []
/-- `@"in"`. -/
def inChannel : Pattern := .apply "NQuote" [.apply "StrIn" []]
/-- `@{@v!(0)}!(1)` with `v = *y` for the received name `y`. -/
def body : Pattern :=
  .apply "POutput" [.apply "NQuote" [.apply "POutput" [.apply "NQuote" [.apply "PDrop" [.bvar 0]], int0]], int1]
/-- `for(@v <- @"in"){ @{@v!(0)}!(1) } | @"in"!(42)`. -/
def source : Pattern :=
  .collection .hashBag [.apply "PInput" [inChannel, .lambda none body], .apply "POutput" [inChannel, int42]] none
/-- `@{@42!(0)}!(1)`. -/
def stored : Pattern :=
  .apply "POutput" [.apply "NQuote" [.apply "POutput" [.apply "NQuote" [int42], int0]], int1]

/-- The COMM bindings of the example. -/
def bindings : Match.Bindings :=
  [("n", inChannel), ("p", body), ("q", int42), ("rest", .collection .hashBag [] none)]

/-- **COMM stores the received process inside the quoted channel.** -/
theorem comm_stores_received :
    applyBindingsForRuleUsing profile GeneralRho.comm bindings = .collection .hashBag [stored] none := by
  decide +kernel

/-- COMM goes through the substitution the presentation declares, which is the apply view. -/
theorem comm_declared :
    applyBindingsForRuleUsing profile GeneralRho.comm bindings =
      .collection .hashBag [substituteDeclared presentation 0 (.apply "NQuote" [int42]) body] none := by
  decide +kernel

theorem comm_applyView :
    substituteDeclared presentation 0 (.apply "NQuote" [int42]) body =
      ReflectiveContextualQuote.substituteUnder presentation (.reaching .apply) 0
        (.apply "NQuote" [int42]) body := by
  decide +kernel

/-! ## The carrier: the Rholang profile admits the term, rho's closed profile does not -/

theorem source_sorted :
    checkOpenPatternWellSorted profile language FreeTypeContext.empty [] (.base "Proc") source = true := by
  decide +kernel

theorem target_sorted :
    checkOpenPatternWellSorted profile language FreeTypeContext.empty [] (.base "Proc") stored = true := by
  decide +kernel

/-- **Rho's closed declaration rejects the same term**: its quotation mentions the received name. -/
theorem source_not_rho_sorted :
    checkOpenPatternWellSorted rhoReflectionProfile language FreeTypeContext.empty [] (.base "Proc")
      source = false := by
  decide +kernel

theorem rho_quotation_not_admitted :
    ¬ QuotesClosed rhoReflectivePresentation.toReflectivePresentationDecl (.lambda none body) := by
  decide +kernel

/-- Rho's opaque substitution would leave the received name dangling inside the quotation. -/
theorem rho_comm_leaves_dangling_index :
    applyBindingsForRuleUsing rhoReflectionProfile GeneralRho.comm bindings =
        .collection .hashBag
          [.apply "POutput" [.apply "NQuote" [.apply "POutput" [.bvar 0, int0]], int1]] none ∧
      (applyBindingsForRuleUsing rhoReflectionProfile GeneralRho.comm bindings).isWellScopedAt 0 = false := by
  decide +kernel

/-! ## Coherence and scope -/

/-- The declared substitution respects the declared equations. -/
theorem comm_respects (depth : Nat) (replacement : Pattern) {left right : Pattern}
    (same : ReflectiveCanonical.canonicalEquivalent presentation left right = true) :
    ReflectiveCanonical.canonicalEquivalent presentation
      (substituteDeclared presentation depth replacement left)
      (substituteDeclared presentation depth replacement right) = true :=
  ReflectiveCoherent.substituteDeclared_respects depth replacement same

/-- The declared binder elimination keeps ordinary scope: a closed replacement and a body scoped
under the eliminated binder give a result with no dangling index. -/
theorem comm_scoped {depth : Nat} {replacement body : Pattern}
    (bodySafe : body.isWellScopedAt (depth + 1) = true)
    (replacementSafe : replacement.isWellScopedAt 0 = true) :
    (ReflectiveInstantiation.instantiateDeclared presentation depth replacement body).isWellScopedAt
      depth = true :=
  ReflectiveContextualQuote.substituteUnder_scoped (declaration := presentation) (.reaching .apply)
    rfl bodySafe replacementSafe

/-- The Rholang profile asks ordinary scope, which is what its substitution needs. -/
theorem scopeSafe_iff {depth : Nat} {pattern : Pattern} :
    ReflectiveScopeSafeAt profile depth pattern ↔ pattern.isWellScopedAt depth = true := by
  simp [ReflectiveScopeSafeAt, profile, presentation]

/-! ## The plan -/

def snapshot : GeneralExecutionAdmission.Snapshot where
  language := language
  freeTypes := []
  provider := { signatures := [], rows := [] }

/-- Rho's standard reduction contexts and COMM, under the Rholang profile. -/
def permissions : GeneralExecutionAdmission.Permissions :=
  { GeneralRho.Standard.permissions with reflection := profile }

def plan : GeneralExecutionAdmission.Plan := GeneralExecutionAdmission.compile snapshot permissions

theorem dependencies_declared :
    dependencySortsDeclared language Mettapedia.GSLT.Examples.ScopedRhoBinding.scopedCommBindingSpec =
      true := by
  decide +kernel

theorem binding_compiled : GeneralRuleBindingInference.compile? language GeneralRho.comm =
    some GeneralRho.declaration.binding := by
  simp only [GeneralRuleBindingInference.compile?,
    show GeneralRho.comm.bindings = some Mettapedia.GSLT.Examples.ScopedRhoBinding.scopedCommBindingSpec
      from rfl,
    GeneralRho.comm_admitted, dependencies_declared, Bool.true_and, ↓reduceIte]
  rfl

theorem premises_admitted : GeneralPremise.rulePremisesAdmitted language snapshot.provider GeneralRho.comm
    Mettapedia.GSLT.Examples.ScopedRhoBinding.scopedCommBindingSpec = true := by
  simp [GeneralPremise.rulePremisesAdmitted, GeneralPremise.premisesFlow,
    GeneralPremise.namesAvailable, GeneralRho.comm, rhoCommRewrite, Pattern.freeFvarNames]

theorem rule_plan_compiled :
    GeneralExecutionAdmission.rulePlan? snapshot 0 GeneralRho.comm = some GeneralRho.declaration := by
  simp only [GeneralExecutionAdmission.rulePlan?, Option.bind_eq_bind,
    show snapshot.language = language from rfl,
    binding_compiled, Option.bind_some,
    show GeneralRho.declaration.binding.spec = Mettapedia.GSLT.Examples.ScopedRhoBinding.scopedCommBindingSpec
      from rfl,
    show GeneralRho.declaration.binding.elaborate GeneralRho.comm = GeneralRho.comm from rfl,
    premises_admitted, GeneralRho.canonical_comm, GeneralRho.canonical_spines, Bool.and_self, ↓reduceIte]
  rfl

theorem selected_rules :
    GeneralExecutionAdmission.selectedRules snapshot permissions = [(GeneralRho.comm, 0)] := rfl

theorem compiled_rules : plan.rules = [GeneralRho.declaration] := by
  unfold plan GeneralExecutionAdmission.compile GeneralExecutionAdmission.rules
  simp only [selected_rules, List.filterMap_cons, rule_plan_compiled, List.filterMap_nil]

theorem compilation_complete : plan.complete = true := by
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
  change (GeneralExecutionAdmission.compile snapshot permissions).obligations = []
  dsimp only [GeneralExecutionAdmission.compile]
  rw [show snapshot.language.validate = [] from language_valid, freeChecked, providerChecked,
    show Reflection.validate snapshot.language permissions.reflection = [] from profile_valid,
    missingRules, missingEquations, ruleChecks, equationSelection, strata, setChecked]
  rfl

end Mettapedia.OSLF.MeTTaIL.Rholang
