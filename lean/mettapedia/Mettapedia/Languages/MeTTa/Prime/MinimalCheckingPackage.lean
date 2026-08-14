import Mettapedia.GSLT.LanguageDef.InferenceChecker
import Mathlib.Tactic

/-!
# Prime minimal checking-package calibration

This module tests a syntax-free authoring boundary for Prime proof packages.
The authored package content is an ordered list of judgment rules.  Fixed data
constructor arities and outer judgment arities are deterministically projected
as a companion cache required by the current generic checker.

The projection does not parse terms and does not make the companion cache an
authority.  Exact projection agreement is required before a cached
presentation can be used.  The examples establish package-relative replay,
not consistency, truth, source adequacy, or completeness of an object logic.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.Prime.MinimalCheckingPackage

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.GSLT.LanguageDef.InferenceChecker

private def symbol (value : Char) : String := String.singleton value

@[simp] private theorem symbol_inj {left right : Char} :
    symbol left = symbol right ↔ left = right := by
  exact String.singleton_inj

@[simp] private theorem symbol_beq (left right : Char) :
    (symbol left == symbol right) = (left == right) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, symbol_inj]

@[simp] private theorem ruleId_symbol_beq (left right : Char) :
    ((⟨symbol left⟩ : RuleId) == (⟨symbol right⟩ : RuleId)) =
      (left == right) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  simp only [RuleId.mk.injEq, symbol_inj]

@[simp] private theorem symbol_ne_empty (value : Char) :
    symbol value ≠ "" := by
  exact String.singleton_ne_empty

private theorem symbol_ne_long (value first second : Char)
    (rest : List Char) :
    symbol value ≠ String.ofList (first :: second :: rest) := by
  intro h
  rw [symbol, String.singleton_eq_ofList] at h
  have hlength := congrArg List.length (String.ofList_injective h)
  simp at hlength

@[simp] private theorem symbol_ne_zip (value : Char) :
    symbol value ≠ Pattern.zipHead := by
  change symbol value ≠ String.ofList ['$', 'z', 'i', 'p']
  exact symbol_ne_long value '$' 'z' ['i', 'p']

@[simp] private theorem symbol_ne_map (value : Char) :
    symbol value ≠ Pattern.mapHead := by
  change symbol value ≠ String.ofList ['$', 'm', 'a', 'p']
  exact symbol_ne_long value '$' 'm' ['a', 'p']

@[simp] private theorem symbol_ne_eval (value : Char) :
    symbol value ≠ Pattern.evalHead := by
  change symbol value ≠ String.ofList ['$', 'e', 'v', 'a', 'l']
  exact symbol_ne_long value '$' 'e' ['v', 'a', 'l']

abbrev ArityTable := List (String × Nat)

inductive ProjectionError where
  | constructorArityConflict
  | judgmentArityConflict
  | judgmentMustBeApplication
deriving Repr, DecidableEq

private def lookupArity? (table : ArityTable) (head : String) : Option Nat :=
  (table.find? fun entry => entry.1 == head).map (·.2)

private def insertArity (conflict : ProjectionError)
    (table : ArityTable) (head : String) (arity : Nat) :
    Except ProjectionError ArityTable :=
  match lookupArity? table head with
  | none => .ok (table ++ [(head, arity)])
  | some prior => if prior = arity then .ok table else .error conflict

mutual

private def collectFixed (constructors : ArityTable) :
    Pattern → Except ProjectionError ArityTable
  | .bvar _ | .fvar _ => .ok constructors
  | .apply head arguments => do
      let next ← insertArity .constructorArityConflict
        constructors head arguments.length
      collectFixedList next arguments
  | .lambda _ body => collectFixed constructors body
  | .multiLambda _ _ body => collectFixed constructors body
  | .subst body replacement => do
      let next ← collectFixed constructors body
      collectFixed next replacement
  | .collection _ elements _ => collectFixedList constructors elements
termination_by pattern => sizeOf pattern

private def collectFixedList (constructors : ArityTable) :
    List Pattern → Except ProjectionError ArityTable
  | [] => .ok constructors
  | pattern :: patterns => do
      let next ← collectFixed constructors pattern
      collectFixedList next patterns
termination_by patterns => sizeOf patterns

end

private def collectJudgment (constructors judgments : ArityTable)
    (pattern : Pattern) :
    Except ProjectionError (ArityTable × ArityTable) :=
  match pattern with
  | .apply head arguments => do
      let nextJudgments ← insertArity .judgmentArityConflict
        judgments head arguments.length
      let nextConstructors ← collectFixedList constructors arguments
      pure (nextConstructors, nextJudgments)
  | _ => .error .judgmentMustBeApplication

private def collectJudgments (constructors judgments : ArityTable) :
    List Pattern → Except ProjectionError (ArityTable × ArityTable)
  | [] => .ok (constructors, judgments)
  | pattern :: patterns => do
      let (nextConstructors, nextJudgments) ←
        collectJudgment constructors judgments pattern
      collectJudgments nextConstructors nextJudgments patterns

private def collectRules (constructors judgments : ArityTable) :
    List RuleSchema → Except ProjectionError (ArityTable × ArityTable)
  | [] => .ok (constructors, judgments)
  | rule :: rules => do
      let (nextConstructors, nextJudgments) ←
        collectJudgments constructors judgments
          (rule.premises ++ [rule.conclusion])
      collectRules nextConstructors nextJudgments rules

private def dataConstructor (label : String) (arity : Nat) : GrammarRule :=
  { label
    category := "PrimeMinimalData"
    params := (List.range arity).map fun index =>
      .simple ("argument" ++ toString index) (.base "PrimeMinimalData")
    syntaxPattern := [] }

private def cacheLanguage (constructors : ArityTable) : LanguageDef :=
  { name := "PrimeMinimalCheckingCache"
    types := [TypeDecl.plain "PrimeMinimalData"]
    terms := constructors.map fun (label, arity) =>
      dataConstructor label arity
    equations := []
    rewrites := [] }

@[simp] private def cachePresentation (constructors : ArityTable)
    (judgments : List JudgmentDecl) (rules : List RuleSchema) : Presentation :=
  { language := cacheLanguage constructors
    calculus := { judgments, rules } }

/-- Deterministically build the current checker's structural companion from
the authored rule list.  This is a calibration projection, not a new source
language definition. -/
def project (rules : List RuleSchema) : Except ProjectionError Presentation := do
  let (constructors, judgments) ← collectRules [] [] rules
  pure <| cachePresentation constructors
    (judgments.map fun (head, arity) => { head, arity }) rules

/-- Exact cache agreement is deliberately propositional.  An implementation
may compare a canonical serialization, but a cache never validates itself. -/
def CacheAgrees (rules : List RuleSchema) (cached : Presentation) : Prop :=
  project rules = .ok cached

/-- Once an exact projected presentation is admitted and its raw checker
accepts a proof, the existing checker reconstructs a typed derivation with the
same proof tree. -/
theorem projected_check_sound
    {rules : List RuleSchema} {presentation : Presentation}
    {goal : Pattern} {proof : RawProof}
    (hagrees : CacheAgrees rules presentation)
    (hvalid : presentation.isValidV2 = true)
    (hcheck : checkRaw ⟨presentation, hvalid⟩ goal proof = true) :
    CacheAgrees rules presentation ∧
      ∃ derivation : Derivation ⟨presentation, hvalid⟩ goal,
        derivation.erase = proof := by
  exact ⟨hagrees,
    checkRaw_exists_derivation_with_exact_erasure hcheck⟩

private def app (head : String) (arguments : List Pattern := []) : Pattern :=
  .apply head arguments

private def pvar (name : String) : Pattern := .fvar name

private def schema (id : String) (metavariables : List (String × Nat))
    (premises : List Pattern) (conclusion : Pattern) : RuleSchema :=
  { id := ⟨id⟩, metavariables, premises, conclusion }

private def ruleInstance (id : String) (arguments : List Pattern := []) :
    RuleInstance :=
  { ruleId := ⟨id⟩, arguments }

/-! ## Modus ponens calibration package -/

private def mpA : Pattern := app (symbol 'A')
private def mpB : Pattern := app (symbol 'B')
private def mpImp (left right : Pattern) : Pattern :=
  app (symbol 'I') [left, right]
private def mpProves (formula : Pattern) : Pattern :=
  app (symbol 'P') [formula]

private def mpRuleA : RuleSchema :=
  schema (symbol 'a') [] [] (mpProves mpA)

private def mpRuleImp : RuleSchema :=
  schema (symbol 'i') [] [] (mpProves (mpImp mpA mpB))

private def mpRule : RuleSchema :=
  schema (symbol 'm')
      [(symbol 'u', 0), (symbol 'v', 0)]
      [mpProves (pvar (symbol 'u')),
       mpProves (mpImp (pvar (symbol 'u')) (pvar (symbol 'v')))]
      (mpProves (pvar (symbol 'v')))

def mpRules : List RuleSchema := [mpRuleA, mpRuleImp, mpRule]

private theorem collect_mp_rule_a :
    collectJudgments [] [] (mpRuleA.premises ++ [mpRuleA.conclusion]) =
      .ok ([(symbol 'A', 0)], [(symbol 'P', 1)]) := by
  simp (config := { zetaDelta := true })
    [mpRuleA, schema, collectJudgments, collectJudgment,
      collectFixedList, collectFixed, insertArity, lookupArity?,
      mpProves, mpA, app, List.find?, Bind.bind, Pure.pure, Except.bind,
      Except.pure]

private theorem collect_mp_rule_imp :
    collectJudgments [(symbol 'A', 0)] [(symbol 'P', 1)]
        (mpRuleImp.premises ++ [mpRuleImp.conclusion]) =
      .ok
        ([(symbol 'A', 0), (symbol 'I', 2), (symbol 'B', 0)],
         [(symbol 'P', 1)]) := by
  simp (config := { zetaDelta := true })
    [mpRuleImp, schema, collectJudgments, collectJudgment,
      collectFixedList, collectFixed, insertArity, lookupArity?,
      mpProves, mpImp, mpA, mpB, app, List.find?, Bind.bind, Pure.pure,
      Except.bind, Except.pure]

private theorem collect_mp_rule :
    collectJudgments
        [(symbol 'A', 0), (symbol 'I', 2), (symbol 'B', 0)]
        [(symbol 'P', 1)] (mpRule.premises ++ [mpRule.conclusion]) =
      .ok
        ([(symbol 'A', 0), (symbol 'I', 2), (symbol 'B', 0)],
         [(symbol 'P', 1)]) := by
  simp (config := { zetaDelta := true })
    [mpRule, schema, collectJudgments, collectJudgment,
      collectFixedList, collectFixed, insertArity, lookupArity?,
      mpProves, mpImp, app, pvar, List.find?, Bind.bind, Pure.pure,
      Except.bind, Except.pure]

/-- Independently written companion cache for the MP package. -/
def mpCache : Presentation :=
  cachePresentation
      [(symbol 'A', 0), (symbol 'I', 2), (symbol 'B', 0)]
    [{ head := symbol 'P', arity := 1 }] mpRules

theorem mp_cache_exact : CacheAgrees mpRules mpCache := by
  simp [CacheAgrees, project, collectRules, mpRules, collect_mp_rule_a,
    collect_mp_rule_imp, collect_mp_rule, mpCache, Bind.bind, Pure.pure,
    Except.bind, Except.pure]

private theorem mp_cache_language_valid : mpCache.language.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorOnly <;>
    simp [mpCache, cacheLanguage, dataConstructor, LanguageDef.typeNames,
      TypeDecl.plain, TermParam.typeExpr, TypeExpr.baseNames]

theorem mp_cache_valid : mpCache.isValidV2 = true := by
  unfold Presentation.isValidV2 Presentation.isValidV1
  rw [mp_cache_language_valid]
  simp [mpCache, mpRules, mpRuleA, mpRuleImp, mpRule, schema,
    cacheLanguage, dataConstructor,
    Presentation.ruleIds, RuleSchema.isValidV1,
    RuleSchema.metavariableNames, RuleSchema.occurrences,
    RuleSchema.patterns, patternMetavariableOccurrencesAt,
    patternsMetavariableOccurrencesAt, patternHasNoCollectionRest,
    patternsHaveNoCollectionRest, Presentation.judgmentSignatureValid,
    Presentation.judgmentHeads, RuleSchema.isValidIn,
    Presentation.judgmentSchemaValid, Presentation.lookupJudgment?,
    fixedConstructorListsValid, fixedConstructorsValid,
    languageHasConstructorArity, Pattern.isWellScoped,
    Pattern.isWellScopedAt, Pattern.isWellScopedListAt,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList, mpProves, mpImp, mpA, mpB,
    app, pvar, List.eraseDups, List.eraseDupsBy]
  norm_num [List.eraseDupsBy.loop]
  decide

def mpValidated : ValidatedPresentation := ⟨mpCache, mp_cache_valid⟩

private def mpProofA : RawProof :=
  .node (ruleInstance (symbol 'a')) []

private def mpProofImp : RawProof :=
  .node (ruleInstance (symbol 'i')) []

def mpProofB : RawProof :=
  .node (ruleInstance (symbol 'm') [mpA, mpB]) [mpProofA, mpProofImp]

def mpBGoal : Pattern := mpProves mpB

theorem mp_proof_b_accepted : checkRaw mpValidated mpBGoal mpProofB = true := by
  simp [mpValidated, mpCache, mpRules, mpRuleA, mpRuleImp, mpRule,
    schema, ruleInstance,
    checkRaw, instantiateRule?, Presentation.lookupRule?,
    argumentsValidAt, argumentValidAt, instantiateSchema?,
    instantiateSchemaAt?, instantiateSchemas?, instantiateSchemasAt?,
    lookupArgumentAt?, Pattern.isGroundAt, Pattern.isGroundListAt,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList, mpBGoal, mpProofB, mpProofA,
    mpProofImp, mpProves, mpImp, mpA, mpB, app, pvar]
  simp [checkRawChildren, checkRaw, instantiateRule?,
    Presentation.lookupRule?, argumentsValidAt, instantiateSchema?,
    instantiateSchemaAt?, instantiateSchemas?, instantiateSchemasAt?]

theorem mp_wrong_goal_rejected :
    checkRaw mpValidated (mpProves mpA) mpProofB = false := by
  simp [mpValidated, mpCache, mpRules, mpRuleA, mpRuleImp, mpRule,
    schema, ruleInstance,
    checkRaw, instantiateRule?, Presentation.lookupRule?,
    argumentsValidAt, argumentValidAt, instantiateSchema?,
    instantiateSchemaAt?, instantiateSchemas?, instantiateSchemasAt?,
    lookupArgumentAt?, Pattern.isGroundAt, Pattern.isGroundListAt,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList, mpProofB, mpProofA, mpProofImp,
    mpProves, mpImp, mpA, mpB, app, pvar]

/-! ## Small DTT-shaped calibration package

This package is intentionally only large enough to exercise a typing judgment
and application rule.  It is not a claim that this rule list is Prime's DTT or
that the generic checker has acquired DTT semantics.
-/

private def dttCtx : Pattern := app (symbol 'C')
private def dttNat : Pattern := app (symbol 'N')
private def dttZero : Pattern := app (symbol 'Z')
private def dttId : Pattern := app (symbol 'i')
private def dttPi (domain codomain : Pattern) : Pattern :=
  app (symbol 'F') [domain, codomain]
private def dttApp (function argument : Pattern) : Pattern :=
  app (symbol '@') [function, argument]
private def dttHasType (context term type : Pattern) : Pattern :=
  app (symbol 'T') [context, term, type]
private def dttReduces (function argument result : Pattern) : Pattern :=
  app (symbol 'E') [function, argument, result]

private def dttRuleZero : RuleSchema :=
  schema (symbol 'z') [] [] (dttHasType dttCtx dttZero dttNat)

private def dttRuleId : RuleSchema :=
  schema (symbol 'j') [] []
    (dttHasType dttCtx dttId (dttPi dttNat dttNat))

private def dttRuleApp : RuleSchema :=
  schema (symbol 'k')
    [(symbol 'f', 0), (symbol 'x', 0),
     (symbol 'd', 0), (symbol 'c', 0)]
    [dttHasType dttCtx (pvar (symbol 'f'))
       (dttPi (pvar (symbol 'd')) (pvar (symbol 'c'))),
     dttHasType dttCtx (pvar (symbol 'x')) (pvar (symbol 'd'))]
    (dttHasType dttCtx
      (dttApp (pvar (symbol 'f')) (pvar (symbol 'x')))
      (pvar (symbol 'c')))

private def dttRuleBeta : RuleSchema :=
  { id := ⟨symbol 'b'⟩
    metavariables :=
      [(symbol 'u', 1), (symbol 'x', 0), (symbol 'v', 0)]
    premises := []
    conclusion :=
      dttReduces (.lambda none (pvar (symbol 'u')))
        (pvar (symbol 'x')) (pvar (symbol 'v'))
    sideConditions := [.explicitSubstitution 0 0 1 2] }

def dttRules : List RuleSchema :=
  [dttRuleZero, dttRuleId, dttRuleApp, dttRuleBeta]

private theorem collect_dtt_rule_zero :
    collectJudgments [] []
        (dttRuleZero.premises ++ [dttRuleZero.conclusion]) =
      .ok
        ([(symbol 'C', 0), (symbol 'Z', 0), (symbol 'N', 0)],
         [(symbol 'T', 3)]) := by
  simp (config := { zetaDelta := true })
    [dttRuleZero, schema, collectJudgments, collectJudgment,
      collectFixedList, collectFixed, insertArity, lookupArity?,
      dttHasType, dttCtx, dttZero, dttNat, app, List.find?, Bind.bind,
      Pure.pure, Except.bind, Except.pure]

private theorem collect_dtt_rule_id :
    collectJudgments
        [(symbol 'C', 0), (symbol 'Z', 0), (symbol 'N', 0)]
        [(symbol 'T', 3)]
        (dttRuleId.premises ++ [dttRuleId.conclusion]) =
      .ok
        ([(symbol 'C', 0), (symbol 'Z', 0), (symbol 'N', 0),
          (symbol 'i', 0), (symbol 'F', 2)],
         [(symbol 'T', 3)]) := by
  simp (config := { zetaDelta := true })
    [dttRuleId, schema, collectJudgments, collectJudgment,
      collectFixedList, collectFixed, insertArity, lookupArity?,
      dttHasType, dttCtx, dttId, dttPi, dttNat, app, List.find?,
      Bind.bind, Pure.pure, Except.bind, Except.pure]

private theorem collect_dtt_rule_app :
    collectJudgments
        [(symbol 'C', 0), (symbol 'Z', 0), (symbol 'N', 0),
         (symbol 'i', 0), (symbol 'F', 2)]
        [(symbol 'T', 3)]
        (dttRuleApp.premises ++ [dttRuleApp.conclusion]) =
      .ok
        ([(symbol 'C', 0), (symbol 'Z', 0), (symbol 'N', 0),
          (symbol 'i', 0), (symbol 'F', 2), (symbol '@', 2)],
         [(symbol 'T', 3)]) := by
  simp (config := { zetaDelta := true })
    [dttRuleApp, schema, collectJudgments, collectJudgment,
      collectFixedList, collectFixed, insertArity, lookupArity?,
      dttHasType, dttCtx, dttPi, dttApp, app, pvar, List.find?,
      Bind.bind, Pure.pure, Except.bind, Except.pure]

private theorem collect_dtt_rule_beta :
    collectJudgments
        [(symbol 'C', 0), (symbol 'Z', 0), (symbol 'N', 0),
         (symbol 'i', 0), (symbol 'F', 2), (symbol '@', 2)]
        [(symbol 'T', 3)]
        (dttRuleBeta.premises ++ [dttRuleBeta.conclusion]) =
      .ok
        ([(symbol 'C', 0), (symbol 'Z', 0), (symbol 'N', 0),
          (symbol 'i', 0), (symbol 'F', 2), (symbol '@', 2)],
         [(symbol 'T', 3), (symbol 'E', 3)]) := by
  simp (config := { zetaDelta := true })
    [dttRuleBeta, collectJudgments, collectJudgment,
      collectFixedList, collectFixed, insertArity, lookupArity?,
      dttReduces, app, pvar, List.find?, Bind.bind, Pure.pure,
      Except.bind, Except.pure]

/-- Independently written companion cache for the DTT-shaped package. -/
def dttCache : Presentation :=
  cachePresentation
      [(symbol 'C', 0), (symbol 'Z', 0), (symbol 'N', 0),
       (symbol 'i', 0), (symbol 'F', 2), (symbol '@', 2)]
    [{ head := symbol 'T', arity := 3 },
     { head := symbol 'E', arity := 3 }] dttRules

theorem dtt_cache_exact : CacheAgrees dttRules dttCache := by
  simp [CacheAgrees, project, collectRules, dttRules,
    collect_dtt_rule_zero, collect_dtt_rule_id, collect_dtt_rule_app,
    collect_dtt_rule_beta, dttCache, Bind.bind, Pure.pure, Except.bind,
    Except.pure]

private theorem dtt_cache_language_valid :
    dttCache.language.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorOnly <;>
    simp [dttCache, cacheLanguage, dataConstructor, LanguageDef.typeNames,
      TypeDecl.plain, TermParam.typeExpr, TypeExpr.baseNames]

theorem dtt_cache_valid : dttCache.isValidV2 = true := by
  unfold Presentation.isValidV2 Presentation.isValidV1
  rw [dtt_cache_language_valid]
  simp [dttCache, dttRules, dttRuleZero, dttRuleId, dttRuleApp,
    dttRuleBeta, schema,
    cacheLanguage, dataConstructor,
    Presentation.ruleIds, RuleSchema.isValidV1,
    RuleSchema.metavariableNames, RuleSchema.occurrences,
    RuleSchema.patterns, patternMetavariableOccurrencesAt,
    patternsMetavariableOccurrencesAt, patternHasNoCollectionRest,
    patternsHaveNoCollectionRest, Presentation.judgmentSignatureValid,
    Presentation.judgmentHeads, RuleSchema.isValidIn,
    Presentation.judgmentSchemaValid, Presentation.lookupJudgment?,
    fixedConstructorListsValid, fixedConstructorsValid,
    languageHasConstructorArity, Pattern.isWellScoped,
    Pattern.isWellScopedAt, Pattern.isWellScopedListAt,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList, dttHasType, dttCtx, dttZero,
    dttNat, dttId, dttPi, dttApp, dttReduces, app, pvar, List.eraseDups,
    List.eraseDupsBy]
  norm_num [List.eraseDupsBy.loop]
  decide

def dttValidated : ValidatedPresentation :=
  ⟨dttCache, dtt_cache_valid⟩

private def dttProofZero : RawProof :=
  .node (ruleInstance (symbol 'z')) []

private def dttProofId : RawProof :=
  .node (ruleInstance (symbol 'j')) []

def dttProofIdZero : RawProof :=
  .node (ruleInstance (symbol 'k') [dttId, dttZero, dttNat, dttNat])
    [dttProofId, dttProofZero]

def dttIdZeroGoal : Pattern :=
  dttHasType dttCtx (dttApp dttId dttZero) dttNat

def dttProofBetaZero : RawProof :=
  .node (ruleInstance (symbol 'b') [.bvar 0, dttZero, dttZero]) []

def dttBetaZeroGoal : Pattern :=
  dttReduces (.lambda none (.bvar 0)) dttZero dttZero

private def dttStructuralBetaBody : Pattern :=
  dttApp
    (.multiLambda 2 [] (.bvar 2))
    (.subst (.bvar 1) (.collection .vec [.bvar 0] none))

private def dttStructuralBetaResult : Pattern :=
  dttApp
    (.multiLambda 2 [] dttZero)
    (.subst dttZero (.collection .vec [dttZero] none))

def dttProofStructuralBeta : RawProof :=
  .node
    (ruleInstance (symbol 'b')
      [dttStructuralBetaBody, dttZero, dttStructuralBetaResult]) []

def dttStructuralBetaGoal : Pattern :=
  dttReduces (.lambda none dttStructuralBetaBody)
    dttZero dttStructuralBetaResult

theorem dtt_id_zero_accepted :
    checkRaw dttValidated dttIdZeroGoal dttProofIdZero = true := by
  simp [dttValidated, dttCache, dttRules, dttRuleZero, dttRuleId,
    dttRuleApp, schema, ruleInstance, checkRaw, instantiateRule?,
    Presentation.lookupRule?, argumentsValidAt, argumentValidAt,
    instantiateSchema?, instantiateSchemaAt?, instantiateSchemas?,
    instantiateSchemasAt?, lookupArgumentAt?, Pattern.isGroundAt,
    Pattern.isGroundListAt, Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList, dttIdZeroGoal, dttProofIdZero,
    dttProofId, dttProofZero, dttHasType, dttCtx, dttZero, dttNat,
    dttId, dttPi, dttApp, app, pvar]
  simp [checkRawChildren, checkRaw, instantiateRule?,
    Presentation.lookupRule?, argumentsValidAt, instantiateSchema?,
    instantiateSchemaAt?, instantiateSchemas?, instantiateSchemasAt?]

theorem dtt_wrong_goal_rejected :
    checkRaw dttValidated (dttHasType dttCtx dttZero dttId)
      dttProofZero = false := by
  simp [dttValidated, dttCache, dttRules, dttRuleZero, dttRuleId,
    dttRuleApp, schema, ruleInstance, checkRaw, instantiateRule?,
    Presentation.lookupRule?, argumentsValidAt,
    instantiateSchema?, instantiateSchemaAt?, instantiateSchemas?,
    instantiateSchemasAt?, dttProofZero, dttHasType, dttCtx, dttZero,
    dttNat, dttId, app, pvar]

theorem dtt_beta_zero_accepted :
    checkRaw dttValidated dttBetaZeroGoal dttProofBetaZero = true := by
  simp [dttValidated, dttCache, dttRules, dttRuleBeta, dttRuleZero,
    dttRuleId, dttRuleApp, schema, ruleInstance, checkRaw,
    instantiateRule?, Presentation.lookupRule?, argumentsValidAt,
    argumentValidAt, instantiateSchema?, instantiateSchemaAt?,
    instantiateSchemas?, instantiateSchemasAt?, lookupArgumentAt?,
    Pattern.isGroundAt, Pattern.isGroundListAt,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList, RuleSchema.sideConditionsHold,
    RuleSideCondition.holds, instantiateBVar, instantiateBVarAt, liftBVars,
    dttBetaZeroGoal, dttProofBetaZero, dttReduces, dttZero, app, pvar]
  simp [checkRawChildren]

theorem dtt_beta_wrong_result_rejected :
    checkRaw dttValidated
      (dttReduces (.lambda none (.bvar 0)) dttZero dttNat)
      (.node (ruleInstance (symbol 'b') [.bvar 0, dttZero, dttNat]) []) =
        false := by
  simp [dttValidated, dttCache, dttRules, dttRuleBeta, dttRuleZero,
    dttRuleId, dttRuleApp, schema, ruleInstance, checkRaw,
    instantiateRule?, Presentation.lookupRule?, argumentsValidAt,
    argumentValidAt,
    Pattern.isGroundAt, Pattern.isGroundListAt,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList, RuleSchema.sideConditionsHold,
    instantiateBVar, instantiateBVarAt, liftBVars,
    dttReduces, dttZero, dttNat, app, pvar]

theorem dtt_structural_beta_accepted :
    checkRaw dttValidated dttStructuralBetaGoal dttProofStructuralBeta =
      true := by
  simp [dttValidated, dttCache, dttRules, dttRuleBeta, dttRuleZero,
    dttRuleId, dttRuleApp, schema, ruleInstance, checkRaw,
    instantiateRule?, Presentation.lookupRule?, argumentsValidAt,
    argumentValidAt, instantiateSchema?, instantiateSchemaAt?,
    instantiateSchemas?, instantiateSchemasAt?, lookupArgumentAt?,
    Pattern.isGroundAt, Pattern.isGroundListAt,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList, RuleSchema.sideConditionsHold,
    RuleSideCondition.holds, instantiateBVar, instantiateBVarAt, liftBVars,
    dttStructuralBetaGoal, dttProofStructuralBeta,
    dttStructuralBetaBody, dttStructuralBetaResult, dttReduces, dttZero,
    dttApp, app, pvar]
  simp [checkRawChildren]

/-! ## Native HOTG-shaped calibration package

The vocabulary is set-theoretic rather than encoded as DTT terms.  These three
rules are only a falsifying peer-package canary; adequacy to Megalodon or HOTG
requires a separate source-faithfulness theorem.
-/

private def hotgN : Pattern := app (symbol 'n')
private def hotgPower (set : Pattern) : Pattern :=
  app (symbol 'W') [set]
private def hotgUnivOf (set : Pattern) : Pattern :=
  app (symbol 'U') [set]
private def hotgIn (element set : Pattern) : Pattern :=
  app (symbol 'I') [element, set]
private def hotgClosed (set : Pattern) : Pattern :=
  app (symbol 'C') [set]
private def hotgProves (proposition : Pattern) : Pattern :=
  app (symbol 'H') [proposition]

private def hotgRuleUniverseMember : RuleSchema :=
  schema (symbol 'q') [] []
    (hotgProves
      (hotgIn hotgN (hotgUnivOf hotgN)))

private def hotgRuleUniverseClosed : RuleSchema :=
  schema (symbol 'r') [(symbol 'n', 0)] []
    (hotgProves (hotgClosed (hotgUnivOf (pvar (symbol 'n')))))

private def hotgRulePowerClosed : RuleSchema :=
  schema (symbol 's') [(symbol 'u', 0), (symbol 'x', 0)]
    [hotgProves (hotgClosed (pvar (symbol 'u'))),
     hotgProves (hotgIn (pvar (symbol 'x')) (pvar (symbol 'u')))]
    (hotgProves
      (hotgIn (hotgPower (pvar (symbol 'x'))) (pvar (symbol 'u'))))

def hotgRules : List RuleSchema :=
  [hotgRuleUniverseMember, hotgRuleUniverseClosed, hotgRulePowerClosed]

private theorem collect_hotg_rule_universe_member :
    collectJudgments [] []
        (hotgRuleUniverseMember.premises ++
          [hotgRuleUniverseMember.conclusion]) =
      .ok
        ([(symbol 'I', 2), (symbol 'n', 0), (symbol 'U', 1)],
         [(symbol 'H', 1)]) := by
  simp (config := { zetaDelta := true })
    [hotgRuleUniverseMember, schema, collectJudgments, collectJudgment,
      collectFixedList, collectFixed, insertArity, lookupArity?,
      hotgProves, hotgIn, hotgUnivOf, hotgN, app, List.find?, Bind.bind,
      Pure.pure, Except.bind, Except.pure]

private theorem collect_hotg_rule_universe_closed :
    collectJudgments [(symbol 'I', 2), (symbol 'n', 0), (symbol 'U', 1)]
        [(symbol 'H', 1)]
        (hotgRuleUniverseClosed.premises ++
          [hotgRuleUniverseClosed.conclusion]) =
      .ok
        ([(symbol 'I', 2), (symbol 'n', 0), (symbol 'U', 1),
          (symbol 'C', 1)],
         [(symbol 'H', 1)]) := by
  simp (config := { zetaDelta := true })
    [hotgRuleUniverseClosed, schema, collectJudgments, collectJudgment,
      collectFixedList, collectFixed, insertArity, lookupArity?,
      hotgProves, hotgClosed, hotgUnivOf, app, pvar, List.find?,
      Bind.bind, Pure.pure, Except.bind, Except.pure]

private theorem collect_hotg_rule_power_closed :
    collectJudgments
        [(symbol 'I', 2), (symbol 'n', 0), (symbol 'U', 1),
          (symbol 'C', 1)]
        [(symbol 'H', 1)]
        (hotgRulePowerClosed.premises ++
          [hotgRulePowerClosed.conclusion]) =
      .ok
        ([(symbol 'I', 2), (symbol 'n', 0), (symbol 'U', 1),
          (symbol 'C', 1), (symbol 'W', 1)],
         [(symbol 'H', 1)]) := by
  simp (config := { zetaDelta := true })
    [hotgRulePowerClosed, schema, collectJudgments, collectJudgment,
      collectFixedList, collectFixed, insertArity, lookupArity?,
      hotgProves, hotgClosed, hotgIn, hotgPower, app, pvar, List.find?,
      Bind.bind, Pure.pure, Except.bind, Except.pure]

/-- Independently written companion cache for the HOTG-shaped package. -/
def hotgCache : Presentation :=
  cachePresentation
      [(symbol 'I', 2), (symbol 'n', 0), (symbol 'U', 1),
       (symbol 'C', 1), (symbol 'W', 1)]
    [{ head := symbol 'H', arity := 1 }] hotgRules

theorem hotg_cache_exact : CacheAgrees hotgRules hotgCache := by
  simp [CacheAgrees, project, collectRules, hotgRules,
    collect_hotg_rule_universe_member, collect_hotg_rule_universe_closed,
    collect_hotg_rule_power_closed, hotgCache, Bind.bind, Pure.pure,
    Except.bind, Except.pure]

private theorem hotg_cache_language_valid :
    hotgCache.language.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorOnly <;>
    simp [hotgCache, cacheLanguage, dataConstructor, LanguageDef.typeNames,
      TypeDecl.plain, TermParam.typeExpr, TypeExpr.baseNames]

theorem hotg_cache_valid : hotgCache.isValidV2 = true := by
  unfold Presentation.isValidV2 Presentation.isValidV1
  rw [hotg_cache_language_valid]
  simp [hotgCache, hotgRules, hotgRuleUniverseMember,
    hotgRuleUniverseClosed, hotgRulePowerClosed, schema, cacheLanguage,
    dataConstructor, Presentation.ruleIds, RuleSchema.isValidV1,
    RuleSchema.metavariableNames, RuleSchema.occurrences,
    RuleSchema.patterns, patternMetavariableOccurrencesAt,
    patternsMetavariableOccurrencesAt, patternHasNoCollectionRest,
    patternsHaveNoCollectionRest, Presentation.judgmentSignatureValid,
    Presentation.judgmentHeads, RuleSchema.isValidIn,
    Presentation.judgmentSchemaValid, Presentation.lookupJudgment?,
    fixedConstructorListsValid, fixedConstructorsValid,
    languageHasConstructorArity, Pattern.isWellScoped,
    Pattern.isWellScopedAt, Pattern.isWellScopedListAt,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList, hotgProves, hotgClosed,
    hotgIn, hotgPower, hotgUnivOf, hotgN, app, pvar, List.eraseDups,
    List.eraseDupsBy]
  norm_num [List.eraseDupsBy.loop]
  decide

def hotgValidated : ValidatedPresentation :=
  ⟨hotgCache, hotg_cache_valid⟩

private def hotgProofUniverseMember : RawProof :=
  .node (ruleInstance (symbol 'q') []) []

private def hotgProofUniverseClosed : RawProof :=
  .node (ruleInstance (symbol 'r') [hotgN]) []

def hotgProofPower : RawProof :=
  .node (ruleInstance (symbol 's') [hotgUnivOf hotgN, hotgN])
    [hotgProofUniverseClosed, hotgProofUniverseMember]

def hotgPowerGoal : Pattern :=
  hotgProves (hotgIn (hotgPower hotgN) (hotgUnivOf hotgN))

theorem hotg_power_accepted :
    checkRaw hotgValidated hotgPowerGoal hotgProofPower = true := by
  simp [hotgValidated, hotgCache, hotgRules, hotgRuleUniverseMember,
    hotgRuleUniverseClosed, hotgRulePowerClosed, schema, ruleInstance,
    checkRaw, instantiateRule?, Presentation.lookupRule?, argumentsValidAt,
    argumentValidAt, instantiateSchema?, instantiateSchemaAt?,
    instantiateSchemas?, instantiateSchemasAt?, lookupArgumentAt?,
    Pattern.isGroundAt, Pattern.isGroundListAt,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList, hotgPowerGoal, hotgProofPower,
    hotgProofUniverseClosed, hotgProofUniverseMember, hotgProves,
    hotgClosed, hotgIn, hotgPower, hotgUnivOf, hotgN, app, pvar]
  simp [checkRawChildren, checkRaw, instantiateRule?,
    Presentation.lookupRule?, argumentsValidAt, argumentValidAt,
    instantiateSchema?, instantiateSchemaAt?, instantiateSchemas?,
    instantiateSchemasAt?, lookupArgumentAt?, Pattern.isGroundAt,
    Pattern.isGroundListAt, Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList]

theorem dtt_proof_rejected_by_hotg_package :
    checkRaw hotgValidated hotgPowerGoal dttProofIdZero = false := by
  simp [hotgValidated, hotgCache, hotgRules, hotgRuleUniverseMember,
    hotgRuleUniverseClosed, hotgRulePowerClosed, schema, dttProofIdZero,
    ruleInstance, checkRaw, instantiateRule?, Presentation.lookupRule?,
    List.find?]

theorem hotg_proof_rejected_by_dtt_package :
    checkRaw dttValidated dttIdZeroGoal hotgProofPower = false := by
  simp [dttValidated, dttCache, dttRules, dttRuleZero, dttRuleId,
    dttRuleApp, dttRuleBeta, schema, hotgProofPower, ruleInstance, checkRaw,
    instantiateRule?, Presentation.lookupRule?, List.find?]

/-! ## Projection conflict calibration -/

private def conflictingRuleZero : RuleSchema :=
  schema (symbol 'x') [] [] (mpProves (app (symbol 'F')))

private def conflictingRuleOne : RuleSchema :=
  schema (symbol 'y') [] [] (mpProves (app (symbol 'F') [mpA]))

def conflictingRules : List RuleSchema :=
  [conflictingRuleZero, conflictingRuleOne]

private theorem collect_conflicting_zero :
    collectJudgments [] []
        (conflictingRuleZero.premises ++ [conflictingRuleZero.conclusion]) =
      .ok ([(symbol 'F', 0)], [(symbol 'P', 1)]) := by
  simp (config := { zetaDelta := true })
    [conflictingRuleZero, schema, collectJudgments, collectJudgment,
      collectFixedList, collectFixed, insertArity, lookupArity?,
      mpProves, app, List.find?, Bind.bind, Pure.pure, Except.bind,
      Except.pure]

private theorem collect_conflicting_one :
    collectJudgments [(symbol 'F', 0)] [(symbol 'P', 1)]
        (conflictingRuleOne.premises ++ [conflictingRuleOne.conclusion]) =
      .error .constructorArityConflict := by
  simp (config := { zetaDelta := true })
    [conflictingRuleOne, schema, collectJudgments, collectJudgment,
      collectFixedList, collectFixed, insertArity, lookupArity?,
      mpProves, mpA, app, List.find?, Bind.bind, Except.bind]

theorem conflicting_constructor_arities_rejected :
    project conflictingRules = .error .constructorArityConflict := by
  simp [project, conflictingRules, collectRules, collect_conflicting_zero,
    collect_conflicting_one, Bind.bind, Except.bind]

end Mettapedia.Languages.MeTTa.Prime.MinimalCheckingPackage
