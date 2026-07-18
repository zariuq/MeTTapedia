import Mettapedia.Languages.MeTTa.Prime.PackageIdentityV1
import Mathlib.Tactic

/-!
# Prime bounded MeTTa-fragment adequacy

This module defines a small source fragment containing the equations exercised
by the addition, list-length, and finite-pick fixtures.  Its rule package is a
deterministic compilation of those source declarations.  A separate typed
evaluation relation and answer-bag function give the source its operational
meaning.

The adequacy statements are deliberately scoped to encoded goals of this
fragment.  The generic checker permits unclassified ground metavariable
payloads, so it would be false to claim that every pattern it accepts is a
typed MeTTa value.  No parser or syntax table participates in proof checking.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.Prime.FragmentAdequacyV1

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.InferenceMeTTaRender

/-! ## Independent source and evaluator -/

inductive NatValue where
  | zero
  | succ (predecessor : NatValue)
deriving Repr, DecidableEq

inductive ItemValue where
  | a
  | b
deriving Repr, DecidableEq

inductive ListValue where
  | nil
  | cons (head : ItemValue) (tail : ListValue)
deriving Repr, DecidableEq

inductive ResultSort where
  | nat
  | pick
deriving Repr, DecidableEq

inductive PickValue where
  | a
  | b
deriving Repr, DecidableEq

inductive FragmentExpr : ResultSort → Type where
  | add (left right : NatValue) : FragmentExpr .nat
  | length (value : ListValue) : FragmentExpr .nat
  | pick : FragmentExpr .pick
deriving Repr

inductive FragmentValue : ResultSort → Type where
  | nat (value : NatValue) : FragmentValue .nat
  | pick (value : PickValue) : FragmentValue .pick
deriving Repr, DecidableEq

def addNat : NatValue → NatValue → NatValue
  | .zero, right => right
  | .succ left, right => .succ (addNat left right)

def lengthNat : ListValue → NatValue
  | .nil => .zero
  | .cons _ tail => .succ (lengthNat tail)

/-- Executable result bags preserve order and multiplicity. -/
def evalBag : {sort : ResultSort} →
    FragmentExpr sort → List (FragmentValue sort)
  | _, .add left right => [.nat (addNat left right)]
  | _, .length value => [.nat (lengthNat value)]
  | _, .pick => [.pick .a, .pick .b]

/-- Declarative evaluator, written independently from the proof-package
compiler below. -/
inductive Evaluates : {sort : ResultSort} →
    FragmentExpr sort → FragmentValue sort → Prop where
  | addZero (right : NatValue) :
      Evaluates (.add .zero right) (.nat right)
  | addSucc (left right result : NatValue)
      (prior : Evaluates (.add left right) (.nat result)) :
      Evaluates (.add (.succ left) right) (.nat (.succ result))
  | lengthNil : Evaluates (.length .nil) (.nat .zero)
  | lengthCons (head : ItemValue) (tail : ListValue) (result : NatValue)
      (prior : Evaluates (.length tail) (.nat result)) :
      Evaluates (.length (.cons head tail)) (.nat (.succ result))
  | pickA : Evaluates .pick (.pick .a)
  | pickB : Evaluates .pick (.pick .b)

theorem evaluates_iff_mem_evalBag {sort : ResultSort}
    {expression : FragmentExpr sort} {value : FragmentValue sort} :
    Evaluates expression value ↔ value ∈ evalBag expression := by
  constructor
  · intro evaluation
    induction evaluation with
    | addZero => simp [evalBag, addNat]
    | addSucc left right result _ ih =>
        simpa [evalBag, addNat] using ih
    | lengthNil => simp [evalBag, lengthNat]
    | lengthCons head tail result _ ih =>
        simpa [evalBag, lengthNat] using ih
    | pickA => simp [evalBag]
    | pickB => simp [evalBag]
  · intro membership
    cases expression with
    | add left right =>
        simp only [evalBag, List.mem_singleton] at membership
        subst value
        induction left with
        | zero => exact .addZero right
        | succ left ih => exact .addSucc left right (addNat left right) ih
    | length input =>
        simp only [evalBag, List.mem_singleton] at membership
        subst value
        induction input with
        | nil => exact .lengthNil
        | cons head tail ih =>
            exact .lengthCons head tail (lengthNat tail) ih
    | pick =>
        simp [evalBag] at membership
        rcases membership with rfl | rfl
        · exact .pickA
        · exact .pickB

/-! ## Source declarations and deterministic package compilation -/

inductive EquationDecl where
  | addZero
  | addSuccessor
  | lengthNil
  | lengthCons
  | pickAlternativeA
  | pickAlternativeB
  | pickAlternativeC
  | addSuccessorWrongSubstitution
deriving Repr, DecidableEq

inductive ClosureDecl where
  | mayEvalMembership
deriving Repr, DecidableEq

inductive SourceDecl where
  | equation (declaration : EquationDecl)
  | closure (declaration : ClosureDecl)
deriving Repr, DecidableEq

private def app (head : String) (arguments : List Pattern := []) : Pattern :=
  .apply head arguments

private def pvar (name : String) : Pattern := .fvar name

private def schema (id : String) (metavariables : List (String × Nat))
    (premises : List Pattern) (conclusion : Pattern) : RuleSchema :=
  { id := ⟨id⟩, metavariables, premises, conclusion }

def natZeroP : Pattern := app "wex.Z"
def natSuccP (value : Pattern) : Pattern := app "wex.S" [value]
def addP (left right : Pattern) : Pattern := app "wex.add" [left, right]
def evalP (expression value : Pattern) : Pattern :=
  app "wex1.Evals" [expression, value]

def nilP : Pattern := app "wex.Nil"
def consP (head tail : Pattern) : Pattern := app "wex.Cons" [head, tail]
def itemAP : Pattern := app "wex.a"
def itemBP : Pattern := app "wex.b"
def lengthP (input result : Pattern) : Pattern :=
  app "wex2.LenIs" [input, result]

def pickP : Pattern := app "wex.pick"
def pickAP : Pattern := app "wex.A"
def pickBP : Pattern := app "wex.B"
def pickCP : Pattern := app "wex.C"
def resultSetP (expression : Pattern) : Pattern :=
  app "wex.ResultSet" [expression]
def mayEvalP (expression value : Pattern) : Pattern :=
  app "wex3.MayEval" [expression, value]
def memberP (value set : Pattern) : Pattern :=
  app "wex3.In" [value, set]

def compileEquation : EquationDecl → RuleSchema
  | .addZero =>
      schema "wex1.add-z" [("n", 0)] []
        (evalP (addP natZeroP (pvar "n")) (pvar "n"))
  | .addSuccessor =>
      schema "wex1.add-s" [("m", 0), ("n", 0), ("v", 0)]
        [evalP (addP (pvar "m") (pvar "n")) (pvar "v")]
        (evalP (addP (natSuccP (pvar "m")) (pvar "n"))
          (natSuccP (pvar "v")))
  | .lengthNil =>
      schema "wex2.len-nil" [] [] (lengthP nilP natZeroP)
  | .lengthCons =>
      schema "wex2.len-cons" [("h", 0), ("t", 0), ("v", 0)]
        [lengthP (pvar "t") (pvar "v")]
        (lengthP (consP (pvar "h") (pvar "t"))
          (natSuccP (pvar "v")))
  | .pickAlternativeA =>
      schema "wex3.pick-a" [] [] (mayEvalP pickP pickAP)
  | .pickAlternativeB =>
      schema "wex3.pick-b" [] [] (mayEvalP pickP pickBP)
  | .pickAlternativeC =>
      schema "wex3.pick-c" [] [] (mayEvalP pickP pickCP)
  | .addSuccessorWrongSubstitution =>
      schema "wex1.add-s" [("m", 0), ("n", 0), ("v", 0)]
        [evalP (addP (pvar "m") (pvar "n")) (pvar "v")]
        (evalP (addP (natSuccP (pvar "m")) (pvar "n"))
          (natSuccP (pvar "m")))

def compileClosure : ClosureDecl → RuleSchema
  | .mayEvalMembership =>
      schema "wex3.mayeval-in" [("x", 0)]
        [mayEvalP pickP (pvar "x")]
        (memberP (pvar "x") (resultSetP pickP))

def compileDecl : SourceDecl → RuleSchema
  | .equation declaration => compileEquation declaration
  | .closure declaration => compileClosure declaration

def compileSource (source : List SourceDecl) : List RuleSchema :=
  source.map compileDecl

def canonicalSource : List SourceDecl :=
  [.equation .addZero,
   .equation .addSuccessor,
   .equation .lengthNil,
   .equation .lengthCons,
   .equation .pickAlternativeA,
   .equation .pickAlternativeB,
   .closure .mayEvalMembership]

def canonicalRules : List RuleSchema := compileSource canonicalSource

private def dataConstructor (label : String) (arity : Nat) : GrammarRule :=
  { label
    category := "PrimeMinimalData"
    params := (List.range arity).map fun index =>
      .simple ("argument" ++ toString index) (.base "PrimeMinimalData")
    syntaxPattern := [] }

private def cacheLanguage : LanguageDef :=
  { name := "PrimeMinimalCheckingCache"
    types := [TypeDecl.plain "PrimeMinimalData"]
    terms := [dataConstructor "wex.add" 2,
      dataConstructor "wex.Z" 0,
      dataConstructor "wex.S" 1,
      dataConstructor "wex.Nil" 0,
      dataConstructor "wex.Cons" 2,
      dataConstructor "wex.pick" 0,
      dataConstructor "wex.A" 0,
      dataConstructor "wex.B" 0,
      dataConstructor "wex.ResultSet" 1]
    equations := []
    rewrites := [] }

/-- Independently specified companion cache. -/
def cache : Presentation :=
  { language := cacheLanguage
    judgments := [
      { head := "wex1.Evals", arity := 2 },
      { head := "wex2.LenIs", arity := 2 },
      { head := "wex3.MayEval", arity := 2 },
      { head := "wex3.In", arity := 2 }]
    rules := canonicalRules }

def projectedCache : Except
    Mettapedia.Languages.MeTTa.Prime.MinimalCheckingPackage.ProjectionError
    Presentation :=
  Mettapedia.Languages.MeTTa.Prime.MinimalCheckingPackage.project
    canonicalRules

private theorem cache_language_valid : cache.language.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorOnly <;>
    simp [cache, cacheLanguage, dataConstructor, LanguageDef.typeNames,
      TypeDecl.plain, TermParam.typeExpr, TypeExpr.baseNames]

theorem cache_is_valid : cache.isValidV2 = true := by
  unfold Presentation.isValidV2 Presentation.isValidV1
  rw [cache_language_valid]
  simp [cache, canonicalRules, canonicalSource, compileSource,
    compileDecl, compileEquation, compileClosure, cacheLanguage,
    dataConstructor, app, pvar, schema, Presentation.ruleIds,
    RuleSchema.isValidV1, RuleSchema.metavariableNames,
    RuleSchema.occurrences, RuleSchema.patterns,
    patternMetavariableOccurrencesAt, patternsMetavariableOccurrencesAt,
    patternHasNoCollectionRest, patternsHaveNoCollectionRest,
    Presentation.judgmentSignatureValid, Presentation.judgmentHeads,
    RuleSchema.isValidIn, Presentation.judgmentSchemaValid,
    Presentation.lookupJudgment?, fixedConstructorListsValid,
    fixedConstructorsValid, languageHasConstructorArity,
    Pattern.isWellScoped, Pattern.isWellScopedAt,
    Pattern.isWellScopedListAt, Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList, List.eraseDups,
    List.eraseDupsBy, natZeroP, natSuccP, addP, evalP, nilP, consP,
    lengthP, pickP, pickAP, pickBP, resultSetP, mayEvalP, memberP]
  norm_num [List.eraseDupsBy.loop]
  decide

def validated : ValidatedPresentation := ⟨cache, cache_is_valid⟩

def package :
    Mettapedia.Languages.MeTTa.Prime.PackageAuthority.PrimeRulePackageV1 :=
  { format := "prime-rule-package-v1"
    dialect := "prime"
    semanticVersion := "0.5"
    rules := canonicalRules
    conversions := [] }

/-! ## Encoding and pattern-level source meaning -/

def encodeNat : NatValue → Pattern
  | .zero => natZeroP
  | .succ predecessor => natSuccP (encodeNat predecessor)

def encodeItem : ItemValue → Pattern
  | .a => itemAP
  | .b => itemBP

def encodePick : PickValue → Pattern
  | .a => pickAP
  | .b => pickBP

def encodeList : ListValue → Pattern
  | .nil => nilP
  | .cons head tail => consP (encodeItem head) (encodeList tail)

@[simp] theorem encodeNat_zero : encodeNat .zero = natZeroP := rfl
@[simp] theorem encodeNat_succ (value : NatValue) :
    encodeNat (.succ value) = natSuccP (encodeNat value) := rfl
@[simp] theorem encodeList_nil : encodeList .nil = nilP := rfl
@[simp] theorem encodeList_cons (head : ItemValue) (tail : ListValue) :
    encodeList (.cons head tail) =
      consP (encodeItem head) (encodeList tail) := rfl
@[simp] theorem encodePick_a : encodePick .a = pickAP := rfl
@[simp] theorem encodePick_b : encodePick .b = pickBP := rfl

def encodeJudgment : {sort : ResultSort} →
    FragmentExpr sort → FragmentValue sort → Pattern
  | _, .add left right, .nat result =>
      evalP (addP (encodeNat left) (encodeNat right)) (encodeNat result)
  | _, .length input, .nat result =>
      lengthP (encodeList input) (encodeNat result)
  | _, .pick, .pick result => mayEvalP pickP (encodePick result)

/-- Exact pattern-level closure of the compiled rules.  This relation can
classify arbitrary ground metavariable payloads; the typed adequacy theorem
below only decodes its encoded fragment goals. -/
inductive PatternMeaning : Pattern → Prop where
  | addZero (right : Pattern) :
      PatternMeaning (evalP (addP natZeroP right) right)
  | addSucc (left right result : Pattern)
      (prior : PatternMeaning (evalP (addP left right) result)) :
      PatternMeaning
        (evalP (addP (natSuccP left) right) (natSuccP result))
  | lengthNil : PatternMeaning (lengthP nilP natZeroP)
  | lengthCons (head tail result : Pattern)
      (prior : PatternMeaning (lengthP tail result)) :
      PatternMeaning
        (lengthP (consP head tail) (natSuccP result))
  | pickA : PatternMeaning (mayEvalP pickP pickAP)
  | pickB : PatternMeaning (mayEvalP pickP pickBP)
  | membership (value : Pattern)
      (prior : PatternMeaning (mayEvalP pickP value)) :
      PatternMeaning (memberP value (resultSetP pickP))

private theorem arguments_nil {arguments : List Pattern}
    (h : argumentsValidAt [] arguments = true) : arguments = [] := by
  cases arguments <;> simp_all [argumentsValidAt]

private theorem arguments_one {name : String} {depth : Nat}
    {arguments : List Pattern}
    (h : argumentsValidAt [(name, depth)] arguments = true) :
    ∃ first, arguments = [first] := by
  cases arguments with
  | nil => simp [argumentsValidAt] at h
  | cons first rest =>
      cases rest with
      | nil => exact ⟨first, rfl⟩
      | cons second rest => simp [argumentsValidAt] at h

private theorem arguments_three {firstName secondName thirdName : String}
    {firstDepth secondDepth thirdDepth : Nat} {arguments : List Pattern}
    (h : argumentsValidAt
      [(firstName, firstDepth), (secondName, secondDepth),
       (thirdName, thirdDepth)] arguments = true) :
    ∃ first second third, arguments = [first, second, third] := by
  cases arguments with
  | nil => simp [argumentsValidAt] at h
  | cons first rest =>
      cases rest with
      | nil => simp [argumentsValidAt] at h
      | cons second rest =>
          cases rest with
          | nil => simp [argumentsValidAt] at h
          | cons third rest =>
              cases rest with
              | nil => exact ⟨first, second, third, rfl⟩
              | cons fourth rest => simp [argumentsValidAt] at h

private theorem rule_mem_of_lookup {ruleInstance : RuleInstance}
    {rule : RuleSchema}
    (lookup : validated.1.lookupRule? ruleInstance.ruleId = some rule) :
    rule ∈ canonicalRules := by
  unfold Presentation.lookupRule? at lookup
  exact List.mem_of_find?_eq_some lookup

/-- Every local application of a rule generated from the canonical source
preserves the source's pattern-level meaning. -/
theorem rule_application_sound
    (ruleInstance : RuleInstance) (premises : List Pattern)
    (conclusion : Pattern)
    (application : RuleApplication validated ruleInstance premises conclusion)
    (premiseMeaning : ∀ premise ∈ premises, PatternMeaning premise) :
    PatternMeaning conclusion := by
  rcases ruleInstance with ⟨ruleId, arguments⟩
  have hlocal := instantiateRule?_eq_some_iff_application.mpr application
  rcases application with
    ⟨rule, lookup, argumentsValid, premisesInstantiate,
      conclusionInstantiates⟩
  have membership : rule ∈ canonicalRules := rule_mem_of_lookup lookup
  simp only [canonicalRules, canonicalSource, compileSource, List.map_cons,
    List.map_nil, compileDecl, List.mem_cons, List.not_mem_nil,
    or_false] at membership
  rcases membership with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rcases arguments_one argumentsValid with ⟨right, harguments⟩
    change arguments = [right] at harguments
    subst arguments
    have hav : argumentsValidAt [("n", 0)] [right] = true := by
      simpa [compileEquation, schema] using argumentsValid
    have calculated : instantiateRule? validated ⟨ruleId, [right]⟩ =
        some ([], evalP (addP natZeroP right) right) := by
      simp [instantiateRule?, lookup, hav,
        compileEquation, schema, instantiateSchemas?,
        instantiateSchemasAt?, instantiateSchema?, instantiateSchemaAt?,
        lookupArgumentAt?, evalP, addP, natZeroP, pvar, app]
    have pairEquality := Option.some.inj (hlocal.symm.trans calculated)
    rcases Prod.mk.inj pairEquality with ⟨hpremises, hconclusion⟩
    subst premises
    subst conclusion
    exact .addZero right
  · rcases arguments_three argumentsValid with
      ⟨left, right, result, harguments⟩
    change arguments = [left, right, result] at harguments
    subst arguments
    have hav : argumentsValidAt
        [("m", 0), ("n", 0), ("v", 0)] [left, right, result] = true := by
      simpa [compileEquation, schema] using argumentsValid
    have calculated : instantiateRule? validated
        ⟨ruleId, [left, right, result]⟩ =
        some ([evalP (addP left right) result],
          evalP (addP (natSuccP left) right) (natSuccP result)) := by
      simp [instantiateRule?, lookup, hav,
        compileEquation, schema, instantiateSchemas?,
        instantiateSchemasAt?, instantiateSchema?, instantiateSchemaAt?,
        lookupArgumentAt?, evalP, addP, natSuccP, pvar, app]
    have pairEquality := Option.some.inj (hlocal.symm.trans calculated)
    rcases Prod.mk.inj pairEquality with ⟨hpremises, hconclusion⟩
    subst premises
    subst conclusion
    exact .addSucc left right result
      (premiseMeaning _ (by simp))
  · have harguments := arguments_nil argumentsValid
    change arguments = [] at harguments
    subst arguments
    have hav : argumentsValidAt [] [] = true := by
      simpa [compileEquation, schema] using argumentsValid
    have calculated : instantiateRule? validated ⟨ruleId, []⟩ =
        some ([], lengthP nilP natZeroP) := by
      simp [instantiateRule?, lookup, hav,
        compileEquation, schema, instantiateSchemas?,
        instantiateSchemasAt?, instantiateSchema?, instantiateSchemaAt?,
        lengthP, nilP, natZeroP, app]
    have pairEquality := Option.some.inj (hlocal.symm.trans calculated)
    rcases Prod.mk.inj pairEquality with ⟨hpremises, hconclusion⟩
    subst premises
    subst conclusion
    exact .lengthNil
  · rcases arguments_three argumentsValid with
      ⟨head, tail, result, harguments⟩
    change arguments = [head, tail, result] at harguments
    subst arguments
    have hav : argumentsValidAt
        [("h", 0), ("t", 0), ("v", 0)] [head, tail, result] = true := by
      simpa [compileEquation, schema] using argumentsValid
    have calculated : instantiateRule? validated
        ⟨ruleId, [head, tail, result]⟩ =
        some ([lengthP tail result],
          lengthP (consP head tail) (natSuccP result)) := by
      simp [instantiateRule?, lookup, hav,
        compileEquation, schema, instantiateSchemas?,
        instantiateSchemasAt?, instantiateSchema?, instantiateSchemaAt?,
        lookupArgumentAt?, lengthP, consP, natSuccP, pvar, app]
    have pairEquality := Option.some.inj (hlocal.symm.trans calculated)
    rcases Prod.mk.inj pairEquality with ⟨hpremises, hconclusion⟩
    subst premises
    subst conclusion
    exact .lengthCons head tail result
      (premiseMeaning _ (by simp))
  · have harguments := arguments_nil argumentsValid
    change arguments = [] at harguments
    subst arguments
    have hav : argumentsValidAt [] [] = true := by
      simpa [compileEquation, schema] using argumentsValid
    have calculated : instantiateRule? validated ⟨ruleId, []⟩ =
        some ([], mayEvalP pickP pickAP) := by
      simp [instantiateRule?, lookup, hav,
        compileEquation, schema, instantiateSchemas?,
        instantiateSchemasAt?, instantiateSchema?, instantiateSchemaAt?,
        mayEvalP, pickP, pickAP, app]
    have pairEquality := Option.some.inj (hlocal.symm.trans calculated)
    rcases Prod.mk.inj pairEquality with ⟨hpremises, hconclusion⟩
    subst premises
    subst conclusion
    exact .pickA
  · have harguments := arguments_nil argumentsValid
    change arguments = [] at harguments
    subst arguments
    have hav : argumentsValidAt [] [] = true := by
      simpa [compileEquation, schema] using argumentsValid
    have calculated : instantiateRule? validated ⟨ruleId, []⟩ =
        some ([], mayEvalP pickP pickBP) := by
      simp [instantiateRule?, lookup, hav,
        compileEquation, schema, instantiateSchemas?,
        instantiateSchemasAt?, instantiateSchema?, instantiateSchemaAt?,
        mayEvalP, pickP, pickBP, app]
    have pairEquality := Option.some.inj (hlocal.symm.trans calculated)
    rcases Prod.mk.inj pairEquality with ⟨hpremises, hconclusion⟩
    subst premises
    subst conclusion
    exact .pickB
  · rcases arguments_one argumentsValid with ⟨value, harguments⟩
    change arguments = [value] at harguments
    subst arguments
    have hav : argumentsValidAt [("x", 0)] [value] = true := by
      simpa [compileClosure, schema] using argumentsValid
    have calculated : instantiateRule? validated ⟨ruleId, [value]⟩ =
        some ([mayEvalP pickP value],
          memberP value (resultSetP pickP)) := by
      simp [instantiateRule?, lookup, hav,
        compileClosure, schema, instantiateSchemas?,
        instantiateSchemasAt?, instantiateSchema?, instantiateSchemaAt?,
        lookupArgumentAt?, mayEvalP, pickP, memberP, resultSetP, pvar, app]
    have pairEquality := Option.some.inj (hlocal.symm.trans calculated)
    rcases Prod.mk.inj pairEquality with ⟨hpremises, hconclusion⟩
    subst premises
    subst conclusion
    exact .membership value (premiseMeaning _ (by simp))

/-- The generic Boolean checker cannot escape the closure generated by the
fragment source rules. -/
theorem checkRaw_pattern_sound {goal : Pattern} {proof : RawProof}
    (accepted : checkRaw validated goal proof = true) :
    PatternMeaning goal := by
  rcases checkRaw_soundness accepted with ⟨derivation⟩
  exact derivation.sound_of_ruleApplications PatternMeaning
    rule_application_sound

private def ruleInstance (id : String) (arguments : List Pattern := []) :
    RuleInstance :=
  { ruleId := ⟨id⟩, arguments }

@[simp] theorem encodeNat_isGroundAt (depth : Nat) (value : NatValue) :
    (encodeNat value).isGroundAt depth = true := by
  induction value with
  | zero =>
      simp [encodeNat, natZeroP, app, Pattern.isGroundAt,
        Pattern.isGroundListAt]
  | succ predecessor ih =>
      simp [encodeNat, natSuccP, app, Pattern.isGroundAt,
        Pattern.isGroundListAt, ih]

@[simp] theorem encodeNat_isGround (value : NatValue) :
    (encodeNat value).isGround = true := by
  exact encodeNat_isGroundAt 0 value

@[simp] theorem encodeNat_isCanonical (value : NatValue) :
    (encodeNat value).hasCanonicalBinderMetadata = true := by
  induction value with
  | zero =>
      simp [encodeNat, natZeroP, app,
        Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList]
  | succ predecessor ih =>
      simp [encodeNat, natSuccP, app,
        Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList, ih]

@[simp] theorem encodeItem_isGroundAt (depth : Nat) (value : ItemValue) :
    (encodeItem value).isGroundAt depth = true := by
  cases value <;>
    simp [encodeItem, itemAP, itemBP, app, Pattern.isGroundAt,
      Pattern.isGroundListAt]

@[simp] theorem encodeItem_isGround (value : ItemValue) :
    (encodeItem value).isGround = true := by
  exact encodeItem_isGroundAt 0 value

@[simp] theorem encodeItem_isCanonical (value : ItemValue) :
    (encodeItem value).hasCanonicalBinderMetadata = true := by
  cases value <;>
    simp [encodeItem, itemAP, itemBP, app,
      Pattern.hasCanonicalBinderMetadata,
      Pattern.hasCanonicalBinderMetadataList]

@[simp] theorem encodePick_isGroundAt (depth : Nat) (value : PickValue) :
    (encodePick value).isGroundAt depth = true := by
  cases value <;>
    simp [encodePick, pickAP, pickBP, app, Pattern.isGroundAt,
      Pattern.isGroundListAt]

@[simp] theorem encodePick_isCanonical (value : PickValue) :
    (encodePick value).hasCanonicalBinderMetadata = true := by
  cases value <;>
    simp [encodePick, pickAP, pickBP, app,
      Pattern.hasCanonicalBinderMetadata,
      Pattern.hasCanonicalBinderMetadataList]

@[simp] theorem encodeList_isGroundAt (depth : Nat) (value : ListValue) :
    (encodeList value).isGroundAt depth = true := by
  induction value with
  | nil =>
      simp [encodeList, nilP, app, Pattern.isGroundAt,
        Pattern.isGroundListAt]
  | cons head tail ih =>
      simp [encodeList, consP, app, Pattern.isGroundAt,
        Pattern.isGroundListAt, ih]

@[simp] theorem encodeList_isGround (value : ListValue) :
    (encodeList value).isGround = true := by
  exact encodeList_isGroundAt 0 value

@[simp] theorem encodeList_isCanonical (value : ListValue) :
    (encodeList value).hasCanonicalBinderMetadata = true := by
  induction value with
  | nil => simp [encodeList, nilP, app,
      Pattern.hasCanonicalBinderMetadata,
      Pattern.hasCanonicalBinderMetadataList]
  | cons head tail ih =>
      simp [encodeList, consP, app,
        Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList, ih]

/-- Candidate proof computed from the expression and claimed result alone.
Wrong results may produce a rejected tree; no Prop-valued witness is erased
into certificate data. -/
def proofCandidate : {sort : ResultSort} →
    FragmentExpr sort → FragmentValue sort → RawProof
  | _, .add .zero right, .nat _ =>
      .node (ruleInstance "wex1.add-z" [encodeNat right]) []
  | _, .add (.succ _left) right, .nat .zero =>
      .node (ruleInstance "wex1.add-z" [encodeNat right]) []
  | _, .add (.succ left) right, .nat (.succ result) =>
      .node (ruleInstance "wex1.add-s"
        [encodeNat left, encodeNat right, encodeNat result])
        [proofCandidate (.add left right) (.nat result)]
  | _, .length .nil, .nat _ =>
      .node (ruleInstance "wex2.len-nil") []
  | _, .length (.cons _head _tail), .nat .zero =>
      .node (ruleInstance "wex2.len-nil") []
  | _, .length (.cons head tail), .nat (.succ result) =>
      .node (ruleInstance "wex2.len-cons"
        [encodeItem head, encodeList tail, encodeNat result])
        [proofCandidate (.length tail) (.nat result)]
  | _, .pick, .pick .a => .node (ruleInstance "wex3.pick-a") []
  | _, .pick, .pick .b => .node (ruleInstance "wex3.pick-b") []

private theorem instantiate_add_zero (right : NatValue) :
    instantiateRule? validated
      (ruleInstance "wex1.add-z" [encodeNat right]) =
      some ([], encodeJudgment (.add .zero right) (.nat right)) := by
  simp [instantiateRule?, Presentation.lookupRule?, validated, cache,
    canonicalRules, canonicalSource, compileSource, compileDecl,
    compileEquation, compileClosure, schema, ruleInstance,
    argumentsValidAt, argumentValidAt, instantiateSchemas?,
    instantiateSchemasAt?, instantiateSchema?, instantiateSchemaAt?,
    lookupArgumentAt?, encodeJudgment, natZeroP, addP, evalP, pvar, app]

private theorem instantiate_add_successor
    (left right result : NatValue) :
    instantiateRule? validated
      (ruleInstance "wex1.add-s"
        [encodeNat left, encodeNat right, encodeNat result]) =
      some ([encodeJudgment (.add left right) (.nat result)],
        encodeJudgment (.add (.succ left) right) (.nat (.succ result))) := by
  simp [instantiateRule?, Presentation.lookupRule?, validated, cache,
    canonicalRules, canonicalSource, compileSource, compileDecl,
    compileEquation, compileClosure, schema, ruleInstance,
    argumentsValidAt, argumentValidAt, instantiateSchemas?,
    instantiateSchemasAt?, instantiateSchema?, instantiateSchemaAt?,
    lookupArgumentAt?, encodeJudgment, natSuccP, addP, evalP, pvar, app]

private theorem instantiate_length_nil :
    instantiateRule? validated (ruleInstance "wex2.len-nil") =
      some ([], encodeJudgment (.length .nil) (.nat .zero)) := by
  simp [instantiateRule?, Presentation.lookupRule?, validated, cache,
    canonicalRules, canonicalSource, compileSource, compileDecl,
    compileEquation, compileClosure, schema, ruleInstance,
    argumentsValidAt, instantiateSchemas?, instantiateSchemasAt?,
    instantiateSchema?, instantiateSchemaAt?, encodeJudgment, nilP,
    natZeroP, lengthP, pvar, app]

private theorem instantiate_length_cons
    (head : ItemValue) (tail : ListValue) (result : NatValue) :
    instantiateRule? validated
      (ruleInstance "wex2.len-cons"
        [encodeItem head, encodeList tail, encodeNat result]) =
      some ([encodeJudgment (.length tail) (.nat result)],
        encodeJudgment (.length (.cons head tail)) (.nat (.succ result))) := by
  simp [instantiateRule?, Presentation.lookupRule?, validated, cache,
    canonicalRules, canonicalSource, compileSource, compileDecl,
    compileEquation, compileClosure, schema, ruleInstance,
    argumentsValidAt, argumentValidAt, instantiateSchemas?,
    instantiateSchemasAt?, instantiateSchema?, instantiateSchemaAt?,
    lookupArgumentAt?, encodeJudgment, consP, natSuccP, lengthP,
    pvar, app]

private theorem instantiate_pick_a :
    instantiateRule? validated (ruleInstance "wex3.pick-a") =
      some ([], encodeJudgment .pick (.pick .a)) := by
  simp [instantiateRule?, Presentation.lookupRule?, validated, cache,
    canonicalRules, canonicalSource, compileSource, compileDecl,
    compileEquation, compileClosure, schema, ruleInstance,
    argumentsValidAt, instantiateSchemas?, instantiateSchemasAt?,
    instantiateSchema?, instantiateSchemaAt?, encodeJudgment, encodePick,
    mayEvalP, pickP, pickAP, pvar, app]

private theorem instantiate_pick_b :
    instantiateRule? validated (ruleInstance "wex3.pick-b") =
      some ([], encodeJudgment .pick (.pick .b)) := by
  simp [instantiateRule?, Presentation.lookupRule?, validated, cache,
    canonicalRules, canonicalSource, compileSource, compileDecl,
    compileEquation, compileClosure, schema, ruleInstance,
    argumentsValidAt, instantiateSchemas?, instantiateSchemasAt?,
    instantiateSchema?, instantiateSchemaAt?, encodeJudgment, encodePick,
    mayEvalP, pickP, pickBP, pvar, app]

/-- Every result of the declarative/native fragment evaluator has a raw proof
accepted by the unchanged generic checker. -/
theorem proofOfEvaluation_checked {sort : ResultSort}
    {expression : FragmentExpr sort} {value : FragmentValue sort}
    (evaluation : Evaluates expression value) :
    checkRaw validated (encodeJudgment expression value)
      (proofCandidate expression value) = true := by
  induction evaluation with
  | addZero right =>
      simp [proofCandidate, checkRaw, instantiate_add_zero,
        checkRawChildren]
  | addSucc left right result prior ih =>
      simp [proofCandidate, checkRaw, instantiate_add_successor,
        checkRawChildren, ih]
  | lengthNil =>
      simp [proofCandidate, checkRaw, instantiate_length_nil,
        checkRawChildren]
  | lengthCons head tail result prior ih =>
      simp [proofCandidate, checkRaw, instantiate_length_cons,
        checkRawChildren, ih]
  | pickA =>
      simp [proofCandidate, checkRaw, instantiate_pick_a,
        checkRawChildren]
  | pickB =>
      simp [proofCandidate, checkRaw, instantiate_pick_b,
        checkRawChildren]

/-! ## Decoding and the reverse adequacy direction -/

def decodeNat : Pattern → Option NatValue
  | .apply "wex.Z" [] => some .zero
  | .apply "wex.S" [predecessor] =>
      NatValue.succ <$> decodeNat predecessor
  | _ => none

def decodeItem : Pattern → Option ItemValue
  | .apply "wex.a" [] => some .a
  | .apply "wex.b" [] => some .b
  | _ => none

def decodePick : Pattern → Option PickValue
  | .apply "wex.A" [] => some .a
  | .apply "wex.B" [] => some .b
  | _ => none

def decodeList : Pattern → Option ListValue
  | .apply "wex.Nil" [] => some .nil
  | .apply "wex.Cons" [head, tail] => do
      let headValue ← decodeItem head
      let tailValue ← decodeList tail
      some (.cons headValue tailValue)
  | _ => none

inductive DecodedEvaluation where
  | nat (expression : FragmentExpr .nat) (value : FragmentValue .nat)
  | pick (expression : FragmentExpr .pick) (value : FragmentValue .pick)

@[simp] def DecodedEvaluation.Holds : DecodedEvaluation → Prop
  | .nat expression value => Evaluates expression value
  | .pick expression value => Evaluates expression value

def decodeEvaluationJudgment : Pattern → Option DecodedEvaluation
  | .apply "wex1.Evals"
      [.apply "wex.add" [left, right], result] => do
      let leftValue ← decodeNat left
      let rightValue ← decodeNat right
      let resultValue ← decodeNat result
      some (.nat (.add leftValue rightValue) (.nat resultValue))
  | .apply "wex2.LenIs" [input, result] => do
      let inputValue ← decodeList input
      let resultValue ← decodeNat result
      some (.nat (.length inputValue) (.nat resultValue))
  | .apply "wex3.MayEval" [.apply "wex.pick" [], result] => do
      let resultValue ← decodePick result
      some (.pick .pick (.pick resultValue))
  | _ => none

def DecodedMeaning (judgment : Pattern) : Prop :=
  match decodeEvaluationJudgment judgment with
  | none => True
  | some decoded => decoded.Holds

@[simp] theorem decodeNat_encodeNat (value : NatValue) :
    decodeNat (encodeNat value) = some value := by
  induction value with
  | zero => simp [decodeNat, encodeNat, natZeroP, app]
  | succ predecessor ih =>
      simp [decodeNat, encodeNat, natSuccP, app, ih]

@[simp] theorem decodeItem_encodeItem (value : ItemValue) :
    decodeItem (encodeItem value) = some value := by
  cases value <;> simp [decodeItem, encodeItem, itemAP, itemBP, app]

@[simp] theorem decodePick_encodePick (value : PickValue) :
    decodePick (encodePick value) = some value := by
  cases value <;> simp [decodePick, encodePick, pickAP, pickBP, app]

@[simp] theorem decodeList_encodeList (value : ListValue) :
    decodeList (encodeList value) = some value := by
  induction value with
  | nil => simp [decodeList, encodeList, nilP, app]
  | cons head tail ih =>
      simp [decodeList, encodeList, consP, app, ih]

/-- Pattern-level rule closure is sound whenever a judgment decodes to the
typed source fragment.  Non-fragment patterns deliberately decode to `none`
instead of being misclassified as errors. -/
theorem patternMeaning_decoded {judgment : Pattern}
    (meaning : PatternMeaning judgment) : DecodedMeaning judgment := by
  induction meaning with
  | addZero right =>
      cases hright : decodeNat right with
      | none =>
          simp [DecodedMeaning, decodeEvaluationJudgment, evalP, addP,
            natZeroP, decodeNat, hright, app]
      | some rightValue =>
          simpa [DecodedMeaning, decodeEvaluationJudgment, evalP, addP,
            natZeroP, decodeNat, hright, app] using
            (Evaluates.addZero rightValue)
  | addSucc left right result prior ih =>
      cases hleft : decodeNat left with
      | none =>
          simp [DecodedMeaning, decodeEvaluationJudgment, evalP, addP,
            natSuccP, decodeNat, hleft, app]
      | some leftValue =>
          cases hright : decodeNat right with
          | none =>
              simp [DecodedMeaning, decodeEvaluationJudgment, evalP, addP,
                natSuccP, decodeNat, hleft, hright, app]
          | some rightValue =>
              cases hresult : decodeNat result with
              | none =>
                  simp [DecodedMeaning, decodeEvaluationJudgment, evalP,
                    addP, natSuccP, decodeNat, hleft, hright, hresult, app]
              | some resultValue =>
                  have priorTyped : Evaluates
                      (.add leftValue rightValue) (.nat resultValue) := by
                    simpa [DecodedMeaning, decodeEvaluationJudgment, evalP,
                      addP, hleft, hright, hresult, app] using ih
                  simpa [DecodedMeaning, decodeEvaluationJudgment, evalP,
                    addP, natSuccP, decodeNat, hleft, hright, hresult, app]
                    using Evaluates.addSucc leftValue rightValue resultValue
                      priorTyped
  | lengthNil =>
      simpa [DecodedMeaning, decodeEvaluationJudgment, lengthP, nilP,
        natZeroP, decodeList, decodeNat, app] using Evaluates.lengthNil
  | lengthCons head tail result prior ih =>
      cases hhead : decodeItem head with
      | none =>
          simp [DecodedMeaning, decodeEvaluationJudgment, lengthP, consP,
            natSuccP, decodeList, decodeNat, hhead, app]
      | some headValue =>
          cases htail : decodeList tail with
          | none =>
              simp [DecodedMeaning, decodeEvaluationJudgment, lengthP,
                consP, natSuccP, decodeList, decodeNat, hhead, htail, app]
          | some tailValue =>
              cases hresult : decodeNat result with
              | none =>
                  simp [DecodedMeaning, decodeEvaluationJudgment, lengthP,
                    consP, natSuccP, decodeList, decodeNat, hhead, htail,
                    hresult, app]
              | some resultValue =>
                  have priorTyped : Evaluates (.length tailValue)
                      (.nat resultValue) := by
                    simpa [DecodedMeaning, decodeEvaluationJudgment, lengthP,
                      htail, hresult, app] using ih
                  simpa [DecodedMeaning, decodeEvaluationJudgment, lengthP,
                    consP, natSuccP, decodeList, decodeNat, hhead, htail,
                    hresult, app] using
                    Evaluates.lengthCons headValue tailValue resultValue
                      priorTyped
  | pickA =>
      simpa [DecodedMeaning, decodeEvaluationJudgment, mayEvalP, pickP,
        pickAP, decodePick, app] using Evaluates.pickA
  | pickB =>
      simpa [DecodedMeaning, decodeEvaluationJudgment, mayEvalP, pickP,
        pickBP, decodePick, app] using Evaluates.pickB
  | membership value prior ih =>
      simp [DecodedMeaning, decodeEvaluationJudgment, memberP, resultSetP,
        app]

@[simp] theorem decodedMeaning_encodeJudgment {sort : ResultSort}
    (expression : FragmentExpr sort) (value : FragmentValue sort) :
    DecodedMeaning (encodeJudgment expression value) ↔
      Evaluates expression value := by
  cases expression with
  | add left right =>
      cases value with
      | nat result =>
          simp [DecodedMeaning, decodeEvaluationJudgment, encodeJudgment,
            evalP, addP, app]
  | length input =>
      cases value with
      | nat result =>
          simp [DecodedMeaning, decodeEvaluationJudgment, encodeJudgment,
            lengthP, app]
  | pick =>
      cases value with
      | pick result =>
          simp [DecodedMeaning, decodeEvaluationJudgment, encodeJudgment,
            mayEvalP, pickP, app]

/-- Reverse adequacy: an arbitrary raw tree accepted for an encoded fragment
evaluation goal denotes a result of the independent evaluator. -/
theorem checked_implies_evaluates {sort : ResultSort}
    {expression : FragmentExpr sort} {value : FragmentValue sort}
    {proof : RawProof}
    (accepted : checkRaw validated (encodeJudgment expression value) proof =
      true) : Evaluates expression value := by
  have patternMeaning := checkRaw_pattern_sound accepted
  have decoded := patternMeaning_decoded patternMeaning
  exact (decodedMeaning_encodeJudgment expression value).mp decoded

/-- The two adequacy directions, stated at the certificate boundary. -/
theorem checked_iff_evaluates {sort : ResultSort}
    (expression : FragmentExpr sort) (value : FragmentValue sort) :
    (∃ proof, checkRaw validated (encodeJudgment expression value) proof =
      true) ↔ Evaluates expression value := by
  constructor
  · rintro ⟨proof, accepted⟩
    exact checked_implies_evaluates accepted
  · intro evaluation
    exact ⟨proofCandidate expression value,
      proofOfEvaluation_checked evaluation⟩

theorem checked_iff_mem_evalBag {sort : ResultSort}
    (expression : FragmentExpr sort) (value : FragmentValue sort) :
    (∃ proof, checkRaw validated (encodeJudgment expression value) proof =
      true) ↔ value ∈ evalBag expression := by
  rw [checked_iff_evaluates, evaluates_iff_mem_evalBag]

/-! ## Executable positive and negative controls -/

def one : NatValue := .succ .zero
def two : NatValue := .succ one

theorem add_one_one_has_certificate :
    ∃ proof, checkRaw validated
      (encodeJudgment (.add one one) (.nat two)) proof = true := by
  apply (checked_iff_mem_evalBag (.add one one) (.nat two)).2
  simp [evalBag, addNat, one, two]

theorem add_one_one_wrong_result_has_no_certificate :
    ¬ ∃ proof, checkRaw validated
      (encodeJudgment (.add one one) (.nat one)) proof = true := by
  rw [checked_iff_mem_evalBag]
  simp [evalBag, addNat, one]

def packageFromSource (source : List SourceDecl) :
    Mettapedia.Languages.MeTTa.Prime.PackageAuthority.PrimeRulePackageV1 :=
  { package with rules := compileSource source }

def addDeletedSource : List SourceDecl :=
  [.equation .addZero]

def pickAddedSource : List SourceDecl :=
  [.equation .pickAlternativeA,
   .equation .pickAlternativeB,
   .equation .pickAlternativeC,
   .closure .mayEvalMembership]

def addWrongSubstitutionSource : List SourceDecl :=
  [.equation .addZero,
   .equation .addSuccessorWrongSubstitution]

def pickDuplicatedSource : List SourceDecl :=
  [.equation .pickAlternativeA,
   .equation .pickAlternativeA,
   .equation .pickAlternativeB,
   .closure .mayEvalMembership]

private def projectionMatchesCache : Bool :=
  match projectedCache with
  | .error _ => false
  | .ok projected =>
      renderPresentation projected == renderPresentation cache

private def runChecks : IO Unit := do
  unless projectionMatchesCache do
    throw <| IO.userError
      "derived presentation differs from the independent companion cache"
  unless Mettapedia.Languages.MeTTa.Prime.PackageAuthority.validatePackage
      package cache do
    throw <| IO.userError "canonical compiled package was rejected"
  let canonicalBytes := package.canonicalBytes
  if canonicalBytes == (packageFromSource addDeletedSource).canonicalBytes then
    throw <| IO.userError "deleted equation preserved canonical package bytes"
  if canonicalBytes == (packageFromSource pickAddedSource).canonicalBytes then
    throw <| IO.userError "added branch preserved canonical package bytes"
  if canonicalBytes ==
      (packageFromSource addWrongSubstitutionSource).canonicalBytes then
    throw <| IO.userError "wrong substitution preserved canonical package bytes"
  if canonicalBytes ==
      (packageFromSource pickDuplicatedSource).canonicalBytes then
    throw <| IO.userError "duplicate branch preserved canonical package bytes"
  let correct := checkRaw validated
    (encodeJudgment (.add one one) (.nat two))
    (proofCandidate (.add one one) (.nat two))
  unless correct do
    throw <| IO.userError "correct concrete result was rejected"
  let wrong := checkRaw validated
    (encodeJudgment (.add one one) (.nat one))
    (proofCandidate (.add one one) (.nat one))
  if wrong then
    throw <| IO.userError "wrong concrete result was accepted"
  IO.println "PRIME_FRAGMENT_PACKAGE_CANONICAL_BEGIN"
  IO.println canonicalBytes
  IO.println "PRIME_FRAGMENT_PACKAGE_CANONICAL_END"
  IO.println "(PrimeFragmentAdequacyLeanSummaryV1 8 8 0)"

end Mettapedia.Languages.MeTTa.Prime.FragmentAdequacyV1

#print axioms Mettapedia.Languages.MeTTa.Prime.FragmentAdequacyV1.checked_iff_mem_evalBag
#print axioms Mettapedia.Languages.MeTTa.Prime.FragmentAdequacyV1.add_one_one_wrong_result_has_no_certificate

#eval Mettapedia.Languages.MeTTa.Prime.FragmentAdequacyV1.runChecks
