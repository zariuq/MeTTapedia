import Mettapedia.GSLT.LanguageDef.CheckedSource
import Mettapedia.GSLT.LanguageDef.HOLNativeSourcePins
import Mettapedia.GSLT.LanguageDef.InferenceExtraction

/-!
# Native GSLT slices for HOL Light and HOL4

These small source-grounded slices turn theorem premises and selected kernel
side conditions into ordered proof premises of one generic inference
presentation.  Successful checking therefore requires a complete native
derivation tree; no relation premise is supplied by an external callback.

The HOL Light slice covers `REFL`, `ASSUME`, and `EQ_MP`.  The HOL4 slice
covers `ASSUME` and `DISCH`.  They remain distinct presentations because their
primitive kernel APIs and context operations are distinct.
-/

namespace Mettapedia.GSLT.LanguageDef.HOLNativeGSLTSlice

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.CheckedSource
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.InferenceExtraction
open Mettapedia.GSLT.LanguageDef.HOLSourceKernel
open Mettapedia.GSLT.LanguageDef.HOLNativeSourcePins

private def ty (name : String) : TypeExpr := .base name

private def termCtor (label category : String)
    (parameters : List (String × String)) : GrammarRule :=
  { label
    category
    params := parameters.map fun (name, typeName) => .simple name (ty typeName)
    syntaxPattern := [] }

private def app (head : String) (arguments : List Pattern := []) : Pattern :=
  .apply head arguments

private def pvar (name : String) : Pattern := .fvar name

private def rw (name : String) (left right : Pattern) : RewriteRule :=
  { name, typeContext := [], premises := [], left, right }

private def check (head : String) (proof : Pattern) : Pattern := app head [proof]
private def ok (head : String) (evidence : Pattern) : Pattern := app head [evidence]

private def tyNil : Pattern := app "TyNil"
private def tyCons (head tail : Pattern) : Pattern := app "TyCons" [head, tail]
private def tyList (values : List Pattern) : Pattern := values.foldr tyCons tyNil

private def equalityNameHead : String := "$hol.name.61"
private def implicationNameHead : String := "$hol.name.61.61.62"
private def boolNameHead : String := "$hol.name.98.111.111.108"
private def functionNameHead : String := "$hol.name.102.117.110"
private def pNameHead : String := "$hol.name.112"
private def qNameHead : String := "$hol.name.113"

private def tyApp (name : Pattern) (arguments : List Pattern := []) : Pattern :=
  app "TyApp" [name, tyList arguments]

private def boolTy : Pattern := app "$hol.type.bool"
private def funTy (domain codomain : Pattern) : Pattern :=
  tyApp (app functionNameHead) [domain, codomain]

private def tmVar (name type : Pattern) : Pattern := app "TmVar" [name, type]
private def tmConst (name type : Pattern) : Pattern :=
  app "TmConst" [name, type]
private def tmApp (function argument : Pattern) : Pattern :=
  app "TmApp" [function, argument]

private def eqTerm (type left right : Pattern) : Pattern :=
  let equalityType := funTy type (funTy type boolTy)
  tmApp (tmApp (tmConst (app equalityNameHead) equalityType) left) right

private def impTerm (antecedent consequent : Pattern) : Pattern :=
  let implicationType := funTy boolTy (funTy boolTy boolTy)
  tmApp (tmApp (tmConst (app implicationNameHead) implicationType) antecedent)
    consequent

private def hypsNil : Pattern := app "HypsNil"
private def hypsCons (head tail : Pattern) : Pattern := app "HypsCons" [head, tail]

private def theoremEvidence (hypotheses conclusion : Pattern) : Pattern :=
  app "Thm" [hypotheses, conclusion]
private def validTypeEvidence (type : Pattern) : Pattern := app "ValidType" [type]
private def hasTypeEvidence (term type : Pattern) : Pattern :=
  app "HasType" [term, type]
private def isBoolEvidence (term : Pattern) : Pattern := app "IsBool" [term]
private def validHypsEvidence (hypotheses : Pattern) : Pattern :=
  app "ValidHyps" [hypotheses]
private def alphaEqEvidence (left right : Pattern) : Pattern :=
  app "AlphaEq" [left, right]
private def hypUnionEvidence (left right output : Pattern) : Pattern :=
  app "HypUnion" [left, right, output]
private def hypRemoveEvidence (term input output : Pattern) : Pattern :=
  app "HypRemove" [term, input, output]

private def commonTypes : List TypeDecl :=
  [ "HolName", "HolType", "HolTypeList", "HolTerm", "HolHyps",
    "HolEvidence", "HolProof", "HolJudgment" ].map TypeDecl.plain

private def commonDataTerms : List GrammarRule :=
  [ termCtor equalityNameHead "HolName" []
  , termCtor implicationNameHead "HolName" []
  , termCtor boolNameHead "HolName" []
  , termCtor functionNameHead "HolName" []
  , termCtor pNameHead "HolName" []
  , termCtor qNameHead "HolName" []
  , termCtor "$hol.type.bool" "HolType" []
  , termCtor "TyApp" "HolType"
      [("name", "HolName"), ("arguments", "HolTypeList")]
  , termCtor "TyNil" "HolTypeList" []
  , termCtor "TyCons" "HolTypeList"
      [("head", "HolType"), ("tail", "HolTypeList")]
  , termCtor "TmVar" "HolTerm" [("name", "HolName"), ("type", "HolType")]
  , termCtor "TmConst" "HolTerm"
      [("name", "HolName"), ("type", "HolType")]
  , termCtor "TmApp" "HolTerm"
      [("function", "HolTerm"), ("argument", "HolTerm")]
  , termCtor "HypsNil" "HolHyps" []
  , termCtor "HypsCons" "HolHyps"
      [("head", "HolTerm"), ("tail", "HolHyps")]
  , termCtor "Thm" "HolEvidence"
      [("hypotheses", "HolHyps"), ("conclusion", "HolTerm")]
  , termCtor "ValidType" "HolEvidence" [("type", "HolType")]
  , termCtor "HasType" "HolEvidence"
      [("term", "HolTerm"), ("type", "HolType")]
  , termCtor "IsBool" "HolEvidence" [("term", "HolTerm")]
  , termCtor "ValidHyps" "HolEvidence" [("hypotheses", "HolHyps")]
  , termCtor "AlphaEq" "HolEvidence"
      [("left", "HolTerm"), ("right", "HolTerm")]
  , termCtor "HypUnion" "HolEvidence"
      [("left", "HolHyps"), ("right", "HolHyps"), ("output", "HolHyps")]
  , termCtor "HypRemove" "HolEvidence"
      [("term", "HolTerm"), ("input", "HolHyps"), ("output", "HolHyps")]
  , termCtor "HLNativeCheck" "HolJudgment" [("proof", "HolProof")]
  , termCtor "HLNativeOk" "HolJudgment" [("evidence", "HolEvidence")]
  , termCtor "H4NativeCheck" "HolJudgment" [("proof", "HolProof")]
  , termCtor "H4NativeOk" "HolJudgment" [("evidence", "HolEvidence")] ]

private def sideProofTerms : List GrammarRule :=
  [ termCtor "SC_BOOL_TYPE" "HolProof" []
  , termCtor "SC_VAR_TYPE" "HolProof"
      [("name", "HolName"), ("type", "HolType"),
       ("typeEvidence", "HolEvidence")]
  , termCtor "SC_IS_BOOL" "HolProof"
      [("term", "HolTerm"), ("typeEvidence", "HolEvidence")]
  , termCtor "SC_ALPHA_REFL" "HolProof"
      [("term", "HolTerm"), ("type", "HolType"),
       ("typeEvidence", "HolEvidence")]
  , termCtor "SC_HYPS_NIL" "HolProof" []
  , termCtor "SC_HYPS_SINGLETON" "HolProof"
      [("term", "HolTerm"), ("boolEvidence", "HolEvidence")]
  , termCtor "SC_UNION_NIL_LEFT" "HolProof"
      [("hypotheses", "HolHyps"), ("validEvidence", "HolEvidence")]
  , termCtor "SC_REMOVE_SINGLETON" "HolProof"
      [("term", "HolTerm"), ("boolEvidence", "HolEvidence")] ]

private def holLightProofTerms : List GrammarRule :=
  [ termCtor "HL_REFL" "HolProof"
      [("term", "HolTerm"), ("type", "HolType"),
       ("typeEvidence", "HolEvidence")]
  , termCtor "HL_ASSUME" "HolProof"
      [("term", "HolTerm"), ("boolEvidence", "HolEvidence")]
  , termCtor "HL_EQ_MP" "HolProof"
      [("equality", "HolEvidence"), ("premise", "HolEvidence"),
       ("alphaEvidence", "HolEvidence"), ("unionEvidence", "HolEvidence")] ]

private def hol4ProofTerms : List GrammarRule :=
  [ termCtor "H4_ASSUME" "HolProof"
      [("term", "HolTerm"), ("boolEvidence", "HolEvidence")]
  , termCtor "H4_DISCH" "HolProof"
      [("term", "HolTerm"), ("input", "HolEvidence"),
       ("boolEvidence", "HolEvidence"), ("removeEvidence", "HolEvidence")] ]

private def N := pvar "N"
private def T := pvar "T"
private def P := pvar "P"
private def Q := pvar "Q"
private def Q2 := pvar "Q2"
private def H := pvar "H"
private def H1 := pvar "H1"
private def H2 := pvar "H2"
private def HO := pvar "HO"

private def sideRewrites (checkHead okHead : String) : List RewriteRule :=
  [ rw "SC_BOOL_TYPE"
      (check checkHead (app "SC_BOOL_TYPE"))
      (ok okHead (validTypeEvidence boolTy))
  , rw "SC_VAR_TYPE"
      (check checkHead (app "SC_VAR_TYPE"
        [N, T, validTypeEvidence T]))
      (ok okHead (hasTypeEvidence (tmVar N T) T))
  , rw "SC_IS_BOOL"
      (check checkHead (app "SC_IS_BOOL"
        [P, hasTypeEvidence P boolTy]))
      (ok okHead (isBoolEvidence P))
  , rw "SC_ALPHA_REFL"
      (check checkHead (app "SC_ALPHA_REFL"
        [P, T, hasTypeEvidence P T]))
      (ok okHead (alphaEqEvidence P P))
  , rw "SC_HYPS_NIL"
      (check checkHead (app "SC_HYPS_NIL"))
      (ok okHead (validHypsEvidence hypsNil))
  , rw "SC_HYPS_SINGLETON"
      (check checkHead (app "SC_HYPS_SINGLETON"
        [P, isBoolEvidence P]))
      (ok okHead (validHypsEvidence (hypsCons P hypsNil)))
  , rw "SC_UNION_NIL_LEFT"
      (check checkHead (app "SC_UNION_NIL_LEFT"
        [H, validHypsEvidence H]))
      (ok okHead (hypUnionEvidence hypsNil H H))
  , rw "SC_REMOVE_SINGLETON"
      (check checkHead (app "SC_REMOVE_SINGLETON"
        [P, isBoolEvidence P]))
      (ok okHead (hypRemoveEvidence P (hypsCons P hypsNil) hypsNil)) ]

private def holLightRewrites : List RewriteRule :=
  [ rw "HL_REFL"
      (check "HLNativeCheck" (app "HL_REFL"
        [P, T, hasTypeEvidence P T]))
      (ok "HLNativeOk" (theoremEvidence hypsNil (eqTerm T P P)))
  , rw "HL_ASSUME"
      (check "HLNativeCheck" (app "HL_ASSUME" [P, isBoolEvidence P]))
      (ok "HLNativeOk" (theoremEvidence (hypsCons P hypsNil) P))
  , rw "HL_EQ_MP"
      (check "HLNativeCheck" (app "HL_EQ_MP"
        [ theoremEvidence H1 (eqTerm boolTy P Q)
        , theoremEvidence H2 Q2
        , alphaEqEvidence P Q2
        , hypUnionEvidence H1 H2 HO ]))
      (ok "HLNativeOk" (theoremEvidence HO Q)) ]

private def hol4Rewrites : List RewriteRule :=
  [ rw "H4_ASSUME"
      (check "H4NativeCheck" (app "H4_ASSUME" [P, isBoolEvidence P]))
      (ok "H4NativeOk" (theoremEvidence (hypsCons P hypsNil) P))
  , rw "H4_DISCH"
      (check "H4NativeCheck" (app "H4_DISCH"
        [ P
        , theoremEvidence H Q
        , isBoolEvidence P
        , hypRemoveEvidence P H HO ]))
      (ok "H4NativeOk" (theoremEvidence HO (impTerm P Q))) ]

def holLightNativeSlice : LanguageDef :=
  { name := "HOLLightNativeGSLTSlice"
    types := commonTypes
    terms := commonDataTerms ++ sideProofTerms ++ holLightProofTerms
    equations := []
    rewrites := sideRewrites "HLNativeCheck" "HLNativeOk" ++ holLightRewrites
    logic := []
    oracles := [] }

def hol4NativeSlice : LanguageDef :=
  { name := "HOL4NativeGSLTSlice"
    types := commonTypes
    terms := commonDataTerms ++ sideProofTerms ++ hol4ProofTerms
    equations := []
    rewrites := sideRewrites "H4NativeCheck" "H4NativeOk" ++ hol4Rewrites
    logic := []
    oracles := [] }

def holLightNativeProfile : EvidenceProfile :=
  { checkHead := "HLNativeCheck"
    okHead := "HLNativeOk"
    proofCategory := "HolProof"
    evidenceCategory := "HolEvidence"
    derivedHead := "$hol.native" }

def hol4NativeProfile : EvidenceProfile :=
  { checkHead := "H4NativeCheck"
    okHead := "H4NativeOk"
    proofCategory := "HolProof"
    evidenceCategory := "HolEvidence"
    derivedHead := "$hol.native" }

def holLightNativePresentation? : Option Presentation :=
  rawPresentation? holLightNativeProfile holLightNativeSlice

def hol4NativePresentation? : Option Presentation :=
  rawPresentation? hol4NativeProfile hol4NativeSlice

/-- A failed extraction must remain invalid at the ordinary presentation
boundary; it must not silently turn into an admissible empty calculus. -/
private def invalidExtractionPresentation (language : LanguageDef) : Presentation :=
  { language
    judgments := [{ head := "", arity := 0 }]
    rules := [] }

def holLightNativePresentation : Presentation :=
  holLightNativePresentation?.getD
    (invalidExtractionPresentation holLightNativeSlice)

def hol4NativePresentation : Presentation :=
  hol4NativePresentation?.getD
    (invalidExtractionPresentation hol4NativeSlice)

private theorem holLightNativeSlice_rewrites :
    holLightNativeSlice.rewrites =
      sideRewrites "HLNativeCheck" "HLNativeOk" ++ holLightRewrites := rfl

private theorem hol4NativeSlice_rewrites :
    hol4NativeSlice.rewrites =
      sideRewrites "H4NativeCheck" "H4NativeOk" ++ hol4Rewrites := rfl

theorem holLightNativePresentation_eq_structural :
    holLightNativePresentation =
      (rawPresentationStructural? holLightNativeProfile
        holLightNativeSlice).getD
          (invalidExtractionPresentation holLightNativeSlice) := by
  unfold holLightNativePresentation holLightNativePresentation?
  rw [rawPresentation?_eq_structural]

theorem hol4NativePresentation_eq_structural :
    hol4NativePresentation =
      (rawPresentationStructural? hol4NativeProfile hol4NativeSlice).getD
        (invalidExtractionPresentation hol4NativeSlice) := by
  unfold hol4NativePresentation hol4NativePresentation?
  rw [rawPresentation?_eq_structural]

private theorem all_eq_mapped_all {α : Type} (values : List α)
    (predicate : α → Bool) :
    values.all predicate = (values.map predicate).all id := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
      rw [List.all_cons, List.map_cons, List.all_cons, ih]
      rfl

set_option maxHeartbeats 4000000 in
private theorem holLightRewriteValid :
    ∀ rewrite ∈ holLightNativeSlice.rewrites,
      LanguageDef.validateRewrite holLightNativeSlice rewrite = [] := by
  intro rewrite hrewrite
  simp only [holLightNativeSlice, sideRewrites, holLightRewrites,
    List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hrewrite
  rcases hrewrite with
    (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) |
    (rfl | rfl | rfl)
  all_goals
    simp (config := { maxSteps := 300000 })
      [LanguageDef.validateRewrite, holLightNativeSlice, commonTypes,
      commonDataTerms, sideProofTerms, holLightProofTerms, sideRewrites,
      holLightRewrites, termCtor, ty, rw, check, ok, validTypeEvidence,
      hasTypeEvidence, isBoolEvidence, validHypsEvidence, alphaEqEvidence,
      hypUnionEvidence, hypRemoveEvidence, theoremEvidence, eqTerm, tyApp,
      funTy, tyList, tyCons, tyNil, boolTy, tmVar, tmConst, tmApp, hypsNil,
      hypsCons, app, equalityNameHead, implicationNameHead, boolNameHead,
      functionNameHead, pNameHead, qNameHead,
      N, T, P, Q, Q2, H, H1, H2, HO, pvar,
      LanguageDef.validatePremises, LanguageDef.validatePatternConstructors,
      LanguageDef.validateRulePatterns, LanguageDef.patternFvarNames,
      LanguageDef.patternBinderNames, Pattern.constructorRefs,
      Pattern.constructorRefsList,
      Pattern.freeFvarNames, Pattern.isWellScoped, Pattern.isWellScopedAt,
      Pattern.isWellScopedListAt, LanguageDef.typeNames, TypeDecl.plain]

set_option maxHeartbeats 4000000 in
private theorem hol4RewriteValid :
    ∀ rewrite ∈ hol4NativeSlice.rewrites,
      LanguageDef.validateRewrite hol4NativeSlice rewrite = [] := by
  intro rewrite hrewrite
  simp only [hol4NativeSlice, sideRewrites, hol4Rewrites,
    List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hrewrite
  rcases hrewrite with
    (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) |
    (rfl | rfl)
  all_goals
    simp (config := { maxSteps := 300000 })
      [LanguageDef.validateRewrite, hol4NativeSlice, commonTypes,
      commonDataTerms, sideProofTerms, hol4ProofTerms, sideRewrites,
      hol4Rewrites, termCtor, ty, rw, check, ok, validTypeEvidence,
      hasTypeEvidence, isBoolEvidence, validHypsEvidence, alphaEqEvidence,
      hypUnionEvidence, hypRemoveEvidence, theoremEvidence, impTerm, tyApp,
      funTy, tyList, tyCons, tyNil, boolTy, tmVar, tmConst, tmApp, hypsNil,
      hypsCons, app, equalityNameHead, implicationNameHead, boolNameHead,
      functionNameHead, pNameHead, qNameHead,
      N, T, P, Q, H, HO, pvar,
      LanguageDef.validatePremises, LanguageDef.validatePatternConstructors,
      LanguageDef.validateRulePatterns, LanguageDef.patternFvarNames,
      LanguageDef.patternBinderNames, Pattern.constructorRefs,
      Pattern.constructorRefsList,
      Pattern.freeFvarNames, Pattern.isWellScoped, Pattern.isWellScopedAt,
      Pattern.isWellScopedListAt, LanguageDef.typeNames, TypeDecl.plain]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem holLightNativeSlice_validate : holLightNativeSlice.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorAndRewrites
  all_goals try decide
  exact holLightRewriteValid

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem hol4NativeSlice_validate : hol4NativeSlice.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorAndRewrites
  all_goals try decide
  exact hol4RewriteValid

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
theorem holLightNativePresentation_valid :
    holLightNativePresentation.isValidV2 = true := by
  simp only [Presentation.isValidV2, Presentation.isValidV1,
    Bool.and_eq_true]
  have hlanguage :
      holLightNativePresentation.language.validate.isEmpty = true := by
    change holLightNativeSlice.validate.isEmpty = true
    rw [holLightNativeSlice_validate]
    rfl
  refine ⟨⟨⟨⟨hlanguage, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [all_eq_mapped_all]
    have hmap :
        holLightNativePresentation.rules.map RuleSchema.isValidV1 =
          [true, true, true, true, true, true, true, true, true, true, true] := by
      unfold holLightNativePresentation holLightNativePresentation?
      rw [rawPresentation?_eq_structural]
      unfold rawPresentationStructural?
      rw [holLightNativeSlice_rewrites]
      unfold List.mapM'
      simp (config := { maxSteps := 800000 })
        [List.mapM'_cons, List.mapM'_nil,
          List.map, List.filterMap, List.flatMap, List.zip, List.find?,
          extractRuleSchema?, checkedInputProof?, checkedOutputResult?,
          evidenceArguments?, extractedSchema, findConstructor?,
          relationJudgmentDecls, relationFactRules, referencedRelations,
          holLightNativeSlice, commonTypes, commonDataTerms, sideProofTerms,
          holLightProofTerms, sideRewrites, holLightRewrites,
          holLightNativeProfile, termCtor, ty, rw, check, ok,
          validTypeEvidence, hasTypeEvidence, isBoolEvidence,
          validHypsEvidence, alphaEqEvidence, hypUnionEvidence,
          hypRemoveEvidence, theoremEvidence, eqTerm, tyApp, funTy, tyList,
          tyCons, tyNil, boolTy, tmVar, tmConst, tmApp, hypsNil, hypsCons,
          app, equalityNameHead, implicationNameHead, boolNameHead,
          functionNameHead, pNameHead, qNameHead, N, T, P, Q, Q2, H, H1,
          H2, HO, pvar, EvidenceProfile.derived,
          EvidenceProfile.relationHead, EvidenceProfile.relationJudgment,
          metavariableOccurrenceEq, occurrenceContains, occurrenceEraseDups,
          occurrenceEraseDupsAux, occurrenceKeepIn, occurrenceKeepOut,
          RuleSchema.isValidV1, RuleSchema.metavariableNames,
          RuleSchema.occurrences, RuleSchema.patterns,
          patternMetavariableOccurrencesAt, patternsMetavariableOccurrencesAt,
          patternHasNoCollectionRest, patternsHaveNoCollectionRest,
          TermParam.typeExpr,
          Pattern.isWellScoped, Pattern.isWellScopedAt,
          Pattern.isWellScopedListAt, Pattern.hasCanonicalBinderMetadata,
          Pattern.hasCanonicalBinderMetadataList]
      decide
    rw [hmap]
    rfl
  · decide
  · decide
  · rw [all_eq_mapped_all]
    have hmap :
        holLightNativePresentation.rules.map
            (RuleSchema.isValidIn holLightNativePresentation) =
          [true, true, true, true, true, true, true, true, true, true, true] := by
      unfold holLightNativePresentation holLightNativePresentation?
      rw [rawPresentation?_eq_structural]
      unfold rawPresentationStructural?
      rw [holLightNativeSlice_rewrites]
      unfold List.mapM'
      simp (config := { maxSteps := 800000 })
        [List.mapM'_cons, List.mapM'_nil, List.map,
          List.filterMap, List.filter, List.flatMap, List.zip, List.find?,
          extractRuleSchema?, checkedInputProof?, checkedOutputResult?,
          evidenceArguments?, extractedSchema, findConstructor?,
          relationJudgmentDecls, relationFactRules, referencedRelations,
          holLightNativeSlice, commonTypes, commonDataTerms, sideProofTerms,
          holLightProofTerms, sideRewrites, holLightRewrites,
          holLightNativeProfile, termCtor, ty, rw, check, ok,
          validTypeEvidence, hasTypeEvidence, isBoolEvidence,
          validHypsEvidence, alphaEqEvidence, hypUnionEvidence,
          hypRemoveEvidence, theoremEvidence, eqTerm, tyApp, funTy, tyList,
          tyCons, tyNil, boolTy, tmVar, tmConst, tmApp, hypsNil, hypsCons,
          app, equalityNameHead, implicationNameHead, boolNameHead,
          functionNameHead, pNameHead, qNameHead, N, T, P, Q, Q2, H, H1,
          H2, HO, pvar, EvidenceProfile.derived,
          EvidenceProfile.relationHead, EvidenceProfile.relationJudgment,
          metavariableOccurrenceEq, occurrenceContains, occurrenceEraseDups,
          occurrenceEraseDupsAux, occurrenceKeepIn, occurrenceKeepOut,
          RuleSchema.isValidIn, RuleSchema.isValidV1,
          RuleSchema.metavariableNames, RuleSchema.occurrences,
          RuleSchema.patterns, patternMetavariableOccurrencesAt,
          patternsMetavariableOccurrencesAt, patternHasNoCollectionRest,
          patternsHaveNoCollectionRest, Presentation.judgmentSchemaValid,
          Presentation.lookupJudgment?, fixedConstructorsValid,
          fixedConstructorListsValid, languageHasConstructorArity,
          TermParam.typeExpr, Pattern.isWellScoped, Pattern.isWellScopedAt,
          Pattern.isWellScopedListAt, Pattern.hasCanonicalBinderMetadata,
          Pattern.hasCanonicalBinderMetadataList]
      decide
    rw [hmap]
    rfl

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
theorem hol4NativePresentation_valid :
    hol4NativePresentation.isValidV2 = true := by
  simp only [Presentation.isValidV2, Presentation.isValidV1,
    Bool.and_eq_true]
  have hlanguage :
      hol4NativePresentation.language.validate.isEmpty = true := by
    change hol4NativeSlice.validate.isEmpty = true
    rw [hol4NativeSlice_validate]
    rfl
  refine ⟨⟨⟨⟨hlanguage, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [all_eq_mapped_all]
    have hmap :
        hol4NativePresentation.rules.map RuleSchema.isValidV1 =
          [true, true, true, true, true, true, true, true, true, true] := by
      unfold hol4NativePresentation hol4NativePresentation?
      rw [rawPresentation?_eq_structural]
      unfold rawPresentationStructural?
      rw [hol4NativeSlice_rewrites]
      unfold List.mapM'
      simp (config := { maxSteps := 800000 })
        [List.mapM'_cons, List.mapM'_nil, List.map, List.filterMap,
          List.flatMap, List.zip, List.find?, extractRuleSchema?,
          checkedInputProof?, checkedOutputResult?, evidenceArguments?,
          extractedSchema, findConstructor?, relationJudgmentDecls,
          relationFactRules, referencedRelations, hol4NativeSlice,
          commonTypes, commonDataTerms, sideProofTerms, hol4ProofTerms,
          sideRewrites, hol4Rewrites, hol4NativeProfile, termCtor, ty, rw,
          check, ok, validTypeEvidence, hasTypeEvidence, isBoolEvidence,
          validHypsEvidence, alphaEqEvidence, hypUnionEvidence,
          hypRemoveEvidence, theoremEvidence, impTerm, tyApp, funTy, tyList,
          tyCons, tyNil, boolTy, tmVar, tmConst, tmApp, hypsNil, hypsCons,
          app, equalityNameHead, implicationNameHead, boolNameHead,
          functionNameHead, pNameHead, qNameHead, N, T, P, Q, H, HO, pvar,
          EvidenceProfile.derived,
          EvidenceProfile.relationHead, EvidenceProfile.relationJudgment,
          metavariableOccurrenceEq, occurrenceContains, occurrenceEraseDups,
          occurrenceEraseDupsAux, occurrenceKeepIn, occurrenceKeepOut,
          RuleSchema.isValidV1, RuleSchema.metavariableNames,
          RuleSchema.occurrences, RuleSchema.patterns,
          patternMetavariableOccurrencesAt, patternsMetavariableOccurrencesAt,
          patternHasNoCollectionRest, patternsHaveNoCollectionRest,
          TermParam.typeExpr, Pattern.isWellScoped, Pattern.isWellScopedAt,
          Pattern.isWellScopedListAt, Pattern.hasCanonicalBinderMetadata,
          Pattern.hasCanonicalBinderMetadataList]
      decide
    rw [hmap]
    rfl
  · decide
  · decide
  · rw [all_eq_mapped_all]
    have hmap :
        hol4NativePresentation.rules.map
            (RuleSchema.isValidIn hol4NativePresentation) =
          [true, true, true, true, true, true, true, true, true, true] := by
      unfold hol4NativePresentation hol4NativePresentation?
      rw [rawPresentation?_eq_structural]
      unfold rawPresentationStructural?
      rw [hol4NativeSlice_rewrites]
      unfold List.mapM'
      simp (config := { maxSteps := 800000 })
        [List.mapM'_cons, List.mapM'_nil, List.map, List.filterMap,
          List.filter, List.flatMap, List.zip, List.find?, extractRuleSchema?,
          checkedInputProof?, checkedOutputResult?, evidenceArguments?,
          extractedSchema, findConstructor?, relationJudgmentDecls,
          relationFactRules, referencedRelations, hol4NativeSlice,
          commonTypes, commonDataTerms, sideProofTerms, hol4ProofTerms,
          sideRewrites, hol4Rewrites, hol4NativeProfile, termCtor, ty, rw,
          check, ok, validTypeEvidence, hasTypeEvidence, isBoolEvidence,
          validHypsEvidence, alphaEqEvidence, hypUnionEvidence,
          hypRemoveEvidence, theoremEvidence, impTerm, tyApp, funTy, tyList,
          tyCons, tyNil, boolTy, tmVar, tmConst, tmApp, hypsNil, hypsCons,
          app, equalityNameHead, implicationNameHead, boolNameHead,
          functionNameHead, pNameHead, qNameHead, N, T, P, Q, H, HO, pvar,
          EvidenceProfile.derived,
          EvidenceProfile.relationHead, EvidenceProfile.relationJudgment,
          metavariableOccurrenceEq, occurrenceContains, occurrenceEraseDups,
          occurrenceEraseDupsAux, occurrenceKeepIn, occurrenceKeepOut,
          RuleSchema.isValidIn, RuleSchema.isValidV1,
          RuleSchema.metavariableNames, RuleSchema.occurrences,
          RuleSchema.patterns, patternMetavariableOccurrencesAt,
          patternsMetavariableOccurrencesAt, patternHasNoCollectionRest,
          patternsHaveNoCollectionRest, Presentation.judgmentSchemaValid,
          Presentation.lookupJudgment?, fixedConstructorsValid,
          fixedConstructorListsValid, languageHasConstructorArity,
          TermParam.typeExpr, Pattern.isWellScoped, Pattern.isWellScopedAt,
          Pattern.isWellScopedListAt, Pattern.hasCanonicalBinderMetadata,
          Pattern.hasCanonicalBinderMetadataList]
      decide
    rw [hmap]
    rfl

private def proofProfilePayload : Pattern := app "ExactNativePremises"

def holLightNativeSource : GSLTSource :=
  { identity := holLightIdentity
    assumptions := { entries := [] }
    profiles :=
      { entries :=
          [{ name := "native-derivations"
             version := "v1"
             payload := proofProfilePayload }] }
    presentation := holLightNativePresentation }

def hol4NativeSource : GSLTSource :=
  { identity := hol4Identity
    assumptions := { entries := [] }
    profiles :=
      { entries :=
          [{ name := "native-derivations"
             version := "v1"
             payload := proofProfilePayload }] }
    presentation := hol4NativePresentation }

theorem holLightNativeSource_identity_valid :
    holLightNativeSource.identity.isValid = true :=
  holLightIdentity_valid

theorem hol4NativeSource_identity_valid :
    hol4NativeSource.identity.isValid = true :=
  hol4Identity_valid

theorem holLightNativeSource_assumptions_valid :
    holLightNativeSource.assumptions.isValid = true := by
  rfl

theorem hol4NativeSource_assumptions_valid :
    hol4NativeSource.assumptions.isValid = true := by
  rfl

theorem holLightNativeSource_profiles_valid :
    holLightNativeSource.profiles.isValid = true := by
  rfl

theorem hol4NativeSource_profiles_valid :
    hol4NativeSource.profiles.isValid = true := by
  rfl

theorem holLightNativeSource_presentation_valid :
    holLightNativeSource.presentation.isValidV2 = true :=
  holLightNativePresentation_valid

theorem hol4NativeSource_presentation_valid :
    hol4NativeSource.presentation.isValidV2 = true :=
  hol4NativePresentation_valid

def holLightAdmittedSource : CheckedGSLT :=
  { source := holLightNativeSource
    identityValid := holLightNativeSource_identity_valid
    assumptionsValid := holLightNativeSource_assumptions_valid
    profilesValid := holLightNativeSource_profiles_valid
    presentationValid := holLightNativeSource_presentation_valid }

def hol4AdmittedSource : CheckedGSLT :=
  { source := hol4NativeSource
    identityValid := hol4NativeSource_identity_valid
    assumptionsValid := hol4NativeSource_assumptions_valid
    profilesValid := hol4NativeSource_profiles_valid
    presentationValid := hol4NativeSource_presentation_valid }

theorem holLightNativeSource_validate :
    holLightNativeSource.validate = .ok holLightAdmittedSource := by
  have hprofilesNonempty :
      holLightNativeSource.profiles.entries.isEmpty = false := by
    rfl
  simp [GSLTSource.validate, holLightAdmittedSource,
    holLightNativeSource_identity_valid,
    holLightNativeSource_assumptions_valid,
    holLightNativeSource_profiles_valid,
    holLightNativeSource_presentation_valid, hprofilesNonempty]

theorem hol4NativeSource_validate :
    hol4NativeSource.validate = .ok hol4AdmittedSource := by
  have hprofilesNonempty :
      hol4NativeSource.profiles.entries.isEmpty = false := by
    rfl
  simp [GSLTSource.validate, hol4AdmittedSource,
    hol4NativeSource_identity_valid, hol4NativeSource_assumptions_valid,
    hol4NativeSource_profiles_valid, hol4NativeSource_presentation_valid,
    hprofilesNonempty]

def checkAdmitted (source : GSLTSource) (goal : Pattern)
    (proof : RawProof) : Bool :=
  match source.validate with
  | .ok checked => checked.checkRaw goal proof
  | .error _ => false

/-- Successful executable admission and checking produces a Type-valued
derivation over the exact source package selected by validation. -/
theorem checkAdmitted_soundness {source : GSLTSource} {goal : Pattern}
    {proof : RawProof} (hcheck : checkAdmitted source goal proof = true) :
    ∃ checked : CheckedGSLT,
      source.validate = .ok checked ∧
        Nonempty (Derivation checked.presentation goal) := by
  cases hvalidation : source.validate with
  | error error => simp [checkAdmitted, hvalidation] at hcheck
  | ok checked =>
      refine ⟨checked, rfl, ?_⟩
      exact CheckedGSLT.checkRaw_soundness
        (by simpa [checkAdmitted, hvalidation] using hcheck)

/-- Stronger exact-object boundary: admission of a raw native proof recovers a
typed derivation whose erasure is that same ordered proof tree. -/
theorem checkAdmitted_exact {source : GSLTSource} {goal : Pattern}
    {proof : RawProof} (hcheck : checkAdmitted source goal proof = true) :
    ∃ (checked : CheckedGSLT)
        (derivation : Derivation checked.presentation goal),
      source.validate = .ok checked ∧ derivation.erase = proof := by
  cases hvalidation : source.validate with
  | error error =>
      simp [checkAdmitted, hvalidation] at hcheck
  | ok checked =>
      have hchecked : checked.checkRaw goal proof = true := by
        simpa [checkAdmitted, hvalidation] using hcheck
      rcases CheckedGSLT.checkRaw_exists_derivation_with_exact_erasure hchecked with
        ⟨derivation, herasure⟩
      exact ⟨checked, derivation, rfl, herasure⟩

private def node (ruleId : String) (arguments : List Pattern)
    (children : List RawProof := []) : RawProof :=
  .node { ruleId := ⟨ruleId⟩, arguments } children

private def nameP : Pattern := app pNameHead
private def nameQ : Pattern := app qNameHead
private def termP : Pattern := tmVar nameP boolTy
private def termQ : Pattern := tmVar nameQ boolTy
private def singletonP : Pattern := hypsCons termP hypsNil

private def boolTypeProof : RawProof := node "SC_BOOL_TYPE" []
private def termPTypeProof : RawProof :=
  node "SC_VAR_TYPE" [nameP, boolTy] [boolTypeProof]
private def termQTypeProof : RawProof :=
  node "SC_VAR_TYPE" [nameQ, boolTy] [boolTypeProof]
private def termPBoolProof : RawProof :=
  node "SC_IS_BOOL" [termP] [termPTypeProof]
private def termQBoolProof : RawProof :=
  node "SC_IS_BOOL" [termQ] [termQTypeProof]
private def termPAlphaProof : RawProof :=
  node "SC_ALPHA_REFL" [termP, boolTy] [termPTypeProof]
private def singletonPValidProof : RawProof :=
  node "SC_HYPS_SINGLETON" [termP] [termPBoolProof]
private def unionNilSingletonPProof : RawProof :=
  node "SC_UNION_NIL_LEFT" [singletonP] [singletonPValidProof]
private def removeSingletonPProof : RawProof :=
  node "SC_REMOVE_SINGLETON" [termP] [termPBoolProof]

private def holLightReflProof : RawProof :=
  node "HL_REFL" [termP, boolTy] [termPTypeProof]
private def holLightAssumeProof : RawProof :=
  node "HL_ASSUME" [termP] [termPBoolProof]
def holLightEqMpProof : RawProof :=
  node "HL_EQ_MP" [hypsNil, termP, termP, singletonP, termP, singletonP]
    [holLightReflProof, holLightAssumeProof, termPAlphaProof,
      unionNilSingletonPProof]

def holLightGoal : Pattern :=
  holLightNativeProfile.derived (theoremEvidence singletonP termP)

private def hol4AssumeProof : RawProof :=
  node "H4_ASSUME" [termP] [termPBoolProof]
def hol4DischProof : RawProof :=
  node "H4_DISCH" [termP, singletonP, termP, hypsNil]
    [hol4AssumeProof, termPBoolProof, removeSingletonPProof]

def hol4Goal : Pattern :=
  hol4NativeProfile.derived (theoremEvidence hypsNil (impTerm termP termP))

def holLightWrongChildOrderProof : RawProof :=
  node "HL_EQ_MP" [hypsNil, termP, termP, singletonP, termP, singletonP]
    [holLightAssumeProof, holLightReflProof, termPAlphaProof,
      unionNilSingletonPProof]

def holLightChangedBindingProof : RawProof :=
  node "HL_EQ_MP" [hypsNil, termQ, termQ, singletonP, termQ, singletonP]
    [holLightReflProof, holLightAssumeProof, termPAlphaProof,
      unionNilSingletonPProof]

def hol4MissingRemovalProof : RawProof :=
  node "H4_DISCH" [termP, singletonP, termP, hypsNil]
    [hol4AssumeProof, termPBoolProof]

def hol4WrongRemovalEvidenceProof : RawProof :=
  node "H4_DISCH" [termP, singletonP, termP, hypsNil]
    [hol4AssumeProof, termPBoolProof, termPBoolProof]

local macro "hol_native_check_core" : tactic =>
  `(tactic|
    simp (config := { maxSteps := 1200000 })
      [CheckedGSLT.checkRaw, CheckedGSLT.presentation,
        holLightAdmittedSource, hol4AdmittedSource, holLightNativeSource,
        hol4NativeSource, holLightNativePresentation_eq_structural,
        hol4NativePresentation_eq_structural, rawPresentationStructural?,
        holLightNativeSlice_rewrites, hol4NativeSlice_rewrites, List.mapM',
        List.map, List.filterMap, List.flatMap, List.zip, List.find?,
        extractRuleSchema?, checkedInputProof?, checkedOutputResult?,
        evidenceArguments?, extractedSchema, findConstructor?,
        TermParam.typeExpr,
        relationJudgmentDecls, relationFactRules, referencedRelations,
        holLightNativeSlice, hol4NativeSlice, commonTypes, commonDataTerms,
        sideProofTerms, holLightProofTerms, hol4ProofTerms, sideRewrites,
        holLightRewrites, hol4Rewrites, holLightNativeProfile,
        hol4NativeProfile, termCtor, ty, rw, check, ok, validTypeEvidence,
        hasTypeEvidence, isBoolEvidence, validHypsEvidence, alphaEqEvidence,
        hypUnionEvidence, hypRemoveEvidence, theoremEvidence, eqTerm, impTerm,
        tyApp, funTy, tyList, tyCons, tyNil, boolTy, tmVar, tmConst, tmApp,
        hypsNil, hypsCons, app, equalityNameHead, implicationNameHead,
        boolNameHead, functionNameHead, pNameHead, qNameHead, N, T, P, Q,
        Q2, H, H1, H2, HO, pvar, EvidenceProfile.derived,
        EvidenceProfile.relationHead, EvidenceProfile.relationJudgment,
        metavariableOccurrenceEq, occurrenceContains, occurrenceEraseDups,
        occurrenceEraseDupsAux, occurrenceKeepIn, occurrenceKeepOut,
        RuleSchema.occurrences, RuleSchema.patterns,
        patternMetavariableOccurrencesAt, patternsMetavariableOccurrencesAt,
        InferenceChecker.checkRaw, InferenceChecker.checkRawChildren,
        instantiateRule?, Presentation.lookupRule?, argumentsValidAt,
        argumentValidAt, instantiateSchema?, instantiateSchemaAt?,
        instantiateSchemas?, instantiateSchemasAt?, lookupArgumentAt?,
        Pattern.isGroundAt, Pattern.isGroundListAt,
        Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList, node, nameP, nameQ, termP,
        termQ, singletonP, boolTypeProof, termPTypeProof, termQTypeProof,
        termPBoolProof, termQBoolProof, termPAlphaProof,
        singletonPValidProof, unionNilSingletonPProof,
        removeSingletonPProof, holLightReflProof, holLightAssumeProof,
        hol4AssumeProof, holLightEqMpProof, hol4DischProof, holLightGoal,
        hol4Goal])

theorem holLightEqMpProof_checked :
    holLightAdmittedSource.checkRaw holLightGoal holLightEqMpProof = true := by
  hol_native_check_core

theorem hol4DischProof_checked :
    hol4AdmittedSource.checkRaw hol4Goal hol4DischProof = true := by
  hol_native_check_core

theorem holLightEqMpProof_exact_derivation :
    ∃ derivation : Derivation holLightAdmittedSource.presentation holLightGoal,
      derivation.erase = holLightEqMpProof :=
  CheckedGSLT.checkRaw_exists_derivation_with_exact_erasure
    holLightEqMpProof_checked

theorem hol4DischProof_exact_derivation :
    ∃ derivation : Derivation hol4AdmittedSource.presentation hol4Goal,
      derivation.erase = hol4DischProof :=
  CheckedGSLT.checkRaw_exists_derivation_with_exact_erasure
    hol4DischProof_checked

def holLightSelectedRuleIds : List String := ["HL_REFL", "HL_ASSUME", "HL_EQ_MP"]
def hol4SelectedRuleIds : List String := ["H4_ASSUME", "H4_DISCH"]

private def mainRuleIds (language : LanguageDef) : List String :=
  language.rewrites.drop sideProofTerms.length |>.map (·.name)

#guard LanguageDef.validate holLightNativeSlice == []
#guard LanguageDef.validate hol4NativeSlice == []
#guard holLightNativeSlice.logic.isEmpty
#guard hol4NativeSlice.logic.isEmpty
#guard holLightNativeSlice.rewrites.all (·.premises.isEmpty)
#guard hol4NativeSlice.rewrites.all (·.premises.isEmpty)
#guard mainRuleIds holLightNativeSlice == holLightSelectedRuleIds
#guard mainRuleIds hol4NativeSlice == hol4SelectedRuleIds
#guard holLightSelectedRuleIds.all (generatedRuleIds holLightPrimitiveRules).contains
#guard hol4SelectedRuleIds.all (generatedRuleIds hol4PrimitiveRules).contains
#guard holLightNativePresentation.isValidV2
#guard hol4NativePresentation.isValidV2
#guard validationAccepted holLightNativeSource.validate
#guard validationAccepted hol4NativeSource.validate

/- Positive: a native multi-premise HOL Light `EQ_MP` derivation is accepted. -/
#guard checkAdmitted holLightNativeSource holLightGoal holLightEqMpProof

/- Negative: theorem-child order is part of the checked proof term. -/
#guard !checkAdmitted holLightNativeSource holLightGoal
  holLightWrongChildOrderProof

/- Negative: a different substitution cannot establish the original goal. -/
#guard !checkAdmitted holLightNativeSource holLightGoal
  holLightChangedBindingProof

/- Positive: HOL4 `DISCH` removes its antecedent and constructs implication. -/
#guard checkAdmitted hol4NativeSource hol4Goal hol4DischProof

/- Negative: omitting the context-removal derivation is rejected. -/
#guard !checkAdmitted hol4NativeSource hol4Goal
  hol4MissingRemovalProof

/- Negative: Booleanhood evidence cannot occupy the context-removal premise. -/
#guard !checkAdmitted hol4NativeSource hol4Goal
  hol4WrongRemovalEvidenceProof

end Mettapedia.GSLT.LanguageDef.HOLNativeGSLTSlice
