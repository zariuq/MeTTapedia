import Mettapedia.GSLT.LanguageDef.Cost.Construction
import Mettapedia.GSLT.LanguageDef.CostElaborationDisplayed
import Mettapedia.GSLT.LanguageDef.Cost.Layer.Basic
import Mettapedia.GSLT.LanguageDef.Cost.Elaboration.Total
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryCanonical
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryGeneratorAlignment
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostGeneratorInvariantCounterexample

/-!
# The hereditary rho Cost object

This module assembles the object laws for the hereditary rho Cost
normalizer.  The construction remains parameterized through the generic
Cost interfaces; only the rho-specific law witnesses live here.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

private theorem isObjectPattern_of_mem_isObjectPatternList
    {patterns : List Pattern}
    (objects : WellSorted.isObjectPatternList patterns = true)
    {pattern : Pattern} (membership : pattern ∈ patterns) :
    WellSorted.isObjectPattern pattern = true := by
  induction patterns with
  | nil => simp at membership
  | cons head tail inductionHypothesis =>
      simp only [WellSorted.isObjectPatternList, Bool.and_eq_true] at objects
      rcases objects with ⟨headObject, tailObjects⟩
      rcases List.mem_cons.mp membership with rfl | membership
      · exact headObject
      · exact inductionHypothesis tailObjects membership

private theorem mem_freeFvarNames_liftBVars_iff
    (name : String) (cutoff shift : Nat) : ∀ pattern : Pattern,
    name ∈ (liftBVars cutoff shift pattern).freeFvarNames ↔
      name ∈ pattern.freeFvarNames := by
  intro pattern
  induction pattern using Pattern.inductionOn generalizing cutoff with
  | hbvar index =>
      by_cases shifted : cutoff ≤ index <;>
        simp [liftBVars, Pattern.freeFvarNames, shifted]
  | hfvar variableName => simp [liftBVars, Pattern.freeFvarNames]
  | happly constructor arguments inductionHypothesis =>
      simp only [liftBVars, Pattern.freeFvarNames, List.mem_flatMap,
        List.mem_map]
      constructor
      · rintro ⟨normalized, ⟨argument, membership, rfl⟩, support⟩
        exact ⟨argument, membership,
          (inductionHypothesis argument membership cutoff).mp support⟩
      · rintro ⟨argument, membership, support⟩
        exact ⟨liftBVars cutoff shift argument,
          ⟨argument, membership, rfl⟩,
          (inductionHypothesis argument membership cutoff).mpr support⟩
  | hlambda binder body inductionHypothesis =>
      simpa [liftBVars, Pattern.freeFvarNames] using
        inductionHypothesis (cutoff + 1)
  | hmultiLambda arity binders body inductionHypothesis =>
      simpa [liftBVars, Pattern.freeFvarNames] using
        inductionHypothesis (cutoff + arity)
  | hsubst body replacement bodyInduction replacementInduction =>
      simp [liftBVars, Pattern.freeFvarNames,
        bodyInduction (cutoff + 1), replacementInduction cutoff]
  | hcollection collectionType elements rest inductionHypothesis =>
      simp only [liftBVars, Pattern.freeFvarNames, List.mem_append,
        List.mem_flatMap, List.mem_map]
      constructor
      · rintro (⟨normalized, ⟨element, membership, rfl⟩, support⟩ | support)
        · exact Or.inl ⟨element, membership,
            (inductionHypothesis element membership cutoff).mp support⟩
        · exact Or.inr support
      · rintro (⟨element, membership, support⟩ | support)
        · exact Or.inl ⟨liftBVars cutoff shift element,
            ⟨element, membership, rfl⟩,
            (inductionHypothesis element membership cutoff).mpr support⟩
        · exact Or.inr support

private theorem mem_freeFvarNames_fill_iff_of_iff
    (context : OneHoleContext) (name : String) {left right : Pattern}
    (sameSupport : name ∈ left.freeFvarNames ↔
      name ∈ right.freeFvarNames) :
    name ∈ (context.fill left).freeFvarNames ↔
      name ∈ (context.fill right).freeFvarNames := by
  induction context with
  | hole => exact sameSupport
  | apply constructor before inner after inductionHypothesis =>
      simp only [OneHoleContext.fill, Pattern.freeFvarNames,
        List.mem_flatMap, List.mem_append, List.mem_cons]
      constructor
      · rintro ⟨argument, membership, support⟩
        rcases membership with beforeMembership | (rfl | afterMembership)
        · exact ⟨argument, Or.inl beforeMembership, support⟩
        · exact ⟨inner.fill right,
            Or.inr (Or.inl rfl),
            inductionHypothesis.mp support⟩
        · exact ⟨argument,
            Or.inr (Or.inr afterMembership),
            support⟩
      · rintro ⟨argument, membership, support⟩
        rcases membership with beforeMembership | (rfl | afterMembership)
        · exact ⟨argument, Or.inl beforeMembership, support⟩
        · exact ⟨inner.fill left,
            Or.inr (Or.inl rfl),
            inductionHypothesis.mpr support⟩
        · exact ⟨argument,
            Or.inr (Or.inr afterMembership),
            support⟩
  | lambda binder inner inductionHypothesis =>
      simpa [OneHoleContext.fill, Pattern.freeFvarNames] using
        inductionHypothesis
  | multiLambda arity binders inner inductionHypothesis =>
      simpa [OneHoleContext.fill, Pattern.freeFvarNames] using
        inductionHypothesis
  | substBody inner replacement inductionHypothesis =>
      simp [OneHoleContext.fill, Pattern.freeFvarNames,
        inductionHypothesis]
  | substReplacement body inner inductionHypothesis =>
      simp [OneHoleContext.fill, Pattern.freeFvarNames,
        inductionHypothesis]
  | collection collectionType before inner after rest inductionHypothesis =>
      simp only [OneHoleContext.fill, Pattern.freeFvarNames,
        List.mem_append, List.mem_flatMap, List.mem_cons]
      constructor
      · rintro (⟨element, membership, support⟩ | restSupport)
        · rcases membership with beforeMembership | (rfl | afterMembership)
          · exact Or.inl ⟨element,
              Or.inl beforeMembership, support⟩
          · exact Or.inl ⟨inner.fill right,
              Or.inr (Or.inl rfl),
              inductionHypothesis.mp support⟩
          · exact Or.inl ⟨element,
              Or.inr (Or.inr afterMembership),
              support⟩
        · exact Or.inr restSupport
      · rintro (⟨element, membership, support⟩ | restSupport)
        · rcases membership with beforeMembership | (rfl | afterMembership)
          · exact Or.inl ⟨element,
              Or.inl beforeMembership, support⟩
          · exact Or.inl ⟨inner.fill left,
              Or.inr (Or.inl rfl),
              inductionHypothesis.mpr support⟩
          · exact Or.inl ⟨element,
              Or.inr (Or.inr afterMembership),
              support⟩
        · exact Or.inr restSupport

private theorem rho_costEquationContextStep_mem_freeFvarNames_iff
    {left right : Pattern}
    (step : ReflectiveEquationSemantics.ReflectiveEquationContextStep
      rhoCIGSLT.costWholeReflectionProfile defaultBasePremises
      rhoCIGSLT.costWholeLanguage left right)
    (name : String) :
    name ∈ left.freeFvarNames ↔ name ∈ right.freeFvarNames := by
  cases step with
  | core coreStep =>
      cases coreStep with
      | @inContext context redex contractum instanceWitness =>
          obtain ⟨declaration, representatives⟩ : ∃ declaration,
              Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
                  declaration redex =
                Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
                  declaration contractum := by
            rcases instanceWitness with ⟨fuel, bounded⟩ | derived
            · obtain ⟨declaration, _membership, representatives⟩ :=
                CostCanonicalLaws.rho_costEquationInstanceAt_canonicalize_eq
                  bounded
              exact ⟨declaration, representatives⟩
            · exact ⟨_,
                CostCanonicalLaws.rho_costDerivedInstance_canonicalize_eq derived⟩
          apply mem_freeFvarNames_fill_iff_of_iff context name
          calc
            name ∈ redex.freeFvarNames ↔
                name ∈ (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
                  declaration redex).freeFvarNames :=
              (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.mem_freeFvarNames_canonicalize_iff
                declaration name redex).symm
            _ ↔ name ∈
                (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
                  declaration contractum).freeFvarNames := by rw [representatives]
            _ ↔ name ∈ contractum.freeFvarNames :=
              Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.mem_freeFvarNames_canonicalize_iff
                declaration name contractum
  | @reflectiveInContext context declaration redex contractum membership
      representatives =>
      apply mem_freeFvarNames_fill_iff_of_iff context name
      calc
        name ∈ redex.freeFvarNames ↔
            name ∈ (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
              declaration redex).freeFvarNames :=
          (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.mem_freeFvarNames_canonicalize_iff
            declaration name redex).symm
        _ ↔ name ∈
            (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
              declaration contractum).freeFvarNames := by rw [representatives]
        _ ↔ name ∈ contractum.freeFvarNames :=
          Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.mem_freeFvarNames_canonicalize_iff
            declaration name contractum

private theorem rho_costEquationEquiv_mem_freeFvarNames_iff
    {left right : Pattern}
    (equivalent : ReflectiveEquationSemantics.ReflectiveEquationEquiv
      rhoCIGSLT.costWholeReflectionProfile defaultBasePremises
      rhoCIGSLT.costWholeLanguage left right)
    (name : String) :
    name ∈ left.freeFvarNames ↔ name ∈ right.freeFvarNames := by
  induction equivalent with
  | rel left right step =>
      exact rho_costEquationContextStep_mem_freeFvarNames_iff step name
  | refl pattern => rfl
  | symm left right relation inductionHypothesis =>
      exact inductionHypothesis.symm
  | trans left middle right first second firstIH secondIH =>
      exact firstIH.trans secondIH

/-- The hereditary executor introduces no free-variable name.  This is a
semantic consequence of its unary generated-rho equation path: both the
ordinary and reflective Quote/Drop generators preserve the exact finite
free-name support through every enclosing context. -/
theorem rhoCostNormalizeOpenHereditary_preservesFreeVariableSupport
    {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
    {sort : LangSort rhoCIGSLT.costWholeLanguage}
    (term : ReflectiveWellSorted.OpenTerm
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      free bound sort)
    {name : String}
    (membership :
      name ∈ (rhoCostNormalizeOpenHereditary term).1.freeFvarNames) :
    name ∈ term.1.freeFvarNames :=
  (rho_costEquationEquiv_mem_freeFvarNames_iff
    (rhoCostNormalizeOpenHereditary_equationEquiv term) name).mp membership

/-! ### Boundary canary for finite-support factorization -/

private def rhoUnusedAmbientProbeName : String :=
  "__cost_unused_ambient_probe"

/-- A genuine extension of the cut-order fixture's free context by one name
that does not occur in either endpoint. -/
private def rhoCutOrderFreeWithUnusedAmbientProbe :
    WellSorted.FreeTypeContext :=
  fun name =>
    match CostGeneratorInvariantCounterexample.rhoCutOrderFree name with
    | some type => some type
    | none =>
        if name = rhoUnusedAmbientProbeName then
          some (.base costWrappedSortName)
        else
          none

private theorem rhoCutOrderFreeWithUnusedAmbientProbe_preserves
    {name : String} {freeType : TypeExpr}
    (lookup : CostGeneratorInvariantCounterexample.rhoCutOrderFree name =
      some freeType) :
    rhoCutOrderFreeWithUnusedAmbientProbe name = some freeType := by
  simp [rhoCutOrderFreeWithUnusedAmbientProbe, lookup]

private def rhoCutOrderLeftWithUnusedAmbientProbe :
    ReflectiveWellSorted.OpenTerm
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      rhoCutOrderFreeWithUnusedAmbientProbe []
      CostGeneratorInvariantCounterexample.rhoCutOrderWrappedProcSort :=
  CostGeneratorInvariantCounterexample.rhoCutOrderLeft.recontextualizeFree
    (fun _membership lookup =>
      rhoCutOrderFreeWithUnusedAmbientProbe_preserves lookup)

private def rhoCutOrderRightWithUnusedAmbientProbe :
    ReflectiveWellSorted.OpenTerm
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      rhoCutOrderFreeWithUnusedAmbientProbe []
      CostGeneratorInvariantCounterexample.rhoCutOrderWrappedProcSort :=
  CostGeneratorInvariantCounterexample.rhoCutOrderRight.recontextualizeFree
    (fun _membership lookup =>
      rhoCutOrderFreeWithUnusedAmbientProbe_preserves lookup)

private theorem rhoUnusedAmbientProbe_present :
    rhoCutOrderFreeWithUnusedAmbientProbe rhoUnusedAmbientProbeName ≠ none := by
  simp [rhoCutOrderFreeWithUnusedAmbientProbe, rhoUnusedAmbientProbeName,
    CostGeneratorInvariantCounterexample.rhoCutOrderFree,
    WellSorted.FreeTypeContext.ofList]

private theorem rhoUnusedAmbientProbe_not_mem_cutOrderLeft :
    rhoUnusedAmbientProbeName ∉
      rhoCutOrderLeftWithUnusedAmbientProbe.1.freeFvarNames := by
  change rhoUnusedAmbientProbeName ∉
    CostGeneratorInvariantCounterexample.rhoCutOrderLeftPattern.freeFvarNames
  simp [rhoUnusedAmbientProbeName,
    CostGeneratorInvariantCounterexample.rhoCutOrderLeftPattern,
    CostGeneratorInvariantCounterexample.rhoCutOrderParallel,
    CostGeneratorInvariantCounterexample.rhoCutOrderWrappedDrop,
    CostGeneratorInvariantCounterexample.rhoCutOrderRedex,
    CostGeneratorInvariantCounterexample.rhoCutOrderBaseQuote,
    CostGeneratorInvariantCounterexample.rhoCutOrderBaseDrop,
    Pattern.freeFvarNames]

private theorem rhoCutOrderRightWithUnusedAmbientProbe_ne_left :
    rhoCutOrderRightWithUnusedAmbientProbe.1 ≠
      rhoCutOrderLeftWithUnusedAmbientProbe.1 := by
  change CostGeneratorInvariantCounterexample.rhoCutOrderRightPattern ≠
    CostGeneratorInvariantCounterexample.rhoCutOrderLeftPattern
  simp [CostGeneratorInvariantCounterexample.rhoCutOrderRightPattern,
    CostGeneratorInvariantCounterexample.rhoCutOrderLeftPattern,
    CostGeneratorInvariantCounterexample.rhoCutOrderParallel,
    CostGeneratorInvariantCounterexample.rhoCutOrderWrappedDrop,
    CostGeneratorInvariantCounterexample.rhoCutOrderRedex,
    CostGeneratorInvariantCounterexample.rhoCutOrderBaseQuote,
    CostGeneratorInvariantCounterexample.rhoCutOrderBaseDrop]

/-- A deliberately context-sensitive negative control.  When the unused probe
is present it chooses a genuinely different inhabitant of the same typed rho
Cost fibre, when one exists.  This remains a valid `CostOpenNormalizer`, so
typing and output support alone cannot make finite-support factorization
automatic. -/
private noncomputable def rhoUnusedAmbientSensitiveNormalizer :
    CostOpenNormalizer rhoCIGSLT := by
  classical
  exact fun {targetFree targetBound targetSort} term =>
    if targetFree rhoUnusedAmbientProbeName = none then
      term
    else if alternatives : ∃ candidate : ReflectiveWellSorted.OpenTerm
        rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
        targetFree targetBound targetSort,
        candidate.1 ≠ term.1 then
      Classical.choose alternatives
    else
      term

private theorem rhoUnusedAmbientSensitiveNormalizer_changes_of_alternative
    {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
    {sort : LangSort rhoCIGSLT.costWholeLanguage}
    (term : ReflectiveWellSorted.OpenTerm
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      free bound sort)
    (present : free rhoUnusedAmbientProbeName ≠ none)
    (alternatives : ∃ candidate : ReflectiveWellSorted.OpenTerm
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      free bound sort, candidate.1 ≠ term.1) :
    (rhoUnusedAmbientSensitiveNormalizer term).1 ≠ term.1 := by
  classical
  unfold rhoUnusedAmbientSensitiveNormalizer
  rw [if_neg present, dif_pos alternatives]
  exact Classical.choose_spec alternatives

/-- Negative control: a polymorphic, well-typed normalizer need not factor
through finite free support.  The two executions receive the same raw input
and agree on every used free name; only the unused probe differs. -/
theorem rhoUnusedAmbientSensitiveNormalizer_not_factorsThroughFreeSupport :
    ¬ CostOpenNormalizerFactorsThroughFreeSupport rhoCIGSLT
      rhoUnusedAmbientSensitiveNormalizer := by
  classical
  intro factors
  let left := rhoCutOrderLeftWithUnusedAmbientProbe
  let right := rhoCutOrderRightWithUnusedAmbientProbe
  have alternatives : ∃ candidate : ReflectiveWellSorted.OpenTerm
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      rhoCutOrderFreeWithUnusedAmbientProbe []
      CostGeneratorInvariantCounterexample.rhoCutOrderWrappedProcSort,
      candidate.1 ≠ left.1 :=
    ⟨right, rhoCutOrderRightWithUnusedAmbientProbe_ne_left⟩
  have changes : (rhoUnusedAmbientSensitiveNormalizer left).1 ≠ left.1 :=
    rhoUnusedAmbientSensitiveNormalizer_changes_of_alternative left
      rhoUnusedAmbientProbe_present alternatives
  have probeAbsent :
      (rhoCutOrderFreeWithUnusedAmbientProbe.restrictTo
        left.1.freeFvarNames) rhoUnusedAmbientProbeName = none := by
    unfold WellSorted.FreeTypeContext.restrictTo
    rw [if_neg]
    simpa [left] using rhoUnusedAmbientProbe_not_mem_cutOrderLeft
  have restrictedIsInput :
      (@rhoUnusedAmbientSensitiveNormalizer
        (rhoCutOrderFreeWithUnusedAmbientProbe.restrictTo
          left.1.freeFvarNames) []
        CostGeneratorInvariantCounterexample.rhoCutOrderWrappedProcSort
        left.restrictFreeContext).1 = left.1 := by
    simp only [rhoUnusedAmbientSensitiveNormalizer, probeAbsent, if_pos,
      ReflectiveWellSorted.OpenTerm.restrictFreeContext_pattern]
  have factored := factors left
  apply changes
  exact factored.symm.trans restrictedIsInput

/-! ### The finite-support hereditary executor -/

/-- The hereditary executor with its coeffect boundary made explicit.
Only the finite free-variable support of the input is presented to the
region compiler.  The checked result is then recontextualized into the
caller's ambient context without changing its raw pattern. -/
def rhoCostNormalizeOpenHereditarySupported : CostOpenNormalizer rhoCIGSLT :=
  fun {targetFree targetBound targetSort} term => by
    let restricted := term.restrictFreeContext
    let normalized := rhoCostNormalizeOpenHereditary restricted
    refine normalized.recontextualizeFree (fun _membership lookup => ?_)
    unfold WellSorted.FreeTypeContext.restrictTo at lookup
    split at lookup
    · exact lookup
    · contradiction

@[simp]
theorem rhoCostNormalizeOpenHereditarySupported_pattern
    {targetFree : WellSorted.FreeTypeContext}
    {targetBound : List TypeExpr}
    {targetSort : LangSort rhoCIGSLT.costWholeLanguage}
    (term : ReflectiveWellSorted.OpenTerm
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      targetFree targetBound targetSort) :
    (rhoCostNormalizeOpenHereditarySupported term).1 =
      (rhoCostNormalizeOpenHereditary term.restrictFreeContext).1 :=
  rfl

/-- Restricting a finite free context to the same support a second time is
idempotent. -/
private theorem restrictTo_idempotent
    (free : WellSorted.FreeTypeContext) (names : List String) :
    (free.restrictTo names).restrictTo names = free.restrictTo names := by
  funext name
  by_cases membership : name ∈ names <;>
    simp [WellSorted.FreeTypeContext.restrictTo, membership]

/-- The supported hereditary executor is structurally independent of unused
ambient free-context entries.  No compiler parametricity assumption is
needed: both executions run in the same finite restricted context. -/
theorem rhoCostNormalizeOpenHereditarySupported_factorsThroughFreeSupport :
    CostOpenNormalizerFactorsThroughFreeSupport rhoCIGSLT
      rhoCostNormalizeOpenHereditarySupported := by
  intro free bound sort term
  let once := term.restrictFreeContext
  let twice := once.restrictFreeContext
  have contextEquality :
      (free.restrictTo term.1.freeFvarNames).restrictTo
          term.1.freeFvarNames =
        free.restrictTo term.1.freeFvarNames :=
    restrictTo_idempotent free term.1.freeFvarNames
  have termEquality : twice.reindex contextEquality rfl rfl = once := by
    apply Subtype.ext
    simp [twice, once]
  have normalizationTransport :=
    CostOpenNormalizer.reindexFree_pattern
      (source := rhoCIGSLT) rhoCostNormalizeOpenHereditary
      contextEquality twice
  rw [rhoCostNormalizeOpenHereditarySupported_pattern,
    rhoCostNormalizeOpenHereditarySupported_pattern]
  change (rhoCostNormalizeOpenHereditary twice).1 =
    (rhoCostNormalizeOpenHereditary once).1
  calc
    (rhoCostNormalizeOpenHereditary twice).1 =
        (rhoCostNormalizeOpenHereditary
          (twice.reindex contextEquality rfl rfl)).1 :=
      normalizationTransport.symm
    _ = (rhoCostNormalizeOpenHereditary once).1 := by
      exact congrArg (fun restricted =>
        (rhoCostNormalizeOpenHereditary restricted).1) termEquality

/-- The supported hereditary executor introduces no free-variable name.  The
finite-context restriction changes only typing evidence, so the established
raw hereditary support theorem applies without an additional compiler law. -/
theorem rhoCostNormalizeOpenHereditarySupported_preservesFreeVariableSupport
    {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
    {sort : LangSort rhoCIGSLT.costWholeLanguage}
    (term : ReflectiveWellSorted.OpenTerm
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      free bound sort)
    {name : String}
    (membership : name ∈
      (rhoCostNormalizeOpenHereditarySupported term).1.freeFvarNames) :
    name ∈ term.1.freeFvarNames := by
  rw [rhoCostNormalizeOpenHereditarySupported_pattern] at membership
  exact rhoCostNormalizeOpenHereditary_preservesFreeVariableSupport
    term.restrictFreeContext membership

/-- The supported hereditary executor is sound in the caller's exact typed
open-equation fibre.  Soundness is first obtained in the finite restriction,
then every typed vertex of that path is recontextualized into the ambient
free context. -/
theorem rhoCostNormalizeOpenHereditarySupported_typed_openEquationSetoid
    {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
    {sort : LangSort rhoCIGSLT.costWholeLanguage}
    (term : ReflectiveWellSorted.OpenTerm
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      free bound sort) :
    (ReflectiveEquationSemantics.reflectiveOpenPatternEquationSetoid
      rhoCIGSLT.costWholeReflectionProfile defaultBasePremises
      rhoCIGSLT.costWholeLanguage free bound (.base sort.1)).r
      (rhoCostNormalizeOpenHereditarySupported term) term := by
  let restricted := term.restrictFreeContext
  have restrictedEquivalent :=
    rhoCostNormalizeOpenHereditary_typed_openEquationSetoid restricted
  have preservesLookup : ∀ {name freeType},
      (free.restrictTo term.1.freeFvarNames) name = some freeType →
        free name = some freeType := by
    intro name freeType lookup
    unfold WellSorted.FreeTypeContext.restrictTo at lookup
    split at lookup
    · exact lookup
    · contradiction
  have ambientEquivalent :=
    ReflectiveWellSorted.reflectiveOpenPatternEquationSetoid_recontextualizeFree
      (sourceFree := free.restrictTo term.1.freeFvarNames)
      (targetFree := free) preservesLookup restrictedEquivalent
  have normalizedEndpoint :
      ReflectiveWellSorted.OpenPattern.recontextualizeFree
          (rhoCostNormalizeOpenHereditary restricted)
          (fun _membership lookup => preservesLookup lookup) =
        rhoCostNormalizeOpenHereditarySupported term := by
    apply Subtype.ext
    rfl
  have inputEndpoint :
      ReflectiveWellSorted.OpenPattern.recontextualizeFree restricted
          (fun _membership lookup => preservesLookup lookup) = term := by
    apply Subtype.ext
    rfl
  simpa only [normalizedEndpoint, inputEndpoint] using ambientEquivalent

/-- Exact generator invariance of the hereditary tree executor descends to
the finite-support executor.  Each generator preserves the finite set of
free names, so both restricted endpoints inhabit one common typed fibre;
the final recontextualization changes no raw result. -/
theorem rhoCostNormalizeOpenHereditarySupported_generatorInvariant
    (invariant : CostOpenGeneratorInvariantFor rhoCIGSLT
      rhoCostNormalizeOpenHereditary) :
    CostOpenGeneratorInvariantFor rhoCIGSLT
      rhoCostNormalizeOpenHereditarySupported := by
  intro targetFree targetBound targetSort left right generator
  have supportIff : ∀ name,
      name ∈ left.1.freeFvarNames ↔ name ∈ right.1.freeFvarNames :=
    fun name => rho_costEquationContextStep_mem_freeFvarNames_iff generator name
  have restrictedContexts :
      targetFree.restrictTo right.1.freeFvarNames =
        targetFree.restrictTo left.1.freeFvarNames := by
    funext name
    by_cases rightMembership : name ∈ right.1.freeFvarNames
    · have leftMembership : name ∈ left.1.freeFvarNames :=
        (supportIff name).mpr rightMembership
      simp [WellSorted.FreeTypeContext.restrictTo, rightMembership,
        leftMembership]
    · have leftMembership : name ∉ left.1.freeFvarNames := by
        intro membership
        exact rightMembership ((supportIff name).mp membership)
      simp [WellSorted.FreeTypeContext.restrictTo, rightMembership,
        leftMembership]
  let rightRestrictedInLeft := right.restrictFreeContext.reindex
    restrictedContexts rfl rfl
  have restrictedGenerator :
      ReflectiveEquationSemantics.reflectiveOpenPatternEquationGenerator
        rhoCIGSLT.costWholeReflectionProfile defaultBasePremises
        rhoCIGSLT.costWholeLanguage
        (targetFree.restrictTo left.1.freeFvarNames) targetBound
        (.base targetSort.1) left.restrictFreeContext
        rightRestrictedInLeft := by
    unfold ReflectiveEquationSemantics.reflectiveOpenPatternEquationGenerator
      at generator ⊢
    simpa only [rightRestrictedInLeft,
      ReflectiveWellSorted.OpenTerm.restrictFreeContext_pattern,
      ReflectiveWellSorted.OpenTerm.reindex_pattern] using generator
  have restrictedEquality := invariant restrictedGenerator
  have restrictedPatternEquality := congrArg Subtype.val restrictedEquality
  have rightTransport := CostOpenNormalizer.reindexFree_pattern
    rhoCostNormalizeOpenHereditary restrictedContexts
      right.restrictFreeContext
  apply Subtype.ext
  rw [rhoCostNormalizeOpenHereditarySupported_pattern,
    rhoCostNormalizeOpenHereditarySupported_pattern]
  exact restrictedPatternEquality.trans rightTransport

/-- Finite-support factorization discharges the supported executor's exact
naturality under changes to unused ambient free-context entries. -/
theorem rhoCostNormalizeOpenHereditarySupported_normalizeRecontextualizeFree
    {sourceFree targetFree : WellSorted.FreeTypeContext}
    {bound : List TypeExpr}
    {sort : LangSort rhoCIGSLT.costWholeLanguage}
    (term : ReflectiveWellSorted.OpenTerm
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      sourceFree bound sort)
    (preserves : ∀ {name freeType},
      name ∈ term.1.freeFvarNames →
      sourceFree name = some freeType →
        targetFree name = some freeType) :
    (@rhoCostNormalizeOpenHereditarySupported targetFree bound sort
      (term.recontextualizeFree preserves)).1 =
      (@rhoCostNormalizeOpenHereditarySupported sourceFree bound sort term).1 :=
  rhoCostNormalizeOpenHereditarySupported_factorsThroughFreeSupport
    |>.normalizeRecontextualizeFree term preserves

/-- On object patterns, reflective supported substitution reads exactly the
finite free-name support of its input.  Collection-rest variables are absent
by object admission, which is why no unsubstituted side channel occurs. -/
private theorem mem_freeFvarNames_reflectiveSubstituteAt_iff
    (profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile)
    (support : ContextSupport.Support)
    (assignment : ContextSupport.Assignment) (outputName : String) :
    ∀ (availableDepth : Nat) (pattern : Pattern),
      WellSorted.isObjectPattern pattern = true →
      (outputName ∈
          (ReflectiveContextSupport.substituteAt profile support assignment
            availableDepth pattern).freeFvarNames ↔
        ∃ inputName, inputName ∈ pattern.freeFvarNames ∧
          outputName ∈ (assignment inputName).freeFvarNames) := by
  intro availableDepth pattern object
  induction pattern using Pattern.inductionOn generalizing availableDepth with
  | hbvar index =>
      simp [ReflectiveContextSupport.substituteAt, Pattern.freeFvarNames]
  | hfvar inputName =>
      simp only [ReflectiveContextSupport.substituteAt,
        Pattern.freeFvarNames, List.mem_singleton]
      rw [mem_freeFvarNames_liftBVars_iff]
      simp
  | happly constructor arguments inductionHypothesis =>
      have objects : WellSorted.isObjectPatternList arguments = true := by
        simpa [WellSorted.isObjectPattern] using object
      simp only [ReflectiveContextSupport.substituteAt,
        Pattern.freeFvarNames, List.mem_flatMap, List.mem_map]
      constructor
      · rintro ⟨normalized, ⟨argument, argumentMembership, rfl⟩,
          outputMembership⟩
        have argumentObject := isObjectPattern_of_mem_isObjectPatternList
          objects argumentMembership
        obtain ⟨inputName, inputMembership, outputMembership⟩ :=
          (inductionHypothesis argument argumentMembership _ argumentObject).mp
            outputMembership
        exact ⟨inputName, ⟨argument, argumentMembership, inputMembership⟩,
          outputMembership⟩
      · rintro ⟨inputName, ⟨argument, argumentMembership,
          inputMembership⟩, outputMembership⟩
        have argumentObject := isObjectPattern_of_mem_isObjectPatternList
          objects argumentMembership
        exact ⟨ReflectiveContextSupport.substituteAt profile support assignment
            (if ReflectiveContextSupport.isQuoteConstructor profile constructor
              then 0 else availableDepth) argument,
          ⟨argument, argumentMembership, rfl⟩,
          (inductionHypothesis argument argumentMembership _ argumentObject).mpr
            ⟨inputName, inputMembership, outputMembership⟩⟩
  | hlambda binder body inductionHypothesis =>
      have bodyObject : WellSorted.isObjectPattern body = true := by
        simpa [WellSorted.isObjectPattern] using object
      simpa [ReflectiveContextSupport.substituteAt, Pattern.freeFvarNames] using
        inductionHypothesis (availableDepth + 1) bodyObject
  | hmultiLambda arity binders body inductionHypothesis =>
      have bodyObject : WellSorted.isObjectPattern body = true := by
        simpa [WellSorted.isObjectPattern] using object
      simpa [ReflectiveContextSupport.substituteAt, Pattern.freeFvarNames] using
        inductionHypothesis (availableDepth + arity) bodyObject
  | hsubst body replacement bodyInduction replacementInduction =>
      simp [WellSorted.isObjectPattern] at object
  | hcollection collectionType elements rest inductionHypothesis =>
      have parts : rest.isNone = true ∧
          WellSorted.isObjectPatternList elements = true := by
        simpa [WellSorted.isObjectPattern] using object
      have restNone : rest = none := Option.isNone_iff_eq_none.mp parts.1
      subst rest
      simp only [ReflectiveContextSupport.substituteAt,
        Pattern.freeFvarNames, Option.toList_none, List.append_nil,
        List.mem_flatMap, List.mem_map]
      constructor
      · rintro ⟨normalized, ⟨element, elementMembership, rfl⟩,
          outputMembership⟩
        have elementObject := isObjectPattern_of_mem_isObjectPatternList
          parts.2 elementMembership
        obtain ⟨inputName, inputMembership, outputMembership⟩ :=
          (inductionHypothesis element elementMembership _ elementObject).mp
            outputMembership
        exact ⟨inputName, ⟨element, elementMembership, inputMembership⟩,
          outputMembership⟩
      · rintro ⟨inputName, ⟨element, elementMembership,
          inputMembership⟩, outputMembership⟩
        have elementObject := isObjectPattern_of_mem_isObjectPatternList
          parts.2 elementMembership
        exact ⟨ReflectiveContextSupport.substituteAt profile support assignment
            availableDepth element,
          ⟨element, elementMembership, rfl⟩,
          (inductionHypothesis element elementMembership _ elementObject).mpr
            ⟨inputName, inputMembership, outputMembership⟩⟩

/-- Rho already inhabits the general displayed Cost elaboration category.
This witness needs no normalization law: it is the checked region-tree
elaboration of an independently typed rho term. -/
def rhoCostElaborationTotal : CostElaborationTotal :=
  CostElaborationTotal.ofOpenTerm rhoCIGSLT
    CostGeneratorInvariantCounterexample.rhoCutOrderLeft

/-- The structural total category is concretely inhabited before the stronger
hereditary cost layer normalization package is assembled. -/
theorem nonempty_costElaborationTotal : Nonempty CostElaborationTotal :=
  ⟨rhoCostElaborationTotal⟩

/-- The concrete rho elaboration enters the retained semantic carrier whose
normalizer is already an exact section. -/
def rhoCostSemanticElaboration :
    CostSemanticElabTerm rhoCIGSLT
      rhoCostElaborationTotal.fiber.1.targetFree
      rhoCostElaborationTotal.fiber.1.targetBound
      rhoCostElaborationTotal.fiber.1.targetSort :=
  rhoCostElaborationTotal.toSemantic
    CostCanonicalLaws.rho_costTypedUnaryNormalizationLaws

/-- Rho's concrete executable decomposition reaches its semantic normal form
without passing through compact re-elaboration. -/
theorem rhoCostSemanticElaboration_normalizes :
    (CostSemanticOpenElaboration.equationSetoid rhoCIGSLT
      rhoCostElaborationTotal.fiber.1.targetFree
      rhoCostElaborationTotal.fiber.1.targetBound
      rhoCostElaborationTotal.fiber.1.targetSort).r
      (CostSemanticOpenElaboration.normalizeTerm rhoCostSemanticElaboration)
      rhoCostSemanticElaboration :=
  rhoCostElaborationTotal.toSemantic_normalizes
    CostCanonicalLaws.rho_costTypedUnaryNormalizationLaws

/-- Rho's hereditary static kernel preserves the constructor alphabet needed
by a further Cost layer.  The local proof remembers which source constructor
was transported and which of the two static colour maps transported it. -/
theorem rhoHereditaryStaticNormalizer_preservesWrappedConstructorSupport :
    CostStaticRegionNormalizerPreservesConstructorSupport rhoCIGSLT
      rhoHereditaryStaticNormalizer
      (· ∈ rhoCIGSLT.costContinuationRetyping.wrappedLabels) := by
  apply rhoHereditaryStaticNormalizer_preservesConstructorSupport_of
  intro color label image
  rcases image with ⟨sourceConstructor, sourceMembership, rfl⟩
  exact rhoCIGSLT.costStaticConstructorLabel_mem_costContinuationLabels_of_mem
    color sourceConstructor sourceMembership

/-- The complete child-first rho executor preserves proof-relevant typing in
the next-layer wrapped constructor fibre.  This is a whole-tree consequence
of the local static-kernel law, not an additional normalization algorithm. -/
theorem rhoCostNormalizeOpenHereditary_preservesWrappedConstructorTyping :
    ∀ {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
      {sort : LangSort rhoCIGSLT.costWholeLanguage}
      (term : ReflectiveWellSorted.OpenTerm
        rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
          free bound sort),
    WellSorted.HasTypeWithConstructors rhoCIGSLT.costWholeLanguage
        (· ∈ rhoCIGSLT.costContinuationRetyping.wrappedLabels)
        free bound term.1 (.base sort.1) →
      WellSorted.HasTypeWithConstructors rhoCIGSLT.costWholeLanguage
        (· ∈ rhoCIGSLT.costContinuationRetyping.wrappedLabels)
        free bound (rhoCostNormalizeOpenHereditary term).1 (.base sort.1) := by
  intro free bound sort term typed
  exact rhoCIGSLT.costNormalizeOpenWithStatic_preservesConstructorTyping
    rhoHereditaryStaticNormalizer
    rhoHereditaryStaticNormalizer_preservesWrappedConstructorSupport
    rhoCIGSLT.costBareCollectionConstructorsWrapped term typed

/-- The finite-support hereditary executor preserves the same wrapped
constructor fragment.  Restricting and restoring the free context changes
only typing evidence; the raw constructor inventory is retained exactly. -/
theorem rhoCostNormalizeOpenHereditarySupported_preservesWrappedConstructorTyping :
    ∀ {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
      {sort : LangSort rhoCIGSLT.costWholeLanguage}
      (term : ReflectiveWellSorted.OpenTerm
        rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
          free bound sort),
    WellSorted.HasTypeWithConstructors rhoCIGSLT.costWholeLanguage
        (· ∈ rhoCIGSLT.costContinuationRetyping.wrappedLabels)
        free bound term.1 (.base sort.1) →
      WellSorted.HasTypeWithConstructors rhoCIGSLT.costWholeLanguage
        (· ∈ rhoCIGSLT.costContinuationRetyping.wrappedLabels)
        free bound (rhoCostNormalizeOpenHereditarySupported term).1
          (.base sort.1) := by
  intro free bound sort term typed
  have restrictedTyped :
      WellSorted.HasTypeWithConstructors rhoCIGSLT.costWholeLanguage
        (· ∈ rhoCIGSLT.costContinuationRetyping.wrappedLabels)
        (free.restrictTo term.1.freeFvarNames) bound
        term.restrictFreeContext.1 (.base sort.1) :=
    term.restrictFreeContext.2.1.1.withConstructors
      typed.constructorsWithin
      rhoCIGSLT.costBareCollectionConstructorsWrapped
  have normalizedRestrictedTyped :=
    rhoCostNormalizeOpenHereditary_preservesWrappedConstructorTyping
      term.restrictFreeContext restrictedTyped
  exact (rhoCostNormalizeOpenHereditarySupported term).2.1.1.withConstructors
    normalizedRestrictedTyped.constructorsWithin
    rhoCIGSLT.costBareCollectionConstructorsWrapped

/-- The remaining whole-tree reflective coeffect obligation for rho's
finite-support hereditary executor. -/
def RhoHereditaryReflectiveSupportPreserving : Prop :=
  ∀ {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
    {sort : LangSort rhoCIGSLT.costWholeLanguage}
    (term : ReflectiveWellSorted.OpenTerm
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
        free bound sort)
    (support : ContextSupport.Support) (available : List TypeExpr)
    (binderImage : TypeExpr → TypeExpr),
  term.2.1.1.ReflectiveSupportSafeAt
      rhoCIGSLT.costWholeReflectionProfile support available binderImage →
    (rhoCostNormalizeOpenHereditarySupported term).2.1.1.ReflectiveSupportSafeAt
      rhoCIGSLT.costWholeReflectionProfile support available binderImage

/-- Assemble the actual finite-support rho cost layer object laws from the two
remaining semantic closure obligations.  All contextual free-name laws,
typed unary soundness, generator transport to the supported executor, and
wrapped-constructor preservation are discharged here. -/
def rhoHereditaryCompactOpenNormalizerLaws_of
    (alignable : CostOpenGeneratorTreeAlignable rhoCIGSLT
      rhoHereditaryNormalizationKernel)
    (preservesReflectiveSupport : RhoHereditaryReflectiveSupportPreserving) :
    Cost.CompactOpenNormalizer.Laws rhoCIGSLT
      rhoCostNormalizeOpenHereditarySupported where
  toCostOpenSectionLawsFor :=
    { toCostContextualOpenLawsFor :=
        { preservesFreeVariableSupport :=
            rhoCostNormalizeOpenHereditarySupported_preservesFreeVariableSupport
          normalizeRecontextualizeFree :=
            rhoCostNormalizeOpenHereditarySupported_normalizeRecontextualizeFree
          preservesReflectiveSupport := preservesReflectiveSupport }
      equivalent :=
        rhoCostNormalizeOpenHereditarySupported_typed_openEquationSetoid
      generatorInvariant :=
        rhoCostNormalizeOpenHereditarySupported_generatorInvariant (by
          intro targetFree targetBound targetSort left right generator
          exact
            CostOpenGeneratorInvariantFor.forCostNormalizeOpenWithStatic
              alignable rhoHereditaryCompactCoherent generator) }
  preservesWrappedConstructorTyping :=
    rhoCostNormalizeOpenHereditarySupported_preservesWrappedConstructorTyping

/-- The actual normalizer-indexed rho cost layer object, once the two remaining
semantic closure obligations are supplied.  The selected compact executor is
the finite-support hereditary executor; the retained semantic carrier keeps
the independently proved unary rho normalization laws. -/
def rhoHereditaryCostLayer_of
    (alignable : CostOpenGeneratorTreeAlignable rhoCIGSLT
      rhoHereditaryNormalizationKernel)
    (preservesReflectiveSupport : RhoHereditaryReflectiveSupportPreserving) :
    Cost.Layer where
  source := ⟨rhoCIGSLT⟩
  normalizeOpen := rhoCostNormalizeOpenHereditarySupported
  compactLaws := rhoHereditaryCompactOpenNormalizerLaws_of alignable
    preservesReflectiveSupport
  semanticLaws := CostCanonicalLaws.rho_costTypedUnaryNormalizationLaws

/-- The concrete rho retained elaboration over the actual hereditary cost layer
object.  This is the total-space endpoint of the construction: the original
checked region tree is retained verbatim above the normalizer-indexed base. -/
def rhoHereditaryCostElaborationTotal_of
    (alignable : CostOpenGeneratorTreeAlignable rhoCIGSLT
      rhoHereditaryNormalizationKernel)
    (preservesReflectiveSupport : RhoHereditaryReflectiveSupportPreserving) :
    Cost.Elaboration.Total where
  base := ⟨rhoHereditaryCostLayer_of alignable
    preservesReflectiveSupport⟩
  fiber := rhoCostElaborationTotal.fiber

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
