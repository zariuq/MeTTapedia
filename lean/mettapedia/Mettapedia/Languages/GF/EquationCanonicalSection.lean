import Mettapedia.GSLT.LanguageDef.CanonicalSection
import Mettapedia.Languages.GF.OSLFBridge_handcrafted
import Mettapedia.OSLF.MeTTaIL.MatchSpec

/-!
# Canonical representatives for the GF equation theory

The GF presentation declares one equation, `UseN(x) = x`.  This module
computes representatives of its contextual congruence by recursively removing
exactly unary `UseN` constructors.  Other GF identity wrappers are directed
rewrites and are deliberately not erased here.

The normalization proof connects the executable representative function to
the equation relation generated from the `LanguageDef`; it is used by
equation-invariant evidence observations without introducing a second GF
semantics.
-/

namespace Mettapedia.Languages.GF.EquationCanonicalSection

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.LogicSemantics
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.Languages.GF.OSLFBridge

/-- Remove exactly the unary `UseN` constructors declared equal to their
argument by the GF presentation. -/
def normalizeUseN : Pattern → Pattern
  | .fvar name => .fvar name
  | .bvar index => .bvar index
  | .apply constructor arguments =>
      let normalized := arguments.map normalizeUseN
      match normalized with
      | [argument] =>
          if constructor = "UseN" then argument
          else .apply constructor [argument]
      | _ => .apply constructor normalized
  | .lambda name body => .lambda name (normalizeUseN body)
  | .multiLambda arity names body =>
      .multiLambda arity names (normalizeUseN body)
  | .subst body replacement =>
      .subst (normalizeUseN body) (normalizeUseN replacement)
  | .collection collectionType elements rest =>
      .collection collectionType (elements.map normalizeUseN) rest

@[simp] theorem normalizeUseN_unary (argument : Pattern) :
    normalizeUseN (.apply "UseN" [argument]) = normalizeUseN argument := by
  simp [normalizeUseN]

/-- Equal normalized holes remain equal after insertion into an arbitrary
structural one-hole context. -/
theorem normalizeUseN_fill_congr (context : OneHoleContext)
    {left right : Pattern} (equal : normalizeUseN left = normalizeUseN right) :
    normalizeUseN (context.fill left) =
      normalizeUseN (context.fill right) := by
  induction context with
  | hole => exact equal
  | apply constructor before inner after inductionHypothesis =>
      simp only [OneHoleContext.fill, normalizeUseN, List.map_append,
        List.map_cons]
      rw [inductionHypothesis]
  | lambda name inner inductionHypothesis =>
      simp only [OneHoleContext.fill, normalizeUseN]
      rw [inductionHypothesis]
  | multiLambda arity names inner inductionHypothesis =>
      simp only [OneHoleContext.fill, normalizeUseN]
      rw [inductionHypothesis]
  | substBody inner replacement inductionHypothesis =>
      simp only [OneHoleContext.fill, normalizeUseN]
      rw [inductionHypothesis]
  | substReplacement body inner inductionHypothesis =>
      simp only [OneHoleContext.fill, normalizeUseN]
      rw [inductionHypothesis]
  | collection collectionType before inner after rest inductionHypothesis =>
      simp only [OneHoleContext.fill, normalizeUseN, List.map_append,
        List.map_cons]
      rw [inductionHypothesis]

private theorem normalizeUseN_equationInstance
    {source target : Pattern}
    (instanceWitness :
      EquationInstance (engineBasePremises RelationEnv.empty)
        gfLegacySemanticLanguageDef source target) :
    normalizeUseN source = normalizeUseN target := by
  obtain ⟨fuel, boundedWitness⟩ := instanceWitness
  cases boundedWitness with
  | @forward equation _ _ initialBindings finalBindings equationMembership
      matchMembership premises application =>
      have equationEquality : equation = useNIdentityEquation := by
        change equation ∈ [useNIdentityEquation] at equationMembership
        simpa using equationMembership
      subst equationEquality
      cases premises with
      | nil =>
          have sourceEquality := matchPattern_correct matchMembership (by rfl)
          calc
            normalizeUseN source =
                normalizeUseN
                  (applyBindings initialBindings useNIdentityEquation.left) :=
              congrArg normalizeUseN sourceEquality.symm
            _ = normalizeUseN
                  (applyBindings initialBindings useNIdentityEquation.right) := by
              simp [useNIdentityEquation, applyBindings]
            _ = normalizeUseN target := congrArg normalizeUseN application
  | @reverse equation _ _ initialBindings finalBindings equationMembership
      matchMembership premises application =>
      have equationEquality : equation = useNIdentityEquation := by
        change equation ∈ [useNIdentityEquation] at equationMembership
        simpa using equationMembership
      subst equationEquality
      cases premises with
      | nil =>
          have sourceEquality := matchPattern_correct matchMembership (by rfl)
          calc
            normalizeUseN source =
                normalizeUseN
                  (applyBindings initialBindings useNIdentityEquation.right) :=
              congrArg normalizeUseN sourceEquality.symm
            _ = normalizeUseN
                  (applyBindings initialBindings useNIdentityEquation.left) := by
              simp [useNIdentityEquation, applyBindings]
            _ = normalizeUseN target := congrArg normalizeUseN application

/-- The GF presentation declares no bag, so no permutation law is generated. -/
private theorem gfLegacySemanticLanguageDef_no_bags :
    gfLegacySemanticLanguageDef.usesCollection .hashBag = false := by
  decide +kernel

/-- The GF presentation declares no set, so no idempotence law is generated. -/
private theorem gfLegacySemanticLanguageDef_no_sets :
    gfLegacySemanticLanguageDef.usesCollection .hashSet = false := by
  decide +kernel

/-- The GF presentation declares no collection algebra. -/
private theorem gfLegacySemanticLanguageDef_no_algebra :
    gfLegacySemanticLanguageDef.hasAlgebraDeclarations = false := by
  decide +kernel

/-- Every generated contextual GF equation preserves the computed
representative. -/
theorem normalizeUseN_equationContextStep
    {source target : Pattern}
    (step : EquationContextStep (engineBasePremises RelationEnv.empty)
      gfLegacySemanticLanguageDef source target) :
    normalizeUseN source = normalizeUseN target := by
  cases step with
  | inContext context generator =>
      rcases generator with instanceWitness | derivedWitness
      · exact normalizeUseN_fill_congr context
          (normalizeUseN_equationInstance instanceWitness)
      · exact absurd derivedWitness
          (no_derivedInstance_of_no_derived_laws
            gfLegacySemanticLanguageDef_no_bags
            gfLegacySemanticLanguageDef_no_sets
            gfLegacySemanticLanguageDef_no_algebra _ _)

/-- Equivalent GF presentations have identical computed representatives. -/
theorem normalizeUseN_complete {left right : Pattern}
    (equivalent :
      EquationEquiv (engineBasePremises RelationEnv.empty)
        gfLegacySemanticLanguageDef left right) :
    normalizeUseN left = normalizeUseN right := by
  induction equivalent with
  | rel left right step => exact normalizeUseN_equationContextStep step
  | refl pattern => rfl
  | symm left right relation inductionHypothesis =>
      exact inductionHypothesis.symm
  | trans left middle right first second firstIH secondIH =>
      exact firstIH.trans secondIH

private theorem useN_equivalent (argument : Pattern) :
    EquationEquiv (engineBasePremises RelationEnv.empty)
      gfLegacySemanticLanguageDef (.apply "UseN" [argument]) argument := by
  apply equationInstance_equivalent
  refine ⟨0, EquationInstanceAt.forward
    (equation := useNIdentityEquation)
    (initialBindings := [("x", argument)])
    (finalBindings := [("x", argument)]) ?_ ?_ (.nil _) ?_⟩
  · exact .head _
  · simp [useNIdentityEquation, matchPattern, matchArgs, mergeBindings]
  · simp [useNIdentityEquation, applyBindings]

/-- Normalization remains in the original GF equation class. -/
theorem normalizeUseN_equivalent (term : Pattern) :
    EquationEquiv (engineBasePremises RelationEnv.empty)
      gfLegacySemanticLanguageDef (normalizeUseN term) term := by
  generalize measureEquality : sizeOf term = measure
  induction measure using Nat.strong_induction_on generalizing term with
  | h measure inductionHypothesis =>
    cases term with
    | fvar name =>
      simp only [normalizeUseN]
      exact Relation.EqvGen.refl _
    | bvar index =>
      simp only [normalizeUseN]
      exact Relation.EqvGen.refl _
    | apply constructor arguments =>
      have argumentSmaller (argument : Pattern) (member : argument ∈ arguments) :
          sizeOf argument < measure := by
        have inList := List.sizeOf_lt_of_mem member
        have listSmaller : sizeOf arguments <
            sizeOf (Pattern.apply constructor arguments) := by simp_wf
        omega
      have pointwise : List.Forall₂
          (EquationEquiv (engineBasePremises RelationEnv.empty)
            gfLegacySemanticLanguageDef)
          (arguments.map normalizeUseN) arguments := by
        rw [List.forall₂_map_left_iff]
        exact List.forall₂_same.mpr fun argument member =>
          inductionHypothesis (sizeOf argument)
            (argumentSmaller argument member) argument rfl
      cases arguments with
      | nil =>
          simpa only [normalizeUseN, List.map] using
            equationEquiv_apply_of_forall₂ constructor pointwise
      | cons argument tail =>
          cases tail with
          | nil =>
              by_cases isUseN : constructor = "UseN"
              · subst constructor
                rw [normalizeUseN_unary]
                change EquationEquiv (engineBasePremises RelationEnv.empty)
                  gfLegacySemanticLanguageDef (normalizeUseN argument)
                    (.apply "UseN" [argument])
                apply Relation.EqvGen.trans
                    (y := .apply "UseN" [normalizeUseN argument])
                · exact Relation.EqvGen.symm _ _
                    (useN_equivalent (normalizeUseN argument))
                · exact equationEquiv_apply_of_forall₂ "UseN" pointwise
              · simpa [normalizeUseN, isUseN] using
                  equationEquiv_apply_of_forall₂ constructor pointwise
          | cons second rest =>
              simpa [normalizeUseN] using
                equationEquiv_apply_of_forall₂ constructor pointwise
    | lambda name body =>
      have bodyIH := inductionHypothesis (sizeOf body) (by
        have bodySmaller : sizeOf body <
            sizeOf (Pattern.lambda name body) := by simp_wf
        omega) body rfl
      simpa [normalizeUseN, OneHoleContext.fill] using
        equationEquiv_fill (.lambda name .hole) bodyIH
    | multiLambda arity names body =>
      have bodyIH := inductionHypothesis (sizeOf body) (by
        have bodySmaller : sizeOf body <
            sizeOf (Pattern.multiLambda arity names body) := by simp_wf
        omega) body rfl
      simpa [normalizeUseN, OneHoleContext.fill] using
        equationEquiv_fill (.multiLambda arity names .hole) bodyIH
    | subst body replacement =>
      have bodyIH := inductionHypothesis (sizeOf body) (by
        have bodySmaller : sizeOf body <
            sizeOf (Pattern.subst body replacement) := by simp_wf; omega
        omega) body rfl
      have replacementIH := inductionHypothesis (sizeOf replacement) (by
        have replacementSmaller : sizeOf replacement <
            sizeOf (Pattern.subst body replacement) := by simp_wf
        omega) replacement rfl
      have first := equationEquiv_fill
        (.substBody .hole (normalizeUseN replacement)) bodyIH
      have second := equationEquiv_fill
        (.substReplacement body .hole) replacementIH
      apply Relation.EqvGen.trans
          (y := .subst body (normalizeUseN replacement))
      · simpa [EquationEquiv, normalizeUseN, OneHoleContext.fill] using first
      · simpa [EquationEquiv, OneHoleContext.fill] using second
    | collection collectionType elements rest =>
      have elementSmaller (element : Pattern) (member : element ∈ elements) :
          sizeOf element < measure := by
        have inList := List.sizeOf_lt_of_mem member
        have listSmaller : sizeOf elements <
            sizeOf (Pattern.collection collectionType elements rest) := by
          simp_wf
          omega
        omega
      simp only [normalizeUseN]
      change EquationEquiv (engineBasePremises RelationEnv.empty)
        gfLegacySemanticLanguageDef
          (.collection collectionType (elements.map normalizeUseN) rest)
          (.collection collectionType elements rest)
      apply equationEquiv_collection_of_forall₂ collectionType rest
      rw [List.forall₂_map_left_iff]
      exact List.forall₂_same.mpr fun element member =>
        inductionHypothesis (sizeOf element)
          (elementSmaller element member) element rfl

/-- Computable representatives for the exact equation theory of the GF
language definition. -/
def gfEquationSection :
    ComputableSetoidSection Pattern
      (langGSLT gfLegacySemanticLanguageDef).equations where
  normalize := normalizeUseN
  equivalent := normalizeUseN_equivalent
  complete := normalizeUseN_complete

end Mettapedia.Languages.GF.EquationCanonicalSection
