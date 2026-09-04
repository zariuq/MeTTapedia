import Mettapedia.GSLT.LanguageDef.EquationSemantics
import Mettapedia.GSLT.LanguageDef.ReflectiveWellSorted
import Mettapedia.OSLF.MeTTaIL.ReflectionProfile
import Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical

/-!
# Equational semantics of a reflection extension

The five-field core generates `EquationEquiv` from authored equations alone.
This module adds canonical equality selected by an explicit
`ReflectionProfile`.  The separate relation makes the semantic dependency on
the extension visible and provides an exact embedding of the core relation.
-/

namespace Mettapedia.GSLT.LanguageDef.ReflectiveEquationSemantics

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.Reflection
open Mettapedia.GSLT.LanguageDef.EquationSemantics

/-- One core equation step or one profile-authorized canonical equality,
placed in a structural context. -/
inductive ReflectiveEquationContextStep
    (profile : ReflectionProfile)
    (base : BasePremiseEvaluator) (language : LanguageDef) :
    Pattern → Pattern → Prop where
  | core {left right : Pattern} :
      EquationContextStep base language left right →
      ReflectiveEquationContextStep profile base language left right
  | reflectiveInContext
      (context : OneHoleContext)
      {declaration : ReflectivePresentationDecl} {left right : Pattern} :
      List.Mem declaration profile.presentations →
      canonicalize declaration left = canonicalize declaration right →
      ReflectiveEquationContextStep profile base language
        (context.fill left) (context.fill right)

/-- Least contextual equivalence generated jointly by the five-field
equations and the explicitly attached reflection profile. -/
def ReflectiveEquationEquiv
    (profile : ReflectionProfile)
    (base : BasePremiseEvaluator) (language : LanguageDef) :
    Pattern → Pattern → Prop :=
  Relation.EqvGen (ReflectiveEquationContextStep profile base language)

def reflectiveEquationSetoid
    (profile : ReflectionProfile)
    (base : BasePremiseEvaluator) (language : LanguageDef) : Setoid Pattern where
  r := ReflectiveEquationEquiv profile base language
  iseqv :=
    ⟨Relation.EqvGen.refl,
      fun relation => Relation.EqvGen.symm _ _ relation,
      fun first second => Relation.EqvGen.trans _ _ _ first second⟩

/-- One reflective generator whose endpoints remain in one exact typed open
fibre. -/
def reflectiveOpenPatternEquationGenerator
    (profile : ReflectionProfile) (base : BasePremiseEvaluator)
    (language : LanguageDef) (free : WellSorted.FreeTypeContext)
    (bound : List TypeExpr) (type : TypeExpr)
    (left right : ReflectiveWellSorted.OpenPattern
      profile language free bound type) : Prop :=
  ReflectiveEquationContextStep profile base language left.1 right.1

/-- Reflective equation equivalence restricted to one exact typed open fibre. -/
def reflectiveOpenPatternEquationSetoid
    (profile : ReflectionProfile) (base : BasePremiseEvaluator)
    (language : LanguageDef) (free : WellSorted.FreeTypeContext)
    (bound : List TypeExpr) (type : TypeExpr) :
    Setoid (ReflectiveWellSorted.OpenPattern profile language free bound type) where
  r := fun left right =>
    Relation.EqvGen
      (reflectiveOpenPatternEquationGenerator profile base language free bound type)
      left right
  iseqv :=
    ⟨Relation.EqvGen.refl,
      fun relation => Relation.EqvGen.symm _ _ relation,
      fun first second => Relation.EqvGen.trans _ _ _ first second⟩

/-- Every generator authorized jointly by the five-field core and a
reflection profile preserves each exact reflective open fibre in both
directions.  Keeping this property on the explicit profile prevents
reflection-specific canonical equality from being attributed to the core
language. -/
def ReflectiveOpenEquationFiberStable
    (profile : ReflectionProfile) (base : BasePremiseEvaluator)
    (language : LanguageDef) : Prop :=
  ∀ {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
    {type : TypeExpr} {left right : Pattern},
    ReflectiveEquationContextStep profile base language left right →
      (ReflectiveWellSorted.OpenPatternWellSorted
          profile language free bound type left ↔
        ReflectiveWellSorted.OpenPatternWellSorted
          profile language free bound type right)

/-- Erasing typed fibre evidence retains the exact raw reflective
equivalence. -/
theorem reflectiveOpenPatternEquationSetoid_to_equiv
    {profile : ReflectionProfile} {base : BasePremiseEvaluator}
    {language : LanguageDef} {free : WellSorted.FreeTypeContext}
    {bound : List TypeExpr} {type : TypeExpr}
    {left right : ReflectiveWellSorted.OpenPattern
      profile language free bound type}
    (equivalent :
      (reflectiveOpenPatternEquationSetoid profile base language free bound type).r
        left right) :
    ReflectiveEquationEquiv profile base language left.1 right.1 := by
  change Relation.EqvGen
    (reflectiveOpenPatternEquationGenerator profile base language free bound type)
    left right at equivalent
  induction equivalent with
  | rel left right step => exact Relation.EqvGen.rel _ _ step
  | refl term => exact Relation.EqvGen.refl term.1
  | symm left right relation inductionHypothesis =>
      exact Relation.EqvGen.symm _ _ inductionHypothesis
  | trans left middle right first second firstIH secondIH =>
      exact Relation.EqvGen.trans _ _ _ firstIH secondIH

/-- Every core equation equivalence remains valid after attaching reflection. -/
theorem core_equivalent
    {profile : ReflectionProfile} {base : BasePremiseEvaluator}
    {language : LanguageDef} {left right : Pattern}
    (equivalent : EquationEquiv base language left right) :
    ReflectiveEquationEquiv profile base language left right := by
  induction equivalent with
  | rel left right step =>
      exact Relation.EqvGen.rel _ _ (.core step)
  | refl pattern => exact Relation.EqvGen.refl pattern
  | symm left right relation inductionHypothesis =>
      exact Relation.EqvGen.symm _ _ inductionHypothesis
  | trans left middle right first second firstIH secondIH =>
      exact Relation.EqvGen.trans _ _ _ firstIH secondIH

@[simp] theorem canonicalizeList_append
    (declaration : ReflectivePresentationDecl) (left right : List Pattern) :
    canonicalizeList declaration (left ++ right) =
      canonicalizeList declaration left ++ canonicalizeList declaration right := by
  induction left with
  | nil => rfl
  | cons pattern patterns inductionHypothesis =>
      simp only [List.cons_append, canonicalizeList, inductionHypothesis]

/-- Canonical equality is congruent under every structural one-hole context. -/
theorem canonicalize_fill_congr
    (declaration : ReflectivePresentationDecl) (context : OneHoleContext)
    {left right : Pattern}
    (representatives : canonicalize declaration left =
      canonicalize declaration right) :
    canonicalize declaration (context.fill left) =
      canonicalize declaration (context.fill right) := by
  induction context with
  | hole => exact representatives
  | apply constructor before inner after inductionHypothesis =>
      simp only [OneHoleContext.fill, canonicalize, canonicalizeList_append,
        canonicalizeList, inductionHypothesis]
  | lambda binderName inner inductionHypothesis =>
      simp only [OneHoleContext.fill, canonicalize, inductionHypothesis]
  | multiLambda arity binderNames inner inductionHypothesis =>
      simp only [OneHoleContext.fill, canonicalize, inductionHypothesis]
  | substBody inner replacement inductionHypothesis =>
      simp only [OneHoleContext.fill, canonicalize, inductionHypothesis]
  | substReplacement body inner inductionHypothesis =>
      simp only [OneHoleContext.fill, canonicalize, inductionHypothesis]
  | collection collectionType before inner after rest inductionHypothesis =>
      cases rest <;>
        simp only [OneHoleContext.fill, canonicalize, canonicalizeList_append,
          canonicalizeList, inductionHypothesis]

theorem equationInstance_equivalent
    {profile : ReflectionProfile} {base : BasePremiseEvaluator}
    {language : LanguageDef} {source target : Pattern}
    (equationWitness : EquationInstance base language source target) :
    ReflectiveEquationEquiv profile base language source target :=
  core_equivalent (EquationSemantics.equationInstance_equivalent equationWitness)

theorem equationInstance_fill_equivalent
    {profile : ReflectionProfile} {base : BasePremiseEvaluator}
    {language : LanguageDef} {source target : Pattern}
    (context : OneHoleContext)
    (equationWitness : EquationInstance base language source target) :
    ReflectiveEquationEquiv profile base language
      (context.fill source) (context.fill target) :=
  core_equivalent
    (EquationSemantics.equationInstance_fill_equivalent context equationWitness)

theorem reflective_fill_equivalent
    {profile : ReflectionProfile} {base : BasePremiseEvaluator}
    {language : LanguageDef}
    {declaration : ReflectivePresentationDecl} {left right : Pattern}
    (membership : List.Mem declaration profile.presentations)
    (context : OneHoleContext)
    (representatives : canonicalize declaration left =
      canonicalize declaration right) :
    ReflectiveEquationEquiv profile base language
      (context.fill left) (context.fill right) := by
  exact Relation.EqvGen.rel _ _
    (.reflectiveInContext context membership representatives)

theorem canonicalize_equationEquiv_self
    {profile : ReflectionProfile} {base : BasePremiseEvaluator}
    {language : LanguageDef} {declaration : ReflectivePresentationDecl}
    (membership : List.Mem declaration profile.presentations)
    (pattern : Pattern) :
    ReflectiveEquationEquiv profile base language
      (canonicalize declaration pattern) pattern := by
  exact Relation.EqvGen.rel _ _
    (.reflectiveInContext .hole membership
      (canonicalize_idempotent declaration pattern))

theorem equationEquiv_fill
    {profile : ReflectionProfile} {base : BasePremiseEvaluator}
    {language : LanguageDef}
    (context : OneHoleContext) {left right : Pattern}
    (equivalent : ReflectiveEquationEquiv profile base language left right) :
    ReflectiveEquationEquiv profile base language
      (context.fill left) (context.fill right) := by
  induction equivalent with
  | rel left right step =>
      apply Relation.EqvGen.rel
      cases step with
      | core coreStep =>
          exact .core (by
            cases coreStep with
            | inContext inner equationWitness =>
                simpa [OneHoleContext.fill_comp] using
                  (EquationContextStep.inContext (context.comp inner)
                    equationWitness))
      | reflectiveInContext inner membership representatives =>
          simpa [OneHoleContext.fill_comp] using
            (ReflectiveEquationContextStep.reflectiveInContext
              (context.comp inner) membership representatives)
  | refl pattern => exact Relation.EqvGen.refl (context.fill pattern)
  | symm left right relation inductionHypothesis =>
      exact Relation.EqvGen.symm _ _ inductionHypothesis
  | trans left middle right first second firstIH secondIH =>
      exact Relation.EqvGen.trans _ _ _ firstIH secondIH

theorem equationEquiv_apply_of_forall₂
    {profile : ReflectionProfile} {base : BasePremiseEvaluator}
    {language : LanguageDef} (constructor : String)
    {left right : List Pattern}
    (pointwise : List.Forall₂
      (ReflectiveEquationEquiv profile base language) left right) :
    ReflectiveEquationEquiv profile base language
      (.apply constructor left) (.apply constructor right) := by
  have withPrefix : ∀ pre,
      ReflectiveEquationEquiv profile base language
        (.apply constructor (pre ++ left))
        (.apply constructor (pre ++ right)) := by
    intro pre
    induction pointwise generalizing pre with
    | nil => exact Relation.EqvGen.refl _
    | @cons leftHead rightHead leftTail rightTail headEquivalent
        tailPointwise inductionHypothesis =>
        have headStep := equationEquiv_fill
          (.apply constructor pre .hole leftTail) headEquivalent
        have tailStep := inductionHypothesis (pre ++ [rightHead])
        exact Relation.EqvGen.trans _ _ _
          (by simpa [ReflectiveEquationEquiv, OneHoleContext.fill] using headStep)
          (by simpa [ReflectiveEquationEquiv, List.append_assoc] using tailStep)
  simpa using withPrefix []

theorem equationEquiv_collection_of_forall₂
    {profile : ReflectionProfile} {base : BasePremiseEvaluator}
    {language : LanguageDef} (collectionType : CollType)
    (rest : Option String) {left right : List Pattern}
    (pointwise : List.Forall₂
      (ReflectiveEquationEquiv profile base language) left right) :
    ReflectiveEquationEquiv profile base language
      (.collection collectionType left rest)
      (.collection collectionType right rest) := by
  have withPrefix : ∀ pre,
      ReflectiveEquationEquiv profile base language
        (.collection collectionType (pre ++ left) rest)
        (.collection collectionType (pre ++ right) rest) := by
    intro pre
    induction pointwise generalizing pre with
    | nil => exact Relation.EqvGen.refl _
    | @cons leftHead rightHead leftTail rightTail headEquivalent
        tailPointwise inductionHypothesis =>
        have headStep := equationEquiv_fill
          (.collection collectionType pre .hole leftTail rest) headEquivalent
        have tailStep := inductionHypothesis (pre ++ [rightHead])
        exact Relation.EqvGen.trans _ _ _
          (by simpa [ReflectiveEquationEquiv, OneHoleContext.fill] using headStep)
          (by simpa [ReflectiveEquationEquiv, List.append_assoc] using tailStep)
  simpa using withPrefix []

theorem equationEquiv_map_of_contextStep
    {sourceProfile targetProfile : ReflectionProfile}
    {base : BasePremiseEvaluator}
    {sourceLanguage targetLanguage : LanguageDef}
    (map : Pattern → Pattern)
    (generatorPreserves : ∀ {left right : Pattern},
      ReflectiveEquationContextStep sourceProfile base sourceLanguage left right →
      ReflectiveEquationEquiv targetProfile base targetLanguage
        (map left) (map right))
    {left right : Pattern}
    (equivalent : ReflectiveEquationEquiv sourceProfile base sourceLanguage
      left right) :
    ReflectiveEquationEquiv targetProfile base targetLanguage
      (map left) (map right) := by
  induction equivalent with
  | rel left right step => exact generatorPreserves step
  | refl pattern => exact Relation.EqvGen.refl (map pattern)
  | symm left right relation inductionHypothesis =>
      exact Relation.EqvGen.symm _ _ inductionHypothesis
  | trans left middle right first second firstIH secondIH =>
      exact Relation.EqvGen.trans _ _ _ firstIH secondIH

/-- With neither core equations nor reflective presentations, the extended
equivalence is exactly syntactic equality. -/
theorem equationEquiv_iff_eq_of_no_generators
    {profile : ReflectionProfile} {base : BasePremiseEvaluator}
    {language : LanguageDef}
    (equationFree : language.isEquationFree = true)
    (presentationsEmpty : profile.presentations = [])
    (source target : Pattern) :
    ReflectiveEquationEquiv profile base language source target ↔
      source = target := by
  have equationsEmpty := equations_eq_nil_of_isEquationFree equationFree
  constructor
  · intro equivalent
    induction equivalent with
    | rel left right step =>
        cases step with
        | core coreStep =>
            cases coreStep with
            | inContext context generator =>
                cases generator with
                | inl equationWitness =>
                    exact False.elim
                      (no_equationInstance_of_equations_eq_nil
                        equationsEmpty _ _ equationWitness)
                | inr derivedWitness =>
                    exact False.elim
                      (no_derivedInstance_of_isEquationFree
                        equationFree _ _ derivedWitness)
        | reflectiveInContext context membership representatives =>
            rw [presentationsEmpty] at membership
            cases membership
    | refl pattern => rfl
    | symm left right relation inductionHypothesis =>
        exact inductionHypothesis.symm
    | trans left middle right first second firstIH secondIH =>
        exact firstIH.trans secondIH
  · rintro rfl
    exact Relation.EqvGen.refl source

end Mettapedia.GSLT.LanguageDef.ReflectiveEquationSemantics
