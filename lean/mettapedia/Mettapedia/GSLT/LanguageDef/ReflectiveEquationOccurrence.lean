import Mettapedia.GSLT.LanguageDef.EquationOccurrence
import Mettapedia.GSLT.LanguageDef.ReflectiveEquationSemantics

/-!
# Proof-relevant occurrences for a reflection extension

The five-field occurrence layer retains authored equation identity.  This
module adds the independently authored `ReflectionProfile` as an explicit
index and retains the selected reflective declaration when that extension
generates the step.
-/

namespace Mettapedia.GSLT.LanguageDef.ReflectiveEquationSemantics

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.Reflection
open Mettapedia.GSLT.LanguageDef.EquationSemantics

/-- A proof-relevant occurrence of either a five-field equation generator or
an explicitly profile-authorized reflective generator. -/
inductive ReflectiveAuthoredGeneratorWitness
    (profile : ReflectionProfile)
    (base : BasePremiseEvaluator) (language : LanguageDef) :
    Pattern → Pattern → Type where
  | core {left right : Pattern} :
      AuthoredGeneratorWitness base language left right →
      ReflectiveAuthoredGeneratorWitness profile base language left right
  | reflective (context : OneHoleContext)
      (declaration : { declaration : ReflectivePresentationDecl //
        declaration ∈ profile.presentations })
      {redex contractum : Pattern}
      (representatives : canonicalize declaration.1 redex =
        canonicalize declaration.1 contractum) :
      ReflectiveAuthoredGeneratorWitness profile base language
        (context.fill redex) (context.fill contractum)

namespace ReflectiveAuthoredGeneratorWitness

/-- Forget occurrence identity while retaining the explicit reflection
profile in the proposition-valued semantics. -/
def erase {profile : ReflectionProfile} {base : BasePremiseEvaluator}
    {language : LanguageDef} {left right : Pattern} :
    ReflectiveAuthoredGeneratorWitness profile base language left right →
      ReflectiveEquationContextStep profile base language left right
  | .core witness => .core witness.erase
  | .reflective context declaration representatives =>
      .reflectiveInContext context declaration.2 representatives

/-- Every proposition-valued reflective generator has a proof-relevant
occurrence above it. -/
theorem exists_erasing_to {profile : ReflectionProfile}
    {base : BasePremiseEvaluator} {language : LanguageDef}
    {left right : Pattern}
    (step : ReflectiveEquationContextStep profile base language left right) :
    ∃ occurrence : ReflectiveAuthoredGeneratorWitness
        profile base language left right,
      occurrence.erase = step := by
  cases step with
  | core step =>
      obtain ⟨occurrence, erases⟩ :=
        AuthoredGeneratorWitness.exists_erasing_to step
      refine ⟨.core occurrence, ?_⟩
      exact Subsingleton.elim _ _
  | @reflectiveInContext context declaration redex contractum membership
      representatives =>
      refine ⟨.reflective context ⟨declaration, membership⟩ representatives, ?_⟩
      exact Subsingleton.elim _ _

def redexContext {profile : ReflectionProfile}
    {base : BasePremiseEvaluator} {language : LanguageDef}
    {left right : Pattern} :
    ReflectiveAuthoredGeneratorWitness profile base language left right →
      OneHoleContext
  | .core witness => witness.redexContext
  | .reflective context _ _ => context

def redex {profile : ReflectionProfile} {base : BasePremiseEvaluator}
    {language : LanguageDef} {left right : Pattern} :
    ReflectiveAuthoredGeneratorWitness profile base language left right → Pattern
  | .core witness => witness.redex
  | .reflective _ _ (redex := redex) _ => redex

def contractum {profile : ReflectionProfile} {base : BasePremiseEvaluator}
    {language : LanguageDef} {left right : Pattern} :
    ReflectiveAuthoredGeneratorWitness profile base language left right → Pattern
  | .core witness => witness.contractum
  | .reflective _ _ (contractum := contractum) _ => contractum

@[simp] theorem redexContext_fill_redex
    {profile : ReflectionProfile} {base : BasePremiseEvaluator}
    {language : LanguageDef} {left right : Pattern}
    (witness : ReflectiveAuthoredGeneratorWitness
      profile base language left right) :
    witness.redexContext.fill witness.redex = left := by
  cases witness with
  | core witness => exact witness.redexContext_fill_redex
  | reflective => rfl

@[simp] theorem redexContext_fill_contractum
    {profile : ReflectionProfile} {base : BasePremiseEvaluator}
    {language : LanguageDef} {left right : Pattern}
    (witness : ReflectiveAuthoredGeneratorWitness
      profile base language left right) :
    witness.redexContext.fill witness.contractum = right := by
  cases witness with
  | core witness => exact witness.redexContext_fill_contractum
  | reflective => rfl

def isEquation {profile : ReflectionProfile} {base : BasePremiseEvaluator}
    {language : LanguageDef} {left right : Pattern} :
    ReflectiveAuthoredGeneratorWitness profile base language left right → Bool
  | .core _ => true
  | .reflective .. => false

end ReflectiveAuthoredGeneratorWitness

end Mettapedia.GSLT.LanguageDef.ReflectiveEquationSemantics
