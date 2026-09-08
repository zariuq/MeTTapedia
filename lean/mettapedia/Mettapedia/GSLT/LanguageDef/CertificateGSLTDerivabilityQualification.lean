import Mathlib.CategoryTheory.Whiskering
import Mettapedia.GSLT.LanguageDef.CertificateGSLTAuthorityFunctor
import Mettapedia.GSLT.LanguageDef.NIKDerivabilitySemanticQualification

/-!
# Factoring generated authority through derivability and semantic qualification

Functorial generation and independent semantic qualification are separate
pieces of structure.  A sound CertificateGSLT presentation generates an exact
native authority.  Applying the derivability-shadow endofunctor retains the
same generated claims, proof fibres, certificates, and checker, while replacing
the independent meaning predicate by native derivability itself.

The original rule-soundness proof then induces a natural transformation from
the derivability-only generation functor to the semantically qualified one.
Every component is operationally the identity; its mathematical content is the
proof that generated derivations preserve the independently supplied meaning.

This qualification is conservative exactly when the generated calculus is
semantically complete.  Thus exact checking, functorial transport, sound
semantic qualification, and semantic completeness remain four distinct
claims.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CertificateGSLTDerivabilityQualification

open CategoryTheory
open scoped CategoryTheory
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.CertifiedTheoryCategory
open Mettapedia.GSLT.LanguageDef.NIKHeterogeneousTheory
open Mettapedia.GSLT.LanguageDef.NIKMetalogic
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.GSLT.LanguageDef.CertificateGSLTAuthorityFunctor
open Mettapedia.GSLT.LanguageDef.NIKDerivabilitySemanticQualification

/-! ## The factorization -/

/-- Generate the native authority and then retain only its derivability
meaning.  This functor has exactly the same checker and certificate transport
as `generationFunctor`. -/
def derivabilityGenerationFunctor (Meaning : Pattern -> Prop) :
    CategoryTheory.Functor (SoundPresentation Meaning) CertifiedTheory :=
  CategoryTheory.Functor.comp (generationFunctor Meaning)
    derivabilityFunctor

/-- Rule soundness naturally qualifies every derivability-only generated
authority with the independently supplied meaning.  This is the componentwise
form of left-whiskering `semanticQualification` by `generationFunctor`; the
target identity functor is definitionally removed. -/
def generationSemanticQualification (Meaning : Pattern -> Prop) :
    derivabilityGenerationFunctor Meaning ⟶ generationFunctor Meaning :=
  { app := fun presentation => qualification (contract presentation)
    naturality := by
      intro source target interpretation
      exact semanticQualification.naturality
        ((generationFunctor Meaning).map interpretation) }

/-- At each presentation, the functor-level qualification is exactly the
authority-level qualification induced by generated scope soundness. -/
@[simp] theorem generationSemanticQualification_app
    {Meaning : Pattern -> Prop}
    (presentation : SoundPresentation Meaning) :
    (generationSemanticQualification Meaning).app presentation =
      qualification (contract presentation) := by
  rfl

/-- The qualification square commutes for every derivation-valued
interpretation of sound presentations. -/
theorem generationSemanticQualification_naturality
    {Meaning : Pattern -> Prop}
    {source target : SoundPresentation Meaning}
    (interpretation : source ⟶ target) :
    CategoryTheory.CategoryStruct.comp
        ((derivabilityGenerationFunctor Meaning).map interpretation)
        ((generationSemanticQualification Meaning).app target) =
      CategoryTheory.CategoryStruct.comp
        ((generationSemanticQualification Meaning).app source)
        ((generationFunctor Meaning).map interpretation) :=
  (generationSemanticQualification Meaning).naturality interpretation

/-! ## Exact operational agreement -/

/-- The derivability shadow and the qualified generated authority use the
identical checker on every claim and certificate. -/
theorem derivabilityGeneration_check_eq
    {Meaning : Pattern -> Prop}
    (presentation : SoundPresentation Meaning)
    (claim : Pattern)
    (certificate : (contract presentation).Certificate ()) :
    (((derivabilityGenerationFunctor Meaning).obj presentation).contract.checker
        ()).check claim certificate =
      ((contract presentation).checker ()).check claim certificate :=
  rfl

/-- Generated proof scope implies the independently supplied semantics.  This
is the content transported by the natural qualification, rather than a
consequence of checker acceptance defining meaning. -/
theorem generated_scope_is_meaningful
    {Meaning : Pattern -> Prop}
    (presentation : SoundPresentation Meaning)
    (claim : Pattern)
    (inScope : Nonempty
      ((cloneNativeProofSystem
        (derivationClone presentation.object)).ProofFibre claim)) :
    Meaning claim :=
  (theory presentation).scope_sound () claim inScope

/-! ## Soundness is not completeness -/

/-- The generated semantic qualification is conservative precisely when every
independently meaningful claim has a generated native derivation. -/
theorem generationQualification_conservative_iff
    {Meaning : Pattern -> Prop}
    (presentation : SoundPresentation Meaning) :
    (qualification (contract presentation)).toTheoryTranslation.Conservative ↔
      ∀ claim, Meaning claim -> Nonempty
        ((cloneNativeProofSystem
          (derivationClone presentation.object)).ProofFibre claim) := by
  rw [qualification_conservative_iff]
  constructor
  · intro complete claim meaningful
    exact complete () claim meaningful
  · intro complete kind claim meaningful
    cases kind
    exact complete claim meaningful

/-- A meaningful claim outside the generated proof fibre refutes
conservativity, even though the qualification remains sound and natural. -/
theorem generationQualification_not_conservative_of_semantic_gap
    {Meaning : Pattern -> Prop}
    (presentation : SoundPresentation Meaning)
    (claim : Pattern)
    (meaningful : Meaning claim)
    (outsideScope : ¬ Nonempty
      ((cloneNativeProofSystem
        (derivationClone presentation.object)).ProofFibre claim)) :
    ¬ ((generationSemanticQualification Meaning).app presentation).toTheoryTranslation.Conservative := by
  rw [generationSemanticQualification_app]
  exact qualification_not_conservative_of_semantic_gap
    (contract presentation) () claim meaningful outsideScope

#print axioms derivabilityGenerationFunctor
#print axioms generationSemanticQualification
#print axioms generationSemanticQualification_app
#print axioms generationSemanticQualification_naturality
#print axioms derivabilityGeneration_check_eq
#print axioms generated_scope_is_meaningful
#print axioms generationQualification_conservative_iff
#print axioms generationQualification_not_conservative_of_semantic_gap

end Mettapedia.GSLT.LanguageDef.CertificateGSLTDerivabilityQualification
