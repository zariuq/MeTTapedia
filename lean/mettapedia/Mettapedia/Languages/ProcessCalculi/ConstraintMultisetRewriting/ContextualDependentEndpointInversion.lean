import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentCheckingReplay
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSupport

/-!
# Recovering both a normal value and its dependent annotation

The annotation is inverted first. Its universe witness comes from the typed
input, and checking reflection reconstructs its formation in the selected
context. The value is then inverted and typed at that recovered annotation.
Only two raw inversions execute; no source annotation or checker budget is
supplied by the caller.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentEndpointInversion

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentNormalChecking ContextualDependentTypedInversion ContextualDependentEta

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

structure Recovered {source target : Context S.R} (inclusion : Inclusion source target) (original : TotalTerm target) where
  value : TotalTerm source
  typeImage : Presentation.rename inclusion.forward value.1.code = original.1.code
  valueImage : Presentation.rename inclusion.forward value.2.code = original.2.code
  level : value.1.level = original.1.level

theorem Recovered.solves {source target : Context S.R} {inclusion : Inclusion source target}
    {original : TotalTerm target} (recovered : Recovered inclusion original) :
    (frames S.levels).E (recovered.value.reindex inclusion.hom) original := by
  constructor
  · change TypeEq S.R target.raw (subst (renSub inclusion.forward) recovered.value.1.code) original.1.code
    rw [subst_renSub, recovered.typeImage]
    exact original.1.isType.refl
  · change Equal S.R target.raw (subst (renSub inclusion.forward) recovered.value.2.code) original.2.code
      (subst (renSub inclusion.forward) recovered.value.1.code)
    rw [subst_renSub, subst_renSub, recovered.typeImage, recovered.valueImage]
    exact .refl original.2.typed

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R)
  (heads : HeadPreserving S.R) (algebra : CumulativeAlgebra S.R)
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)
  (complete : AlgorithmicComplete S.R S.roles) (declared : DeclaredTypesFormed S.R)
  (reflects : ContextualDependentReductionReflection.RootReflectsInjections S.R.computation)

def recover {source target : Context S.R} (inclusion : Inclusion source target)
    (compatible : CtxRen source.raw target.raw inclusion.forward) (original : TotalTerm target)
    (typeNormal : Normal (S := S) original.1.code) (valueNormal : Normal (S := S) original.2.code) :
    Option (Recovered inclusion original) :=
  match typeFound : ContextualDependentInversion.invert (ContextualDependentInversion.lookup inclusion.forward) original.1.code with
  | none => none
  | some typeCode =>
      match valueFound : ContextualDependentInversion.invert (ContextualDependentInversion.lookup inclusion.forward) original.2.code with
      | none => none
      | some valueCode => some <| by
          have typeImage := ContextualDependentInversion.invert_sound original.1.code inclusion.forward _
            (ContextualDependentInversion.lookup_exact inclusion.forward inclusion.injective) typeCode typeFound
          have valueImage := ContextualDependentInversion.invert_sound original.2.code inclusion.forward _
            (ContextualDependentInversion.lookup_exact inclusion.forward inclusion.injective) valueCode valueFound
          have typeCertificate := ContextualDependentCheckingReplay.normal_certificate facts algebra headTypingUnique complete
            target.formed original.1.formed typeNormal
          have typeReflected := ContextualDependentCheckingReflection.checking_reflects reflects typeCertificate
            source.raw inclusion.forward inclusion.injective compatible typeCode (.head original.1.level) typeImage rfl
          have typeTyped : Typed S.R source.raw typeCode (.head original.1.level) :=
            CheckingAlgorithm.sound facts roots heads algebra declared typeReflected source.formed
              (universe_type (S := S) original.1.universeWitness)
          let annotation : TypeOver source := ⟨typeCode, original.1.level, original.1.universeWitness, typeTyped⟩
          have valueCertificate := ContextualDependentCheckingReplay.normal_certificate facts algebra headTypingUnique complete
            target.formed original.2.typed valueNormal
          have valueReflected := ContextualDependentCheckingReflection.checking_reflects reflects valueCertificate
            source.raw inclusion.forward inclusion.injective compatible valueCode typeCode valueImage typeImage
          let value : Term source annotation :=
            ⟨valueCode, CheckingAlgorithm.sound facts roots heads algebra declared valueReflected source.formed annotation.isType⟩
          exact ⟨⟨annotation, value⟩, typeImage, valueImage, rfl⟩

theorem success_iff {source target : Context S.R} (inclusion : Inclusion source target)
    (compatible : CtxRen source.raw target.raw inclusion.forward) (original : TotalTerm target)
    (typeNormal : Normal (S := S) original.1.code) (valueNormal : Normal (S := S) original.2.code) :
    (recover facts roots heads algebra headTypingUnique complete declared reflects
      inclusion compatible original typeNormal valueNormal).isSome = true ↔
      (ContextualDependentInversion.invert (ContextualDependentInversion.lookup inclusion.forward) original.1.code).isSome = true ∧
      (ContextualDependentInversion.invert (ContextualDependentInversion.lookup inclusion.forward) original.2.code).isSome = true := by
  unfold recover
  split
  · simp_all
  · split <;> simp_all

/-- The exact condition includes the annotation's dependencies as well as
the value's. The source type is reconstructed by the operation itself. -/
theorem success_iff_support {source target : Context S.R} (inclusion : Inclusion source target)
    (compatible : CtxRen source.raw target.raw inclusion.forward) (original : TotalTerm target)
    (typeNormal : Normal (S := S) original.1.code) (valueNormal : Normal (S := S) original.2.code) :
    (recover facts roots heads algebra headTypingUnique complete declared reflects
      inclusion compatible original typeNormal valueNormal).isSome = true ↔
      ∀ index ∈ original.1.code.support ∪ original.2.code.support, ∃ prior, inclusion.forward prior = index := by
  rw [success_iff, ContextualDependentSupport.invert_lookup_defined_iff inclusion.forward inclusion.injective,
    ContextualDependentSupport.invert_lookup_defined_iff inclusion.forward inclusion.injective]
  simp only [Finset.mem_union, or_imp, forall_and]

end ContextualDependentEndpointInversion
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
