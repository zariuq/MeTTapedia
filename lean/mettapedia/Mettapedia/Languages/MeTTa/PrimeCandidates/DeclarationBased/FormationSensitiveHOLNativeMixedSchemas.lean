import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.HOLNativeMixedConversionDevelopmentComplete
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.FormationSensitiveNativeIdentity
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.FormationSensitiveNativeRelatorEliminationPreservation

/-!
# Independently formed native schemas in the joint HOL/native environment

Level substitution and the already proved compatible signature inclusion
transport declaration and schema formation. Argument recovery remains an
operation on judgments in the joint system, using its proved Pi boundary;
an input need not have been typed in the smaller native source theory.
-/

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
namespace FormationSensitiveHOLNativeMixedSchemas

open Presentation Presentation.Declaration NativeIndexedFamilies RussellTarski
open IntrinsicMaps
open FormationSensitive
open FormationSensitiveHOLProofListIntegration (rules)

abbrev lowerTerm {n : Nat} (term : Tower.Tm n) :=
  substLevelsTm (sameLevelSubstitution Tower.zero) term
abbrev lowerContext {n : Nat} (context : Tower.Ctx n) :=
  substLevelsCtx (sameLevelSubstitution Tower.zero) context

abbrev Typing {n : Nat} (context : Tower.Ctx n) (term type : Tower.Tm n) :=
  FormationSensitive.Typing rules context term type

theorem universes : UniverseRegularity rules :=
  (towerUniverseRegularity.includeSignature
    FormationSensitiveNativeHOLMapExecution.nativeInstance.signature).includeSignature
      FormationSensitiveHOLProofFamily.declarations

theorem heads : HeadPreservation rules :=
  HeadPreservation.includeSignature
    (base := FormationSensitiveNativeHOLMapExecution.nativeInstance.rules)
    (HeadPreservation.includeSignature towerHeadPreservation
      FormationSensitiveNativeHOLMapExecution.nativeInstance.signature)
    FormationSensitiveHOLProofFamily.declarations

theorem native_typed {n : Nat} {context : Tower.Ctx n} {term type : Tower.Tm n}
    (typed : FormationSensitive.Typing IntrinsicRelator.rules context term type) :
    Typing (lowerContext context) (lowerTerm term) (lowerTerm type) :=
  FormationSensitiveHOLProofListIntegration.execution_typed
    (FormationSensitiveNativeHOLMapExecution.native_typed typed)

theorem native_judgment {n : Nat} {context : Tower.Ctx n} {term type : Tower.Tm n}
    (judgment : Judgment IntrinsicRelator.rules context term type) :
    Judgment rules (lowerContext context) (lowerTerm term) (lowerTerm type) := by
  have formed := judgment.context.mapHead
    FormationSensitiveNativeHOLMapExecution.nativeInstance.morphism
  have included := formed.mapHead
    (includeMorphism FormationSensitiveNativeHOLMapExecution.nativeInstance.rules
      FormationSensitiveHOLProofFamily.declarations)
  exact ⟨by simpa only [Ctx.mapHead_id, lowerContext, substLevelsCtx,
    FormationSensitiveHOLProofListIntegration.rules] using included, native_typed judgment.typing⟩

theorem schema_substitute {n k : Nat}
    {schemaContext : Tower.Ctx k} {term type : Tower.Tm k}
    (judgment : Judgment IntrinsicRelator.rules schemaContext term type)
    {context : Tower.Ctx n} {substitution : Sub Tower.Head k n}
    (formed : ContextFormation rules context)
    (arguments : FormationSensitive.CtxMor rules (lowerContext schemaContext) context substitution) :
    Judgment rules context (subst substitution (lowerTerm term))
      (subst substitution (lowerTerm type)) :=
  (native_judgment judgment).substitute formed arguments

theorem nativeSpine {n : Nat} (context : Tower.Ctx n) {name : DeclName}
    {type : Tower.Tm 0} {universeHead : Tower.Head}
    (known : IntrinsicRelator.rules.constantType name = some type)
    (formed : FormationSensitive.Typing IntrinsicRelator.rules .nil type (.head universeHead))
    (isUniverse : IntrinsicRelator.rules.isUniverse universeHead) :
    DeclarationSpine rules context (.const name) (liftClosed (lowerTerm type)) := by
  apply DeclarationSpine.constant
  · have first := FormationSensitiveNativeHOLMapExecution.nativeInstance.morphism.constantType known
    have second := (includeMorphism FormationSensitiveNativeHOLMapExecution.nativeInstance.rules
      FormationSensitiveHOLProofFamily.declarations).constantType first
    simpa only [Tm.mapHead_id, lowerTerm, substLevelsTm,
      FormationSensitiveHOLProofListIntegration.rules] using second
  · exact native_typed formed
  · exact FormationSensitiveNativeHOLMapExecution.nativeInstance.morphism.isUniverse isUniverse

#print axioms universes
#print axioms heads
#print axioms native_typed
#print axioms native_judgment
#print axioms schema_substitute
#print axioms nativeSpine

end FormationSensitiveHOLNativeMixedSchemas
end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
