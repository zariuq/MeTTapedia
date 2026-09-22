import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeWireRelatorCompatibility
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.OpaqueRelatorExtension

/-!
# Full preservation for opaque wire data with native List, J and relators

The five existing roots preserve arbitrary formation-sensitive source
judgments of the combined declaration package. This is the wire-data instance
of the opaque-extension theorem; it does not require source admission in the
old package. The closed mixed workload below uses actual new Data declarations
as native List contents and as the result of admitted J computation.

No new equations, K/UIP assumption, proof decoder, or evaluation policy is
introduced. Preservation does not assert model validity of every declaration.
-/

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
namespace NativeWireRelatorPreservation

open Presentation Presentation.Declaration NativeIndexedFamilies
open Presentation.FormationSensitive (Typing Judgment ContextFormation)
open NativeWireRelatorCompatibility

variable {n : Nat}

theorem wire_opacity : OpaqueRelatorExtension.Opacity NativeWireData.signature where
  values := wire_values_opaque
  roots := fun impossible => impossible.elim

theorem universes : FormationSensitive.UniverseRegularity rules :=
  OpaqueRelatorExtension.universes

theorem list_nil_preserves {context : Tower.Ctx n}
    (formed : ContextFormation rules context)
    {element motive nilCase consCase displayed : Tower.Tm n}
    (observed : Typing rules context
      (Intrinsic.eliminateApp element motive nilCase consCase (Intrinsic.nilApp element)) displayed) :
    Typing rules context nilCase displayed :=
  OpaqueRelatorExtension.list_nil_preserves (OpaqueRelatorExtension.pi_conversion_boundary wire_opacity) formed observed

theorem list_cons_preserves {context : Tower.Ctx n}
    (formed : ContextFormation rules context)
    {element motive nilCase consCase head tail displayed : Tower.Tm n}
    (observed : Typing rules context
      (Intrinsic.eliminateApp element motive nilCase consCase (Intrinsic.consApp element head tail))
      displayed) :
    Typing rules context
      (.app (.app (.app consCase head) tail)
        (Intrinsic.eliminateApp element motive nilCase consCase tail)) displayed :=
  OpaqueRelatorExtension.list_cons_preserves (OpaqueRelatorExtension.pi_conversion_boundary wire_opacity) formed observed

theorem identity_preserves {context : Tower.Ctx n}
    (formed : ContextFormation rules context)
    {element point motive reflCase displayed : Tower.Tm n}
    (observed : Typing rules context
      (Intrinsic.identityEliminateApp element point motive reflCase point (.refl point)) displayed) :
    Typing rules context reflCase displayed :=
  OpaqueRelatorExtension.identity_preserves (OpaqueRelatorExtension.pi_conversion_boundary wire_opacity) formed observed

theorem relator_nil_preserves {context : Tower.Ctx n}
    (formed : ContextFormation rules context)
    {source target relation motive nilCase consCase displayed : Tower.Tm n}
    (observed : Typing rules context
      (IntrinsicRelator.eliminateApp source target relation motive nilCase consCase
        (Intrinsic.nilApp source) (Intrinsic.nilApp target)
        (IntrinsicRelator.nilRelApp source target relation)) displayed) :
    Typing rules context nilCase displayed :=
  OpaqueRelatorExtension.relator_nil_preserves (OpaqueRelatorExtension.pi_conversion_boundary wire_opacity) formed observed

theorem relator_cons_preserves {context : Tower.Ctx n}
    (formed : ContextFormation rules context)
    {source target relation motive nilCase consCase sourceHead targetHead sourceTail
      targetTail headEvidence tailEvidence displayed : Tower.Tm n}
    (observed : Typing rules context
      (IntrinsicRelator.eliminateApp source target relation motive nilCase consCase
        (Intrinsic.consApp source sourceHead sourceTail)
        (Intrinsic.consApp target targetHead targetTail)
        (IntrinsicRelator.consRelApp source target relation sourceHead targetHead sourceTail
          targetTail headEvidence tailEvidence)) displayed) :
    Typing rules context
      (.app (.app (.app (.app (.app (.app (.app consCase sourceHead) targetHead) sourceTail)
        targetTail) headEvidence) tailEvidence)
        (IntrinsicRelator.eliminateApp source target relation motive nilCase consCase
          sourceTail targetTail tailEvidence)) displayed :=
  OpaqueRelatorExtension.relator_cons_preserves (OpaqueRelatorExtension.pi_conversion_boundary wire_opacity) formed observed

theorem root_preservation : FormationSensitive.RootPreservation rules :=
  OpaqueRelatorExtension.root_preservation wire_opacity

theorem step_preserves {context : Tower.Ctx n} {source target type : Tower.Tm n}
    (admitted : Judgment rules context source type)
    (step : Step rules.headEq source target rules.computation) :
    Judgment rules context target type :=
  OpaqueRelatorExtension.step_preserves wire_opacity admitted step

theorem steps_preserve {context : Tower.Ctx n} {source target type : Tower.Tm n}
    (admitted : Judgment rules context source type)
    (steps : ConversionCoherence.StepStar rules source target) :
    Judgment rules context target type :=
  OpaqueRelatorExtension.steps_preserve wire_opacity admitted steps

theorem checked_step_preserves {context : Tower.Ctx n} {source target type : Tower.Tm n}
    (admitted : Judgment rules context source type)
    {code : NativeRelatorConversionChecking.StepCode n}
    (checked : NativeRelatorConversionChecking.checkStep code source target = true) :
    Judgment rules context target type :=
  OpaqueRelatorExtension.checked_step_preserves wire_opacity admitted checked

theorem checked_step_inside_identity {context : Tower.Ctx n}
    {source target type : Tower.Tm n} (admitted : Judgment rules context source type)
    {code : NativeRelatorConversionChecking.StepCode n}
    (checked : NativeRelatorConversionChecking.checkStep code source target = true) :
    Judgment rules context (.refl target) (.id type source source) :=
  OpaqueRelatorExtension.checked_step_inside_identity wire_opacity admitted checked

/-! ## Closed mixed Data/List/J computation -/

/-- A Data-valued motive may inspect a native List point and its identity
evidence. This example chooses the constant motive, without identifying
encoded wire data with a native equality witness. -/
def dataMotive : Tower.Tm n := .lam (.lam NativeWireData.dataType)

/-- J is applied to a native singleton containing the original wire value.
Its reflexivity branch returns that same encoded value. -/
def mixedSource (wire : NativeWireData.Wire) : Tower.Tm 0 :=
  Intrinsic.identityEliminateApp (Intrinsic.listApp NativeWireData.dataType)
    (singleton wire) dataMotive (NativeWireData.encode wire)
    (singleton wire) (.refl (singleton wire))

def mixedResultType (wire : NativeWireData.Wire) : Tower.Tm 0 :=
  .app (.app dataMotive (singleton wire)) (.refl (singleton wire))

private def mixedPointSubstitution (wire : NativeWireData.Wire) : Sub Tower.Head 2 0 :=
  consSub (singleton wire)
    (Intrinsic.elementSchemaSubstitution (Intrinsic.listApp NativeWireData.dataType))

private theorem mixedPointSubstitution_typed (wire : NativeWireData.Wire) :
    FormationSensitive.CtxMor rules Intrinsic.contextAX .nil (mixedPointSubstitution wire) := by
  have empty : FormationSensitive.CtxMor rules .nil .nil Intrinsic.emptySchemaSubstitution :=
    fun index => Fin.elim0 index
  have element : FormationSensitive.CtxMor rules Intrinsic.contextA .nil
      (Intrinsic.elementSchemaSubstitution (Intrinsic.listApp NativeWireData.dataType)) :=
    empty.extend (list_data_formed .nil)
  exact element.extend (singleton_typed .nil wire)

private theorem dataMotive_typed (wire : NativeWireData.Wire) :
    Typing rules .nil dataMotive
      (subst (mixedPointSubstitution wire) Intrinsic.identityMotiveType) := by
  have formed : Typing rules .nil
      (subst (mixedPointSubstitution wire) Intrinsic.identityMotiveType)
      (sortTm Intrinsic.identityMotiveLevel) :=
    (relator_typing FormationSensitiveNativeIdentity.identityMotiveType_hasType).substitute
      (mixedPointSubstitution_typed wire)
  obtain ⟨_, _, _, _, _, innerFormed, innerUniverse, _⟩ := formed.piFormation
  exact .lamIntro formed (.sort Intrinsic.identityMotiveLevel)
    (.lamIntro innerFormed innerUniverse
      (.cumul (dataType_formed _) (fun _ => Nat.zero_le _)))

private theorem mixedMotiveSubstitution_typed (wire : NativeWireData.Wire) :
    FormationSensitive.CtxMor rules Intrinsic.contextAXP .nil
      (consSub dataMotive (mixedPointSubstitution wire)) :=
  (mixedPointSubstitution_typed wire).extend (dataMotive_typed wire)

theorem mixedResultType_formed (wire : NativeWireData.Wire) :
    Typing rules .nil (mixedResultType wire) (sortTm Intrinsic.motiveLevel) := by
  have formed :=
    (relator_typing FormationSensitiveNativeIdentity.identityReflCaseType_hasType).substitute
      (mixedMotiveSubstitution_typed wire)
  exact formed

theorem mixedResultType_conversion (wire : NativeWireData.Wire) :
    Conv rules.headEq (mixedResultType wire) NativeWireData.dataType rules.computation := by
  have first : Step rules.headEq (mixedResultType wire)
      (.app (.lam NativeWireData.dataType) (.refl (singleton wire))) rules.computation := by
    simpa [mixedResultType, dataMotive, NativeWireData.dataType, inst0, subst] using
      (Step.congAppFun
        (a := .refl (singleton wire))
        (Step.betaPi (root := rules.computation) (headEq := rules.headEq)
          (.lam NativeWireData.dataType) (singleton wire)))
  have second : Step (n := 0) rules.headEq
      (.app (.lam NativeWireData.dataType) (.refl (singleton wire)))
      NativeWireData.dataType rules.computation := by
    simpa [NativeWireData.dataType, inst0, subst] using
      (Step.betaPi (root := rules.computation) (headEq := rules.headEq)
        NativeWireData.dataType (.refl (singleton wire)))
  exact .trans _ _ _ (.rel _ _ first) (.rel _ _ second)

private theorem mixedArguments_typed (wire : NativeWireData.Wire) :
    FormationSensitive.CtxMor rules Intrinsic.contextAXPD .nil
      (Intrinsic.identitySchemaSubstitution (Intrinsic.listApp NativeWireData.dataType)
        (singleton wire) dataMotive (NativeWireData.encode wire)) := by
  have branch : Typing rules .nil (NativeWireData.encode wire)
      (subst (consSub dataMotive (mixedPointSubstitution wire)) Intrinsic.identityReflCaseType) := by
    have typed : Typing rules .nil (NativeWireData.encode wire) (mixedResultType wire) :=
      .conv (encode_typed .nil wire) (mixedResultType_formed wire) (.sort Intrinsic.motiveLevel)
        (.symm _ _ (mixedResultType_conversion wire))
    exact typed
  exact (mixedMotiveSubstitution_typed wire).extend branch

/-- Formation-sensitive admission is established independently of running
the step checker, by instantiating the actual admitted J schema. -/
theorem mixedSource_admitted (wire : NativeWireData.Wire) :
    Judgment rules .nil (mixedSource wire) NativeWireData.dataType := by
  have admitted : Judgment rules .nil (mixedSource wire) (mixedResultType wire) := by
    have schema := (identity_schema_substitute .nil (mixedArguments_typed wire)).1
    exact schema
  exact ⟨.nil, .conv admitted.typing (dataType_formed .nil) (.sort Tower.zero)
    (mixedResultType_conversion wire)⟩

def mixedStep (wire : NativeWireData.Wire) : NativeRelatorConversionChecking.StepCode 0 :=
  .root (.indexed (.identity (Intrinsic.listApp NativeWireData.dataType)
    (singleton wire) dataMotive (NativeWireData.encode wire)))

theorem mixedStep_checked (wire : NativeWireData.Wire) :
    NativeRelatorConversionChecking.checkStep (mixedStep wire) (mixedSource wire)
      (NativeWireData.encode wire) = true := by
  simp [NativeRelatorConversionChecking.checkStep, StructuralConversionCode.StepCode.check,
    StructuralConversionCode.StepCode.decode, NativeRelatorRootConversionCode.decode,
    NativeIndexedRootConversionCode.decode, mixedStep, mixedSource]

/-- This conclusion uses full combined-package checked-step preservation;
the source contains declarations absent from the original relator package. -/
theorem mixedStep_preserves (wire : NativeWireData.Wire) :
    Judgment rules .nil (NativeWireData.encode wire) NativeWireData.dataType :=
  checked_step_preserves (mixedSource_admitted wire) (mixedStep_checked wire)

theorem mixedStep_inside_identity (wire : NativeWireData.Wire) :
    Judgment rules .nil (.refl (NativeWireData.encode wire))
      (.id NativeWireData.dataType (mixedSource wire) (mixedSource wire)) :=
  checked_step_inside_identity (mixedSource_admitted wire) (mixedStep_checked wire)

/-- Changing the returned wire fails the original endpoint checker for
every wire value, not only for the concrete literal control below. -/
theorem mixedStep_rejects_other_wire {wire other : NativeWireData.Wire}
    (different : wire ≠ other) :
    NativeRelatorConversionChecking.checkStep (mixedStep wire) (mixedSource wire)
      (NativeWireData.encode other) = false := by
  have encodedDifferent : NativeWireData.encode (n := 0) wire ≠ NativeWireData.encode other :=
    fun equal => different (NativeWireData.encode_injective equal)
  simpa [NativeRelatorConversionChecking.checkStep, StructuralConversionCode.StepCode.check,
    StructuralConversionCode.StepCode.decode, NativeRelatorRootConversionCode.decode,
    NativeIndexedRootConversionCode.decode, mixedStep, mixedSource] using encodedDifferent

theorem mixedStep_rejects_changed_output :
    NativeRelatorConversionChecking.checkStep (mixedStep (.natural 0))
      (mixedSource (.natural 0)) (NativeWireData.encode (.natural 1)) = false := by
  exact mixedStep_rejects_other_wire (by decide)

#print axioms list_nil_preserves
#print axioms list_cons_preserves
#print axioms identity_preserves
#print axioms relator_nil_preserves
#print axioms relator_cons_preserves
#print axioms root_preservation
#print axioms step_preserves
#print axioms steps_preserve
#print axioms checked_step_preserves
#print axioms checked_step_inside_identity
#print axioms mixedResultType_formed
#print axioms mixedResultType_conversion
#print axioms mixedSource_admitted
#print axioms mixedStep_checked
#print axioms mixedStep_preserves
#print axioms mixedStep_inside_identity
#print axioms mixedStep_rejects_other_wire
#print axioms mixedStep_rejects_changed_output

end NativeWireRelatorPreservation
end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
