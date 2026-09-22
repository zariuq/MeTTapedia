import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveHOLNativeMixedSchemas

/-!
# Proof-relevant relator preservation in the actual mixed environment

All six cons payloads are recovered from the actual joint constructor
declaration. Independently formed original schemas are level-instantiated
and substituted; they retain both indices and both proof witnesses.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
namespace FormationSensitiveHOLNativeMixedRelatorPreservation

open Presentation Presentation.Declaration NativeIndexedFamilies
open IntrinsicRelator
open FormationSensitiveHOLNativeMixedSchemas
open FormationSensitiveHOLNativeMixedSchemas (Typing universes)
abbrev jointRules := FormationSensitiveHOLProofListIntegration.rules
open FormationSensitive (DeclarationSpine ContextFormation)
open HOLNativeMixedConversionParallel (mixedPiConversionBoundary)
open FormationSensitiveNativeRelatorElimination
  (parameterSubstitution consSchemaSubstitution eliminatorContext eliminatorResult
   eliminatorSubstitution constructorContext constructorResult constructorSubstitution)

variable {n : Nat}

theorem eliminateArguments {context : Tower.Ctx n} (formed : ContextFormation jointRules context)
    {source target relation motive nilCase consCase sourceList targetList evidence
      displayed : Tower.Tm n}
    (observed : Typing context
      (eliminateApp source target relation motive nilCase consCase sourceList targetList evidence)
      displayed) :
    FormationSensitive.CtxMor jointRules (lowerContext contextABRPZS) context
        (parameterSubstitution source target relation motive nilCase consCase) ∧
      Typing context sourceList (Intrinsic.listApp source) ∧
      Typing context targetList (Intrinsic.listApp target) ∧
      Typing context evidence (mapRelApp source target relation sourceList targetList) ∧
      (∀ {replacement},
        Typing context replacement (motiveApp motive sourceList targetList evidence) →
        Typing context replacement displayed) := by
  obtain ⟨typed, _, _, replay⟩ := DeclarationSpine.recoverTelescope universes mixedPiConversionBoundary formed
    (lowerContext eliminatorContext) (lowerTerm eliminatorResult)
    (eliminatorSubstitution source target relation motive nilCase consCase
      sourceList targetList evidence) (nativeSpine context (by decide)
      FormationSensitiveNativeRelatorElimination.eliminateType_hasType (.sort _)) observed
  exact ⟨typed.dropNewest.dropNewest.dropNewest,
    typed (2 : Fin 9), typed (1 : Fin 9), typed (0 : Fin 9), replay⟩

/-- Payload typing is recovered from the original constructor declaration,
not supplied by a permissive source receipt or an assumed injectivity law. -/
theorem consRelArguments {context : Tower.Ctx n} (formed : ContextFormation jointRules context)
    {source target relation sourceHead targetHead sourceTail targetTail headEvidence
      tailEvidence displayed : Tower.Tm n}
    (observed : Typing context
      (consRelApp source target relation sourceHead targetHead sourceTail targetTail
        headEvidence tailEvidence) displayed) :
    Typing context sourceHead source ∧ Typing context targetHead target ∧
      Typing context sourceTail (Intrinsic.listApp source) ∧
      Typing context targetTail (Intrinsic.listApp target) ∧
      Typing context headEvidence (.app (.app relation sourceHead) targetHead) ∧
      Typing context tailEvidence (mapRelApp source target relation sourceTail targetTail) := by
  obtain ⟨typed, _, _, _⟩ := DeclarationSpine.recoverTelescope universes mixedPiConversionBoundary formed
    (lowerContext constructorContext) (lowerTerm constructorResult)
    (constructorSubstitution source target relation sourceHead targetHead
      sourceTail targetTail headEvidence tailEvidence) (nativeSpine context (by decide)
      FormationSensitiveNativeList.consRelType_hasType (.sort _)) observed
  exact ⟨typed (5 : Fin 9), typed (4 : Fin 9), typed (3 : Fin 9),
    typed (2 : Fin 9), typed (1 : Fin 9), typed (0 : Fin 9)⟩

theorem consSchema_typed {context : Tower.Ctx n}
    {source target relation motive nilCase consCase sourceHead targetHead sourceTail
      targetTail headEvidence tailEvidence : Tower.Tm n}
    (parameters : FormationSensitive.CtxMor jointRules (lowerContext contextABRPZS) context
      (parameterSubstitution source target relation motive nilCase consCase))
    (sourceHeadTyped : Typing context sourceHead source)
    (targetHeadTyped : Typing context targetHead target)
    (sourceTailTyped : Typing context sourceTail (Intrinsic.listApp source))
    (targetTailTyped : Typing context targetTail (Intrinsic.listApp target))
    (headEvidenceTyped : Typing context headEvidence (.app (.app relation sourceHead) targetHead))
    (tailEvidenceTyped : Typing context tailEvidence
      (mapRelApp source target relation sourceTail targetTail)) :
    FormationSensitive.CtxMor jointRules
      (lowerContext contextABRPZSSourceTargetHeadSourceTargetTailHeadTail) context
      (consSchemaSubstitution source target relation motive nilCase consCase
        sourceHead targetHead sourceTail targetTail headEvidence tailEvidence) := by
  have withSourceHead : FormationSensitive.CtxMor jointRules (lowerContext contextABRPZSSourceHead) context
      (consSub sourceHead (parameterSubstitution source target relation motive nilCase consCase)) :=
    parameters.extend sourceHeadTyped
  have withTargetHead : FormationSensitive.CtxMor jointRules (lowerContext contextABRPZSSourceTargetHead) context
      (consSub targetHead (consSub sourceHead
        (parameterSubstitution source target relation motive nilCase consCase))) :=
    withSourceHead.extend targetHeadTyped
  have withSourceTail : FormationSensitive.CtxMor jointRules
      (lowerContext contextABRPZSSourceTargetHeadSourceTail) context
      (consSub sourceTail (consSub targetHead (consSub sourceHead
        (parameterSubstitution source target relation motive nilCase consCase)))) :=
    withTargetHead.extend sourceTailTyped
  have withTargetTail : FormationSensitive.CtxMor jointRules
      (lowerContext contextABRPZSSourceTargetHeadSourceTargetTail) context
      (consSub targetTail (consSub sourceTail (consSub targetHead (consSub sourceHead
        (parameterSubstitution source target relation motive nilCase consCase))))) :=
    withSourceTail.extend targetTailTyped
  have withHeadEvidence : FormationSensitive.CtxMor jointRules
      (lowerContext contextABRPZSSourceTargetHeadSourceTargetTailHead) context
      (consSub headEvidence (consSub targetTail (consSub sourceTail
        (consSub targetHead (consSub sourceHead
          (parameterSubstitution source target relation motive nilCase consCase)))))) :=
    withTargetTail.extend headEvidenceTyped
  exact withHeadEvidence.extend tailEvidenceTyped

theorem nil_preserves {context : Tower.Ctx n} (formed : ContextFormation jointRules context)
    {source target relation motive nilCase consCase displayed : Tower.Tm n}
    (observed : Typing context
      (eliminateApp source target relation motive nilCase consCase
        (Intrinsic.nilApp source) (Intrinsic.nilApp target) (nilRelApp source target relation))
      displayed) : Typing context nilCase displayed := by
  obtain ⟨parameters, _, _, _, replay⟩ := eliminateArguments formed observed
  exact replay (schema_substitute
    FormationSensitiveNativeRelatorElimination.nilIota_judgments.2 formed parameters).typing

/-- The original branch consumes both heads, both tails, both witnesses and
the recursive elimination at precisely the selected tail witness. -/
theorem cons_preserves {context : Tower.Ctx n} (formed : ContextFormation jointRules context)
    {source target relation motive nilCase consCase sourceHead targetHead sourceTail
      targetTail headEvidence tailEvidence displayed : Tower.Tm n}
    (observed : Typing context
      (eliminateApp source target relation motive nilCase consCase
        (Intrinsic.consApp source sourceHead sourceTail)
        (Intrinsic.consApp target targetHead targetTail)
        (consRelApp source target relation sourceHead targetHead sourceTail targetTail
          headEvidence tailEvidence)) displayed) :
    Typing context
      (.app (.app (.app (.app (.app (.app (.app consCase sourceHead) targetHead)
        sourceTail) targetTail) headEvidence) tailEvidence)
        (eliminateApp source target relation motive nilCase consCase
          sourceTail targetTail tailEvidence)) displayed := by
  obtain ⟨parameters, _, _, evidenceTyped, replay⟩ := eliminateArguments formed observed
  obtain ⟨sourceHeadTyped, targetHeadTyped, sourceTailTyped, targetTailTyped,
    headEvidenceTyped, tailEvidenceTyped⟩ := consRelArguments formed evidenceTyped
  have typed := consSchema_typed parameters sourceHeadTyped targetHeadTyped sourceTailTyped
    targetTailTyped headEvidenceTyped tailEvidenceTyped
  exact replay (schema_substitute
    FormationSensitiveNativeRelatorElimination.consIota_judgments.2 formed typed).typing

theorem iota_preserves {context : Tower.Ctx n} (formed : ContextFormation jointRules context)
    {left right displayed : Tower.Tm n} (evidence : IotaEvidence n left right)
    (observed : Typing context left displayed) : Typing context right displayed := by
  cases evidence with
  | nil => exact nil_preserves formed observed
  | cons => exact cons_preserves formed observed


#print axioms eliminateArguments
#print axioms consRelArguments
#print axioms consSchema_typed
#print axioms nil_preserves
#print axioms cons_preserves
#print axioms iota_preserves

end FormationSensitiveHOLNativeMixedRelatorPreservation
end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
