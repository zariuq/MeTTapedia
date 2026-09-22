import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentNativeBooleanRootPreservation

/-!
# Relator root preservation with genuine Boolean computation

Declaration-spine recovery is performed under the extended rules, including
Boolean conversions in arbitrary source typing. The independently proved
relator branch schemas are level-instantiated and then substituted by the
recovered, extended-calculus arguments.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentNativeBooleanRelatorPreservation

open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
open Presentation Presentation.Declaration Presentation.FormationSensitive RussellTarski
open NativeIndexedFamilies IntrinsicRelator
open FormationSensitiveNativeRelatorElimination
open SharedJudgmentNativeBooleanRootPreservation (levelContext levelTerm nativeSpine includeNative)

abbrev rules := SharedJudgmentNativeBooleanRegion.rules
private theorem universes : UniverseRegularity rules := SharedJudgmentNativeBooleanRootPreservation.universes

variable {n : Nat}

theorem eliminateSpine (context : Tower.Ctx n) :
    DeclarationSpine rules context (.const eliminateName) (liftClosed (levelTerm eliminateType)) :=
  nativeSpine context (by decide) eliminateType_hasType

theorem eliminateArguments (boundary : PiConversionBoundary rules)
    {context : Tower.Ctx n} (formed : ContextFormation rules context)
    {source target relation motive nilCase consCase sourceList targetList evidence
      displayed : Tower.Tm n}
    (observed : Typing rules context
      (eliminateApp source target relation motive nilCase consCase sourceList targetList evidence)
      displayed) :
    FormationSensitive.CtxMor rules (levelContext contextABRPZS) context
        (parameterSubstitution source target relation motive nilCase consCase) ∧
      Typing rules context sourceList (Intrinsic.listApp source) ∧
      Typing rules context targetList (Intrinsic.listApp target) ∧
      Typing rules context evidence (mapRelApp source target relation sourceList targetList) ∧
      (∀ {replacement},
        Typing rules context replacement (motiveApp motive sourceList targetList evidence) →
        Typing rules context replacement displayed) := by
  obtain ⟨typed, _, _, replay⟩ := DeclarationSpine.recoverTelescope universes boundary formed
    (levelContext eliminatorContext) (levelTerm eliminatorResult)
    (eliminatorSubstitution source target relation motive nilCase consCase
      sourceList targetList evidence) (eliminateSpine context) observed
  exact ⟨typed.dropNewest.dropNewest.dropNewest,
    typed (2 : Fin 9), typed (1 : Fin 9), typed (0 : Fin 9), replay⟩

theorem consRelSpine (context : Tower.Ctx n) :
    DeclarationSpine rules context (.const consRelName) (liftClosed (levelTerm consRelType)) :=
  nativeSpine context (by decide) FormationSensitiveNativeList.consRelType_hasType

/-- Payload typing is recovered from the original constructor declaration,
not supplied by a permissive source receipt or an assumed injectivity law. -/
theorem consRelArguments (boundary : PiConversionBoundary rules)
    {context : Tower.Ctx n} (formed : ContextFormation rules context)
    {source target relation sourceHead targetHead sourceTail targetTail headEvidence
      tailEvidence displayed : Tower.Tm n}
    (observed : Typing rules context
      (consRelApp source target relation sourceHead targetHead sourceTail targetTail
        headEvidence tailEvidence) displayed) :
    Typing rules context sourceHead source ∧ Typing rules context targetHead target ∧
      Typing rules context sourceTail (Intrinsic.listApp source) ∧
      Typing rules context targetTail (Intrinsic.listApp target) ∧
      Typing rules context headEvidence (.app (.app relation sourceHead) targetHead) ∧
      Typing rules context tailEvidence (mapRelApp source target relation sourceTail targetTail) := by
  obtain ⟨typed, _, _, _⟩ := DeclarationSpine.recoverTelescope universes boundary formed
    (levelContext constructorContext) (levelTerm constructorResult)
    (constructorSubstitution source target relation sourceHead targetHead
      sourceTail targetTail headEvidence tailEvidence) (consRelSpine context) observed
  exact ⟨typed (5 : Fin 9), typed (4 : Fin 9), typed (3 : Fin 9),
    typed (2 : Fin 9), typed (1 : Fin 9), typed (0 : Fin 9)⟩

theorem consSchema_typed {context : Tower.Ctx n}
    {source target relation motive nilCase consCase sourceHead targetHead sourceTail
      targetTail headEvidence tailEvidence : Tower.Tm n}
    (parameters : FormationSensitive.CtxMor rules (levelContext contextABRPZS) context
      (parameterSubstitution source target relation motive nilCase consCase))
    (sourceHeadTyped : Typing rules context sourceHead source)
    (targetHeadTyped : Typing rules context targetHead target)
    (sourceTailTyped : Typing rules context sourceTail (Intrinsic.listApp source))
    (targetTailTyped : Typing rules context targetTail (Intrinsic.listApp target))
    (headEvidenceTyped : Typing rules context headEvidence (.app (.app relation sourceHead) targetHead))
    (tailEvidenceTyped : Typing rules context tailEvidence
      (mapRelApp source target relation sourceTail targetTail)) :
    FormationSensitive.CtxMor rules
      (levelContext contextABRPZSSourceTargetHeadSourceTargetTailHeadTail) context
      (consSchemaSubstitution source target relation motive nilCase consCase
        sourceHead targetHead sourceTail targetTail headEvidence tailEvidence) := by
  have withSourceHead : FormationSensitive.CtxMor rules (levelContext contextABRPZSSourceHead) context
      (consSub sourceHead (parameterSubstitution source target relation motive nilCase consCase)) :=
    parameters.extend sourceHeadTyped
  have withTargetHead : FormationSensitive.CtxMor rules (levelContext contextABRPZSSourceTargetHead) context
      (consSub targetHead (consSub sourceHead
        (parameterSubstitution source target relation motive nilCase consCase))) :=
    withSourceHead.extend targetHeadTyped
  have withSourceTail : FormationSensitive.CtxMor rules
      (levelContext contextABRPZSSourceTargetHeadSourceTail) context
      (consSub sourceTail (consSub targetHead (consSub sourceHead
        (parameterSubstitution source target relation motive nilCase consCase)))) :=
    withTargetHead.extend sourceTailTyped
  have withTargetTail : FormationSensitive.CtxMor rules
      (levelContext contextABRPZSSourceTargetHeadSourceTargetTail) context
      (consSub targetTail (consSub sourceTail (consSub targetHead (consSub sourceHead
        (parameterSubstitution source target relation motive nilCase consCase))))) :=
    withSourceTail.extend targetTailTyped
  have withHeadEvidence : FormationSensitive.CtxMor rules
      (levelContext contextABRPZSSourceTargetHeadSourceTargetTailHead) context
      (consSub headEvidence (consSub targetTail (consSub sourceTail
        (consSub targetHead (consSub sourceHead
          (parameterSubstitution source target relation motive nilCase consCase)))))) :=
    withTargetTail.extend headEvidenceTyped
  exact withHeadEvidence.extend tailEvidenceTyped

theorem nil_preserves (boundary : PiConversionBoundary rules)
    {context : Tower.Ctx n} (formed : ContextFormation rules context)
    {source target relation motive nilCase consCase displayed : Tower.Tm n}
    (observed : Typing rules context
      (eliminateApp source target relation motive nilCase consCase
        (Intrinsic.nilApp source) (Intrinsic.nilApp target) (nilRelApp source target relation))
      displayed) : Typing rules context nilCase displayed := by
  obtain ⟨parameters, _, _, _, replay⟩ := eliminateArguments boundary formed observed
  exact replay ((includeNative nilIotaRight_hasType).substitute parameters)

/-- The original branch consumes both heads, both tails, both witnesses and
the recursive elimination at precisely the selected tail witness. -/
theorem cons_preserves (boundary : PiConversionBoundary rules)
    {context : Tower.Ctx n} (formed : ContextFormation rules context)
    {source target relation motive nilCase consCase sourceHead targetHead sourceTail
      targetTail headEvidence tailEvidence displayed : Tower.Tm n}
    (observed : Typing rules context
      (eliminateApp source target relation motive nilCase consCase
        (Intrinsic.consApp source sourceHead sourceTail)
        (Intrinsic.consApp target targetHead targetTail)
        (consRelApp source target relation sourceHead targetHead sourceTail targetTail
          headEvidence tailEvidence)) displayed) :
    Typing rules context
      (.app (.app (.app (.app (.app (.app (.app consCase sourceHead) targetHead)
        sourceTail) targetTail) headEvidence) tailEvidence)
        (eliminateApp source target relation motive nilCase consCase
          sourceTail targetTail tailEvidence)) displayed := by
  obtain ⟨parameters, _, _, evidenceTyped, replay⟩ := eliminateArguments boundary formed observed
  obtain ⟨sourceHeadTyped, targetHeadTyped, sourceTailTyped, targetTailTyped,
    headEvidenceTyped, tailEvidenceTyped⟩ := consRelArguments boundary formed evidenceTyped
  have typed := consSchema_typed parameters sourceHeadTyped targetHeadTyped sourceTailTyped
    targetTailTyped headEvidenceTyped tailEvidenceTyped
  exact replay ((includeNative consIotaRight_hasType).substitute typed)

theorem iota_preserves (boundary : PiConversionBoundary rules)
    {context : Tower.Ctx n} (formed : ContextFormation rules context)
    {left right displayed : Tower.Tm n} (evidence : IotaEvidence n left right)
    (observed : Typing rules context left displayed) : Typing rules context right displayed := by
  cases evidence with
  | nil => exact nil_preserves boundary formed observed
  | cons => exact cons_preserves boundary formed observed


end Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentNativeBooleanRelatorPreservation
