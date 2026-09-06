import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.FormationSensitiveNativeRelatorElimination
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.FormationSensitiveTelescopeSpine
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.FormationSensitivePreservationInstances

/-!
# Proof-relevant relator argument recovery and root preservation

The actual nine-argument eliminator declaration recovers its independently
typed parameters, both list indices and relational evidence from arbitrary
refined source typing. Constructor-spine recovery supplies all six cons
payloads. The admitted schema then replays the source's displayed result
adjustments, including conversion and cumulativity.

The Pi-conversion boundary qualifies the unchanged combined rules. It is
explicit here; normalization and that boundary are not assumed typing laws.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
namespace FormationSensitiveNativeRelatorElimination

open Presentation Presentation.Declaration NativeIndexedFamilies RussellTarski
open IntrinsicRelator
open FormationSensitiveNativeList (Typing)
open FormationSensitive (DeclarationSpine ContextFormation)

variable {n : Nat}

def universes : FormationSensitive.UniverseRegularity rules :=
  FormationSensitive.towerUniverseRegularity.includeSignature rawSignature

def parameterSubstitution
    (source target relation motive nilCase consCase : Tower.Tm n) : Sub Tower.Head 6 n :=
  consSub consCase (consSub nilCase (consSub motive
    (consSub relation (consSub target (consSub source Fin.elim0)))))

def consSchemaSubstitution
    (source target relation motive nilCase consCase sourceHead targetHead
      sourceTail targetTail headEvidence tailEvidence : Tower.Tm n) : Sub Tower.Head 12 n :=
  consSub tailEvidence (consSub headEvidence (consSub targetTail
    (consSub sourceTail (consSub targetHead (consSub sourceHead
      (parameterSubstitution source target relation motive nilCase consCase))))))

def eliminatorContext : Tower.Ctx 9 :=
  .snoc (.snoc (.snoc contextABRPZS (Intrinsic.listApp (.var 5)))
    (Intrinsic.listApp (.var 5)))
    (mapRelApp (.var 7) (.var 6) (.var 5) (.var 1) (.var 0))

def eliminatorResult : Tower.Tm 9 :=
  motiveApp (.var 5) (.var 2) (.var 1) (.var 0)

def eliminatorSubstitution
    (source target relation motive nilCase consCase sourceList targetList evidence : Tower.Tm n) :
    Sub Tower.Head 9 n :=
  consSub evidence (consSub targetList (consSub sourceList
    (parameterSubstitution source target relation motive nilCase consCase)))

theorem eliminateSpine (context : Tower.Ctx n) :
    DeclarationSpine rules context (.const eliminateName) (liftClosed eliminateType) := by
  apply DeclarationSpine.constant (u := .sort eliminateDeclarationLevel)
  · decide
  · exact eliminateType_hasType
  · exact .sort _

theorem eliminateArguments (boundary : PiConversionBoundary rules)
    {context : Tower.Ctx n} (formed : ContextFormation rules context)
    {source target relation motive nilCase consCase sourceList targetList evidence
      displayed : Tower.Tm n}
    (observed : Typing context
      (eliminateApp source target relation motive nilCase consCase sourceList targetList evidence)
      displayed) :
    FormationSensitive.CtxMor rules contextABRPZS context
        (parameterSubstitution source target relation motive nilCase consCase) ∧
      Typing context sourceList (Intrinsic.listApp source) ∧
      Typing context targetList (Intrinsic.listApp target) ∧
      Typing context evidence (mapRelApp source target relation sourceList targetList) ∧
      (∀ {replacement},
        Typing context replacement (motiveApp motive sourceList targetList evidence) →
        Typing context replacement displayed) := by
  obtain ⟨typed, _, _, replay⟩ := DeclarationSpine.recoverTelescope universes boundary formed
    eliminatorContext eliminatorResult
    (eliminatorSubstitution source target relation motive nilCase consCase
      sourceList targetList evidence) (eliminateSpine context) observed
  exact ⟨typed.dropNewest.dropNewest.dropNewest,
    typed (2 : Fin 9), typed (1 : Fin 9), typed (0 : Fin 9), replay⟩

def constructorContext : Tower.Ctx 9 :=
  .snoc
    (.snoc
      (.snoc
        (.snoc
          (.snoc (.snoc contextABR (.var 2)) (.var 2))
          (Intrinsic.listApp (.var 4)))
        (Intrinsic.listApp (.var 4)))
      (.app (.app (.var 4) (.var 3)) (.var 2)))
    (mapRelApp (.var 7) (.var 6) (.var 5) (.var 2) (.var 1))

def constructorResult : Tower.Tm 9 :=
  mapRelApp (.var 8) (.var 7) (.var 6)
    (Intrinsic.consApp (.var 8) (.var 5) (.var 3))
    (Intrinsic.consApp (.var 7) (.var 4) (.var 2))

def constructorSubstitution
    (source target relation sourceHead targetHead sourceTail targetTail headEvidence
      tailEvidence : Tower.Tm n) : Sub Tower.Head 9 n :=
  consSub tailEvidence (consSub headEvidence (consSub targetTail (consSub sourceTail
    (consSub targetHead (consSub sourceHead (consSub relation
      (consSub target (consSub source Fin.elim0))))))))

theorem consRelSpine (context : Tower.Ctx n) :
    DeclarationSpine rules context (.const consRelName) (liftClosed consRelType) := by
  apply DeclarationSpine.constant (u := .sort consRelDeclarationLevel)
  · decide
  · exact FormationSensitiveNativeList.consRelType_hasType
  · exact .sort _

/-- Payload typing is recovered from the original constructor declaration,
not supplied by a permissive source receipt or an assumed injectivity law. -/
theorem consRelArguments (boundary : PiConversionBoundary rules)
    {context : Tower.Ctx n} (formed : ContextFormation rules context)
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
  obtain ⟨typed, _, _, _⟩ := DeclarationSpine.recoverTelescope universes boundary formed
    constructorContext constructorResult
    (constructorSubstitution source target relation sourceHead targetHead
      sourceTail targetTail headEvidence tailEvidence) (consRelSpine context) observed
  exact ⟨typed (5 : Fin 9), typed (4 : Fin 9), typed (3 : Fin 9),
    typed (2 : Fin 9), typed (1 : Fin 9), typed (0 : Fin 9)⟩

theorem consSchema_typed {context : Tower.Ctx n}
    {source target relation motive nilCase consCase sourceHead targetHead sourceTail
      targetTail headEvidence tailEvidence : Tower.Tm n}
    (parameters : FormationSensitive.CtxMor rules contextABRPZS context
      (parameterSubstitution source target relation motive nilCase consCase))
    (sourceHeadTyped : Typing context sourceHead source)
    (targetHeadTyped : Typing context targetHead target)
    (sourceTailTyped : Typing context sourceTail (Intrinsic.listApp source))
    (targetTailTyped : Typing context targetTail (Intrinsic.listApp target))
    (headEvidenceTyped : Typing context headEvidence (.app (.app relation sourceHead) targetHead))
    (tailEvidenceTyped : Typing context tailEvidence
      (mapRelApp source target relation sourceTail targetTail)) :
    FormationSensitive.CtxMor rules
      contextABRPZSSourceTargetHeadSourceTargetTailHeadTail context
      (consSchemaSubstitution source target relation motive nilCase consCase
        sourceHead targetHead sourceTail targetTail headEvidence tailEvidence) := by
  have withSourceHead : FormationSensitive.CtxMor rules contextABRPZSSourceHead context
      (consSub sourceHead (parameterSubstitution source target relation motive nilCase consCase)) :=
    parameters.extend sourceHeadTyped
  have withTargetHead : FormationSensitive.CtxMor rules contextABRPZSSourceTargetHead context
      (consSub targetHead (consSub sourceHead
        (parameterSubstitution source target relation motive nilCase consCase))) :=
    withSourceHead.extend targetHeadTyped
  have withSourceTail : FormationSensitive.CtxMor rules
      contextABRPZSSourceTargetHeadSourceTail context
      (consSub sourceTail (consSub targetHead (consSub sourceHead
        (parameterSubstitution source target relation motive nilCase consCase)))) :=
    withTargetHead.extend sourceTailTyped
  have withTargetTail : FormationSensitive.CtxMor rules
      contextABRPZSSourceTargetHeadSourceTargetTail context
      (consSub targetTail (consSub sourceTail (consSub targetHead (consSub sourceHead
        (parameterSubstitution source target relation motive nilCase consCase))))) :=
    withSourceTail.extend targetTailTyped
  have withHeadEvidence : FormationSensitive.CtxMor rules
      contextABRPZSSourceTargetHeadSourceTargetTailHead context
      (consSub headEvidence (consSub targetTail (consSub sourceTail
        (consSub targetHead (consSub sourceHead
          (parameterSubstitution source target relation motive nilCase consCase)))))) :=
    withTargetTail.extend headEvidenceTyped
  exact withHeadEvidence.extend tailEvidenceTyped

theorem nil_preserves (boundary : PiConversionBoundary rules)
    {context : Tower.Ctx n} (formed : ContextFormation rules context)
    {source target relation motive nilCase consCase displayed : Tower.Tm n}
    (observed : Typing context
      (eliminateApp source target relation motive nilCase consCase
        (Intrinsic.nilApp source) (Intrinsic.nilApp target) (nilRelApp source target relation))
      displayed) : Typing context nilCase displayed := by
  obtain ⟨parameters, _, _, _, replay⟩ := eliminateArguments boundary formed observed
  exact replay (nilIota_substitute formed parameters).2.typing

/-- The original branch consumes both heads, both tails, both witnesses and
the recursive elimination at precisely the selected tail witness. -/
theorem cons_preserves (boundary : PiConversionBoundary rules)
    {context : Tower.Ctx n} (formed : ContextFormation rules context)
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
  obtain ⟨parameters, _, _, evidenceTyped, replay⟩ := eliminateArguments boundary formed observed
  obtain ⟨sourceHeadTyped, targetHeadTyped, sourceTailTyped, targetTailTyped,
    headEvidenceTyped, tailEvidenceTyped⟩ := consRelArguments boundary formed evidenceTyped
  have typed := consSchema_typed parameters sourceHeadTyped targetHeadTyped sourceTailTyped
    targetTailTyped headEvidenceTyped tailEvidenceTyped
  exact replay (consIota_substitute formed typed).2.typing

theorem iota_preserves (boundary : PiConversionBoundary rules)
    {context : Tower.Ctx n} (formed : ContextFormation rules context)
    {left right displayed : Tower.Tm n} (evidence : IotaEvidence n left right)
    (observed : Typing context left displayed) : Typing context right displayed := by
  cases evidence with
  | nil => exact nil_preserves boundary formed observed
  | cons => exact cons_preserves boundary formed observed

theorem iota_judgment_preserved (boundary : PiConversionBoundary rules)
    {context : Tower.Ctx n} {left right displayed : Tower.Tm n}
    (evidence : IotaEvidence n left right)
    (judgment : FormationSensitive.Judgment rules context left displayed) :
    FormationSensitive.Judgment rules context right displayed :=
  ⟨judgment.context, iota_preserves boundary judgment.context evidence judgment.typing⟩

#print axioms eliminateArguments
#print axioms consRelArguments
#print axioms consSchema_typed
#print axioms nil_preserves
#print axioms cons_preserves
#print axioms iota_preserves
#print axioms iota_judgment_preserved

#print axioms eliminateSpine
#print axioms consRelSpine

end FormationSensitiveNativeRelatorElimination
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
