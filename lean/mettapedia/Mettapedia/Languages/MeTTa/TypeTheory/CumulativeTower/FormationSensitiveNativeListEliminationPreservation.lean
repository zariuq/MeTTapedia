import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.FormationSensitiveNativeListElimination
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.FormationSensitiveTelescopeSpine
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.FormationSensitivePreservationInstances

/-!
# Dependent List argument recovery and iota preservation

The declaration-telescope theorem recovers all five eliminator arguments
from an arbitrary refined source typing. Constructor recovery determines the
head and tail. The independently admitted nil/cons schema instances then
replay all conversion and cumulativity adjustments of the displayed type.

The Pi-conversion boundary is an explicit qualification of the unchanged
List/mapRel rule package. This file neither supplies that boundary nor
claims preservation for identity/mapRel roots, arbitrary contextual steps,
or normalization of the combined package.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
namespace FormationSensitiveNativeListElimination

open Presentation Presentation.Declaration NativeIndexedFamilies RussellTarski
open Intrinsic
open FormationSensitiveNativeList (Typing)
open FormationSensitive (DeclarationSpine ContextFormation)

variable {n : Nat}

def universes : FormationSensitive.UniverseRegularity IntrinsicRelator.rules :=
  FormationSensitive.towerUniverseRegularity.includeSignature IntrinsicRelator.rawSignature

def eliminatorContext : Tower.Ctx 5 :=
  .snoc contextAPZS (listApp (.var 3))

def eliminatorResult : Tower.Tm 5 := .app (.var 3) (.var 0)

def eliminatorSubstitution
    (element motive nilCase consCase list : Tower.Tm n) : Sub Tower.Head 5 n :=
  consSub list (nilSchemaSubstitution element motive nilCase consCase)

theorem eliminateSpine (context : Tower.Ctx n) :
    DeclarationSpine IntrinsicRelator.rules context
      (.const eliminateName) (liftClosed eliminateType) := by
  apply DeclarationSpine.constant (u := .sort eliminateDeclarationLevel)
  · decide
  · exact eliminateType_hasType
  · exact .sort _

/-- All independently declared parameter types and the selected List fibre
are recovered, with replay at the original displayed result type. -/
theorem eliminateArguments (boundary : PiConversionBoundary IntrinsicRelator.rules)
    {context : Tower.Ctx n} (formed : ContextFormation IntrinsicRelator.rules context)
    {element motive nilCase consCase list displayed : Tower.Tm n}
    (observed : Typing context (eliminateApp element motive nilCase consCase list) displayed) :
    FormationSensitive.CtxMor IntrinsicRelator.rules contextAPZS context
        (nilSchemaSubstitution element motive nilCase consCase) ∧
      Typing context list (listApp element) ∧
      (∀ {replacement}, Typing context replacement (.app motive list) →
        Typing context replacement displayed) := by
  obtain ⟨typed, _, _, replay⟩ := DeclarationSpine.recoverTelescope universes boundary formed
    eliminatorContext eliminatorResult
    (eliminatorSubstitution element motive nilCase consCase list)
    (eliminateSpine context) observed
  exact ⟨typed.dropNewest, typed (0 : Fin 5), replay⟩

def constructorContext : Tower.Ctx 3 :=
  .snoc (.snoc contextA (.var 0)) (listApp (.var 1))

def constructorResult : Tower.Tm 3 := listApp (.var 2)

def constructorSubstitution (element head tail : Tower.Tm n) : Sub Tower.Head 3 n :=
  consSub tail (consSub head (elementSchemaSubstitution element))

theorem consSpine (context : Tower.Ctx n) :
    DeclarationSpine IntrinsicRelator.rules context
      (.const consName) (liftClosed consType) := by
  apply DeclarationSpine.constant (u := .sort consDeclarationLevel)
  · decide
  · exact FormationSensitiveNativeList.consType_hasType
  · exact .sort _

/-- Recovery is declaration-rooted, not a premise asserting arbitrary raw
term typing uniqueness. -/
theorem consArguments (boundary : PiConversionBoundary IntrinsicRelator.rules)
    {context : Tower.Ctx n} (formed : ContextFormation IntrinsicRelator.rules context)
    {element head tail displayed : Tower.Tm n}
    (observed : Typing context (consApp element head tail) displayed) :
    Typing context head element ∧ Typing context tail (listApp element) := by
  obtain ⟨typed, _, _, _⟩ := DeclarationSpine.recoverTelescope universes boundary formed
    constructorContext constructorResult (constructorSubstitution element head tail)
    (consSpine context) observed
  exact ⟨typed (1 : Fin 3), typed (0 : Fin 3)⟩

theorem consSchema_typed {context : Tower.Ctx n}
    {element motive nilCase consCase head tail : Tower.Tm n}
    (parameters : FormationSensitive.CtxMor IntrinsicRelator.rules contextAPZS context
      (nilSchemaSubstitution element motive nilCase consCase))
    (headTyped : Typing context head element)
    (tailTyped : Typing context tail (listApp element)) :
    FormationSensitive.CtxMor IntrinsicRelator.rules contextAPZSHeadTail context
      (consSchemaSubstitution element motive nilCase consCase head tail) := by
  have withHead : FormationSensitive.CtxMor IntrinsicRelator.rules contextAPZSHead context
      (consSub head (nilSchemaSubstitution element motive nilCase consCase)) :=
    parameters.extend headTyped
  exact withHead.extend tailTyped

/-- The actual nil reduction preserves the exact displayed source type,
including any final formation-sensitive conversion or cumulativity. -/
theorem nil_preserves (boundary : PiConversionBoundary IntrinsicRelator.rules)
    {context : Tower.Ctx n} (formed : ContextFormation IntrinsicRelator.rules context)
    {element motive nilCase consCase displayed : Tower.Tm n}
    (observed : Typing context
      (eliminateApp element motive nilCase consCase (nilApp element)) displayed) :
    Typing context nilCase displayed := by
  obtain ⟨parameters, _, replay⟩ := eliminateArguments boundary formed observed
  exact replay (nilIota_substitute formed parameters).2.typing

/-- The cons branch receives the exact selected head, tail and recursive
elimination result; no canonical quotation premise is needed. -/
theorem cons_preserves (boundary : PiConversionBoundary IntrinsicRelator.rules)
    {context : Tower.Ctx n} (formed : ContextFormation IntrinsicRelator.rules context)
    {element motive nilCase consCase head tail displayed : Tower.Tm n}
    (observed : Typing context
      (eliminateApp element motive nilCase consCase (consApp element head tail)) displayed) :
    Typing context
      (.app (.app (.app consCase head) tail)
        (eliminateApp element motive nilCase consCase tail)) displayed := by
  obtain ⟨parameters, listTyped, replay⟩ := eliminateArguments boundary formed observed
  obtain ⟨headTyped, tailTyped⟩ := consArguments boundary formed listTyped
  have typed := consSchema_typed parameters headTyped tailTyped
  exact replay (consIota_substitute formed typed).2.typing

theorem nil_judgment_preserved (boundary : PiConversionBoundary IntrinsicRelator.rules)
    {context : Tower.Ctx n} {element motive nilCase consCase displayed : Tower.Tm n}
    (judgment : FormationSensitive.Judgment IntrinsicRelator.rules context
      (eliminateApp element motive nilCase consCase (nilApp element)) displayed) :
    FormationSensitive.Judgment IntrinsicRelator.rules context nilCase displayed :=
  ⟨judgment.context, nil_preserves boundary judgment.context judgment.typing⟩

theorem cons_judgment_preserved (boundary : PiConversionBoundary IntrinsicRelator.rules)
    {context : Tower.Ctx n} {element motive nilCase consCase head tail displayed : Tower.Tm n}
    (judgment : FormationSensitive.Judgment IntrinsicRelator.rules context
      (eliminateApp element motive nilCase consCase (consApp element head tail)) displayed) :
    FormationSensitive.Judgment IntrinsicRelator.rules context
      (.app (.app (.app consCase head) tail)
        (eliminateApp element motive nilCase consCase tail)) displayed :=
  ⟨judgment.context, cons_preserves boundary judgment.context judgment.typing⟩

#print axioms eliminateArguments
#print axioms consArguments
#print axioms consSchema_typed
#print axioms nil_preserves
#print axioms cons_preserves
#print axioms nil_judgment_preserved
#print axioms cons_judgment_preserved

end FormationSensitiveNativeListElimination
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
