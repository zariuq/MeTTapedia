import Mettapedia.GSLT.LanguageDef.CostAuthoredAtom
import Mettapedia.GSLT.LanguageDef.CostRestorationFvarPairLeaf
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryCrossColorProCanary

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

namespace A2xDualNonemptyCospanCanary

def nameType : TypeExpr := .base (costBaseSortName "Name")

def authored : CostAuthoredAtomKey where
  sourceType := nameType
  sourceSupport := []
  targetType := nameType
  targetSupport := []
  authoredNormal :=
    .apply "NQuote" [.apply "PZero" []]

def leftKey (_ : Fin 1) : CostStaticAtomKey where
  sourceType := authored.sourceType
  sourceSupport := authored.sourceSupport
  targetType := authored.targetType
  targetSupport := authored.targetSupport
  normal := authored.reifyAt rhoCIGSLT .base

def rightKey (_ : Fin 1) : CostStaticAtomKey where
  sourceType := authored.sourceType
  sourceSupport := authored.sourceSupport
  targetType := authored.targetType
  targetSupport := authored.targetSupport
  normal := authored.reifyAt rhoCIGSLT .wrapped

def cospan : CostStaticAtomKeyCospan leftKey rightKey :=
  CostStaticAtomKeyCospan.ofFunctions leftKey rightKey

def leftResolve (name : String) : Option (Fin 1) :=
  if name = "left" then some 0 else none

def rightResolve (name : String) : Option (Fin 1) :=
  if name = "right" then some 0 else none

theorem left_selected : leftResolve "left" = some 0 := by decide

theorem right_selected : rightResolve "right" = some 0 := by decide

theorem authored_section_base :
    CostAuthoredAtomKey.eraseColor .base (leftKey 0).normal =
      authored.authoredNormal := by
  exact CostAuthoredAtomKey.reifyAt_eraseColor rhoCIGSLT .base authored

theorem authored_section_wrapped :
    CostAuthoredAtomKey.eraseColor .wrapped (rightKey 0).normal =
      authored.authoredNormal := by
  exact CostAuthoredAtomKey.reifyAt_eraseColor rhoCIGSLT .wrapped authored

theorem raw_normals_ne : (leftKey 0).normal ≠ (rightKey 0).normal := by
  decide

theorem cospan_legs_distinct : cospan.leftSlot 0 ≠ cospan.rightSlot 0 := by
  intro equal
  exact raw_normals_ne
    (congrArg CostStaticAtomKey.normal
      ((cospan.crossExtensional 0 0).mp equal))

theorem left_reify :
    cospan.reifyWith leftResolve cospan.leftSlot (.fvar "left") =
      .fvar (cospan.commonAtomName (cospan.leftSlot 0)) := by
  rw [CostStaticAtomKeyCospan.reifyWith_fvar,
    CostStaticAtomKeyCospan.reifyNameWith, left_selected]

theorem right_reify :
    cospan.reifyWith rightResolve cospan.rightSlot (.fvar "right") =
      .fvar (cospan.commonAtomName (cospan.rightSlot 0)) := by
  rw [CostStaticAtomKeyCospan.reifyWith_fvar,
    CostStaticAtomKeyCospan.reifyNameWith, right_selected]

theorem common_support_lengths_eq :
    (cospan.commonSupport
        (cospan.commonAtomName (cospan.leftSlot 0))).length =
      (cospan.commonSupport
        (cospan.commonAtomName (cospan.rightSlot 0))).length := by
  rw [cospan.commonSupport_commonAtomName,
    cospan.commonSupport_commonAtomName,
    cospan.leftCommutes, cospan.rightCommutes]
  rfl

theorem common_assignments_ne :
    cospan.commonAssignment
        (cospan.commonAtomName (cospan.leftSlot 0)) ≠
      cospan.commonAssignment
        (cospan.commonAtomName (cospan.rightSlot 0)) := by
  rw [cospan.commonAssignment_commonAtomName,
    cospan.commonAssignment_commonAtomName,
    cospan.leftCommutes, cospan.rightCommutes]
  exact raw_normals_ne

/-- Two nonempty endpoint inventories realizing one authored atom at
different colours do not admit the legacy raw restoration leaf. -/
theorem not_raw_restoresTogether :
    ¬ ReflectiveContextSupport.RestoresTogether
      rhoCIGSLT.costWholeReflectionProfile cospan.commonSupport
        cospan.commonAssignment
        (cospan.reifyWith leftResolve cospan.leftSlot (.fvar "left"))
        (cospan.reifyWith rightResolve cospan.rightSlot (.fvar "right")) := by
  rw [left_reify, right_reify]
  exact not_restoresTogether_fvar_fvar_of_assignment_ne
    common_support_lengths_eq common_assignments_ne

end A2xDualNonemptyCospanCanary

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
