import Mettapedia.Languages.GF.HandCrafted.English.Examples
import Mettapedia.Languages.GF.OSLFBridge_handcrafted
import Mettapedia.Languages.GF.Typing
import Mettapedia.Languages.GF.LinguisticInvariance
import Mettapedia.Languages.GF.WorldModelSemantics
import Mettapedia.Languages.GF.Generated.PaperAmbiguityPGFWitnesses
import Mettapedia.Logic.PLNWorldModel
import Mettapedia.Logic.EvidenceQuantale

namespace Mettapedia.Languages.GF.HandCrafted.English.ContextualDisambiguation

open Mettapedia.Languages.GF.HandCrafted.Core
open Mettapedia.Languages.GF.HandCrafted.Abstract
open Mettapedia.Languages.GF.OSLFBridge
open Mettapedia.Languages.GF.Typing
open Mettapedia.Languages.GF.LinguisticInvariance
open Mettapedia.Languages.GF.WorldModelSemantics
open Mettapedia.Languages.GF.Generated.PaperAmbiguityPGFWitnesses
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Languages.GF.HandCrafted.English
open Mettapedia.Languages.GF.HandCrafted.English.Examples
open Nouns Verbs Adjectives Syntax Pronouns Relatives

/-! ## Same-Surface Telescope Ambiguity -/

/-- NP-attachment reading: John saw [the man with the telescope]. -/
def telescopeNPAttachmentSurface : String := Examples.telescopeNPAttachmentSurface

/-- VP-attachment reading: John [saw the man] [with the telescope]. -/
def telescopeVPAttachmentSurface : String := Examples.telescopeVPAttachmentSurface

theorem telescope_np_surface :
    telescopeNPAttachmentSurface = "John sees the man with the telescope" := by
  rfl

theorem telescope_vp_surface :
    telescopeVPAttachmentSurface = "John sees the man with the telescope" := by
  rfl

theorem telescope_same_surface :
    telescopeNPAttachmentSurface = telescopeVPAttachmentSurface := by
  rw [telescope_np_surface, telescope_vp_surface]

private def mkApp3 (fname : String) (d1 d2 d3 res : String)
    (a1 a2 a3 : AbstractNode) : AbstractNode :=
  .apply { name := fname
         , type := .arrow (.base d1) (.arrow (.base d2) (.arrow (.base d3) (.base res))) }
    [a1, a2, a3]

private def presTemp : AbstractNode :=
  mkApp2 "TTAnt" "Tense" "Ant" "Temp"
    (mkLeaf "TPres" "Tense") (mkLeaf "ASimul" "Ant")

private def posPol : AbstractNode := mkLeaf "PPos" "Pol"

private def johnNPTree : AbstractNode := mkApp1 "UsePN" "PN" "NP" (mkLeaf "john_PN" "PN")
private def manCNTree : AbstractNode := mkApp1 "UseN" "N" "CN" (mkLeaf "man_N" "N")
private def telescopeCNTree : AbstractNode := mkApp1 "UseN" "N" "CN" (mkLeaf "telescope_N" "N")
private def theManTree : AbstractNode :=
  mkApp2 "DetCN" "Det" "CN" "NP" (mkLeaf "the_Det" "Det") manCNTree
private def theTelescopeTree : AbstractNode :=
  mkApp2 "DetCN" "Det" "CN" "NP" (mkLeaf "the_Det" "Det") telescopeCNTree
private def withTelescopeAdvTree : AbstractNode :=
  mkApp2 "PrepNP" "Prep" "NP" "Adv" (mkLeaf "with_Prep" "Prep") theTelescopeTree

/-- Same-surface NP-attachment tree. -/
def telescopeNPAttachmentTree : AbstractNode :=
  englishTelescopeAbstractNode2

/-- Same-surface VP-attachment tree. -/
def telescopeVPAttachmentTree : AbstractNode :=
  englishTelescopeAbstractNode1

theorem telescope_patterns_differ :
    gfAbstractToPattern telescopeNPAttachmentTree ≠
    gfAbstractToPattern telescopeVPAttachmentTree := by
  simp [telescopeNPAttachmentTree, telescopeVPAttachmentTree,
    englishTelescopeAbstractNode1, englishTelescopeAbstractNode2, List.map]

theorem telescope_shared_lexical_profile :
    containsLexical "john_PN" (gfAbstractToPattern telescopeNPAttachmentTree) = true ∧
    containsLexical "john_PN" (gfAbstractToPattern telescopeVPAttachmentTree) = true ∧
    containsLexical "see_V2" (gfAbstractToPattern telescopeNPAttachmentTree) = true ∧
    containsLexical "see_V2" (gfAbstractToPattern telescopeVPAttachmentTree) = true ∧
    containsLexical "man_N" (gfAbstractToPattern telescopeNPAttachmentTree) = true ∧
    containsLexical "man_N" (gfAbstractToPattern telescopeVPAttachmentTree) = true ∧
    containsLexical "telescope_N" (gfAbstractToPattern telescopeNPAttachmentTree) = true ∧
    containsLexical "telescope_N" (gfAbstractToPattern telescopeVPAttachmentTree) = true ∧
    containsLexical "with_Prep" (gfAbstractToPattern telescopeNPAttachmentTree) = true ∧
    containsLexical "with_Prep" (gfAbstractToPattern telescopeVPAttachmentTree) = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [containsLexical, containsLexical.go,
      telescopeNPAttachmentTree, telescopeVPAttachmentTree,
      englishTelescopeAbstractNode1, englishTelescopeAbstractNode2]

/-! ## A Tiny Query-Sensitive World Model for Telescope Attachment -/

abbrev GFPattern := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern

abbrev TelescopeState := BinaryEvidence × BinaryEvidence

noncomputable instance : EvidenceType TelescopeState :=
  { inferInstanceAs (AddCommMonoid TelescopeState) with }

private def telescopeNPQuery : GFPattern := gfAbstractToPattern telescopeNPAttachmentTree
private def telescopeVPQuery : GFPattern := gfAbstractToPattern telescopeVPAttachmentTree

private theorem telescopeNPQuery_ne_telescopeVPQuery :
    telescopeNPQuery ≠ telescopeVPQuery := telescope_patterns_differ

private theorem telescopeVPQuery_ne_telescopeNPQuery :
    telescopeVPQuery ≠ telescopeNPQuery := by
  intro h
  exact telescope_patterns_differ h.symm

noncomputable instance : BinaryWorldModel TelescopeState GFPattern where
  evidence W q :=
    if q = telescopeNPQuery then W.1
    else if q = telescopeVPQuery then W.2
    else 0
  evidence_add W₁ W₂ q := by
    by_cases hnp : q = telescopeNPQuery
    · subst hnp
      cases W₁
      cases W₂
      simp
    · by_cases hvp : q = telescopeVPQuery
      · subst hvp
        cases W₁
        cases W₂
        simp [telescopeVPQuery_ne_telescopeNPQuery]
      · simp [hnp, hvp]

def ev (p n : Nat) : BinaryEvidence := ⟨p, n⟩

def telescopeInstrumentScene : TelescopeState := (ev 1 2, ev 3 0)
def telescopeModifierScene : TelescopeState := (ev 3 0, ev 1 2)

theorem telescope_instrument_scene_values :
    gfEvidenceDenote telescopeInstrumentScene telescopeNPAttachmentTree = ev 1 2 ∧
    gfEvidenceDenote telescopeInstrumentScene telescopeVPAttachmentTree = ev 3 0 := by
  constructor
  · change
      (if gfAbstractToPattern telescopeNPAttachmentTree = telescopeNPQuery
       then telescopeInstrumentScene.1
       else if gfAbstractToPattern telescopeNPAttachmentTree = telescopeVPQuery
       then telescopeInstrumentScene.2
       else 0) = ev 1 2
    simp [telescopeInstrumentScene, telescopeNPQuery, ev]
  · change
      (if gfAbstractToPattern telescopeVPAttachmentTree = telescopeNPQuery
       then telescopeInstrumentScene.1
       else if gfAbstractToPattern telescopeVPAttachmentTree = telescopeVPQuery
       then telescopeInstrumentScene.2
       else 0) = ev 3 0
    have hneq : gfAbstractToPattern telescopeVPAttachmentTree ≠
        gfAbstractToPattern telescopeNPAttachmentTree := telescopeVPQuery_ne_telescopeNPQuery
    simp [telescopeInstrumentScene, telescopeNPQuery, telescopeVPQuery, hneq, ev]

theorem telescope_modifier_scene_values :
    gfEvidenceDenote telescopeModifierScene telescopeNPAttachmentTree = ev 3 0 ∧
    gfEvidenceDenote telescopeModifierScene telescopeVPAttachmentTree = ev 1 2 := by
  constructor
  · change
      (if gfAbstractToPattern telescopeNPAttachmentTree = telescopeNPQuery
       then telescopeModifierScene.1
       else if gfAbstractToPattern telescopeNPAttachmentTree = telescopeVPQuery
       then telescopeModifierScene.2
       else 0) = ev 3 0
    simp [telescopeModifierScene, telescopeNPQuery, ev]
  · change
      (if gfAbstractToPattern telescopeVPAttachmentTree = telescopeNPQuery
       then telescopeModifierScene.1
       else if gfAbstractToPattern telescopeVPAttachmentTree = telescopeVPQuery
       then telescopeModifierScene.2
       else 0) = ev 1 2
    have hneq : gfAbstractToPattern telescopeVPAttachmentTree ≠
        gfAbstractToPattern telescopeNPAttachmentTree := telescopeVPQuery_ne_telescopeNPQuery
    simp [telescopeModifierScene, telescopeNPQuery, telescopeVPQuery, hneq, ev]

/-! ## Same-Surface Anna Ambiguity -/

/-- NP-attachment reading: Anna dressed [the baby in the crib]. -/
def annaNPAttachmentSurface : String := Examples.annaNPAttachmentSurface

/-- VP-attachment reading: Anna [dressed the baby] [in the crib]. -/
def annaVPAttachmentSurface : String := Examples.annaVPAttachmentSurface

theorem anna_np_surface :
    annaNPAttachmentSurface = "Anna dresses the baby in the crib" := by
  rfl

theorem anna_vp_surface :
    annaVPAttachmentSurface = "Anna dresses the baby in the crib" := by
  rfl

theorem anna_same_surface :
    annaNPAttachmentSurface = annaVPAttachmentSurface := by
  rw [anna_np_surface, anna_vp_surface]

private def annaPNTree : AbstractNode := mkApp1 "UsePN" "PN" "NP" (mkLeaf "anna_PN" "PN")
private def babyCNTree : AbstractNode := mkApp1 "UseN" "N" "CN" (mkLeaf "baby_N" "N")
private def cribCNTree : AbstractNode := mkApp1 "UseN" "N" "CN" (mkLeaf "crib_N" "N")
private def theBabyTree : AbstractNode :=
  mkApp2 "DetCN" "Det" "CN" "NP" (mkLeaf "the_Det" "Det") babyCNTree
private def theCribTree : AbstractNode :=
  mkApp2 "DetCN" "Det" "CN" "NP" (mkLeaf "the_Det" "Det") cribCNTree
private def inCribAdvTree : AbstractNode :=
  mkApp2 "PrepNP" "Prep" "NP" "Adv" (mkLeaf "in_Prep" "Prep") theCribTree

/-- NP-attachment tree: Anna dressed [the baby in the crib]. -/
def annaNPAttachmentTree : AbstractNode :=
  englishAnnaAbstractNode2

/-- VP-attachment tree: Anna [dressed the baby] [in the crib]. -/
def annaVPAttachmentTree : AbstractNode :=
  englishAnnaAbstractNode1

theorem anna_patterns_differ :
    gfAbstractToPattern annaNPAttachmentTree ≠
    gfAbstractToPattern annaVPAttachmentTree := by
  simp [annaNPAttachmentTree, annaVPAttachmentTree,
    englishAnnaAbstractNode1, englishAnnaAbstractNode2, List.map]

theorem anna_shared_lexical_profile :
    containsLexical "anna_PN" (gfAbstractToPattern annaNPAttachmentTree) = true ∧
    containsLexical "anna_PN" (gfAbstractToPattern annaVPAttachmentTree) = true ∧
    containsLexical "baby_N" (gfAbstractToPattern annaNPAttachmentTree) = true ∧
    containsLexical "baby_N" (gfAbstractToPattern annaVPAttachmentTree) = true ∧
    containsLexical "dress_V2" (gfAbstractToPattern annaNPAttachmentTree) = true ∧
    containsLexical "dress_V2" (gfAbstractToPattern annaVPAttachmentTree) = true ∧
    containsLexical "crib_N" (gfAbstractToPattern annaNPAttachmentTree) = true ∧
    containsLexical "crib_N" (gfAbstractToPattern annaVPAttachmentTree) = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [containsLexical, containsLexical.go,
      annaNPAttachmentTree, annaVPAttachmentTree,
      englishAnnaAbstractNode1, englishAnnaAbstractNode2]

/-! ## BinaryEvidence-Sensitive Anna Worlds -/

private def annaNPQuery : GFPattern := gfAbstractToPattern annaNPAttachmentTree
private def annaVPQuery : GFPattern := gfAbstractToPattern annaVPAttachmentTree

private theorem annaNPQuery_ne_annaVPQuery :
    annaNPQuery ≠ annaVPQuery := anna_patterns_differ

private theorem annaVPQuery_ne_annaNPQuery :
    annaVPQuery ≠ annaNPQuery := by
  intro h
  exact anna_patterns_differ h.symm

abbrev AnnaState := BinaryEvidence × BinaryEvidence

noncomputable instance : EvidenceType AnnaState :=
  { inferInstanceAs (AddCommMonoid AnnaState) with }

noncomputable instance : BinaryWorldModel AnnaState GFPattern where
  evidence W q :=
    if q = annaNPQuery then W.1
    else if q = annaVPQuery then W.2
    else 0
  evidence_add W₁ W₂ q := by
    by_cases hNP : q = annaNPQuery
    · subst hNP
      simp
    · by_cases hVP : q = annaVPQuery
      · subst hVP
        simp [annaVPQuery_ne_annaNPQuery]
      · simp [hNP, hVP]

/-- World favoring the NP-attachment reading: the baby is the one in the crib. -/
def annaBabyInCribScene : AnnaState :=
  (ev 3 0, ev 1 2)

/-- World favoring the VP-attachment reading: the dressing happened in the crib. -/
def annaDressingInCribScene : AnnaState :=
  (ev 1 2, ev 3 0)

theorem anna_baby_in_crib_scene_values :
    gfEvidenceDenote annaBabyInCribScene annaNPAttachmentTree = ev 3 0 ∧
    gfEvidenceDenote annaBabyInCribScene annaVPAttachmentTree = ev 1 2 := by
  constructor
  · change
      (if gfAbstractToPattern annaNPAttachmentTree = annaNPQuery
       then annaBabyInCribScene.1
       else if gfAbstractToPattern annaNPAttachmentTree = annaVPQuery
       then annaBabyInCribScene.2
       else 0) = ev 3 0
    simp [annaBabyInCribScene, annaNPQuery, ev]
  · change
      (if gfAbstractToPattern annaVPAttachmentTree = annaNPQuery
       then annaBabyInCribScene.1
       else if gfAbstractToPattern annaVPAttachmentTree = annaVPQuery
       then annaBabyInCribScene.2
       else 0) = ev 1 2
    have hneq : gfAbstractToPattern annaVPAttachmentTree ≠
        gfAbstractToPattern annaNPAttachmentTree := annaVPQuery_ne_annaNPQuery
    simp [annaBabyInCribScene, annaNPQuery, annaVPQuery, hneq, ev]

theorem anna_dressing_in_crib_scene_values :
    gfEvidenceDenote annaDressingInCribScene annaNPAttachmentTree = ev 1 2 ∧
    gfEvidenceDenote annaDressingInCribScene annaVPAttachmentTree = ev 3 0 := by
  constructor
  · change
      (if gfAbstractToPattern annaNPAttachmentTree = annaNPQuery
       then annaDressingInCribScene.1
       else if gfAbstractToPattern annaNPAttachmentTree = annaVPQuery
       then annaDressingInCribScene.2
       else 0) = ev 1 2
    simp [annaDressingInCribScene, annaNPQuery, ev]
  · change
      (if gfAbstractToPattern annaVPAttachmentTree = annaNPQuery
       then annaDressingInCribScene.1
       else if gfAbstractToPattern annaVPAttachmentTree = annaVPQuery
       then annaDressingInCribScene.2
       else 0) = ev 3 0
    have hneq : gfAbstractToPattern annaVPAttachmentTree ≠
        gfAbstractToPattern annaNPAttachmentTree := annaVPQuery_ne_annaNPQuery
    simp [annaDressingInCribScene, annaNPQuery, annaVPQuery, hneq, ev]

theorem anna_scene_rankings_reverse :
    gfEvidenceDenote annaBabyInCribScene annaNPAttachmentTree =
      gfEvidenceDenote annaDressingInCribScene annaVPAttachmentTree ∧
    gfEvidenceDenote annaBabyInCribScene annaVPAttachmentTree =
      gfEvidenceDenote annaDressingInCribScene annaNPAttachmentTree := by
  constructor
  · exact (anna_baby_in_crib_scene_values.1).trans (anna_dressing_in_crib_scene_values.2).symm
  · exact (anna_baby_in_crib_scene_values.2).trans (anna_dressing_in_crib_scene_values.1).symm

end Mettapedia.Languages.GF.HandCrafted.English.ContextualDisambiguation
