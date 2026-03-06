import Mettapedia.Languages.GF.English.Linearization

namespace Mettapedia.Languages.GF.English.Linearization

open Mettapedia.Languages.GF
open Core Abstract
open English
open Syntax Pronouns Relatives
open Nouns Verbs Adjectives

/-- Local abstract-tree helpers for public witness lemmas. -/
private def wMkLeaf (name : String) (cat : String) : AbstractNode :=
  .leaf name (.base cat)

private def wMkApp1 (fname : String) (dom res : String) (arg : AbstractNode) : AbstractNode :=
  .apply { name := fname, type := .arrow (.base dom) (.base res) } [arg]

private def wMkApp2 (fname : String) (d1 d2 res : String)
    (a1 a2 : AbstractNode) : AbstractNode :=
  .apply { name := fname, type := .arrow (.base d1) (.arrow (.base d2) (.base res)) } [a1, a2]

/-- Canonical subject witness used in interface-contrast bridges: "the cat". -/
def witnessSubjCat : AbstractNode :=
  wMkApp2 "DetCN" "Det" "CN" "NP"
    (wMkLeaf "the_Det" "Det")
    (wMkApp1 "UseN" "N" "CN" (wMkLeaf "cat_N" "N"))

/-- Canonical object witness used in interface-contrast bridges: "the dog". -/
def witnessObjDog : AbstractNode :=
  wMkApp2 "DetCN" "Det" "CN" "NP"
    (wMkLeaf "the_Det" "Det")
    (wMkApp1 "UseN" "N" "CN" (wMkLeaf "dog_N" "N"))

/-- Active witness tree used by interface-contrast bridges:
"the cat loves the dog". -/
def witnessActiveClause : AbstractNode :=
  wMkApp2 "PredVP" "NP" "VP" "Cl"
    witnessSubjCat
    (wMkApp2 "ComplSlash" "VPSlash" "NP" "VP"
      (wMkApp1 "SlashV2a" "V2" "VPSlash" (wMkLeaf "love_V2" "V2"))
      witnessObjDog)

/-- Passive witness tree used by interface-contrast bridges:
"the dog is loved". -/
def witnessPassiveClause : AbstractNode :=
  wMkApp2 "PredVP" "NP" "VP" "Cl"
    witnessObjDog
    (wMkApp1 "PassV2" "V2" "VP" (wMkLeaf "love_V2" "V2"))

/-- Public passive constructor matching the `PassV2` dispatch branch. -/
def passV2Canonical (v2 : EnglishV2) : EnglishVP :=
  passiveVP v2

/-- Canonical NP witness values used in theorem endpoints. -/
def witnessSubjNP : EnglishNP :=
  linDetCN theDefArt (linUseN cat_N)

def witnessObjNP : EnglishNP :=
  linDetCN theDefArt (linUseN dog_N)

/-- Canonical VP witness values used in theorem endpoints. -/
def witnessActiveVP : EnglishVP :=
  fillSlashPreservingBase (slashV2a love_V2) witnessObjNP

def witnessPassiveVP : EnglishVP :=
  passV2Canonical love_V2

/-! ### Witness-path lemma ladder

Each step reduces exactly one `evalNode` application so no single proof
needs to unfold the full 274-arm `dispatchApply` more than once. -/

section WitnessLadder

set_option maxHeartbeats 1600000

private theorem evalNode_leaf_cat_N :
    evalNode {} (wMkLeaf "cat_N" "N") = .noun cat_N := by
  unfold evalNode wMkLeaf
  simpa using evalLeafValue_cat_N

private theorem evalNode_leaf_dog_N :
    evalNode {} (wMkLeaf "dog_N" "N") = .noun dog_N := by
  unfold evalNode wMkLeaf
  simpa using evalLeafValue_dog_N

private theorem evalNode_leaf_the_Det :
    evalNode {} (wMkLeaf "the_Det" "Det") = .det theDefArt := by
  unfold evalNode wMkLeaf
  simpa using evalLeafValue_the_Det

private theorem evalNode_leaf_love_V2 :
    evalNode {} (wMkLeaf "love_V2" "V2") = .verb2 love_V2 := by
  unfold evalNode wMkLeaf
  simpa using evalLeafValue_love_V2

private theorem evalNode_UseN_cat :
    evalNode {} (wMkApp1 "UseN" "N" "CN" (wMkLeaf "cat_N" "N")) =
      .cn (linUseN cat_N) := by
  unfold evalNode wMkApp1
  simp only [evalArgs, evalNode_leaf_cat_N, dispatchApply_UseN_noun]

private theorem evalNode_UseN_dog :
    evalNode {} (wMkApp1 "UseN" "N" "CN" (wMkLeaf "dog_N" "N")) =
      .cn (linUseN dog_N) := by
  unfold evalNode wMkApp1
  simp only [evalArgs, evalNode_leaf_dog_N, dispatchApply_UseN_noun]

private theorem evalNode_subjCat :
    evalNode {} witnessSubjCat = .np witnessSubjNP := by
  unfold evalNode witnessSubjCat wMkApp2
  simp only [evalArgs, evalNode_leaf_the_Det, evalNode_UseN_cat, dispatchApply_DetCN]
  simp [witnessSubjNP]

private theorem evalNode_objDog :
    evalNode {} witnessObjDog = .np witnessObjNP := by
  unfold evalNode witnessObjDog wMkApp2
  simp only [evalArgs, evalNode_leaf_the_Det, evalNode_UseN_dog, dispatchApply_DetCN]
  simp [witnessObjNP]

private theorem evalNode_SlashV2a_love :
    evalNode {} (wMkApp1 "SlashV2a" "V2" "VPSlash" (wMkLeaf "love_V2" "V2")) =
      .vpslash (slashV2a love_V2) := by
  unfold evalNode wMkApp1
  simp only [evalArgs, evalNode_leaf_love_V2, dispatchApply_SlashV2a]

private theorem evalNode_ComplSlash_love_dog :
    evalNode {}
      (wMkApp2 "ComplSlash" "VPSlash" "NP" "VP"
        (wMkApp1 "SlashV2a" "V2" "VPSlash" (wMkLeaf "love_V2" "V2"))
        witnessObjDog) =
      .vp witnessActiveVP := by
  unfold evalNode wMkApp2
  simp only [evalArgs, evalNode_SlashV2a_love, evalNode_objDog, dispatchApply_ComplSlash]
  simp [witnessActiveVP]

private theorem evalNode_PassV2_love :
    evalNode {} (wMkApp1 "PassV2" "V2" "VP" (wMkLeaf "love_V2" "V2")) =
      .vp witnessPassiveVP := by
  unfold evalNode wMkApp1
  simp only [evalArgs, evalNode_leaf_love_V2, dispatchApply_PassV2]
  simp [witnessPassiveVP, passV2Canonical]

private theorem evalNode_witnessActiveClause :
    evalNode {} witnessActiveClause =
      .cls (linPredVP witnessSubjNP witnessActiveVP) := by
  have hCompl :
      evalNode {}
        (AbstractNode.apply
          { name := "ComplSlash",
            type := .arrow (.base "VPSlash") (.arrow (.base "NP") (.base "VP")) }
          [wMkApp1 "SlashV2a" "V2" "VPSlash" (wMkLeaf "love_V2" "V2"), witnessObjDog]) =
        .vp witnessActiveVP := by
    simpa [wMkApp2] using evalNode_ComplSlash_love_dog
  unfold evalNode witnessActiveClause wMkApp2
  simp only [evalArgs, evalNode_subjCat]
  rw [hCompl]
  simp only [dispatchApply_PredVP]

private theorem evalNode_witnessPassiveClause :
    evalNode {} witnessPassiveClause =
      .cls (linPredVP witnessObjNP witnessPassiveVP) := by
  unfold evalNode witnessPassiveClause wMkApp2
  simp only [evalArgs, evalNode_objDog, evalNode_PassV2_love, dispatchApply_PredVP]

private theorem renderCls_active :
    renderValue (.cls (linPredVP witnessSubjNP witnessActiveVP))
      { case := .Nom, number := .Sg } = "the cat loves the dog" := by rfl

private theorem renderCls_passive :
    renderValue (.cls (linPredVP witnessObjNP witnessPassiveVP))
      { case := .Nom, number := .Sg } = "the dog is loved" := by rfl

end WitnessLadder

theorem linearize_witnessActiveClause_nom_sg :
    linearizeTree {} witnessActiveClause .Nom .Sg =
      "the cat loves the dog" := by
  show renderValue (evalNode {} witnessActiveClause) _ = _
  rw [evalNode_witnessActiveClause, renderCls_active]

theorem linearize_witnessPassiveClause_nom_sg :
    linearizeTree {} witnessPassiveClause .Nom .Sg =
      "the dog is loved" := by
  show renderValue (evalNode {} witnessPassiveClause) _ = _
  rw [evalNode_witnessPassiveClause, renderCls_passive]

/-- Concrete string endpoint for the active PredVP/ComplSlash witness path. -/
theorem predvp_complslash_surface_eq_string :
    linearizeTree {} witnessActiveClause .Nom .Sg = "the cat loves the dog" :=
  linearize_witnessActiveClause_nom_sg

/-- Concrete string endpoint for the passive PredVP/PassV2 witness path. -/
theorem predvp_passv2_surface_eq_string :
    linearizeTree {} witnessPassiveClause .Nom .Sg = "the dog is loved" :=
  linearize_witnessPassiveClause_nom_sg

end Mettapedia.Languages.GF.English.Linearization
