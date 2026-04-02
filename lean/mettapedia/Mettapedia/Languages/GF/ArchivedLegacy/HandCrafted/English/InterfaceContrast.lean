import Mettapedia.Languages.GF.WorldModelSemantics
import Mettapedia.Languages.GF.HandCrafted.English.Linearization.Witnesses
import Mettapedia.Languages.GF.HandCrafted.English.Syntax
import Mettapedia.Languages.GF.HandCrafted.English.Nouns
import Mettapedia.Languages.GF.HandCrafted.English.Verbs
import Mettapedia.OSLF.Framework.TypeSynthesis

/-!
# GF English Interface Contrast

A compact theorem bundle showing an LF/PF split on a concrete English witness:

- LF-side consequence: active clause reduces to passive clause in GF/OSLF.
- PF-side distinction: English linearization keeps the two surfaces distinct.

This is a small but semantically meaningful endpoint for interface-relative
equivalence claims.

Conceptual source note:
- Interface-relative equivalence framing follows the TUG/Hyperseed line:
  observe LF consequences while retaining PF-level distinguishability.
-/

namespace Mettapedia.Languages.GF.HandCrafted.English.InterfaceContrast

open Mettapedia.Languages.GF
open Mettapedia.Languages.GF.HandCrafted.Abstract
open Mettapedia.Languages.GF.Typing
open Mettapedia.Languages.GF.OSLFBridge
open Mettapedia.Languages.GF.WorldModelSemantics
open Mettapedia.Languages.GF.HandCrafted.English.Linearization
open Mettapedia.Languages.GF.HandCrafted.English.Syntax
open Mettapedia.Languages.GF.HandCrafted.English.Nouns
open Mettapedia.Languages.GF.HandCrafted.English.Verbs
open Mettapedia.OSLF.Framework.TypeSynthesis

/-- Subject NP: "the cat". -/
def subjCat : AbstractNode :=
  mkApp2 "DetCN" "Det" "CN" "NP"
    (mkLeaf "the_Det" "Det")
    (mkApp1 "UseN" "N" "CN" (mkLeaf "cat_N" "N"))

/-- Object NP: "the dog". -/
def objDog : AbstractNode :=
  mkApp2 "DetCN" "Det" "CN" "NP"
    (mkLeaf "the_Det" "Det")
    (mkApp1 "UseN" "N" "CN" (mkLeaf "dog_N" "N"))

/-- Active clause witness: "the cat loves the dog". -/
def activeClause : AbstractNode :=
  mkApp2 "PredVP" "NP" "VP" "Cl"
    subjCat
    (mkApp2 "ComplSlash" "VPSlash" "NP" "VP"
      (mkApp1 "SlashV2a" "V2" "VPSlash" (mkLeaf "love_V2" "V2"))
      objDog)

/-- Passive clause witness: "the dog is loved". -/
def passiveClause : AbstractNode :=
  mkApp2 "PredVP" "NP" "VP" "Cl"
    objDog
    (mkApp1 "PassV2" "V2" "VP" (mkLeaf "love_V2" "V2"))

/-- LF consequence endpoint: the active witness reduces to the passive witness. -/
theorem active_reduces_to_passive :
    langReduces gfRGLLanguageDef
      (gfAbstractToPattern activeClause)
      (gfAbstractToPattern passiveClause) := by
  simpa [activeClause, passiveClause, subjCat, objDog, mkApp2, mkApp1, mkLeaf]
    using
      (langReduces_activePassive
        (gfAbstractToPattern subjCat)
        (gfAbstractToPattern objDog)
        (gfAbstractToPattern (mkLeaf "love_V2" "V2")))

/-- Derivational witness: active and passive trees are syntactically distinct. -/
theorem active_clause_ne_passive_clause :
    activeClause ≠ passiveClause := by
  intro hEq
  simp [activeClause, passiveClause, subjCat, objDog, mkApp2, mkApp1, mkLeaf] at hEq

-- Executable PF witnesses (for paper/demo use).
#eval! linearizeTree {} activeClause .Nom .Sg
#eval! linearizeTree {} passiveClause .Nom .Sg

/-! ## Certified PF Decision Procedure (Kernel-Checked)

This layer computes active/passive surface witnesses through total `Syntax`
combinators (no opaque `partial` evaluator calls).
-/

/-- Public passive VP constructor mirroring the `PassV2` branch used in
English linearization. -/
def passV2Certified (v2 : EnglishV2) : EnglishVP :=
  passV2Canonical v2

/-- Certified active surface witness through total `Syntax` constructors. -/
def activeSurfaceCertified : String :=
  linUseCl .Pres .Simul .CPos
    (linPredVP
      (linDetCN theDefArt (linUseN cat_N))
      (complV2 love_V2 (linDetCN theDefArt (linUseN dog_N))))

/-- Certified passive surface witness through total `Syntax` constructors. -/
def passiveSurfaceCertified : String :=
  linUseCl .Pres .Simul .CPos
    (linPredVP
      (linDetCN theDefArt (linUseN dog_N))
      (passV2Certified love_V2))

theorem activeSurfaceCertified_eq :
    activeSurfaceCertified = "the cat loves the dog" := by
  decide

theorem passiveSurfaceCertified_eq :
    passiveSurfaceCertified = "the dog is loved" := by
  decide

theorem activeSurfaceCertified_ne_passiveSurfaceCertified :
    activeSurfaceCertified ≠ passiveSurfaceCertified := by
  decide

/-- Bridge endpoint for active witness against the certified surface. -/
theorem active_linearize_eq_certified :
    linearizeTree {} activeClause .Nom .Sg = activeSurfaceCertified := by
  calc
    linearizeTree {} activeClause .Nom .Sg
        = "the cat loves the dog" := by
          simpa [activeClause, subjCat, objDog, mkApp2, mkApp1, mkLeaf]
            using linearize_witnessActiveClause_nom_sg
    _ = activeSurfaceCertified := by
      simpa [activeSurfaceCertified] using (Eq.symm activeSurfaceCertified_eq)

/-- Bridge endpoint for passive witness against the certified surface. -/
theorem passive_linearize_eq_certified :
    linearizeTree {} passiveClause .Nom .Sg = passiveSurfaceCertified := by
  calc
    linearizeTree {} passiveClause .Nom .Sg
        = "the dog is loved" := by
          simpa [passiveClause, objDog, mkApp2, mkApp1, mkLeaf]
            using linearize_witnessPassiveClause_nom_sg
    _ = passiveSurfaceCertified := by
      simpa [passiveSurfaceCertified, passV2Certified] using (Eq.symm passiveSurfaceCertified_eq)

/-- Bridge theorem: if the opaque runtime linearizer agrees on these two
witnesses with the certified surfaces, PF distinction follows kernel-checkably. -/
theorem active_pf_string_ne_passive_pf_string_of_certified_bridge
    (hActive :
      linearizeTree {} activeClause .Nom .Sg = activeSurfaceCertified)
    (hPassive :
      linearizeTree {} passiveClause .Nom .Sg = passiveSurfaceCertified) :
    linearizeTree {} activeClause .Nom .Sg ≠
      linearizeTree {} passiveClause .Nom .Sg := by
  intro hEq
  have hcert : activeSurfaceCertified = passiveSurfaceCertified := by
    simpa [hActive, hPassive] using hEq
  exact activeSurfaceCertified_ne_passiveSurfaceCertified hcert

/-- PF witness: active and passive linearizations are distinct strings. -/
theorem active_pf_string_ne_passive_pf_string :
    linearizeTree {} activeClause .Nom .Sg ≠
      linearizeTree {} passiveClause .Nom .Sg := by
  exact active_pf_string_ne_passive_pf_string_of_certified_bridge
    active_linearize_eq_certified
    passive_linearize_eq_certified

/-- Combined interface contrast endpoint:
LF consequence holds while PF strings remain distinct. -/
theorem lf_consequence_distinct_witness :
    langReduces gfRGLLanguageDef
      (gfAbstractToPattern activeClause)
      (gfAbstractToPattern passiveClause) ∧
    activeClause ≠ passiveClause :=
  ⟨active_reduces_to_passive, active_clause_ne_passive_clause⟩

end Mettapedia.Languages.GF.HandCrafted.English.InterfaceContrast
