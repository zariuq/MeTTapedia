-- AUTO-GENERATED from GF PGF export. Do not edit.
-- Grammar: PaperAmbiguity
-- Source hash: 
-- Functions: 26

import GFCore.Syntax
import Std.Data.HashMap

namespace Algorithms.GF.Generated.PaperAmbiguitySig

open GFCore

private def see_V2 : FunDecl :=
  { name := "see_V2", argCats := #[], resultCat := "V2", status := .primitive }

private def baby_N : FunDecl :=
  { name := "baby_N", argCats := #[], resultCat := "N", status := .primitive }

private def AdvVP : FunDecl :=
  { name := "AdvVP", argCats := #["VP", "Adv"], resultCat := "VP", status := .primitive }

private def anna_PN : FunDecl :=
  { name := "anna_PN", argCats := #[], resultCat := "PN", status := .primitive }

private def telescope_N : FunDecl :=
  { name := "telescope_N", argCats := #[], resultCat := "N", status := .primitive }

private def SlashV2a : FunDecl :=
  { name := "SlashV2a", argCats := #["V2"], resultCat := "VPSlash", status := .primitive }

private def UseN : FunDecl :=
  { name := "UseN", argCats := #["N"], resultCat := "CN", status := .primitive }

private def TTAnt : FunDecl :=
  { name := "TTAnt", argCats := #["Tense", "Ant"], resultCat := "Temp", status := .primitive }

private def DetCN : FunDecl :=
  { name := "DetCN", argCats := #["Det", "CN"], resultCat := "NP", status := .primitive }

private def UsePN : FunDecl :=
  { name := "UsePN", argCats := #["PN"], resultCat := "NP", status := .primitive }

private def the_Det : FunDecl :=
  { name := "the_Det", argCats := #[], resultCat := "Det", status := .primitive }

private def UseCl : FunDecl :=
  { name := "UseCl", argCats := #["Temp", "Pol", "Cl"], resultCat := "S", status := .primitive }

private def john_PN : FunDecl :=
  { name := "john_PN", argCats := #[], resultCat := "PN", status := .primitive }

private def with_Prep : FunDecl :=
  { name := "with_Prep", argCats := #[], resultCat := "Prep", status := .primitive }

private def TPast : FunDecl :=
  { name := "TPast", argCats := #[], resultCat := "Tense", status := .primitive }

private def AdvCN : FunDecl :=
  { name := "AdvCN", argCats := #["CN", "Adv"], resultCat := "CN", status := .primitive }

private def ASimul : FunDecl :=
  { name := "ASimul", argCats := #[], resultCat := "Ant", status := .primitive }

private def TPres : FunDecl :=
  { name := "TPres", argCats := #[], resultCat := "Tense", status := .primitive }

private def crib_N : FunDecl :=
  { name := "crib_N", argCats := #[], resultCat := "N", status := .primitive }

private def in_Prep : FunDecl :=
  { name := "in_Prep", argCats := #[], resultCat := "Prep", status := .primitive }

private def PrepNP : FunDecl :=
  { name := "PrepNP", argCats := #["Prep", "NP"], resultCat := "Adv", status := .primitive }

private def PPos : FunDecl :=
  { name := "PPos", argCats := #[], resultCat := "Pol", status := .primitive }

private def man_N : FunDecl :=
  { name := "man_N", argCats := #[], resultCat := "N", status := .primitive }

private def ComplSlash : FunDecl :=
  { name := "ComplSlash", argCats := #["VPSlash", "NP"], resultCat := "VP", status := .primitive }

private def dress_V2 : FunDecl :=
  { name := "dress_V2", argCats := #[], resultCat := "V2", status := .primitive }

private def PredVP : FunDecl :=
  { name := "PredVP", argCats := #["NP", "VP"], resultCat := "Cl", status := .primitive }

/-- The list of function declarations (kernel-reducible).
    Use this for proofs; `sig.funs` (HashMap) is for runtime lookup. -/
def funsList : List (String × FunDecl) :=
  [
    ("see_V2", see_V2),
    ("baby_N", baby_N),
    ("AdvVP", AdvVP),
    ("anna_PN", anna_PN),
    ("telescope_N", telescope_N),
    ("SlashV2a", SlashV2a),
    ("UseN", UseN),
    ("TTAnt", TTAnt),
    ("DetCN", DetCN),
    ("UsePN", UsePN),
    ("the_Det", the_Det),
    ("UseCl", UseCl),
    ("john_PN", john_PN),
    ("with_Prep", with_Prep),
    ("TPast", TPast),
    ("AdvCN", AdvCN),
    ("ASimul", ASimul),
    ("TPres", TPres),
    ("crib_N", crib_N),
    ("in_Prep", in_Prep),
    ("PrepNP", PrepNP),
    ("PPos", PPos),
    ("man_N", man_N),
    ("ComplSlash", ComplSlash),
    ("dress_V2", dress_V2),
    ("PredVP", PredVP),
  ]

def sig : GrammarSig where
  grammar := "PaperAmbiguity"
  startCats := #["S"]
  sourceHash := ""
  funs := Std.HashMap.ofList funsList

end Algorithms.GF.Generated.PaperAmbiguitySig
