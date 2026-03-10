import Algorithms.GF.CYK
namespace Algorithms.GF.Generated.PaperAmbiguityIR

open Algorithms.GF.CompiledIR
open Algorithms.GF.Tokenize
open Algorithms.GF.CYK

def englishGrammar : NormalizedGrammar :=
  { language := "PaperAmbiguityEng", startCats := #["S"], productions := #[
  { lhs := "PN__englishTelescope__p1__2_0_0", rhs := .terminal "john", funName := "john_PN", sem := .node "john_PN" [] },
  { lhs := "NP__englishTelescope__p1__2_0", rhs := .unary "PN__englishTelescope__p1__2_0_0", funName := "UsePN", sem := .node "UsePN" [
    .ref 0
  ] },
  { lhs := "V2__englishTelescope__p1__2_1_0_0_0", rhs := .terminal "sees", funName := "see_V2", sem := .node "see_V2" [] },
  { lhs := "VPSlash__englishTelescope__p1__2_1_0_0", rhs := .unary "V2__englishTelescope__p1__2_1_0_0_0", funName := "SlashV2a", sem := .node "SlashV2a" [
    .ref 0
  ] },
  { lhs := "Det__englishTelescope__p1__2_1_0_1_0", rhs := .terminal "the", funName := "the_Det", sem := .node "the_Det" [] },
  { lhs := "N__englishTelescope__p1__2_1_0_1_1_0", rhs := .terminal "man", funName := "man_N", sem := .node "man_N" [] },
  { lhs := "CN__englishTelescope__p1__2_1_0_1_1", rhs := .unary "N__englishTelescope__p1__2_1_0_1_1_0", funName := "UseN", sem := .node "UseN" [
    .ref 0
  ] },
  { lhs := "NP__englishTelescope__p1__2_1_0_1", rhs := .binary "Det__englishTelescope__p1__2_1_0_1_0" "CN__englishTelescope__p1__2_1_0_1_1", funName := "DetCN", sem := .node "DetCN" [
    .ref 0,
    .ref 1
  ] },
  { lhs := "VP__englishTelescope__p1__2_1_0", rhs := .binary "VPSlash__englishTelescope__p1__2_1_0_0" "NP__englishTelescope__p1__2_1_0_1", funName := "ComplSlash", sem := .node "ComplSlash" [
    .ref 0,
    .ref 1
  ] },
  { lhs := "Prep__englishTelescope__p1__2_1_1_0", rhs := .terminal "with", funName := "with_Prep", sem := .node "with_Prep" [] },
  { lhs := "Det__englishTelescope__p1__2_1_1_1_0", rhs := .terminal "the", funName := "the_Det", sem := .node "the_Det" [] },
  { lhs := "N__englishTelescope__p1__2_1_1_1_1_0", rhs := .terminal "telescope", funName := "telescope_N", sem := .node "telescope_N" [] },
  { lhs := "CN__englishTelescope__p1__2_1_1_1_1", rhs := .unary "N__englishTelescope__p1__2_1_1_1_1_0", funName := "UseN", sem := .node "UseN" [
    .ref 0
  ] },
  { lhs := "NP__englishTelescope__p1__2_1_1_1", rhs := .binary "Det__englishTelescope__p1__2_1_1_1_0" "CN__englishTelescope__p1__2_1_1_1_1", funName := "DetCN", sem := .node "DetCN" [
    .ref 0,
    .ref 1
  ] },
  { lhs := "Adv__englishTelescope__p1__2_1_1", rhs := .binary "Prep__englishTelescope__p1__2_1_1_0" "NP__englishTelescope__p1__2_1_1_1", funName := "PrepNP", sem := .node "PrepNP" [
    .ref 0,
    .ref 1
  ] },
  { lhs := "VP__englishTelescope__p1__2_1", rhs := .binary "VP__englishTelescope__p1__2_1_0" "Adv__englishTelescope__p1__2_1_1", funName := "AdvVP", sem := .node "AdvVP" [
    .ref 0,
    .ref 1
  ] },
  { lhs := "Cl__englishTelescope__p1__2", rhs := .binary "NP__englishTelescope__p1__2_0" "VP__englishTelescope__p1__2_1", funName := "PredVP", sem := .node "PredVP" [
    .ref 0,
    .ref 1
  ] },
  { lhs := "S", rhs := .unary "Cl__englishTelescope__p1__2", funName := "UseCl", sem := .node "UseCl" [
    .node "TTAnt" [
      .node "TPres" [],
      .node "ASimul" []
    ],
    .node "PPos" [],
    .ref 0
  ] },
  { lhs := "PN__englishTelescope__p2__2_0_0", rhs := .terminal "john", funName := "john_PN", sem := .node "john_PN" [] },
  { lhs := "NP__englishTelescope__p2__2_0", rhs := .unary "PN__englishTelescope__p2__2_0_0", funName := "UsePN", sem := .node "UsePN" [
    .ref 0
  ] },
  { lhs := "V2__englishTelescope__p2__2_1_0_0", rhs := .terminal "sees", funName := "see_V2", sem := .node "see_V2" [] },
  { lhs := "VPSlash__englishTelescope__p2__2_1_0", rhs := .unary "V2__englishTelescope__p2__2_1_0_0", funName := "SlashV2a", sem := .node "SlashV2a" [
    .ref 0
  ] },
  { lhs := "Det__englishTelescope__p2__2_1_1_0", rhs := .terminal "the", funName := "the_Det", sem := .node "the_Det" [] },
  { lhs := "N__englishTelescope__p2__2_1_1_1_0_0", rhs := .terminal "man", funName := "man_N", sem := .node "man_N" [] },
  { lhs := "CN__englishTelescope__p2__2_1_1_1_0", rhs := .unary "N__englishTelescope__p2__2_1_1_1_0_0", funName := "UseN", sem := .node "UseN" [
    .ref 0
  ] },
  { lhs := "Prep__englishTelescope__p2__2_1_1_1_1_0", rhs := .terminal "with", funName := "with_Prep", sem := .node "with_Prep" [] },
  { lhs := "Det__englishTelescope__p2__2_1_1_1_1_1_0", rhs := .terminal "the", funName := "the_Det", sem := .node "the_Det" [] },
  { lhs := "N__englishTelescope__p2__2_1_1_1_1_1_1_0", rhs := .terminal "telescope", funName := "telescope_N", sem := .node "telescope_N" [] },
  { lhs := "CN__englishTelescope__p2__2_1_1_1_1_1_1", rhs := .unary "N__englishTelescope__p2__2_1_1_1_1_1_1_0", funName := "UseN", sem := .node "UseN" [
    .ref 0
  ] },
  { lhs := "NP__englishTelescope__p2__2_1_1_1_1_1", rhs := .binary "Det__englishTelescope__p2__2_1_1_1_1_1_0" "CN__englishTelescope__p2__2_1_1_1_1_1_1", funName := "DetCN", sem := .node "DetCN" [
    .ref 0,
    .ref 1
  ] },
  { lhs := "Adv__englishTelescope__p2__2_1_1_1_1", rhs := .binary "Prep__englishTelescope__p2__2_1_1_1_1_0" "NP__englishTelescope__p2__2_1_1_1_1_1", funName := "PrepNP", sem := .node "PrepNP" [
    .ref 0,
    .ref 1
  ] },
  { lhs := "CN__englishTelescope__p2__2_1_1_1", rhs := .binary "CN__englishTelescope__p2__2_1_1_1_0" "Adv__englishTelescope__p2__2_1_1_1_1", funName := "AdvCN", sem := .node "AdvCN" [
    .ref 0,
    .ref 1
  ] },
  { lhs := "NP__englishTelescope__p2__2_1_1", rhs := .binary "Det__englishTelescope__p2__2_1_1_0" "CN__englishTelescope__p2__2_1_1_1", funName := "DetCN", sem := .node "DetCN" [
    .ref 0,
    .ref 1
  ] },
  { lhs := "VP__englishTelescope__p2__2_1", rhs := .binary "VPSlash__englishTelescope__p2__2_1_0" "NP__englishTelescope__p2__2_1_1", funName := "ComplSlash", sem := .node "ComplSlash" [
    .ref 0,
    .ref 1
  ] },
  { lhs := "Cl__englishTelescope__p2__2", rhs := .binary "NP__englishTelescope__p2__2_0" "VP__englishTelescope__p2__2_1", funName := "PredVP", sem := .node "PredVP" [
    .ref 0,
    .ref 1
  ] },
  { lhs := "S", rhs := .unary "Cl__englishTelescope__p2__2", funName := "UseCl", sem := .node "UseCl" [
    .node "TTAnt" [
      .node "TPres" [],
      .node "ASimul" []
    ],
    .node "PPos" [],
    .ref 0
  ] },
  { lhs := "PN__englishAnna__p1__2_0_0", rhs := .terminal "anna", funName := "anna_PN", sem := .node "anna_PN" [] },
  { lhs := "NP__englishAnna__p1__2_0", rhs := .unary "PN__englishAnna__p1__2_0_0", funName := "UsePN", sem := .node "UsePN" [
    .ref 0
  ] },
  { lhs := "V2__englishAnna__p1__2_1_0_0_0", rhs := .terminal "dresses", funName := "dress_V2", sem := .node "dress_V2" [] },
  { lhs := "VPSlash__englishAnna__p1__2_1_0_0", rhs := .unary "V2__englishAnna__p1__2_1_0_0_0", funName := "SlashV2a", sem := .node "SlashV2a" [
    .ref 0
  ] },
  { lhs := "Det__englishAnna__p1__2_1_0_1_0", rhs := .terminal "the", funName := "the_Det", sem := .node "the_Det" [] },
  { lhs := "N__englishAnna__p1__2_1_0_1_1_0", rhs := .terminal "baby", funName := "baby_N", sem := .node "baby_N" [] },
  { lhs := "CN__englishAnna__p1__2_1_0_1_1", rhs := .unary "N__englishAnna__p1__2_1_0_1_1_0", funName := "UseN", sem := .node "UseN" [
    .ref 0
  ] },
  { lhs := "NP__englishAnna__p1__2_1_0_1", rhs := .binary "Det__englishAnna__p1__2_1_0_1_0" "CN__englishAnna__p1__2_1_0_1_1", funName := "DetCN", sem := .node "DetCN" [
    .ref 0,
    .ref 1
  ] },
  { lhs := "VP__englishAnna__p1__2_1_0", rhs := .binary "VPSlash__englishAnna__p1__2_1_0_0" "NP__englishAnna__p1__2_1_0_1", funName := "ComplSlash", sem := .node "ComplSlash" [
    .ref 0,
    .ref 1
  ] },
  { lhs := "Prep__englishAnna__p1__2_1_1_0", rhs := .terminal "in", funName := "in_Prep", sem := .node "in_Prep" [] },
  { lhs := "Det__englishAnna__p1__2_1_1_1_0", rhs := .terminal "the", funName := "the_Det", sem := .node "the_Det" [] },
  { lhs := "N__englishAnna__p1__2_1_1_1_1_0", rhs := .terminal "crib", funName := "crib_N", sem := .node "crib_N" [] },
  { lhs := "CN__englishAnna__p1__2_1_1_1_1", rhs := .unary "N__englishAnna__p1__2_1_1_1_1_0", funName := "UseN", sem := .node "UseN" [
    .ref 0
  ] },
  { lhs := "NP__englishAnna__p1__2_1_1_1", rhs := .binary "Det__englishAnna__p1__2_1_1_1_0" "CN__englishAnna__p1__2_1_1_1_1", funName := "DetCN", sem := .node "DetCN" [
    .ref 0,
    .ref 1
  ] },
  { lhs := "Adv__englishAnna__p1__2_1_1", rhs := .binary "Prep__englishAnna__p1__2_1_1_0" "NP__englishAnna__p1__2_1_1_1", funName := "PrepNP", sem := .node "PrepNP" [
    .ref 0,
    .ref 1
  ] },
  { lhs := "VP__englishAnna__p1__2_1", rhs := .binary "VP__englishAnna__p1__2_1_0" "Adv__englishAnna__p1__2_1_1", funName := "AdvVP", sem := .node "AdvVP" [
    .ref 0,
    .ref 1
  ] },
  { lhs := "Cl__englishAnna__p1__2", rhs := .binary "NP__englishAnna__p1__2_0" "VP__englishAnna__p1__2_1", funName := "PredVP", sem := .node "PredVP" [
    .ref 0,
    .ref 1
  ] },
  { lhs := "S", rhs := .unary "Cl__englishAnna__p1__2", funName := "UseCl", sem := .node "UseCl" [
    .node "TTAnt" [
      .node "TPres" [],
      .node "ASimul" []
    ],
    .node "PPos" [],
    .ref 0
  ] },
  { lhs := "PN__englishAnna__p2__2_0_0", rhs := .terminal "anna", funName := "anna_PN", sem := .node "anna_PN" [] },
  { lhs := "NP__englishAnna__p2__2_0", rhs := .unary "PN__englishAnna__p2__2_0_0", funName := "UsePN", sem := .node "UsePN" [
    .ref 0
  ] },
  { lhs := "V2__englishAnna__p2__2_1_0_0", rhs := .terminal "dresses", funName := "dress_V2", sem := .node "dress_V2" [] },
  { lhs := "VPSlash__englishAnna__p2__2_1_0", rhs := .unary "V2__englishAnna__p2__2_1_0_0", funName := "SlashV2a", sem := .node "SlashV2a" [
    .ref 0
  ] },
  { lhs := "Det__englishAnna__p2__2_1_1_0", rhs := .terminal "the", funName := "the_Det", sem := .node "the_Det" [] },
  { lhs := "N__englishAnna__p2__2_1_1_1_0_0", rhs := .terminal "baby", funName := "baby_N", sem := .node "baby_N" [] },
  { lhs := "CN__englishAnna__p2__2_1_1_1_0", rhs := .unary "N__englishAnna__p2__2_1_1_1_0_0", funName := "UseN", sem := .node "UseN" [
    .ref 0
  ] },
  { lhs := "Prep__englishAnna__p2__2_1_1_1_1_0", rhs := .terminal "in", funName := "in_Prep", sem := .node "in_Prep" [] },
  { lhs := "Det__englishAnna__p2__2_1_1_1_1_1_0", rhs := .terminal "the", funName := "the_Det", sem := .node "the_Det" [] },
  { lhs := "N__englishAnna__p2__2_1_1_1_1_1_1_0", rhs := .terminal "crib", funName := "crib_N", sem := .node "crib_N" [] },
  { lhs := "CN__englishAnna__p2__2_1_1_1_1_1_1", rhs := .unary "N__englishAnna__p2__2_1_1_1_1_1_1_0", funName := "UseN", sem := .node "UseN" [
    .ref 0
  ] },
  { lhs := "NP__englishAnna__p2__2_1_1_1_1_1", rhs := .binary "Det__englishAnna__p2__2_1_1_1_1_1_0" "CN__englishAnna__p2__2_1_1_1_1_1_1", funName := "DetCN", sem := .node "DetCN" [
    .ref 0,
    .ref 1
  ] },
  { lhs := "Adv__englishAnna__p2__2_1_1_1_1", rhs := .binary "Prep__englishAnna__p2__2_1_1_1_1_0" "NP__englishAnna__p2__2_1_1_1_1_1", funName := "PrepNP", sem := .node "PrepNP" [
    .ref 0,
    .ref 1
  ] },
  { lhs := "CN__englishAnna__p2__2_1_1_1", rhs := .binary "CN__englishAnna__p2__2_1_1_1_0" "Adv__englishAnna__p2__2_1_1_1_1", funName := "AdvCN", sem := .node "AdvCN" [
    .ref 0,
    .ref 1
  ] },
  { lhs := "NP__englishAnna__p2__2_1_1", rhs := .binary "Det__englishAnna__p2__2_1_1_0" "CN__englishAnna__p2__2_1_1_1", funName := "DetCN", sem := .node "DetCN" [
    .ref 0,
    .ref 1
  ] },
  { lhs := "VP__englishAnna__p2__2_1", rhs := .binary "VPSlash__englishAnna__p2__2_1_0" "NP__englishAnna__p2__2_1_1", funName := "ComplSlash", sem := .node "ComplSlash" [
    .ref 0,
    .ref 1
  ] },
  { lhs := "Cl__englishAnna__p2__2", rhs := .binary "NP__englishAnna__p2__2_0" "VP__englishAnna__p2__2_1", funName := "PredVP", sem := .node "PredVP" [
    .ref 0,
    .ref 1
  ] },
  { lhs := "S", rhs := .unary "Cl__englishAnna__p2__2", funName := "UseCl", sem := .node "UseCl" [
    .node "TTAnt" [
      .node "TPres" [],
      .node "ASimul" []
    ],
    .node "PPos" [],
    .ref 0
  ] }
  ] }

def czechGrammar : NormalizedGrammar :=
  { language := "PaperAmbiguityCze", startCats := #["S"], productions := #[
  { lhs := "PN__czechTelescope__p1__2_0_0", rhs := .terminal "jan", funName := "john_PN", sem := .node "john_PN" [] },
  { lhs := "NP__czechTelescope__p1__2_0", rhs := .unary "PN__czechTelescope__p1__2_0_0", funName := "UsePN", sem := .node "UsePN" [
    .ref 0
  ] },
  { lhs := "V2__czechTelescope__p1__2_1_0_0_0", rhs := .terminal "vidí", funName := "see_V2", sem := .node "see_V2" [] },
  { lhs := "VPSlash__czechTelescope__p1__2_1_0_0", rhs := .unary "V2__czechTelescope__p1__2_1_0_0_0", funName := "SlashV2a", sem := .node "SlashV2a" [
    .ref 0
  ] },
  { lhs := "N__czechTelescope__p1__2_1_0_1_1_0", rhs := .terminal "muže", funName := "man_N", sem := .node "man_N" [] },
  { lhs := "CN__czechTelescope__p1__2_1_0_1_1", rhs := .unary "N__czechTelescope__p1__2_1_0_1_1_0", funName := "UseN", sem := .node "UseN" [
    .ref 0
  ] },
  { lhs := "NP__czechTelescope__p1__2_1_0_1", rhs := .unary "CN__czechTelescope__p1__2_1_0_1_1", funName := "DetCN", sem := .node "DetCN" [
    .node "the_Det" [],
    .ref 0
  ] },
  { lhs := "VP__czechTelescope__p1__2_1_0", rhs := .binary "VPSlash__czechTelescope__p1__2_1_0_0" "NP__czechTelescope__p1__2_1_0_1", funName := "ComplSlash", sem := .node "ComplSlash" [
    .ref 0,
    .ref 1
  ] },
  { lhs := "Prep__czechTelescope__p1__2_1_1_0", rhs := .terminal "s", funName := "with_Prep", sem := .node "with_Prep" [] },
  { lhs := "N__czechTelescope__p1__2_1_1_1_1_0", rhs := .terminal "teleskopem", funName := "telescope_N", sem := .node "telescope_N" [] },
  { lhs := "CN__czechTelescope__p1__2_1_1_1_1", rhs := .unary "N__czechTelescope__p1__2_1_1_1_1_0", funName := "UseN", sem := .node "UseN" [
    .ref 0
  ] },
  { lhs := "NP__czechTelescope__p1__2_1_1_1", rhs := .unary "CN__czechTelescope__p1__2_1_1_1_1", funName := "DetCN", sem := .node "DetCN" [
    .node "the_Det" [],
    .ref 0
  ] },
  { lhs := "Adv__czechTelescope__p1__2_1_1", rhs := .binary "Prep__czechTelescope__p1__2_1_1_0" "NP__czechTelescope__p1__2_1_1_1", funName := "PrepNP", sem := .node "PrepNP" [
    .ref 0,
    .ref 1
  ] },
  { lhs := "VP__czechTelescope__p1__2_1", rhs := .binary "VP__czechTelescope__p1__2_1_0" "Adv__czechTelescope__p1__2_1_1", funName := "AdvVP", sem := .node "AdvVP" [
    .ref 0,
    .ref 1
  ] },
  { lhs := "Cl__czechTelescope__p1__2", rhs := .binary "NP__czechTelescope__p1__2_0" "VP__czechTelescope__p1__2_1", funName := "PredVP", sem := .node "PredVP" [
    .ref 0,
    .ref 1
  ] },
  { lhs := "S", rhs := .unary "Cl__czechTelescope__p1__2", funName := "UseCl", sem := .node "UseCl" [
    .node "TTAnt" [
      .node "TPres" [],
      .node "ASimul" []
    ],
    .node "PPos" [],
    .ref 0
  ] },
  { lhs := "PN__czechTelescope__p2__2_0_0", rhs := .terminal "jan", funName := "john_PN", sem := .node "john_PN" [] },
  { lhs := "NP__czechTelescope__p2__2_0", rhs := .unary "PN__czechTelescope__p2__2_0_0", funName := "UsePN", sem := .node "UsePN" [
    .ref 0
  ] },
  { lhs := "V2__czechTelescope__p2__2_1_0_0", rhs := .terminal "vidí", funName := "see_V2", sem := .node "see_V2" [] },
  { lhs := "VPSlash__czechTelescope__p2__2_1_0", rhs := .unary "V2__czechTelescope__p2__2_1_0_0", funName := "SlashV2a", sem := .node "SlashV2a" [
    .ref 0
  ] },
  { lhs := "N__czechTelescope__p2__2_1_1_1_0_0", rhs := .terminal "muže", funName := "man_N", sem := .node "man_N" [] },
  { lhs := "CN__czechTelescope__p2__2_1_1_1_0", rhs := .unary "N__czechTelescope__p2__2_1_1_1_0_0", funName := "UseN", sem := .node "UseN" [
    .ref 0
  ] },
  { lhs := "Prep__czechTelescope__p2__2_1_1_1_1_0", rhs := .terminal "s", funName := "with_Prep", sem := .node "with_Prep" [] },
  { lhs := "N__czechTelescope__p2__2_1_1_1_1_1_1_0", rhs := .terminal "teleskopem", funName := "telescope_N", sem := .node "telescope_N" [] },
  { lhs := "CN__czechTelescope__p2__2_1_1_1_1_1_1", rhs := .unary "N__czechTelescope__p2__2_1_1_1_1_1_1_0", funName := "UseN", sem := .node "UseN" [
    .ref 0
  ] },
  { lhs := "NP__czechTelescope__p2__2_1_1_1_1_1", rhs := .unary "CN__czechTelescope__p2__2_1_1_1_1_1_1", funName := "DetCN", sem := .node "DetCN" [
    .node "the_Det" [],
    .ref 0
  ] },
  { lhs := "Adv__czechTelescope__p2__2_1_1_1_1", rhs := .binary "Prep__czechTelescope__p2__2_1_1_1_1_0" "NP__czechTelescope__p2__2_1_1_1_1_1", funName := "PrepNP", sem := .node "PrepNP" [
    .ref 0,
    .ref 1
  ] },
  { lhs := "CN__czechTelescope__p2__2_1_1_1", rhs := .binary "CN__czechTelescope__p2__2_1_1_1_0" "Adv__czechTelescope__p2__2_1_1_1_1", funName := "AdvCN", sem := .node "AdvCN" [
    .ref 0,
    .ref 1
  ] },
  { lhs := "NP__czechTelescope__p2__2_1_1", rhs := .unary "CN__czechTelescope__p2__2_1_1_1", funName := "DetCN", sem := .node "DetCN" [
    .node "the_Det" [],
    .ref 0
  ] },
  { lhs := "VP__czechTelescope__p2__2_1", rhs := .binary "VPSlash__czechTelescope__p2__2_1_0" "NP__czechTelescope__p2__2_1_1", funName := "ComplSlash", sem := .node "ComplSlash" [
    .ref 0,
    .ref 1
  ] },
  { lhs := "Cl__czechTelescope__p2__2", rhs := .binary "NP__czechTelescope__p2__2_0" "VP__czechTelescope__p2__2_1", funName := "PredVP", sem := .node "PredVP" [
    .ref 0,
    .ref 1
  ] },
  { lhs := "S", rhs := .unary "Cl__czechTelescope__p2__2", funName := "UseCl", sem := .node "UseCl" [
    .node "TTAnt" [
      .node "TPres" [],
      .node "ASimul" []
    ],
    .node "PPos" [],
    .ref 0
  ] },
  { lhs := "PN__czechAnna__p1__2_0_0", rhs := .terminal "anna", funName := "anna_PN", sem := .node "anna_PN" [] },
  { lhs := "NP__czechAnna__p1__2_0", rhs := .unary "PN__czechAnna__p1__2_0_0", funName := "UsePN", sem := .node "UsePN" [
    .ref 0
  ] },
  { lhs := "V2__czechAnna__p1__2_1_0_0_0", rhs := .terminal "obléká", funName := "dress_V2", sem := .node "dress_V2" [] },
  { lhs := "VPSlash__czechAnna__p1__2_1_0_0", rhs := .unary "V2__czechAnna__p1__2_1_0_0_0", funName := "SlashV2a", sem := .node "SlashV2a" [
    .ref 0
  ] },
  { lhs := "N__czechAnna__p1__2_1_0_1_1_0", rhs := .terminal "dítě", funName := "baby_N", sem := .node "baby_N" [] },
  { lhs := "CN__czechAnna__p1__2_1_0_1_1", rhs := .unary "N__czechAnna__p1__2_1_0_1_1_0", funName := "UseN", sem := .node "UseN" [
    .ref 0
  ] },
  { lhs := "NP__czechAnna__p1__2_1_0_1", rhs := .unary "CN__czechAnna__p1__2_1_0_1_1", funName := "DetCN", sem := .node "DetCN" [
    .node "the_Det" [],
    .ref 0
  ] },
  { lhs := "VP__czechAnna__p1__2_1_0", rhs := .binary "VPSlash__czechAnna__p1__2_1_0_0" "NP__czechAnna__p1__2_1_0_1", funName := "ComplSlash", sem := .node "ComplSlash" [
    .ref 0,
    .ref 1
  ] },
  { lhs := "Prep__czechAnna__p1__2_1_1_0", rhs := .terminal "v", funName := "in_Prep", sem := .node "in_Prep" [] },
  { lhs := "N__czechAnna__p1__2_1_1_1_1_0", rhs := .terminal "kolébkě", funName := "crib_N", sem := .node "crib_N" [] },
  { lhs := "CN__czechAnna__p1__2_1_1_1_1", rhs := .unary "N__czechAnna__p1__2_1_1_1_1_0", funName := "UseN", sem := .node "UseN" [
    .ref 0
  ] },
  { lhs := "NP__czechAnna__p1__2_1_1_1", rhs := .unary "CN__czechAnna__p1__2_1_1_1_1", funName := "DetCN", sem := .node "DetCN" [
    .node "the_Det" [],
    .ref 0
  ] },
  { lhs := "Adv__czechAnna__p1__2_1_1", rhs := .binary "Prep__czechAnna__p1__2_1_1_0" "NP__czechAnna__p1__2_1_1_1", funName := "PrepNP", sem := .node "PrepNP" [
    .ref 0,
    .ref 1
  ] },
  { lhs := "VP__czechAnna__p1__2_1", rhs := .binary "VP__czechAnna__p1__2_1_0" "Adv__czechAnna__p1__2_1_1", funName := "AdvVP", sem := .node "AdvVP" [
    .ref 0,
    .ref 1
  ] },
  { lhs := "Cl__czechAnna__p1__2", rhs := .binary "NP__czechAnna__p1__2_0" "VP__czechAnna__p1__2_1", funName := "PredVP", sem := .node "PredVP" [
    .ref 0,
    .ref 1
  ] },
  { lhs := "S", rhs := .unary "Cl__czechAnna__p1__2", funName := "UseCl", sem := .node "UseCl" [
    .node "TTAnt" [
      .node "TPres" [],
      .node "ASimul" []
    ],
    .node "PPos" [],
    .ref 0
  ] },
  { lhs := "PN__czechAnna__p2__2_0_0", rhs := .terminal "anna", funName := "anna_PN", sem := .node "anna_PN" [] },
  { lhs := "NP__czechAnna__p2__2_0", rhs := .unary "PN__czechAnna__p2__2_0_0", funName := "UsePN", sem := .node "UsePN" [
    .ref 0
  ] },
  { lhs := "V2__czechAnna__p2__2_1_0_0", rhs := .terminal "obléká", funName := "dress_V2", sem := .node "dress_V2" [] },
  { lhs := "VPSlash__czechAnna__p2__2_1_0", rhs := .unary "V2__czechAnna__p2__2_1_0_0", funName := "SlashV2a", sem := .node "SlashV2a" [
    .ref 0
  ] },
  { lhs := "N__czechAnna__p2__2_1_1_1_0_0", rhs := .terminal "dítě", funName := "baby_N", sem := .node "baby_N" [] },
  { lhs := "CN__czechAnna__p2__2_1_1_1_0", rhs := .unary "N__czechAnna__p2__2_1_1_1_0_0", funName := "UseN", sem := .node "UseN" [
    .ref 0
  ] },
  { lhs := "Prep__czechAnna__p2__2_1_1_1_1_0", rhs := .terminal "v", funName := "in_Prep", sem := .node "in_Prep" [] },
  { lhs := "N__czechAnna__p2__2_1_1_1_1_1_1_0", rhs := .terminal "kolébkě", funName := "crib_N", sem := .node "crib_N" [] },
  { lhs := "CN__czechAnna__p2__2_1_1_1_1_1_1", rhs := .unary "N__czechAnna__p2__2_1_1_1_1_1_1_0", funName := "UseN", sem := .node "UseN" [
    .ref 0
  ] },
  { lhs := "NP__czechAnna__p2__2_1_1_1_1_1", rhs := .unary "CN__czechAnna__p2__2_1_1_1_1_1_1", funName := "DetCN", sem := .node "DetCN" [
    .node "the_Det" [],
    .ref 0
  ] },
  { lhs := "Adv__czechAnna__p2__2_1_1_1_1", rhs := .binary "Prep__czechAnna__p2__2_1_1_1_1_0" "NP__czechAnna__p2__2_1_1_1_1_1", funName := "PrepNP", sem := .node "PrepNP" [
    .ref 0,
    .ref 1
  ] },
  { lhs := "CN__czechAnna__p2__2_1_1_1", rhs := .binary "CN__czechAnna__p2__2_1_1_1_0" "Adv__czechAnna__p2__2_1_1_1_1", funName := "AdvCN", sem := .node "AdvCN" [
    .ref 0,
    .ref 1
  ] },
  { lhs := "NP__czechAnna__p2__2_1_1", rhs := .unary "CN__czechAnna__p2__2_1_1_1", funName := "DetCN", sem := .node "DetCN" [
    .node "the_Det" [],
    .ref 0
  ] },
  { lhs := "VP__czechAnna__p2__2_1", rhs := .binary "VPSlash__czechAnna__p2__2_1_0" "NP__czechAnna__p2__2_1_1", funName := "ComplSlash", sem := .node "ComplSlash" [
    .ref 0,
    .ref 1
  ] },
  { lhs := "Cl__czechAnna__p2__2", rhs := .binary "NP__czechAnna__p2__2_0" "VP__czechAnna__p2__2_1", funName := "PredVP", sem := .node "PredVP" [
    .ref 0,
    .ref 1
  ] },
  { lhs := "S", rhs := .unary "Cl__czechAnna__p2__2", funName := "UseCl", sem := .node "UseCl" [
    .node "TTAnt" [
      .node "TPres" [],
      .node "ASimul" []
    ],
    .node "PPos" [],
    .ref 0
  ] }
  ] }

def englishTelescopeSurface : String := "John sees the man with the telescope"
def englishTelescopeTokens : Array Tok := tokenize englishTelescopeSurface
def englishTelescopeExpected : Array ExportedTree := #[
  .node "UseCl" [
    .node "TTAnt" [
      .node "TPres" [],
      .node "ASimul" []
    ],
    .node "PPos" [],
    .node "PredVP" [
      .node "UsePN" [
        .node "john_PN" []
      ],
      .node "AdvVP" [
        .node "ComplSlash" [
          .node "SlashV2a" [
            .node "see_V2" []
          ],
          .node "DetCN" [
            .node "the_Det" [],
            .node "UseN" [
              .node "man_N" []
            ]
          ]
        ],
        .node "PrepNP" [
          .node "with_Prep" [],
          .node "DetCN" [
            .node "the_Det" [],
            .node "UseN" [
              .node "telescope_N" []
            ]
          ]
        ]
      ]
    ]
  ],
  .node "UseCl" [
    .node "TTAnt" [
      .node "TPres" [],
      .node "ASimul" []
    ],
    .node "PPos" [],
    .node "PredVP" [
      .node "UsePN" [
        .node "john_PN" []
      ],
      .node "ComplSlash" [
        .node "SlashV2a" [
          .node "see_V2" []
        ],
        .node "DetCN" [
          .node "the_Det" [],
          .node "AdvCN" [
            .node "UseN" [
              .node "man_N" []
            ],
            .node "PrepNP" [
              .node "with_Prep" [],
              .node "DetCN" [
                .node "the_Det" [],
                .node "UseN" [
                  .node "telescope_N" []
                ]
              ]
            ]
          ]
        ]
      ]
    ]
  ]
]
def englishTelescopeParsed : Array Parsed := parsesForStart englishGrammar englishTelescopeTokens
def englishTelescopeRecovered : Array ExportedTree := englishTelescopeParsed.map Parsed.recovered

def englishAnnaSurface : String := "Anna dresses the baby in the crib"
def englishAnnaTokens : Array Tok := tokenize englishAnnaSurface
def englishAnnaExpected : Array ExportedTree := #[
  .node "UseCl" [
    .node "TTAnt" [
      .node "TPres" [],
      .node "ASimul" []
    ],
    .node "PPos" [],
    .node "PredVP" [
      .node "UsePN" [
        .node "anna_PN" []
      ],
      .node "AdvVP" [
        .node "ComplSlash" [
          .node "SlashV2a" [
            .node "dress_V2" []
          ],
          .node "DetCN" [
            .node "the_Det" [],
            .node "UseN" [
              .node "baby_N" []
            ]
          ]
        ],
        .node "PrepNP" [
          .node "in_Prep" [],
          .node "DetCN" [
            .node "the_Det" [],
            .node "UseN" [
              .node "crib_N" []
            ]
          ]
        ]
      ]
    ]
  ],
  .node "UseCl" [
    .node "TTAnt" [
      .node "TPres" [],
      .node "ASimul" []
    ],
    .node "PPos" [],
    .node "PredVP" [
      .node "UsePN" [
        .node "anna_PN" []
      ],
      .node "ComplSlash" [
        .node "SlashV2a" [
          .node "dress_V2" []
        ],
        .node "DetCN" [
          .node "the_Det" [],
          .node "AdvCN" [
            .node "UseN" [
              .node "baby_N" []
            ],
            .node "PrepNP" [
              .node "in_Prep" [],
              .node "DetCN" [
                .node "the_Det" [],
                .node "UseN" [
                  .node "crib_N" []
                ]
              ]
            ]
          ]
        ]
      ]
    ]
  ]
]
def englishAnnaParsed : Array Parsed := parsesForStart englishGrammar englishAnnaTokens
def englishAnnaRecovered : Array ExportedTree := englishAnnaParsed.map Parsed.recovered

def czechTelescopeSurface : String := "Jan vidí muže s teleskopem"
def czechTelescopeTokens : Array Tok := tokenize czechTelescopeSurface
def czechTelescopeExpected : Array ExportedTree := #[
  .node "UseCl" [
    .node "TTAnt" [
      .node "TPres" [],
      .node "ASimul" []
    ],
    .node "PPos" [],
    .node "PredVP" [
      .node "UsePN" [
        .node "john_PN" []
      ],
      .node "AdvVP" [
        .node "ComplSlash" [
          .node "SlashV2a" [
            .node "see_V2" []
          ],
          .node "DetCN" [
            .node "the_Det" [],
            .node "UseN" [
              .node "man_N" []
            ]
          ]
        ],
        .node "PrepNP" [
          .node "with_Prep" [],
          .node "DetCN" [
            .node "the_Det" [],
            .node "UseN" [
              .node "telescope_N" []
            ]
          ]
        ]
      ]
    ]
  ],
  .node "UseCl" [
    .node "TTAnt" [
      .node "TPres" [],
      .node "ASimul" []
    ],
    .node "PPos" [],
    .node "PredVP" [
      .node "UsePN" [
        .node "john_PN" []
      ],
      .node "ComplSlash" [
        .node "SlashV2a" [
          .node "see_V2" []
        ],
        .node "DetCN" [
          .node "the_Det" [],
          .node "AdvCN" [
            .node "UseN" [
              .node "man_N" []
            ],
            .node "PrepNP" [
              .node "with_Prep" [],
              .node "DetCN" [
                .node "the_Det" [],
                .node "UseN" [
                  .node "telescope_N" []
                ]
              ]
            ]
          ]
        ]
      ]
    ]
  ]
]
def czechTelescopeParsed : Array Parsed := parsesForStart czechGrammar czechTelescopeTokens
def czechTelescopeRecovered : Array ExportedTree := czechTelescopeParsed.map Parsed.recovered

def czechAnnaSurface : String := "Anna obléká dítě v kolébkě"
def czechAnnaTokens : Array Tok := tokenize czechAnnaSurface
def czechAnnaExpected : Array ExportedTree := #[
  .node "UseCl" [
    .node "TTAnt" [
      .node "TPres" [],
      .node "ASimul" []
    ],
    .node "PPos" [],
    .node "PredVP" [
      .node "UsePN" [
        .node "anna_PN" []
      ],
      .node "AdvVP" [
        .node "ComplSlash" [
          .node "SlashV2a" [
            .node "dress_V2" []
          ],
          .node "DetCN" [
            .node "the_Det" [],
            .node "UseN" [
              .node "baby_N" []
            ]
          ]
        ],
        .node "PrepNP" [
          .node "in_Prep" [],
          .node "DetCN" [
            .node "the_Det" [],
            .node "UseN" [
              .node "crib_N" []
            ]
          ]
        ]
      ]
    ]
  ],
  .node "UseCl" [
    .node "TTAnt" [
      .node "TPres" [],
      .node "ASimul" []
    ],
    .node "PPos" [],
    .node "PredVP" [
      .node "UsePN" [
        .node "anna_PN" []
      ],
      .node "ComplSlash" [
        .node "SlashV2a" [
          .node "dress_V2" []
        ],
        .node "DetCN" [
          .node "the_Det" [],
          .node "AdvCN" [
            .node "UseN" [
              .node "baby_N" []
            ],
            .node "PrepNP" [
              .node "in_Prep" [],
              .node "DetCN" [
                .node "the_Det" [],
                .node "UseN" [
                  .node "crib_N" []
                ]
              ]
            ]
          ]
        ]
      ]
    ]
  ]
]
def czechAnnaParsed : Array Parsed := parsesForStart czechGrammar czechAnnaTokens
def czechAnnaRecovered : Array ExportedTree := czechAnnaParsed.map Parsed.recovered

end Algorithms.GF.Generated.PaperAmbiguityIR
