-- AUTO-GENERATED from ParseEng PGF witnesses. Do not edit.
-- Grammar: Parse
-- Source hash: 11d54d0644a29fc587e839c6710ddd362cd2c0ad45f693487d0ce1840bed4d34
-- Functions: 213

import GFCore.Syntax
import Std.Data.HashMap

namespace Algorithms.GF.Generated.USConstitutionMainSig

open GFCore

private def fd0 : FunDecl :=
  { name := "ASimul", argCats := #[], resultCat := "Ant", status := .primitive }
private def fd1 : FunDecl :=
  { name := "AdVVPSlash", argCats := #["AdV", "VPSlash"], resultCat := "VPSlash", status := .primitive }
private def fd2 : FunDecl :=
  { name := "AdjAsNP", argCats := #["AP"], resultCat := "NP", status := .primitive }
private def fd3 : FunDecl :=
  { name := "AdjCN", argCats := #["AP", "CN"], resultCat := "CN", status := .primitive }
private def fd4 : FunDecl :=
  { name := "AdvCN", argCats := #["CN", "Adv"], resultCat := "CN", status := .primitive }
private def fd5 : FunDecl :=
  { name := "AdvRNP", argCats := #["NP", "Prep", "RNP"], resultCat := "RNP", status := .primitive }
private def fd6 : FunDecl :=
  { name := "AdvVPSlash", argCats := #["VPSlash", "Adv"], resultCat := "VPSlash", status := .primitive }
private def fd7 : FunDecl :=
  { name := "ApposCN", argCats := #["CN", "NP"], resultCat := "CN", status := .primitive }
private def fd8 : FunDecl :=
  { name := "BaseCN", argCats := #["CN", "CN"], resultCat := "ListCN", status := .primitive }
private def fd9 : FunDecl :=
  { name := "BaseCNN", argCats := #["Num", "CN", "Num", "CN"], resultCat := "CNN", status := .primitive }
private def fd10 : FunDecl :=
  { name := "CompAP", argCats := #["AP"], resultCat := "Comp", status := .primitive }
private def fd11 : FunDecl :=
  { name := "CompCN", argCats := #["CN"], resultCat := "Comp", status := .primitive }
private def fd12 : FunDecl :=
  { name := "CompNP", argCats := #["NP"], resultCat := "Comp", status := .primitive }
private def fd13 : FunDecl :=
  { name := "ComplSlashPartLast", argCats := #["VPSlash", "NP"], resultCat := "VP", status := .primitive }
private def fd14 : FunDecl :=
  { name := "ComplVPI2", argCats := #["VPI2", "NP"], resultCat := "VPI", status := .primitive }
private def fd15 : FunDecl :=
  { name := "ComplVPIVV", argCats := #["VV", "VPI"], resultCat := "VP", status := .primitive }
private def fd16 : FunDecl :=
  { name := "ComplVPS2", argCats := #["VPS2", "NP"], resultCat := "VPS", status := .primitive }
private def fd17 : FunDecl :=
  { name := "ConjCN", argCats := #["Conj", "ListCN"], resultCat := "CN", status := .primitive }
private def fd18 : FunDecl :=
  { name := "DefArt", argCats := #[], resultCat := "Quant", status := .primitive }
private def fd19 : FunDecl :=
  { name := "DetCN", argCats := #["Det", "CN"], resultCat := "NP", status := .primitive }
private def fd20 : FunDecl :=
  { name := "DetCNN", argCats := #["Quant", "Conj", "CNN"], resultCat := "NP", status := .primitive }
private def fd21 : FunDecl :=
  { name := "DetDAP", argCats := #["Det"], resultCat := "DAP", status := .primitive }
private def fd22 : FunDecl :=
  { name := "DetQuant", argCats := #["Quant", "Num"], resultCat := "Det", status := .primitive }
private def fd23 : FunDecl :=
  { name := "GenModNP", argCats := #["Num", "NP", "CN"], resultCat := "NP", status := .primitive }
private def fd24 : FunDecl :=
  { name := "GerundNP", argCats := #["VP"], resultCat := "NP", status := .primitive }
private def fd25 : FunDecl :=
  { name := "IdRP", argCats := #[], resultCat := "RP", status := .primitive }
private def fd26 : FunDecl :=
  { name := "ImpersCl", argCats := #["VP"], resultCat := "Cl", status := .primitive }
private def fd27 : FunDecl :=
  { name := "IndefArt", argCats := #[], resultCat := "Quant", status := .primitive }
private def fd28 : FunDecl :=
  { name := "MassNP", argCats := #["CN"], resultCat := "NP", status := .primitive }
private def fd29 : FunDecl :=
  { name := "MkVPI", argCats := #["VP"], resultCat := "VPI", status := .primitive }
private def fd30 : FunDecl :=
  { name := "MkVPI2", argCats := #["VPSlash"], resultCat := "VPI2", status := .primitive }
private def fd31 : FunDecl :=
  { name := "MkVPS", argCats := #["Temp", "Pol", "VP"], resultCat := "VPS", status := .primitive }
private def fd32 : FunDecl :=
  { name := "MkVPS2", argCats := #["Temp", "Pol", "VPSlash"], resultCat := "VPS2", status := .primitive }
private def fd33 : FunDecl :=
  { name := "NoPConj", argCats := #[], resultCat := "PConj", status := .primitive }
private def fd34 : FunDecl :=
  { name := "NoVoc", argCats := #[], resultCat := "Voc", status := .primitive }
private def fd35 : FunDecl :=
  { name := "NumCard", argCats := #["Card"], resultCat := "Num", status := .primitive }
private def fd36 : FunDecl :=
  { name := "NumNumeral", argCats := #["Numeral"], resultCat := "Card", status := .primitive }
private def fd37 : FunDecl :=
  { name := "NumPl", argCats := #[], resultCat := "Num", status := .primitive }
private def fd38 : FunDecl :=
  { name := "NumSg", argCats := #[], resultCat := "Num", status := .primitive }
private def fd39 : FunDecl :=
  { name := "PNeg", argCats := #[], resultCat := "Pol", status := .primitive }
private def fd40 : FunDecl :=
  { name := "PPos", argCats := #[], resultCat := "Pol", status := .primitive }
private def fd41 : FunDecl :=
  { name := "PartNP", argCats := #["CN", "NP"], resultCat := "CN", status := .primitive }
private def fd42 : FunDecl :=
  { name := "PassAgentVPSlash", argCats := #["VPSlash", "NP"], resultCat := "VP", status := .primitive }
private def fd43 : FunDecl :=
  { name := "PassVPSlash", argCats := #["VPSlash"], resultCat := "VP", status := .primitive }
private def fd44 : FunDecl :=
  { name := "PastPartAP", argCats := #["VPSlash"], resultCat := "AP", status := .primitive }
private def fd45 : FunDecl :=
  { name := "PastPartAgentAP", argCats := #["VPSlash", "NP"], resultCat := "AP", status := .primitive }
private def fd46 : FunDecl :=
  { name := "PhrUtt", argCats := #["PConj", "Utt", "Voc"], resultCat := "Phr", status := .primitive }
private def fd47 : FunDecl :=
  { name := "PositA", argCats := #["A"], resultCat := "AP", status := .primitive }
private def fd48 : FunDecl :=
  { name := "PossNP", argCats := #["CN", "NP"], resultCat := "CN", status := .primitive }
private def fd49 : FunDecl :=
  { name := "PredVPS", argCats := #["NP", "VPS"], resultCat := "S", status := .primitive }
private def fd50 : FunDecl :=
  { name := "PredetNP", argCats := #["Predet", "NP"], resultCat := "NP", status := .primitive }
private def fd51 : FunDecl :=
  { name := "PrepNP", argCats := #["Prep", "NP"], resultCat := "Adv", status := .primitive }
private def fd52 : FunDecl :=
  { name := "ReflPoss", argCats := #["Num", "CN"], resultCat := "RNP", status := .primitive }
private def fd53 : FunDecl :=
  { name := "ReflVPS2", argCats := #["VPS2", "RNP"], resultCat := "VPS", status := .primitive }
private def fd54 : FunDecl :=
  { name := "RelCN", argCats := #["CN", "RS"], resultCat := "CN", status := .primitive }
private def fd55 : FunDecl :=
  { name := "RelVPS", argCats := #["RP", "VPS"], resultCat := "RS", status := .primitive }
private def fd56 : FunDecl :=
  { name := "Slash3V3", argCats := #["V3", "NP"], resultCat := "VPSlash", status := .primitive }
private def fd57 : FunDecl :=
  { name := "SlashV2a", argCats := #["V2"], resultCat := "VPSlash", status := .primitive }
private def fd58 : FunDecl :=
  { name := "SlashVV", argCats := #["VV", "Ant", "Pol", "VPSlash"], resultCat := "VPSlash", status := .primitive }
private def fd59 : FunDecl :=
  { name := "TPres", argCats := #[], resultCat := "Tense", status := .primitive }
private def fd60 : FunDecl :=
  { name := "TTAnt", argCats := #["Tense", "Ant"], resultCat := "Temp", status := .primitive }
private def fd61 : FunDecl :=
  { name := "TimeNP", argCats := #["NP"], resultCat := "Adv", status := .primitive }
private def fd62 : FunDecl :=
  { name := "UseCl", argCats := #["Temp", "Pol", "Cl"], resultCat := "S", status := .primitive }
private def fd63 : FunDecl :=
  { name := "UseComp", argCats := #["Comp"], resultCat := "VP", status := .primitive }
private def fd64 : FunDecl :=
  { name := "UseComp_estar", argCats := #["Comp"], resultCat := "VP", status := .primitive }
private def fd65 : FunDecl :=
  { name := "UseComp_ser", argCats := #["Comp"], resultCat := "VP", status := .primitive }
private def fd66 : FunDecl :=
  { name := "UseDAP", argCats := #["DAP"], resultCat := "NP", status := .primitive }
private def fd67 : FunDecl :=
  { name := "UseDAPFem", argCats := #["DAP"], resultCat := "NP", status := .primitive }
private def fd68 : FunDecl :=
  { name := "UseDAPMasc", argCats := #["DAP"], resultCat := "NP", status := .primitive }
private def fd69 : FunDecl :=
  { name := "UseLN", argCats := #["LN"], resultCat := "NP", status := .primitive }
private def fd70 : FunDecl :=
  { name := "UseN", argCats := #["N"], resultCat := "CN", status := .primitive }
private def fd71 : FunDecl :=
  { name := "UsePN", argCats := #["PN"], resultCat := "NP", status := .primitive }
private def fd72 : FunDecl :=
  { name := "UsePron", argCats := #["Pron"], resultCat := "NP", status := .primitive }
private def fd73 : FunDecl :=
  { name := "UseV", argCats := #["V"], resultCat := "VP", status := .primitive }
private def fd74 : FunDecl :=
  { name := "UttNP", argCats := #["NP"], resultCat := "Utt", status := .primitive }
private def fd75 : FunDecl :=
  { name := "UttS", argCats := #["S"], resultCat := "Utt", status := .primitive }
private def fd76 : FunDecl :=
  { name := "UttVPShort", argCats := #["VP"], resultCat := "Utt", status := .primitive }
private def fd77 : FunDecl :=
  { name := "VPSlashPrep", argCats := #["VP", "Prep"], resultCat := "VPSlash", status := .primitive }
private def fd78 : FunDecl :=
  { name := "act_3_N", argCats := #[], resultCat := "N", status := .primitive }
private def fd79 : FunDecl :=
  { name := "against_Prep", argCats := #[], resultCat := "Prep", status := .primitive }
private def fd80 : FunDecl :=
  { name := "age_2_N", argCats := #[], resultCat := "N", status := .primitive }
private def fd81 : FunDecl :=
  { name := "age_3_N", argCats := #[], resultCat := "N", status := .primitive }
private def fd82 : FunDecl :=
  { name := "all_1_Predet", argCats := #[], resultCat := "Predet", status := .primitive }
private def fd83 : FunDecl :=
  { name := "all_2_Predet", argCats := #[], resultCat := "Predet", status := .primitive }
private def fd84 : FunDecl :=
  { name := "amendment_2_N", argCats := #[], resultCat := "N", status := .primitive }
private def fd85 : FunDecl :=
  { name := "america_1_LN", argCats := #[], resultCat := "LN", status := .primitive }
private def fd86 : FunDecl :=
  { name := "and_Conj", argCats := #[], resultCat := "Conj", status := .primitive }
private def fd87 : FunDecl :=
  { name := "anySg_2_Det", argCats := #[], resultCat := "Det", status := .primitive }
private def fd88 : FunDecl :=
  { name := "army_3_N", argCats := #[], resultCat := "N", status := .primitive }
private def fd89 : FunDecl :=
  { name := "as_Prep", argCats := #[], resultCat := "Prep", status := .primitive }
private def fd90 : FunDecl :=
  { name := "attain_3_V2", argCats := #[], resultCat := "V2", status := .primitive }
private def fd91 : FunDecl :=
  { name := "bill_9_N", argCats := #[], resultCat := "N", status := .primitive }
private def fd92 : FunDecl :=
  { name := "chiefMasc_3_N", argCats := #[], resultCat := "N", status := .primitive }
private def fd93 : FunDecl :=
  { name := "choose_2_V2", argCats := #[], resultCat := "V2", status := .primitive }
private def fd94 : FunDecl :=
  { name := "commanderFem_2_N", argCats := #[], resultCat := "N", status := .primitive }
private def fd95 : FunDecl :=
  { name := "compose_4_V2", argCats := #[], resultCat := "V2", status := .primitive }
private def fd96 : FunDecl :=
  { name := "congress_2_N", argCats := #[], resultCat := "N", status := .primitive }
private def fd97 : FunDecl :=
  { name := "congress_3_N", argCats := #[], resultCat := "N", status := .primitive }
private def fd98 : FunDecl :=
  { name := "consist_4_V", argCats := #[], resultCat := "V", status := .primitive }
private def fd99 : FunDecl :=
  { name := "constitution_1_N", argCats := #[], resultCat := "N", status := .primitive }
private def fd100 : FunDecl :=
  { name := "constitution_PN", argCats := #[], resultCat := "PN", status := .primitive }
private def fd101 : FunDecl :=
  { name := "convention_2_N", argCats := #[], resultCat := "N", status := .primitive }
private def fd102 : FunDecl :=
  { name := "credit_9_N", argCats := #[], resultCat := "N", status := .primitive }
private def fd103 : FunDecl :=
  { name := "declare_6_V2", argCats := #[], resultCat := "V2", status := .primitive }
private def fd104 : FunDecl :=
  { name := "determine_7_V2", argCats := #[], resultCat := "V2", status := .primitive }
private def fd105 : FunDecl :=
  { name := "each_Det", argCats := #[], resultCat := "Det", status := .primitive }
private def fd106 : FunDecl :=
  { name := "establish_4_V2", argCats := #[], resultCat := "V2", status := .primitive }
private def fd107 : FunDecl :=
  { name := "establishment_4_N", argCats := #[], resultCat := "N", status := .primitive }
private def fd108 : FunDecl :=
  { name := "ever_1_AdV", argCats := #[], resultCat := "AdV", status := .primitive }
private def fd109 : FunDecl :=
  { name := "every_Det", argCats := #[], resultCat := "Det", status := .primitive }
private def fd110 : FunDecl :=
  { name := "executive_A", argCats := #[], resultCat := "A", status := .primitive }
private def fd111 : FunDecl :=
  { name := "faith_1_N", argCats := #[], resultCat := "N", status := .primitive }
private def fd112 : FunDecl :=
  { name := "for_Prep", argCats := #[], resultCat := "Prep", status := .primitive }
private def fd113 : FunDecl :=
  { name := "full_2_A", argCats := #[], resultCat := "A", status := .primitive }
private def fd114 : FunDecl :=
  { name := "gen_Quant", argCats := #[], resultCat := "Quant", status := .primitive }
private def fd115 : FunDecl :=
  { name := "give_22_V2", argCats := #[], resultCat := "V2", status := .primitive }
private def fd116 : FunDecl :=
  { name := "grant_1_V2", argCats := #[], resultCat := "V2", status := .primitive }
private def fd117 : FunDecl :=
  { name := "grant_7_V2", argCats := #[], resultCat := "V2", status := .primitive }
private def fd118 : FunDecl :=
  { name := "habeas_corpus_2_N", argCats := #[], resultCat := "N", status := .primitive }
private def fd119 : FunDecl :=
  { name := "have_15_V2", argCats := #[], resultCat := "V2", status := .primitive }
private def fd120 : FunDecl :=
  { name := "have_8_V2", argCats := #[], resultCat := "V2", status := .primitive }
private def fd121 : FunDecl :=
  { name := "he_Pron", argCats := #[], resultCat := "Pron", status := .primitive }
private def fd122 : FunDecl :=
  { name := "herein_Adv", argCats := #[], resultCat := "Adv", status := .primitive }
private def fd123 : FunDecl :=
  { name := "house_4_N", argCats := #[], resultCat := "N", status := .primitive }
private def fd124 : FunDecl :=
  { name := "house_6_N", argCats := #[], resultCat := "N", status := .primitive }
private def fd125 : FunDecl :=
  { name := "impeachment_N", argCats := #[], resultCat := "N", status := .primitive }
private def fd126 : FunDecl :=
  { name := "in_1_Prep", argCats := #[], resultCat := "Prep", status := .primitive }
private def fd127 : FunDecl :=
  { name := "in_2_Prep", argCats := #[], resultCat := "Prep", status := .primitive }
private def fd128 : FunDecl :=
  { name := "in_4_Prep", argCats := #[], resultCat := "Prep", status := .primitive }
private def fd129 : FunDecl :=
  { name := "in_5_Prep", argCats := #[], resultCat := "Prep", status := .primitive }
private def fd130 : FunDecl :=
  { name := "it_Pron", argCats := #[], resultCat := "Pron", status := .primitive }
private def fd131 : FunDecl :=
  { name := "judicial_1_A", argCats := #[], resultCat := "A", status := .primitive }
private def fd132 : FunDecl :=
  { name := "justiceFem_3_N", argCats := #[], resultCat := "N", status := .primitive }
private def fd133 : FunDecl :=
  { name := "land_9_N", argCats := #[], resultCat := "N", status := .primitive }
private def fd134 : FunDecl :=
  { name := "law_1_N", argCats := #[], resultCat := "N", status := .primitive }
private def fd135 : FunDecl :=
  { name := "law_3_N", argCats := #[], resultCat := "N", status := .primitive }
private def fd136 : FunDecl :=
  { name := "legislative_1_A", argCats := #[], resultCat := "A", status := .primitive }
private def fd137 : FunDecl :=
  { name := "levy_1_V2", argCats := #[], resultCat := "V2", status := .primitive }
private def fd138 : FunDecl :=
  { name := "may_1_VV", argCats := #[], resultCat := "VV", status := .primitive }
private def fd139 : FunDecl :=
  { name := "memberMasc_1_N", argCats := #[], resultCat := "N", status := .primitive }
private def fd140 : FunDecl :=
  { name := "n2", argCats := #[], resultCat := "Digit", status := .primitive }
private def fd141 : FunDecl :=
  { name := "n3", argCats := #[], resultCat := "Digit", status := .primitive }
private def fd142 : FunDecl :=
  { name := "n5", argCats := #[], resultCat := "Digit", status := .primitive }
private def fd143 : FunDecl :=
  { name := "n9", argCats := #[], resultCat := "Digit", status := .primitive }
private def fd144 : FunDecl :=
  { name := "navy_3_N", argCats := #[], resultCat := "N", status := .primitive }
private def fd145 : FunDecl :=
  { name := "no_Quant", argCats := #[], resultCat := "Quant", status := .primitive }
private def fd146 : FunDecl :=
  { name := "nobility_2_N", argCats := #[], resultCat := "N", status := .primitive }
private def fd147 : FunDecl :=
  { name := "num", argCats := #["Sub1000000000000"], resultCat := "Numeral", status := .primitive }
private def fd148 : FunDecl :=
  { name := "of_2_Prep", argCats := #[], resultCat := "Prep", status := .primitive }
private def fd149 : FunDecl :=
  { name := "office_3_N", argCats := #[], resultCat := "N", status := .primitive }
private def fd150 : FunDecl :=
  { name := "only_7_Adv", argCats := #[], resultCat := "Adv", status := .primitive }
private def fd151 : FunDecl :=
  { name := "or_Conj", argCats := #[], resultCat := "Conj", status := .primitive }
private def fd152 : FunDecl :=
  { name := "other_4_A", argCats := #[], resultCat := "A", status := .primitive }
private def fd153 : FunDecl :=
  { name := "people_4_N", argCats := #[], resultCat := "N", status := .primitive }
private def fd154 : FunDecl :=
  { name := "person_2_N", argCats := #[], resultCat := "N", status := .primitive }
private def fd155 : FunDecl :=
  { name := "pot0", argCats := #["Digit"], resultCat := "Sub10", status := .primitive }
private def fd156 : FunDecl :=
  { name := "pot0as1", argCats := #["Sub10"], resultCat := "Sub100", status := .primitive }
private def fd157 : FunDecl :=
  { name := "pot1", argCats := #["Digit"], resultCat := "Sub100", status := .primitive }
private def fd158 : FunDecl :=
  { name := "pot1as2", argCats := #["Sub100"], resultCat := "Sub1000", status := .primitive }
private def fd159 : FunDecl :=
  { name := "pot2as3", argCats := #["Sub1000"], resultCat := "Sub1000000", status := .primitive }
private def fd160 : FunDecl :=
  { name := "pot3as4", argCats := #["Sub1000000"], resultCat := "Sub1000000000", status := .primitive }
private def fd161 : FunDecl :=
  { name := "pot4as5", argCats := #["Sub1000000000"], resultCat := "Sub1000000000000", status := .primitive }
private def fd162 : FunDecl :=
  { name := "power_10_N", argCats := #[], resultCat := "N", status := .primitive }
private def fd163 : FunDecl :=
  { name := "power_2_N", argCats := #[], resultCat := "N", status := .primitive }
private def fd164 : FunDecl :=
  { name := "power_7_N", argCats := #[], resultCat := "N", status := .primitive }
private def fd165 : FunDecl :=
  { name := "present_to_V3", argCats := #[], resultCat := "V3", status := .primitive }
private def fd166 : FunDecl :=
  { name := "presidentFem_1_N", argCats := #[], resultCat := "N", status := .primitive }
private def fd167 : FunDecl :=
  { name := "presidentMasc_2_N", argCats := #[], resultCat := "N", status := .primitive }
private def fd168 : FunDecl :=
  { name := "presidentMasc_6_N", argCats := #[], resultCat := "N", status := .primitive }
private def fd169 : FunDecl :=
  { name := "privilege_2_N", argCats := #[], resultCat := "N", status := .primitive }
private def fd170 : FunDecl :=
  { name := "proceedings_1_N", argCats := #[], resultCat := "N", status := .primitive }
private def fd171 : FunDecl :=
  { name := "proceedings_2_N", argCats := #[], resultCat := "N", status := .primitive }
private def fd172 : FunDecl :=
  { name := "propose_4_V2", argCats := #[], resultCat := "V2", status := .primitive }
private def fd173 : FunDecl :=
  { name := "public_1_A", argCats := #[], resultCat := "A", status := .primitive }
private def fd174 : FunDecl :=
  { name := "qualification_3_N", argCats := #[], resultCat := "N", status := .primitive }
private def fd175 : FunDecl :=
  { name := "ratification_N", argCats := #[], resultCat := "N", status := .primitive }
private def fd176 : FunDecl :=
  { name := "record_2_N", argCats := #[], resultCat := "N", status := .primitive }
private def fd177 : FunDecl :=
  { name := "religious_4_A", argCats := #[], resultCat := "A", status := .primitive }
private def fd178 : FunDecl :=
  { name := "representativeFem_1_N", argCats := #[], resultCat := "N", status := .primitive }
private def fd179 : FunDecl :=
  { name := "representativeMasc_2_N", argCats := #[], resultCat := "N", status := .primitive }
private def fd180 : FunDecl :=
  { name := "require_1_V2", argCats := #[], resultCat := "V2", status := .primitive }
private def fd181 : FunDecl :=
  { name := "rule_3_N", argCats := #[], resultCat := "N", status := .primitive }
private def fd182 : FunDecl :=
  { name := "second_10_N", argCats := #[], resultCat := "N", status := .primitive }
private def fd183 : FunDecl :=
  { name := "senate_2_N", argCats := #[], resultCat := "N", status := .primitive }
private def fd184 : FunDecl :=
  { name := "several_Card", argCats := #[], resultCat := "Card", status := .primitive }
private def fd185 : FunDecl :=
  { name := "shall_VV", argCats := #[], resultCat := "VV", status := .primitive }
private def fd186 : FunDecl :=
  { name := "sign_2_V2", argCats := #[], resultCat := "V2", status := .primitive }
private def fd187 : FunDecl :=
  { name := "sole_1_A", argCats := #[], resultCat := "A", status := .primitive }
private def fd188 : FunDecl :=
  { name := "state_1_N", argCats := #[], resultCat := "N", status := .primitive }
private def fd189 : FunDecl :=
  { name := "state_4_N", argCats := #[], resultCat := "N", status := .primitive }
private def fd190 : FunDecl :=
  { name := "state_8_N", argCats := #[], resultCat := "N", status := .primitive }
private def fd191 : FunDecl :=
  { name := "sufficient_A", argCats := #[], resultCat := "A", status := .primitive }
private def fd192 : FunDecl :=
  { name := "supreme_2_A", argCats := #[], resultCat := "A", status := .primitive }
private def fd193 : FunDecl :=
  { name := "suspend_5_V2", argCats := #[], resultCat := "V2", status := .primitive }
private def fd194 : FunDecl :=
  { name := "test_4_N", argCats := #[], resultCat := "N", status := .primitive }
private def fd195 : FunDecl :=
  { name := "theyFem_Pron", argCats := #[], resultCat := "Pron", status := .primitive }
private def fd196 : FunDecl :=
  { name := "this_Quant", argCats := #[], resultCat := "Quant", status := .primitive }
private def fd197 : FunDecl :=
  { name := "timeunitAdv", argCats := #["Card", "Timeunit"], resultCat := "Adv", status := .primitive }
private def fd198 : FunDecl :=
  { name := "title_2_N", argCats := #[], resultCat := "N", status := .primitive }
private def fd199 : FunDecl :=
  { name := "to_1_Prep", argCats := #[], resultCat := "Prep", status := .primitive }
private def fd200 : FunDecl :=
  { name := "to_4_Prep", argCats := #[], resultCat := "Prep", status := .primitive }
private def fd201 : FunDecl :=
  { name := "to_5_Prep", argCats := #[], resultCat := "Prep", status := .primitive }
private def fd202 : FunDecl :=
  { name := "treason_2_N", argCats := #[], resultCat := "N", status := .primitive }
private def fd203 : FunDecl :=
  { name := "trust_3_N", argCats := #[], resultCat := "N", status := .primitive }
private def fd204 : FunDecl :=
  { name := "try_3_V2", argCats := #[], resultCat := "V2", status := .primitive }
private def fd205 : FunDecl :=
  { name := "under_Prep", argCats := #[], resultCat := "Prep", status := .primitive }
private def fd206 : FunDecl :=
  { name := "united_states_LN", argCats := #[], resultCat := "LN", status := .primitive }
private def fd207 : FunDecl :=
  { name := "vest_2_V2", argCats := #[], resultCat := "V2", status := .primitive }
private def fd208 : FunDecl :=
  { name := "vest_4_V2", argCats := #[], resultCat := "V2", status := .primitive }
private def fd209 : FunDecl :=
  { name := "war_4_N", argCats := #[], resultCat := "N", status := .primitive }
private def fd210 : FunDecl :=
  { name := "writ_N", argCats := #[], resultCat := "N", status := .primitive }
private def fd211 : FunDecl :=
  { name := "year_1_N", argCats := #[], resultCat := "N", status := .primitive }
private def fd212 : FunDecl :=
  { name := "year_Timeunit", argCats := #[], resultCat := "Timeunit", status := .primitive }

/-- The list of function declarations (kernel-reducible). -/
def funsList : List (String × FunDecl) :=
  [
    ("ASimul", fd0),
    ("AdVVPSlash", fd1),
    ("AdjAsNP", fd2),
    ("AdjCN", fd3),
    ("AdvCN", fd4),
    ("AdvRNP", fd5),
    ("AdvVPSlash", fd6),
    ("ApposCN", fd7),
    ("BaseCN", fd8),
    ("BaseCNN", fd9),
    ("CompAP", fd10),
    ("CompCN", fd11),
    ("CompNP", fd12),
    ("ComplSlashPartLast", fd13),
    ("ComplVPI2", fd14),
    ("ComplVPIVV", fd15),
    ("ComplVPS2", fd16),
    ("ConjCN", fd17),
    ("DefArt", fd18),
    ("DetCN", fd19),
    ("DetCNN", fd20),
    ("DetDAP", fd21),
    ("DetQuant", fd22),
    ("GenModNP", fd23),
    ("GerundNP", fd24),
    ("IdRP", fd25),
    ("ImpersCl", fd26),
    ("IndefArt", fd27),
    ("MassNP", fd28),
    ("MkVPI", fd29),
    ("MkVPI2", fd30),
    ("MkVPS", fd31),
    ("MkVPS2", fd32),
    ("NoPConj", fd33),
    ("NoVoc", fd34),
    ("NumCard", fd35),
    ("NumNumeral", fd36),
    ("NumPl", fd37),
    ("NumSg", fd38),
    ("PNeg", fd39),
    ("PPos", fd40),
    ("PartNP", fd41),
    ("PassAgentVPSlash", fd42),
    ("PassVPSlash", fd43),
    ("PastPartAP", fd44),
    ("PastPartAgentAP", fd45),
    ("PhrUtt", fd46),
    ("PositA", fd47),
    ("PossNP", fd48),
    ("PredVPS", fd49),
    ("PredetNP", fd50),
    ("PrepNP", fd51),
    ("ReflPoss", fd52),
    ("ReflVPS2", fd53),
    ("RelCN", fd54),
    ("RelVPS", fd55),
    ("Slash3V3", fd56),
    ("SlashV2a", fd57),
    ("SlashVV", fd58),
    ("TPres", fd59),
    ("TTAnt", fd60),
    ("TimeNP", fd61),
    ("UseCl", fd62),
    ("UseComp", fd63),
    ("UseComp_estar", fd64),
    ("UseComp_ser", fd65),
    ("UseDAP", fd66),
    ("UseDAPFem", fd67),
    ("UseDAPMasc", fd68),
    ("UseLN", fd69),
    ("UseN", fd70),
    ("UsePN", fd71),
    ("UsePron", fd72),
    ("UseV", fd73),
    ("UttNP", fd74),
    ("UttS", fd75),
    ("UttVPShort", fd76),
    ("VPSlashPrep", fd77),
    ("act_3_N", fd78),
    ("against_Prep", fd79),
    ("age_2_N", fd80),
    ("age_3_N", fd81),
    ("all_1_Predet", fd82),
    ("all_2_Predet", fd83),
    ("amendment_2_N", fd84),
    ("america_1_LN", fd85),
    ("and_Conj", fd86),
    ("anySg_2_Det", fd87),
    ("army_3_N", fd88),
    ("as_Prep", fd89),
    ("attain_3_V2", fd90),
    ("bill_9_N", fd91),
    ("chiefMasc_3_N", fd92),
    ("choose_2_V2", fd93),
    ("commanderFem_2_N", fd94),
    ("compose_4_V2", fd95),
    ("congress_2_N", fd96),
    ("congress_3_N", fd97),
    ("consist_4_V", fd98),
    ("constitution_1_N", fd99),
    ("constitution_PN", fd100),
    ("convention_2_N", fd101),
    ("credit_9_N", fd102),
    ("declare_6_V2", fd103),
    ("determine_7_V2", fd104),
    ("each_Det", fd105),
    ("establish_4_V2", fd106),
    ("establishment_4_N", fd107),
    ("ever_1_AdV", fd108),
    ("every_Det", fd109),
    ("executive_A", fd110),
    ("faith_1_N", fd111),
    ("for_Prep", fd112),
    ("full_2_A", fd113),
    ("gen_Quant", fd114),
    ("give_22_V2", fd115),
    ("grant_1_V2", fd116),
    ("grant_7_V2", fd117),
    ("habeas_corpus_2_N", fd118),
    ("have_15_V2", fd119),
    ("have_8_V2", fd120),
    ("he_Pron", fd121),
    ("herein_Adv", fd122),
    ("house_4_N", fd123),
    ("house_6_N", fd124),
    ("impeachment_N", fd125),
    ("in_1_Prep", fd126),
    ("in_2_Prep", fd127),
    ("in_4_Prep", fd128),
    ("in_5_Prep", fd129),
    ("it_Pron", fd130),
    ("judicial_1_A", fd131),
    ("justiceFem_3_N", fd132),
    ("land_9_N", fd133),
    ("law_1_N", fd134),
    ("law_3_N", fd135),
    ("legislative_1_A", fd136),
    ("levy_1_V2", fd137),
    ("may_1_VV", fd138),
    ("memberMasc_1_N", fd139),
    ("n2", fd140),
    ("n3", fd141),
    ("n5", fd142),
    ("n9", fd143),
    ("navy_3_N", fd144),
    ("no_Quant", fd145),
    ("nobility_2_N", fd146),
    ("num", fd147),
    ("of_2_Prep", fd148),
    ("office_3_N", fd149),
    ("only_7_Adv", fd150),
    ("or_Conj", fd151),
    ("other_4_A", fd152),
    ("people_4_N", fd153),
    ("person_2_N", fd154),
    ("pot0", fd155),
    ("pot0as1", fd156),
    ("pot1", fd157),
    ("pot1as2", fd158),
    ("pot2as3", fd159),
    ("pot3as4", fd160),
    ("pot4as5", fd161),
    ("power_10_N", fd162),
    ("power_2_N", fd163),
    ("power_7_N", fd164),
    ("present_to_V3", fd165),
    ("presidentFem_1_N", fd166),
    ("presidentMasc_2_N", fd167),
    ("presidentMasc_6_N", fd168),
    ("privilege_2_N", fd169),
    ("proceedings_1_N", fd170),
    ("proceedings_2_N", fd171),
    ("propose_4_V2", fd172),
    ("public_1_A", fd173),
    ("qualification_3_N", fd174),
    ("ratification_N", fd175),
    ("record_2_N", fd176),
    ("religious_4_A", fd177),
    ("representativeFem_1_N", fd178),
    ("representativeMasc_2_N", fd179),
    ("require_1_V2", fd180),
    ("rule_3_N", fd181),
    ("second_10_N", fd182),
    ("senate_2_N", fd183),
    ("several_Card", fd184),
    ("shall_VV", fd185),
    ("sign_2_V2", fd186),
    ("sole_1_A", fd187),
    ("state_1_N", fd188),
    ("state_4_N", fd189),
    ("state_8_N", fd190),
    ("sufficient_A", fd191),
    ("supreme_2_A", fd192),
    ("suspend_5_V2", fd193),
    ("test_4_N", fd194),
    ("theyFem_Pron", fd195),
    ("this_Quant", fd196),
    ("timeunitAdv", fd197),
    ("title_2_N", fd198),
    ("to_1_Prep", fd199),
    ("to_4_Prep", fd200),
    ("to_5_Prep", fd201),
    ("treason_2_N", fd202),
    ("trust_3_N", fd203),
    ("try_3_V2", fd204),
    ("under_Prep", fd205),
    ("united_states_LN", fd206),
    ("vest_2_V2", fd207),
    ("vest_4_V2", fd208),
    ("war_4_N", fd209),
    ("writ_N", fd210),
    ("year_1_N", fd211),
    ("year_Timeunit", fd212),
  ]

def sig : GrammarSig where
  grammar := "Parse"
  startCats := #["Phr"]
  sourceHash := "11d54d0644a29fc587e839c6710ddd362cd2c0ad45f693487d0ce1840bed4d34"
  funs := Std.HashMap.ofList funsList

end Algorithms.GF.Generated.USConstitutionMainSig
