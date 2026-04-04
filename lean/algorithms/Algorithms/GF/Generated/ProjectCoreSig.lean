-- AUTO-GENERATED from GF PGF export. Do not edit.
-- Grammar: Grammar
-- Source hash: 7238564362398693196
-- Functions: 384

import GFCore.Syntax
import Std.Data.HashMap

namespace Algorithms.GF.Generated.ProjectCoreSig

open GFCore

private def CompIAdv : FunDecl :=
  { name := "CompIAdv", argCats := #["IAdv"], resultCat := "IComp", status := .primitive }

private def UseA2 : FunDecl :=
  { name := "UseA2", argCats := #["A2"], resultCat := "AP", status := .primitive }

private def nd10 : FunDecl :=
  { name := "nd10", argCats := #["Sub10"], resultCat := "Digits", status := .primitive }

private def except_Prep : FunDecl :=
  { name := "except_Prep", argCats := #[], resultCat := "Prep", status := .primitive }

private def ImpP3 : FunDecl :=
  { name := "ImpP3", argCats := #["NP", "VP"], resultCat := "Utt", status := .primitive }

private def pot1as2 : FunDecl :=
  { name := "pot1as2", argCats := #["Sub100"], resultCat := "Sub1000", status := .primitive }

private def and_Conj : FunDecl :=
  { name := "and_Conj", argCats := #[], resultCat := "Conj", status := .primitive }

private def AdvVP : FunDecl :=
  { name := "AdvVP", argCats := #["VP", "Adv"], resultCat := "VP", status := .primitive }

private def pot1to19 : FunDecl :=
  { name := "pot1to19", argCats := #["Digit"], resultCat := "Sub100", status := .primitive }

private def either7or_DConj : FunDecl :=
  { name := "either7or_DConj", argCats := #[], resultCat := "Conj", status := .primitive }

private def NumSg : FunDecl :=
  { name := "NumSg", argCats := #[], resultCat := "Num", status := .primitive }

private def pot3decimal : FunDecl :=
  { name := "pot3decimal", argCats := #["Decimal"], resultCat := "Sub1000000", status := .primitive }

private def can_VV : FunDecl :=
  { name := "can_VV", argCats := #[], resultCat := "VV", status := .primitive }

private def UttNP : FunDecl :=
  { name := "UttNP", argCats := #["NP"], resultCat := "Utt", status := .primitive }

private def ConjDet : FunDecl :=
  { name := "ConjDet", argCats := #["Conj", "ListDAP"], resultCat := "Det", status := .primitive }

private def IndefArt : FunDecl :=
  { name := "IndefArt", argCats := #[], resultCat := "Quant", status := .primitive }

private def NumCard : FunDecl :=
  { name := "NumCard", argCats := #["Card"], resultCat := "Num", status := .primitive }

private def TEmpty : FunDecl :=
  { name := "TEmpty", argCats := #[], resultCat := "Text", status := .primitive }

private def pot21 : FunDecl :=
  { name := "pot21", argCats := #[], resultCat := "Sub1000", status := .primitive }

private def here_Adv : FunDecl :=
  { name := "here_Adv", argCats := #[], resultCat := "Adv", status := .primitive }

private def VPSlashPrep : FunDecl :=
  { name := "VPSlashPrep", argCats := #["VP", "Prep"], resultCat := "VPSlash", status := .primitive }

private def but_PConj : FunDecl :=
  { name := "but_PConj", argCats := #[], resultCat := "PConj", status := .primitive }

private def both7and_DConj : FunDecl :=
  { name := "both7and_DConj", argCats := #[], resultCat := "Conj", status := .primitive }

private def when_IAdv : FunDecl :=
  { name := "when_IAdv", argCats := #[], resultCat := "IAdv", status := .primitive }

private def TPast : FunDecl :=
  { name := "TPast", argCats := #[], resultCat := "Tense", status := .primitive }

private def ConjNP : FunDecl :=
  { name := "ConjNP", argCats := #["Conj", "ListNP"], resultCat := "NP", status := .primitive }

private def RelNP : FunDecl :=
  { name := "RelNP", argCats := #["NP", "RS"], resultCat := "NP", status := .primitive }

private def too_AdA : FunDecl :=
  { name := "too_AdA", argCats := #[], resultCat := "AdA", status := .primitive }

private def QuantityNP : FunDecl :=
  { name := "QuantityNP", argCats := #["Decimal", "MU"], resultCat := "NP", status := .primitive }

private def PConjConj : FunDecl :=
  { name := "PConjConj", argCats := #["Conj"], resultCat := "PConj", status := .primitive }

private def pot41 : FunDecl :=
  { name := "pot41", argCats := #[], resultCat := "Sub1000000000", status := .primitive }

private def DetDAP : FunDecl :=
  { name := "DetDAP", argCats := #["Det"], resultCat := "DAP", status := .primitive }

private def nd100 : FunDecl :=
  { name := "nd100", argCats := #["Sub100"], resultCat := "Digits", status := .primitive }

private def D_8 : FunDecl :=
  { name := "D_8", argCats := #[], resultCat := "Dig", status := .primitive }

private def UseQCl : FunDecl :=
  { name := "UseQCl", argCats := #["Temp", "Pol", "QCl"], resultCat := "QS", status := .primitive }

private def AdvAP : FunDecl :=
  { name := "AdvAP", argCats := #["AP", "Adv"], resultCat := "AP", status := .primitive }

private def pot0 : FunDecl :=
  { name := "pot0", argCats := #["Digit"], resultCat := "Sub10", status := .primitive }

private def whatPl_IP : FunDecl :=
  { name := "whatPl_IP", argCats := #[], resultCat := "IP", status := .primitive }

private def pot3as4 : FunDecl :=
  { name := "pot3as4", argCats := #["Sub1000000"], resultCat := "Sub1000000000", status := .primitive }

private def ConjS : FunDecl :=
  { name := "ConjS", argCats := #["Conj", "ListS"], resultCat := "S", status := .primitive }

private def BaseIAdv : FunDecl :=
  { name := "BaseIAdv", argCats := #["IAdv", "IAdv"], resultCat := "ListIAdv", status := .primitive }

private def ExistIPAdv : FunDecl :=
  { name := "ExistIPAdv", argCats := #["IP", "Adv"], resultCat := "QCl", status := .primitive }

private def PredSCVP : FunDecl :=
  { name := "PredSCVP", argCats := #["SC", "VP"], resultCat := "Cl", status := .primitive }

private def pot110 : FunDecl :=
  { name := "pot110", argCats := #[], resultCat := "Sub100", status := .primitive }

private def at_most_AdN : FunDecl :=
  { name := "at_most_AdN", argCats := #[], resultCat := "AdN", status := .primitive }

private def AddAdvQVP : FunDecl :=
  { name := "AddAdvQVP", argCats := #["QVP", "IAdv"], resultCat := "QVP", status := .primitive }

private def most_Predet : FunDecl :=
  { name := "most_Predet", argCats := #[], resultCat := "Predet", status := .primitive }

private def n2 : FunDecl :=
  { name := "n2", argCats := #[], resultCat := "Digit", status := .primitive }

private def IFrac : FunDecl :=
  { name := "IFrac", argCats := #["Decimal", "Dig"], resultCat := "Decimal", status := .primitive }

private def AdvImp : FunDecl :=
  { name := "AdvImp", argCats := #["Adv", "Imp"], resultCat := "Imp", status := .primitive }

private def D_7 : FunDecl :=
  { name := "D_7", argCats := #[], resultCat := "Dig", status := .primitive }

private def PPartNP : FunDecl :=
  { name := "PPartNP", argCats := #["NP", "V2"], resultCat := "NP", status := .primitive }

private def because_Subj : FunDecl :=
  { name := "because_Subj", argCats := #[], resultCat := "Subj", status := .primitive }

private def although_Subj : FunDecl :=
  { name := "although_Subj", argCats := #[], resultCat := "Subj", status := .primitive }

private def where_IAdv : FunDecl :=
  { name := "where_IAdv", argCats := #[], resultCat := "IAdv", status := .primitive }

private def every_Det : FunDecl :=
  { name := "every_Det", argCats := #[], resultCat := "Det", status := .primitive }

private def PNeg : FunDecl :=
  { name := "PNeg", argCats := #[], resultCat := "Pol", status := .primitive }

private def DetCN : FunDecl :=
  { name := "DetCN", argCats := #["Det", "CN"], resultCat := "NP", status := .primitive }

private def PlSurname : FunDecl :=
  { name := "PlSurname", argCats := #["SN"], resultCat := "NP", status := .primitive }

private def when_Subj : FunDecl :=
  { name := "when_Subj", argCats := #[], resultCat := "Subj", status := .primitive }

private def SlashPrep : FunDecl :=
  { name := "SlashPrep", argCats := #["Cl", "Prep"], resultCat := "ClSlash", status := .primitive }

private def ExistNPAdv : FunDecl :=
  { name := "ExistNPAdv", argCats := #["NP", "Adv"], resultCat := "Cl", status := .primitive }

private def quite_Adv : FunDecl :=
  { name := "quite_Adv", argCats := #[], resultCat := "AdA", status := .primitive }

private def SlashV2V : FunDecl :=
  { name := "SlashV2V", argCats := #["V2V", "VP"], resultCat := "VPSlash", status := .primitive }

private def CAdvAP : FunDecl :=
  { name := "CAdvAP", argCats := #["CAdv", "AP", "NP"], resultCat := "AP", status := .primitive }

private def here7to_Adv : FunDecl :=
  { name := "here7to_Adv", argCats := #[], resultCat := "Adv", status := .primitive }

private def AdnCAdv : FunDecl :=
  { name := "AdnCAdv", argCats := #["CAdv"], resultCat := "AdN", status := .primitive }

private def ConjAP : FunDecl :=
  { name := "ConjAP", argCats := #["Conj", "ListAP"], resultCat := "AP", status := .primitive }

private def IdetIP : FunDecl :=
  { name := "IdetIP", argCats := #["IDet"], resultCat := "IP", status := .primitive }

private def between_Prep : FunDecl :=
  { name := "between_Prep", argCats := #[], resultCat := "Prep", status := .primitive }

private def AdvCN : FunDecl :=
  { name := "AdvCN", argCats := #["CN", "Adv"], resultCat := "CN", status := .primitive }

private def whoSg_IP : FunDecl :=
  { name := "whoSg_IP", argCats := #[], resultCat := "IP", status := .primitive }

private def ConjAdV : FunDecl :=
  { name := "ConjAdV", argCats := #["Conj", "ListAdV"], resultCat := "AdV", status := .primitive }

private def D_5 : FunDecl :=
  { name := "D_5", argCats := #[], resultCat := "Dig", status := .primitive }

private def EmbedS : FunDecl :=
  { name := "EmbedS", argCats := #["S"], resultCat := "SC", status := .primitive }

private def someSg_Det : FunDecl :=
  { name := "someSg_Det", argCats := #[], resultCat := "Det", status := .primitive }

private def ConsCN : FunDecl :=
  { name := "ConsCN", argCats := #["CN", "ListCN"], resultCat := "ListCN", status := .primitive }

private def we_Pron : FunDecl :=
  { name := "we_Pron", argCats := #[], resultCat := "Pron", status := .primitive }

private def in_Prep : FunDecl :=
  { name := "in_Prep", argCats := #[], resultCat := "Prep", status := .primitive }

private def AdvIAdv : FunDecl :=
  { name := "AdvIAdv", argCats := #["IAdv", "Adv"], resultCat := "IAdv", status := .primitive }

private def n8 : FunDecl :=
  { name := "n8", argCats := #[], resultCat := "Digit", status := .primitive }

private def ExtAdvS : FunDecl :=
  { name := "ExtAdvS", argCats := #["Adv", "S"], resultCat := "S", status := .primitive }

private def n7 : FunDecl :=
  { name := "n7", argCats := #[], resultCat := "Digit", status := .primitive }

private def IIDig : FunDecl :=
  { name := "IIDig", argCats := #["Dig", "Digits"], resultCat := "Digits", status := .primitive }

private def FemaleSurname : FunDecl :=
  { name := "FemaleSurname", argCats := #["SN"], resultCat := "NP", status := .primitive }

private def pot51 : FunDecl :=
  { name := "pot51", argCats := #[], resultCat := "Sub1000000000000", status := .primitive }

private def language_title_Utt : FunDecl :=
  { name := "language_title_Utt", argCats := #[], resultCat := "Utt", status := .primitive }

private def can8know_VV : FunDecl :=
  { name := "can8know_VV", argCats := #[], resultCat := "VV", status := .primitive }

private def ComplVS : FunDecl :=
  { name := "ComplVS", argCats := #["VS", "S"], resultCat := "VP", status := .primitive }

private def PrepIP : FunDecl :=
  { name := "PrepIP", argCats := #["Prep", "IP"], resultCat := "IAdv", status := .primitive }

private def Use2N3 : FunDecl :=
  { name := "Use2N3", argCats := #["N3"], resultCat := "N2", status := .primitive }

private def AdjLN : FunDecl :=
  { name := "AdjLN", argCats := #["AP", "LN"], resultCat := "LN", status := .primitive }

private def nobody_NP : FunDecl :=
  { name := "nobody_NP", argCats := #[], resultCat := "NP", status := .primitive }

private def EmbedVP : FunDecl :=
  { name := "EmbedVP", argCats := #["VP"], resultCat := "SC", status := .primitive }

private def IDig : FunDecl :=
  { name := "IDig", argCats := #["Dig"], resultCat := "Digits", status := .primitive }

private def please_Voc : FunDecl :=
  { name := "please_Voc", argCats := #[], resultCat := "Voc", status := .primitive }

private def so_AdA : FunDecl :=
  { name := "so_AdA", argCats := #[], resultCat := "AdA", status := .primitive }

private def youSg_Pron : FunDecl :=
  { name := "youSg_Pron", argCats := #[], resultCat := "Pron", status := .primitive }

private def UttImpPl : FunDecl :=
  { name := "UttImpPl", argCats := #["Pol", "Imp"], resultCat := "Utt", status := .primitive }

private def UttIAdv : FunDecl :=
  { name := "UttIAdv", argCats := #["IAdv"], resultCat := "Utt", status := .primitive }

private def ConjIAdv : FunDecl :=
  { name := "ConjIAdv", argCats := #["Conj", "ListIAdv"], resultCat := "IAdv", status := .primitive }

private def Slash2V3 : FunDecl :=
  { name := "Slash2V3", argCats := #["V3", "NP"], resultCat := "VPSlash", status := .primitive }

private def pot4decimal : FunDecl :=
  { name := "pot4decimal", argCats := #["Decimal"], resultCat := "Sub1000000000", status := .primitive }

private def AdvQVP : FunDecl :=
  { name := "AdvQVP", argCats := #["VP", "IAdv"], resultCat := "QVP", status := .primitive }

private def here7from_Adv : FunDecl :=
  { name := "here7from_Adv", argCats := #[], resultCat := "Adv", status := .primitive }

private def SlashV2S : FunDecl :=
  { name := "SlashV2S", argCats := #["V2S", "S"], resultCat := "VPSlash", status := .primitive }

private def SentCN : FunDecl :=
  { name := "SentCN", argCats := #["CN", "SC"], resultCat := "CN", status := .primitive }

private def UseComparA : FunDecl :=
  { name := "UseComparA", argCats := #["A"], resultCat := "AP", status := .primitive }

private def IdRP : FunDecl :=
  { name := "IdRP", argCats := #[], resultCat := "RP", status := .primitive }

private def RelS : FunDecl :=
  { name := "RelS", argCats := #["S", "RS"], resultCat := "S", status := .primitive }

private def SlashV2a : FunDecl :=
  { name := "SlashV2a", argCats := #["V2"], resultCat := "VPSlash", status := .primitive }

private def TTAnt : FunDecl :=
  { name := "TTAnt", argCats := #["Tense", "Ant"], resultCat := "Temp", status := .primitive }

private def CleftNP : FunDecl :=
  { name := "CleftNP", argCats := #["NP", "RS"], resultCat := "Cl", status := .primitive }

private def ConsRS : FunDecl :=
  { name := "ConsRS", argCats := #["RS", "ListRS"], resultCat := "ListRS", status := .primitive }

private def CleftAdv : FunDecl :=
  { name := "CleftAdv", argCats := #["Adv", "S"], resultCat := "Cl", status := .primitive }

private def pot5decimal : FunDecl :=
  { name := "pot5decimal", argCats := #["Decimal"], resultCat := "Sub1000000000000", status := .primitive }

private def AAnter : FunDecl :=
  { name := "AAnter", argCats := #[], resultCat := "Ant", status := .primitive }

private def PartNP : FunDecl :=
  { name := "PartNP", argCats := #["CN", "NP"], resultCat := "CN", status := .primitive }

private def otherwise_PConj : FunDecl :=
  { name := "otherwise_PConj", argCats := #[], resultCat := "PConj", status := .primitive }

private def AdNum : FunDecl :=
  { name := "AdNum", argCats := #["AdN", "Card"], resultCat := "Card", status := .primitive }

private def youPl_Pron : FunDecl :=
  { name := "youPl_Pron", argCats := #[], resultCat := "Pron", status := .primitive }

private def pot4 : FunDecl :=
  { name := "pot4", argCats := #["Sub1000"], resultCat := "Sub1000000000", status := .primitive }

private def UttAP : FunDecl :=
  { name := "UttAP", argCats := #["AP"], resultCat := "Utt", status := .primitive }

private def pot5plus : FunDecl :=
  { name := "pot5plus", argCats := #["Sub1000", "Sub1000000000"], resultCat := "Sub1000000000000", status := .primitive }

private def behind_Prep : FunDecl :=
  { name := "behind_Prep", argCats := #[], resultCat := "Prep", status := .primitive }

private def ImpPl1 : FunDecl :=
  { name := "ImpPl1", argCats := #["VP"], resultCat := "Utt", status := .primitive }

private def AdjOrd : FunDecl :=
  { name := "AdjOrd", argCats := #["Ord"], resultCat := "AP", status := .primitive }

private def BaseAP : FunDecl :=
  { name := "BaseAP", argCats := #["AP", "AP"], resultCat := "ListAP", status := .primitive }

private def PhrUtt : FunDecl :=
  { name := "PhrUtt", argCats := #["PConj", "Utt", "Voc"], resultCat := "Phr", status := .primitive }

private def SelfAdvVP : FunDecl :=
  { name := "SelfAdvVP", argCats := #["VP"], resultCat := "VP", status := .primitive }

private def that_Subj : FunDecl :=
  { name := "that_Subj", argCats := #[], resultCat := "Subj", status := .primitive }

private def CountNP : FunDecl :=
  { name := "CountNP", argCats := #["Det", "NP"], resultCat := "NP", status := .primitive }

private def n6 : FunDecl :=
  { name := "n6", argCats := #[], resultCat := "Digit", status := .primitive }

private def ConsAdv : FunDecl :=
  { name := "ConsAdv", argCats := #["Adv", "ListAdv"], resultCat := "ListAdv", status := .primitive }

private def PPos : FunDecl :=
  { name := "PPos", argCats := #[], resultCat := "Pol", status := .primitive }

private def NumNumeral : FunDecl :=
  { name := "NumNumeral", argCats := #["Numeral"], resultCat := "Card", status := .primitive }

private def PossPron : FunDecl :=
  { name := "PossPron", argCats := #["Pron"], resultCat := "Quant", status := .primitive }

private def AdvSlash : FunDecl :=
  { name := "AdvSlash", argCats := #["ClSlash", "Adv"], resultCat := "ClSlash", status := .primitive }

private def youPol_Pron : FunDecl :=
  { name := "youPol_Pron", argCats := #[], resultCat := "Pron", status := .primitive }

private def QuestIAdv : FunDecl :=
  { name := "QuestIAdv", argCats := #["IAdv", "Cl"], resultCat := "QCl", status := .primitive }

private def DefArt : FunDecl :=
  { name := "DefArt", argCats := #[], resultCat := "Quant", status := .primitive }

private def nothing_NP : FunDecl :=
  { name := "nothing_NP", argCats := #[], resultCat := "NP", status := .primitive }

private def somewhere_Adv : FunDecl :=
  { name := "somewhere_Adv", argCats := #[], resultCat := "Adv", status := .primitive }

private def very_AdA : FunDecl :=
  { name := "very_AdA", argCats := #[], resultCat := "AdA", status := .primitive }

private def dn1000000b : FunDecl :=
  { name := "dn1000000b", argCats := #["Dig", "Dig", "Dig", "Dig", "Dig"], resultCat := "Sub1000000", status := .primitive }

private def UttVP : FunDecl :=
  { name := "UttVP", argCats := #["VP"], resultCat := "Utt", status := .primitive }

private def TExclMark : FunDecl :=
  { name := "TExclMark", argCats := #["Phr", "Text"], resultCat := "Text", status := .primitive }

private def ConsAdV : FunDecl :=
  { name := "ConsAdV", argCats := #["AdV", "ListAdV"], resultCat := "ListAdV", status := .primitive }

private def PredVP : FunDecl :=
  { name := "PredVP", argCats := #["NP", "VP"], resultCat := "Cl", status := .primitive }

private def QuestCl : FunDecl :=
  { name := "QuestCl", argCats := #["Cl"], resultCat := "QCl", status := .primitive }

private def therefore_PConj : FunDecl :=
  { name := "therefore_PConj", argCats := #[], resultCat := "PConj", status := .primitive }

private def dconcat : FunDecl :=
  { name := "dconcat", argCats := #["Digits", "Digits"], resultCat := "Digits", status := .primitive }

private def ComparAdvAdj : FunDecl :=
  { name := "ComparAdvAdj", argCats := #["CAdv", "A", "NP"], resultCat := "Adv", status := .primitive }

private def GivenName : FunDecl :=
  { name := "GivenName", argCats := #["GN"], resultCat := "NP", status := .primitive }

private def Slash3V3 : FunDecl :=
  { name := "Slash3V3", argCats := #["V3", "NP"], resultCat := "VPSlash", status := .primitive }

private def IdetQuant : FunDecl :=
  { name := "IdetQuant", argCats := #["IQuant", "Num"], resultCat := "IDet", status := .primitive }

private def ExistNP : FunDecl :=
  { name := "ExistNP", argCats := #["NP"], resultCat := "Cl", status := .primitive }

private def Use3N3 : FunDecl :=
  { name := "Use3N3", argCats := #["N3"], resultCat := "N2", status := .primitive }

private def pot3 : FunDecl :=
  { name := "pot3", argCats := #["Sub1000"], resultCat := "Sub1000000", status := .primitive }

private def ComparA : FunDecl :=
  { name := "ComparA", argCats := #["A", "NP"], resultCat := "AP", status := .primitive }

private def no_Utt : FunDecl :=
  { name := "no_Utt", argCats := #[], resultCat := "Utt", status := .primitive }

private def i_Pron : FunDecl :=
  { name := "i_Pron", argCats := #[], resultCat := "Pron", status := .primitive }

private def pot3plus : FunDecl :=
  { name := "pot3plus", argCats := #["Sub1000", "Sub1000"], resultCat := "Sub1000000", status := .primitive }

private def UttImpPol : FunDecl :=
  { name := "UttImpPol", argCats := #["Pol", "Imp"], resultCat := "Utt", status := .primitive }

private def UsePron : FunDecl :=
  { name := "UsePron", argCats := #["Pron"], resultCat := "NP", status := .primitive }

private def BaseCN : FunDecl :=
  { name := "BaseCN", argCats := #["CN", "CN"], resultCat := "ListCN", status := .primitive }

private def MassNP : FunDecl :=
  { name := "MassNP", argCats := #["CN"], resultCat := "NP", status := .primitive }

private def by8means_Prep : FunDecl :=
  { name := "by8means_Prep", argCats := #[], resultCat := "Prep", status := .primitive }

private def OrdNumeralSuperl : FunDecl :=
  { name := "OrdNumeralSuperl", argCats := #["Numeral", "A"], resultCat := "Ord", status := .primitive }

private def SubjS : FunDecl :=
  { name := "SubjS", argCats := #["Subj", "S"], resultCat := "Adv", status := .primitive }

private def BaseRS : FunDecl :=
  { name := "BaseRS", argCats := #["RS", "RS"], resultCat := "ListRS", status := .primitive }

private def BaseAdv : FunDecl :=
  { name := "BaseAdv", argCats := #["Adv", "Adv"], resultCat := "ListAdv", status := .primitive }

private def NumPl : FunDecl :=
  { name := "NumPl", argCats := #[], resultCat := "Num", status := .primitive }

private def always_AdV : FunDecl :=
  { name := "always_AdV", argCats := #[], resultCat := "AdV", status := .primitive }

private def n4 : FunDecl :=
  { name := "n4", argCats := #[], resultCat := "Digit", status := .primitive }

private def OrdSuperl : FunDecl :=
  { name := "OrdSuperl", argCats := #["A"], resultCat := "Ord", status := .primitive }

private def in8front_Prep : FunDecl :=
  { name := "in8front_Prep", argCats := #[], resultCat := "Prep", status := .primitive }

private def ComplSlashIP : FunDecl :=
  { name := "ComplSlashIP", argCats := #["VPSlash", "IP"], resultCat := "QVP", status := .primitive }

private def there_Adv : FunDecl :=
  { name := "there_Adv", argCats := #[], resultCat := "Adv", status := .primitive }

private def BaseDAP : FunDecl :=
  { name := "BaseDAP", argCats := #["DAP", "DAP"], resultCat := "ListDAP", status := .primitive }

private def ExtAdvNP : FunDecl :=
  { name := "ExtAdvNP", argCats := #["NP", "Adv"], resultCat := "NP", status := .primitive }

private def QuestQVP : FunDecl :=
  { name := "QuestQVP", argCats := #["IP", "QVP"], resultCat := "QCl", status := .primitive }

private def that_Quant : FunDecl :=
  { name := "that_Quant", argCats := #[], resultCat := "Quant", status := .primitive }

private def less_CAdv : FunDecl :=
  { name := "less_CAdv", argCats := #[], resultCat := "CAdv", status := .primitive }

private def UttAdv : FunDecl :=
  { name := "UttAdv", argCats := #["Adv"], resultCat := "Utt", status := .primitive }

private def ComplSlash : FunDecl :=
  { name := "ComplSlash", argCats := #["VPSlash", "NP"], resultCat := "VP", status := .primitive }

private def PositAdAAdj : FunDecl :=
  { name := "PositAdAAdj", argCats := #["A"], resultCat := "AdA", status := .primitive }

private def after_Prep : FunDecl :=
  { name := "after_Prep", argCats := #[], resultCat := "Prep", status := .primitive }

private def ConsDAP : FunDecl :=
  { name := "ConsDAP", argCats := #["DAP", "ListDAP"], resultCat := "ListDAP", status := .primitive }

private def InLN : FunDecl :=
  { name := "InLN", argCats := #["LN"], resultCat := "Adv", status := .primitive }

private def SelfAdVVP : FunDecl :=
  { name := "SelfAdVVP", argCats := #["VP"], resultCat := "VP", status := .primitive }

private def SlashVP : FunDecl :=
  { name := "SlashVP", argCats := #["NP", "VPSlash"], resultCat := "ClSlash", status := .primitive }

private def must_VV : FunDecl :=
  { name := "must_VV", argCats := #[], resultCat := "VV", status := .primitive }

private def only_Predet : FunDecl :=
  { name := "only_Predet", argCats := #[], resultCat := "Predet", status := .primitive }

private def UseCopula : FunDecl :=
  { name := "UseCopula", argCats := #[], resultCat := "VP", status := .primitive }

private def ApposCN : FunDecl :=
  { name := "ApposCN", argCats := #["CN", "NP"], resultCat := "CN", status := .primitive }

private def pot01 : FunDecl :=
  { name := "pot01", argCats := #[], resultCat := "Sub10", status := .primitive }

private def QuestSlash : FunDecl :=
  { name := "QuestSlash", argCats := #["IP", "ClSlash"], resultCat := "QCl", status := .primitive }

private def digits2num : FunDecl :=
  { name := "digits2num", argCats := #["Digits"], resultCat := "Numeral", status := .primitive }

private def to_Prep : FunDecl :=
  { name := "to_Prep", argCats := #[], resultCat := "Prep", status := .primitive }

private def whoPl_IP : FunDecl :=
  { name := "whoPl_IP", argCats := #[], resultCat := "IP", status := .primitive }

private def or_Conj : FunDecl :=
  { name := "or_Conj", argCats := #[], resultCat := "Conj", status := .primitive }

private def dn : FunDecl :=
  { name := "dn", argCats := #["Dig"], resultCat := "Digit", status := .primitive }

private def ImpVP : FunDecl :=
  { name := "ImpVP", argCats := #["VP"], resultCat := "Imp", status := .primitive }

private def n5 : FunDecl :=
  { name := "n5", argCats := #[], resultCat := "Digit", status := .primitive }

private def ComparAdvAdjS : FunDecl :=
  { name := "ComparAdvAdjS", argCats := #["CAdv", "A", "S"], resultCat := "Adv", status := .primitive }

private def somePl_Det : FunDecl :=
  { name := "somePl_Det", argCats := #[], resultCat := "Det", status := .primitive }

private def D_6 : FunDecl :=
  { name := "D_6", argCats := #[], resultCat := "Dig", status := .primitive }

private def NegDecimal : FunDecl :=
  { name := "NegDecimal", argCats := #["Digits"], resultCat := "Decimal", status := .primitive }

private def UseN2 : FunDecl :=
  { name := "UseN2", argCats := #["N2"], resultCat := "CN", status := .primitive }

private def by8agent_Prep : FunDecl :=
  { name := "by8agent_Prep", argCats := #[], resultCat := "Prep", status := .primitive }

private def ReflA2 : FunDecl :=
  { name := "ReflA2", argCats := #["A2"], resultCat := "AP", status := .primitive }

private def VocNP : FunDecl :=
  { name := "VocNP", argCats := #["NP"], resultCat := "Voc", status := .primitive }

private def PossNP : FunDecl :=
  { name := "PossNP", argCats := #["CN", "NP"], resultCat := "CN", status := .primitive }

private def UseSlash : FunDecl :=
  { name := "UseSlash", argCats := #["Temp", "Pol", "ClSlash"], resultCat := "SSlash", status := .primitive }

private def AdvS : FunDecl :=
  { name := "AdvS", argCats := #["Adv", "S"], resultCat := "S", status := .primitive }

private def AdjCN : FunDecl :=
  { name := "AdjCN", argCats := #["AP", "CN"], resultCat := "CN", status := .primitive }

private def D_0 : FunDecl :=
  { name := "D_0", argCats := #[], resultCat := "Dig", status := .primitive }

private def pot1 : FunDecl :=
  { name := "pot1", argCats := #["Digit"], resultCat := "Sub100", status := .primitive }

private def CompAdv : FunDecl :=
  { name := "CompAdv", argCats := #["Adv"], resultCat := "Comp", status := .primitive }

private def BaseAdV : FunDecl :=
  { name := "BaseAdV", argCats := #["AdV", "AdV"], resultCat := "ListAdV", status := .primitive }

private def whatSg_IP : FunDecl :=
  { name := "whatSg_IP", argCats := #[], resultCat := "IP", status := .primitive }

private def everywhere_Adv : FunDecl :=
  { name := "everywhere_Adv", argCats := #[], resultCat := "Adv", status := .primitive }

private def if_Subj : FunDecl :=
  { name := "if_Subj", argCats := #[], resultCat := "Subj", status := .primitive }

private def many_Det : FunDecl :=
  { name := "many_Det", argCats := #[], resultCat := "Det", status := .primitive }

private def this_Quant : FunDecl :=
  { name := "this_Quant", argCats := #[], resultCat := "Quant", status := .primitive }

private def PositAdvAdj : FunDecl :=
  { name := "PositAdvAdj", argCats := #["A"], resultCat := "Adv", status := .primitive }

private def CompAP : FunDecl :=
  { name := "CompAP", argCats := #["AP"], resultCat := "Comp", status := .primitive }

private def ConjCN : FunDecl :=
  { name := "ConjCN", argCats := #["Conj", "ListCN"], resultCat := "CN", status := .primitive }

private def nd1000 : FunDecl :=
  { name := "nd1000", argCats := #["Sub1000"], resultCat := "Digits", status := .primitive }

private def UseV : FunDecl :=
  { name := "UseV", argCats := #["V"], resultCat := "VP", status := .primitive }

private def before_Prep : FunDecl :=
  { name := "before_Prep", argCats := #[], resultCat := "Prep", status := .primitive }

private def pot111 : FunDecl :=
  { name := "pot111", argCats := #[], resultCat := "Sub100", status := .primitive }

private def QuestVP : FunDecl :=
  { name := "QuestVP", argCats := #["IP", "VP"], resultCat := "QCl", status := .primitive }

private def have_V2 : FunDecl :=
  { name := "have_V2", argCats := #[], resultCat := "V2", status := .primitive }

private def UttQS : FunDecl :=
  { name := "UttQS", argCats := #["QS"], resultCat := "Utt", status := .primitive }

private def ConjRS : FunDecl :=
  { name := "ConjRS", argCats := #["Conj", "ListRS"], resultCat := "RS", status := .primitive }

private def ConsS : FunDecl :=
  { name := "ConsS", argCats := #["S", "ListS"], resultCat := "ListS", status := .primitive }

private def D_1 : FunDecl :=
  { name := "D_1", argCats := #[], resultCat := "Dig", status := .primitive }

private def SSubjS : FunDecl :=
  { name := "SSubjS", argCats := #["S", "Subj", "S"], resultCat := "S", status := .primitive }

private def dn100 : FunDecl :=
  { name := "dn100", argCats := #["Dig", "Dig"], resultCat := "Sub100", status := .primitive }

private def BaseNP : FunDecl :=
  { name := "BaseNP", argCats := #["NP", "NP"], resultCat := "ListNP", status := .primitive }

private def MaleSurname : FunDecl :=
  { name := "MaleSurname", argCats := #["SN"], resultCat := "NP", status := .primitive }

private def num : FunDecl :=
  { name := "num", argCats := #["Sub1000000"], resultCat := "Numeral", status := .primitive }

private def NumDigits : FunDecl :=
  { name := "NumDigits", argCats := #["Digits"], resultCat := "Card", status := .primitive }

private def want_VV : FunDecl :=
  { name := "want_VV", argCats := #[], resultCat := "VV", status := .primitive }

private def dn10 : FunDecl :=
  { name := "dn10", argCats := #["Dig"], resultCat := "Sub10", status := .primitive }

private def RelCl : FunDecl :=
  { name := "RelCl", argCats := #["Cl"], resultCat := "RCl", status := .primitive }

private def CompIP : FunDecl :=
  { name := "CompIP", argCats := #["IP"], resultCat := "IComp", status := .primitive }

private def ComplA2 : FunDecl :=
  { name := "ComplA2", argCats := #["A2", "NP"], resultCat := "AP", status := .primitive }

private def during_Prep : FunDecl :=
  { name := "during_Prep", argCats := #[], resultCat := "Prep", status := .primitive }

private def TFut : FunDecl :=
  { name := "TFut", argCats := #[], resultCat := "Tense", status := .primitive }

private def TFullStop : FunDecl :=
  { name := "TFullStop", argCats := #["Phr", "Text"], resultCat := "Text", status := .primitive }

private def pot1plus : FunDecl :=
  { name := "pot1plus", argCats := #["Digit", "Sub10"], resultCat := "Sub100", status := .primitive }

private def UseRCl : FunDecl :=
  { name := "UseRCl", argCats := #["Temp", "Pol", "RCl"], resultCat := "RS", status := .primitive }

private def much_Det : FunDecl :=
  { name := "much_Det", argCats := #[], resultCat := "Det", status := .primitive }

private def few_Det : FunDecl :=
  { name := "few_Det", argCats := #[], resultCat := "Det", status := .primitive }

private def AdAP : FunDecl :=
  { name := "AdAP", argCats := #["AdA", "AP"], resultCat := "AP", status := .primitive }

private def PositA : FunDecl :=
  { name := "PositA", argCats := #["A"], resultCat := "AP", status := .primitive }

private def AdvVPSlash : FunDecl :=
  { name := "AdvVPSlash", argCats := #["VPSlash", "Adv"], resultCat := "VPSlash", status := .primitive }

private def pot0as1 : FunDecl :=
  { name := "pot0as1", argCats := #["Sub10"], resultCat := "Sub100", status := .primitive }

private def UseCl : FunDecl :=
  { name := "UseCl", argCats := #["Temp", "Pol", "Cl"], resultCat := "S", status := .primitive }

private def CompNP : FunDecl :=
  { name := "CompNP", argCats := #["NP"], resultCat := "Comp", status := .primitive }

private def pot4plus : FunDecl :=
  { name := "pot4plus", argCats := #["Sub1000", "Sub1000000"], resultCat := "Sub1000000000", status := .primitive }

private def dn1000000c : FunDecl :=
  { name := "dn1000000c", argCats := #["Dig", "Dig", "Dig", "Dig", "Dig", "Dig"], resultCat := "Sub1000000", status := .primitive }

private def there7from_Adv : FunDecl :=
  { name := "there7from_Adv", argCats := #[], resultCat := "Adv", status := .primitive }

private def OrdNumeral : FunDecl :=
  { name := "OrdNumeral", argCats := #["Numeral"], resultCat := "Ord", status := .primitive }

private def he_Pron : FunDecl :=
  { name := "he_Pron", argCats := #[], resultCat := "Pron", status := .primitive }

private def SlashV2VNP : FunDecl :=
  { name := "SlashV2VNP", argCats := #["V2V", "NP", "VPSlash"], resultCat := "VPSlash", status := .primitive }

private def something_NP : FunDecl :=
  { name := "something_NP", argCats := #[], resultCat := "NP", status := .primitive }

private def TQuestMark : FunDecl :=
  { name := "TQuestMark", argCats := #["Phr", "Text"], resultCat := "Text", status := .primitive }

private def SlashVS : FunDecl :=
  { name := "SlashVS", argCats := #["NP", "VS", "SSlash"], resultCat := "ClSlash", status := .primitive }

private def which_IQuant : FunDecl :=
  { name := "which_IQuant", argCats := #[], resultCat := "IQuant", status := .primitive }

private def TPres : FunDecl :=
  { name := "TPres", argCats := #[], resultCat := "Tense", status := .primitive }

private def it_Pron : FunDecl :=
  { name := "it_Pron", argCats := #[], resultCat := "Pron", status := .primitive }

private def part_Prep : FunDecl :=
  { name := "part_Prep", argCats := #[], resultCat := "Prep", status := .primitive }

private def there7to_Adv : FunDecl :=
  { name := "there7to_Adv", argCats := #[], resultCat := "Adv", status := .primitive }

private def active2passive : FunDecl :=
  { name := "active2passive", argCats := #["Cl"], resultCat := "Cl", status := .primitive }

private def FunRP : FunDecl :=
  { name := "FunRP", argCats := #["Prep", "NP", "RP"], resultCat := "RP", status := .primitive }

private def she_Pron : FunDecl :=
  { name := "she_Pron", argCats := #[], resultCat := "Pron", status := .primitive }

private def PassV2 : FunDecl :=
  { name := "PassV2", argCats := #["V2"], resultCat := "VP", status := .primitive }

private def pot2plus : FunDecl :=
  { name := "pot2plus", argCats := #["Sub10", "Sub100"], resultCat := "Sub1000", status := .primitive }

private def QuestIComp : FunDecl :=
  { name := "QuestIComp", argCats := #["IComp", "NP"], resultCat := "QCl", status := .primitive }

private def digits2numeral : FunDecl :=
  { name := "digits2numeral", argCats := #["Card"], resultCat := "Card", status := .primitive }

private def UttImpSg : FunDecl :=
  { name := "UttImpSg", argCats := #["Pol", "Imp"], resultCat := "Utt", status := .primitive }

private def ComplN2 : FunDecl :=
  { name := "ComplN2", argCats := #["N2", "NP"], resultCat := "CN", status := .primitive }

private def NoPConj : FunDecl :=
  { name := "NoPConj", argCats := #[], resultCat := "PConj", status := .primitive }

private def ReflVP : FunDecl :=
  { name := "ReflVP", argCats := #["VPSlash"], resultCat := "VP", status := .primitive }

private def SlashV2Q : FunDecl :=
  { name := "SlashV2Q", argCats := #["V2Q", "QS"], resultCat := "VPSlash", status := .primitive }

private def ConsAP : FunDecl :=
  { name := "ConsAP", argCats := #["AP", "ListAP"], resultCat := "ListAP", status := .primitive }

private def D_3 : FunDecl :=
  { name := "D_3", argCats := #[], resultCat := "Dig", status := .primitive }

private def DetNP : FunDecl :=
  { name := "DetNP", argCats := #["Det"], resultCat := "NP", status := .primitive }

private def FullName : FunDecl :=
  { name := "FullName", argCats := #["GN", "SN"], resultCat := "NP", status := .primitive }

private def ConjAdv : FunDecl :=
  { name := "ConjAdv", argCats := #["Conj", "ListAdv"], resultCat := "Adv", status := .primitive }

private def possess_Prep : FunDecl :=
  { name := "possess_Prep", argCats := #[], resultCat := "Prep", status := .primitive }

private def RelVP : FunDecl :=
  { name := "RelVP", argCats := #["RP", "VP"], resultCat := "RCl", status := .primitive }

private def almost_AdN : FunDecl :=
  { name := "almost_AdN", argCats := #[], resultCat := "AdN", status := .primitive }

private def almost_AdA : FunDecl :=
  { name := "almost_AdA", argCats := #[], resultCat := "AdA", status := .primitive }

private def SelfNP : FunDecl :=
  { name := "SelfNP", argCats := #["NP"], resultCat := "NP", status := .primitive }

private def ImpersCl : FunDecl :=
  { name := "ImpersCl", argCats := #["VP"], resultCat := "Cl", status := .primitive }

private def dn1000 : FunDecl :=
  { name := "dn1000", argCats := #["Dig", "Dig", "Dig"], resultCat := "Sub1000", status := .primitive }

private def n3 : FunDecl :=
  { name := "n3", argCats := #[], resultCat := "Digit", status := .primitive }

private def from_Prep : FunDecl :=
  { name := "from_Prep", argCats := #[], resultCat := "Prep", status := .primitive }

private def everything_NP : FunDecl :=
  { name := "everything_NP", argCats := #[], resultCat := "NP", status := .primitive }

private def AdVVPSlash : FunDecl :=
  { name := "AdVVPSlash", argCats := #["AdV", "VPSlash"], resultCat := "VPSlash", status := .primitive }

private def CompCN : FunDecl :=
  { name := "CompCN", argCats := #["CN"], resultCat := "Comp", status := .primitive }

private def GenericCl : FunDecl :=
  { name := "GenericCl", argCats := #["VP"], resultCat := "Cl", status := .primitive }

private def UsePN : FunDecl :=
  { name := "UsePN", argCats := #["PN"], resultCat := "NP", status := .primitive }

private def NumDecimal : FunDecl :=
  { name := "NumDecimal", argCats := #["Decimal"], resultCat := "Card", status := .primitive }

private def ProgrVP : FunDecl :=
  { name := "ProgrVP", argCats := #["VP"], resultCat := "VP", status := .primitive }

private def pot2as3 : FunDecl :=
  { name := "pot2as3", argCats := #["Sub1000"], resultCat := "Sub1000000", status := .primitive }

private def RelCN : FunDecl :=
  { name := "RelCN", argCats := #["CN", "RS"], resultCat := "CN", status := .primitive }

private def pot4as5 : FunDecl :=
  { name := "pot4as5", argCats := #["Sub1000000000"], resultCat := "Sub1000000000000", status := .primitive }

private def everybody_NP : FunDecl :=
  { name := "everybody_NP", argCats := #[], resultCat := "NP", status := .primitive }

private def UttIP : FunDecl :=
  { name := "UttIP", argCats := #["IP"], resultCat := "Utt", status := .primitive }

private def through_Prep : FunDecl :=
  { name := "through_Prep", argCats := #[], resultCat := "Prep", status := .primitive }

private def all_Predet : FunDecl :=
  { name := "all_Predet", argCats := #[], resultCat := "Predet", status := .primitive }

private def SlashVV : FunDecl :=
  { name := "SlashVV", argCats := #["VV", "VPSlash"], resultCat := "VPSlash", status := .primitive }

private def for_Prep : FunDecl :=
  { name := "for_Prep", argCats := #[], resultCat := "Prep", status := .primitive }

private def not_Predet : FunDecl :=
  { name := "not_Predet", argCats := #[], resultCat := "Predet", status := .primitive }

private def pot5 : FunDecl :=
  { name := "pot5", argCats := #["Sub1000"], resultCat := "Sub1000000000000", status := .primitive }

private def NoVoc : FunDecl :=
  { name := "NoVoc", argCats := #[], resultCat := "Voc", status := .primitive }

private def PlainLN : FunDecl :=
  { name := "PlainLN", argCats := #["LN"], resultCat := "NP", status := .primitive }

private def on_Prep : FunDecl :=
  { name := "on_Prep", argCats := #[], resultCat := "Prep", status := .primitive }

private def PrepNP : FunDecl :=
  { name := "PrepNP", argCats := #["Prep", "NP"], resultCat := "Adv", status := .primitive }

private def UseComp : FunDecl :=
  { name := "UseComp", argCats := #["Comp"], resultCat := "VP", status := .primitive }

private def AdvNP : FunDecl :=
  { name := "AdvNP", argCats := #["NP", "Adv"], resultCat := "NP", status := .primitive }

private def under_Prep : FunDecl :=
  { name := "under_Prep", argCats := #[], resultCat := "Prep", status := .primitive }

private def pot2 : FunDecl :=
  { name := "pot2", argCats := #["Sub10"], resultCat := "Sub1000", status := .primitive }

private def yes_Utt : FunDecl :=
  { name := "yes_Utt", argCats := #[], resultCat := "Utt", status := .primitive }

private def AdvIP : FunDecl :=
  { name := "AdvIP", argCats := #["IP", "Adv"], resultCat := "IP", status := .primitive }

private def PredetNP : FunDecl :=
  { name := "PredetNP", argCats := #["Predet", "NP"], resultCat := "NP", status := .primitive }

private def UttS : FunDecl :=
  { name := "UttS", argCats := #["S"], resultCat := "Utt", status := .primitive }

private def ConsIAdv : FunDecl :=
  { name := "ConsIAdv", argCats := #["IAdv", "ListIAdv"], resultCat := "ListIAdv", status := .primitive }

private def D_4 : FunDecl :=
  { name := "D_4", argCats := #[], resultCat := "Dig", status := .primitive }

private def somebody_NP : FunDecl :=
  { name := "somebody_NP", argCats := #[], resultCat := "NP", status := .primitive }

private def without_Prep : FunDecl :=
  { name := "without_Prep", argCats := #[], resultCat := "Prep", status := .primitive }

private def ConsNP : FunDecl :=
  { name := "ConsNP", argCats := #["NP", "ListNP"], resultCat := "ListNP", status := .primitive }

private def DetQuantOrd : FunDecl :=
  { name := "DetQuantOrd", argCats := #["Quant", "Num", "Ord"], resultCat := "Det", status := .primitive }

private def n9 : FunDecl :=
  { name := "n9", argCats := #[], resultCat := "Digit", status := .primitive }

private def how8many_IDet : FunDecl :=
  { name := "how8many_IDet", argCats := #[], resultCat := "IDet", status := .primitive }

private def UttInterj : FunDecl :=
  { name := "UttInterj", argCats := #["Interj"], resultCat := "Utt", status := .primitive }

private def D_9 : FunDecl :=
  { name := "D_9", argCats := #[], resultCat := "Dig", status := .primitive }

private def BaseS : FunDecl :=
  { name := "BaseS", argCats := #["S", "S"], resultCat := "ListS", status := .primitive }

private def EmbedQS : FunDecl :=
  { name := "EmbedQS", argCats := #["QS"], resultCat := "SC", status := .primitive }

private def nd : FunDecl :=
  { name := "nd", argCats := #["Digit"], resultCat := "Dig", status := .primitive }

private def UseLN : FunDecl :=
  { name := "UseLN", argCats := #["LN"], resultCat := "NP", status := .primitive }

private def AdjDAP : FunDecl :=
  { name := "AdjDAP", argCats := #["DAP", "AP"], resultCat := "DAP", status := .primitive }

private def OrdDigits : FunDecl :=
  { name := "OrdDigits", argCats := #["Digits"], resultCat := "Ord", status := .primitive }

private def SlashV2A : FunDecl :=
  { name := "SlashV2A", argCats := #["V2A", "AP"], resultCat := "VPSlash", status := .primitive }

private def UseN : FunDecl :=
  { name := "UseN", argCats := #["N"], resultCat := "CN", status := .primitive }

private def ComplVA : FunDecl :=
  { name := "ComplVA", argCats := #["VA", "AP"], resultCat := "VP", status := .primitive }

private def PosDecimal : FunDecl :=
  { name := "PosDecimal", argCats := #["Digits"], resultCat := "Decimal", status := .primitive }

private def TCond : FunDecl :=
  { name := "TCond", argCats := #[], resultCat := "Tense", status := .primitive }

private def RelSlash : FunDecl :=
  { name := "RelSlash", argCats := #["RP", "ClSlash"], resultCat := "RCl", status := .primitive }

private def ComplN3 : FunDecl :=
  { name := "ComplN3", argCats := #["N3", "NP"], resultCat := "N2", status := .primitive }

private def SentAP : FunDecl :=
  { name := "SentAP", argCats := #["AP", "SC"], resultCat := "AP", status := .primitive }

private def with_Prep : FunDecl :=
  { name := "with_Prep", argCats := #[], resultCat := "Prep", status := .primitive }

private def as_CAdv : FunDecl :=
  { name := "as_CAdv", argCats := #[], resultCat := "CAdv", status := .primitive }

private def ASimul : FunDecl :=
  { name := "ASimul", argCats := #[], resultCat := "Ant", status := .primitive }

private def ExtAdvVP : FunDecl :=
  { name := "ExtAdvVP", argCats := #["VP", "Adv"], resultCat := "VP", status := .primitive }

private def DetQuant : FunDecl :=
  { name := "DetQuant", argCats := #["Quant", "Num"], resultCat := "Det", status := .primitive }

private def how8much_IAdv : FunDecl :=
  { name := "how8much_IAdv", argCats := #[], resultCat := "IAdv", status := .primitive }

private def ComplVV : FunDecl :=
  { name := "ComplVV", argCats := #["VV", "VP"], resultCat := "VP", status := .primitive }

private def why_IAdv : FunDecl :=
  { name := "why_IAdv", argCats := #[], resultCat := "IAdv", status := .primitive }

private def nd1000000 : FunDecl :=
  { name := "nd1000000", argCats := #["Sub1000000"], resultCat := "Digits", status := .primitive }

private def at_least_AdN : FunDecl :=
  { name := "at_least_AdN", argCats := #[], resultCat := "AdN", status := .primitive }

private def D_2 : FunDecl :=
  { name := "D_2", argCats := #[], resultCat := "Dig", status := .primitive }

private def they_Pron : FunDecl :=
  { name := "they_Pron", argCats := #[], resultCat := "Pron", status := .primitive }

private def AdAdv : FunDecl :=
  { name := "AdAdv", argCats := #["AdA", "Adv"], resultCat := "Adv", status := .primitive }

private def above_Prep : FunDecl :=
  { name := "above_Prep", argCats := #[], resultCat := "Prep", status := .primitive }

private def UttCN : FunDecl :=
  { name := "UttCN", argCats := #["CN"], resultCat := "Utt", status := .primitive }

private def pot31 : FunDecl :=
  { name := "pot31", argCats := #[], resultCat := "Sub1000000", status := .primitive }

private def ComplVQ : FunDecl :=
  { name := "ComplVQ", argCats := #["VQ", "QS"], resultCat := "VP", status := .primitive }

private def no_Quant : FunDecl :=
  { name := "no_Quant", argCats := #[], resultCat := "Quant", status := .primitive }

private def if_then_Conj : FunDecl :=
  { name := "if_then_Conj", argCats := #[], resultCat := "Conj", status := .primitive }

private def dn1000000a : FunDecl :=
  { name := "dn1000000a", argCats := #["Dig", "Dig", "Dig", "Dig"], resultCat := "Sub1000000", status := .primitive }

private def ExistIP : FunDecl :=
  { name := "ExistIP", argCats := #["IP"], resultCat := "QCl", status := .primitive }

private def num2digits : FunDecl :=
  { name := "num2digits", argCats := #["Numeral"], resultCat := "Digits", status := .primitive }

private def UttCard : FunDecl :=
  { name := "UttCard", argCats := #["Card"], resultCat := "Utt", status := .primitive }

private def IdetCN : FunDecl :=
  { name := "IdetCN", argCats := #["IDet", "CN"], resultCat := "IP", status := .primitive }

private def AdVVP : FunDecl :=
  { name := "AdVVP", argCats := #["AdV", "VP"], resultCat := "VP", status := .primitive }

private def more_CAdv : FunDecl :=
  { name := "more_CAdv", argCats := #[], resultCat := "CAdv", status := .primitive }

private def how_IAdv : FunDecl :=
  { name := "how_IAdv", argCats := #[], resultCat := "IAdv", status := .primitive }

/-- The list of function declarations (kernel-reducible).
    Use this for proofs; `sig.funs` (HashMap) is for runtime lookup. -/
def funsList : List (String × FunDecl) :=
  [
    ("CompIAdv", CompIAdv),
    ("UseA2", UseA2),
    ("nd10", nd10),
    ("except_Prep", except_Prep),
    ("ImpP3", ImpP3),
    ("pot1as2", pot1as2),
    ("and_Conj", and_Conj),
    ("AdvVP", AdvVP),
    ("pot1to19", pot1to19),
    ("either7or_DConj", either7or_DConj),
    ("NumSg", NumSg),
    ("pot3decimal", pot3decimal),
    ("can_VV", can_VV),
    ("UttNP", UttNP),
    ("ConjDet", ConjDet),
    ("IndefArt", IndefArt),
    ("NumCard", NumCard),
    ("TEmpty", TEmpty),
    ("pot21", pot21),
    ("here_Adv", here_Adv),
    ("VPSlashPrep", VPSlashPrep),
    ("but_PConj", but_PConj),
    ("both7and_DConj", both7and_DConj),
    ("when_IAdv", when_IAdv),
    ("TPast", TPast),
    ("ConjNP", ConjNP),
    ("RelNP", RelNP),
    ("too_AdA", too_AdA),
    ("QuantityNP", QuantityNP),
    ("PConjConj", PConjConj),
    ("pot41", pot41),
    ("DetDAP", DetDAP),
    ("nd100", nd100),
    ("D_8", D_8),
    ("UseQCl", UseQCl),
    ("AdvAP", AdvAP),
    ("pot0", pot0),
    ("whatPl_IP", whatPl_IP),
    ("pot3as4", pot3as4),
    ("ConjS", ConjS),
    ("BaseIAdv", BaseIAdv),
    ("ExistIPAdv", ExistIPAdv),
    ("PredSCVP", PredSCVP),
    ("pot110", pot110),
    ("at_most_AdN", at_most_AdN),
    ("AddAdvQVP", AddAdvQVP),
    ("most_Predet", most_Predet),
    ("n2", n2),
    ("IFrac", IFrac),
    ("AdvImp", AdvImp),
    ("D_7", D_7),
    ("PPartNP", PPartNP),
    ("because_Subj", because_Subj),
    ("although_Subj", although_Subj),
    ("where_IAdv", where_IAdv),
    ("every_Det", every_Det),
    ("PNeg", PNeg),
    ("DetCN", DetCN),
    ("PlSurname", PlSurname),
    ("when_Subj", when_Subj),
    ("SlashPrep", SlashPrep),
    ("ExistNPAdv", ExistNPAdv),
    ("quite_Adv", quite_Adv),
    ("SlashV2V", SlashV2V),
    ("CAdvAP", CAdvAP),
    ("here7to_Adv", here7to_Adv),
    ("AdnCAdv", AdnCAdv),
    ("ConjAP", ConjAP),
    ("IdetIP", IdetIP),
    ("between_Prep", between_Prep),
    ("AdvCN", AdvCN),
    ("whoSg_IP", whoSg_IP),
    ("ConjAdV", ConjAdV),
    ("D_5", D_5),
    ("EmbedS", EmbedS),
    ("someSg_Det", someSg_Det),
    ("ConsCN", ConsCN),
    ("we_Pron", we_Pron),
    ("in_Prep", in_Prep),
    ("AdvIAdv", AdvIAdv),
    ("n8", n8),
    ("ExtAdvS", ExtAdvS),
    ("n7", n7),
    ("IIDig", IIDig),
    ("FemaleSurname", FemaleSurname),
    ("pot51", pot51),
    ("language_title_Utt", language_title_Utt),
    ("can8know_VV", can8know_VV),
    ("ComplVS", ComplVS),
    ("PrepIP", PrepIP),
    ("Use2N3", Use2N3),
    ("AdjLN", AdjLN),
    ("nobody_NP", nobody_NP),
    ("EmbedVP", EmbedVP),
    ("IDig", IDig),
    ("please_Voc", please_Voc),
    ("so_AdA", so_AdA),
    ("youSg_Pron", youSg_Pron),
    ("UttImpPl", UttImpPl),
    ("UttIAdv", UttIAdv),
    ("ConjIAdv", ConjIAdv),
    ("Slash2V3", Slash2V3),
    ("pot4decimal", pot4decimal),
    ("AdvQVP", AdvQVP),
    ("here7from_Adv", here7from_Adv),
    ("SlashV2S", SlashV2S),
    ("SentCN", SentCN),
    ("UseComparA", UseComparA),
    ("IdRP", IdRP),
    ("RelS", RelS),
    ("SlashV2a", SlashV2a),
    ("TTAnt", TTAnt),
    ("CleftNP", CleftNP),
    ("ConsRS", ConsRS),
    ("CleftAdv", CleftAdv),
    ("pot5decimal", pot5decimal),
    ("AAnter", AAnter),
    ("PartNP", PartNP),
    ("otherwise_PConj", otherwise_PConj),
    ("AdNum", AdNum),
    ("youPl_Pron", youPl_Pron),
    ("pot4", pot4),
    ("UttAP", UttAP),
    ("pot5plus", pot5plus),
    ("behind_Prep", behind_Prep),
    ("ImpPl1", ImpPl1),
    ("AdjOrd", AdjOrd),
    ("BaseAP", BaseAP),
    ("PhrUtt", PhrUtt),
    ("SelfAdvVP", SelfAdvVP),
    ("that_Subj", that_Subj),
    ("CountNP", CountNP),
    ("n6", n6),
    ("ConsAdv", ConsAdv),
    ("PPos", PPos),
    ("NumNumeral", NumNumeral),
    ("PossPron", PossPron),
    ("AdvSlash", AdvSlash),
    ("youPol_Pron", youPol_Pron),
    ("QuestIAdv", QuestIAdv),
    ("DefArt", DefArt),
    ("nothing_NP", nothing_NP),
    ("somewhere_Adv", somewhere_Adv),
    ("very_AdA", very_AdA),
    ("dn1000000b", dn1000000b),
    ("UttVP", UttVP),
    ("TExclMark", TExclMark),
    ("ConsAdV", ConsAdV),
    ("PredVP", PredVP),
    ("QuestCl", QuestCl),
    ("therefore_PConj", therefore_PConj),
    ("dconcat", dconcat),
    ("ComparAdvAdj", ComparAdvAdj),
    ("GivenName", GivenName),
    ("Slash3V3", Slash3V3),
    ("IdetQuant", IdetQuant),
    ("ExistNP", ExistNP),
    ("Use3N3", Use3N3),
    ("pot3", pot3),
    ("ComparA", ComparA),
    ("no_Utt", no_Utt),
    ("i_Pron", i_Pron),
    ("pot3plus", pot3plus),
    ("UttImpPol", UttImpPol),
    ("UsePron", UsePron),
    ("BaseCN", BaseCN),
    ("MassNP", MassNP),
    ("by8means_Prep", by8means_Prep),
    ("OrdNumeralSuperl", OrdNumeralSuperl),
    ("SubjS", SubjS),
    ("BaseRS", BaseRS),
    ("BaseAdv", BaseAdv),
    ("NumPl", NumPl),
    ("always_AdV", always_AdV),
    ("n4", n4),
    ("OrdSuperl", OrdSuperl),
    ("in8front_Prep", in8front_Prep),
    ("ComplSlashIP", ComplSlashIP),
    ("there_Adv", there_Adv),
    ("BaseDAP", BaseDAP),
    ("ExtAdvNP", ExtAdvNP),
    ("QuestQVP", QuestQVP),
    ("that_Quant", that_Quant),
    ("less_CAdv", less_CAdv),
    ("UttAdv", UttAdv),
    ("ComplSlash", ComplSlash),
    ("PositAdAAdj", PositAdAAdj),
    ("after_Prep", after_Prep),
    ("ConsDAP", ConsDAP),
    ("InLN", InLN),
    ("SelfAdVVP", SelfAdVVP),
    ("SlashVP", SlashVP),
    ("must_VV", must_VV),
    ("only_Predet", only_Predet),
    ("UseCopula", UseCopula),
    ("ApposCN", ApposCN),
    ("pot01", pot01),
    ("QuestSlash", QuestSlash),
    ("digits2num", digits2num),
    ("to_Prep", to_Prep),
    ("whoPl_IP", whoPl_IP),
    ("or_Conj", or_Conj),
    ("dn", dn),
    ("ImpVP", ImpVP),
    ("n5", n5),
    ("ComparAdvAdjS", ComparAdvAdjS),
    ("somePl_Det", somePl_Det),
    ("D_6", D_6),
    ("NegDecimal", NegDecimal),
    ("UseN2", UseN2),
    ("by8agent_Prep", by8agent_Prep),
    ("ReflA2", ReflA2),
    ("VocNP", VocNP),
    ("PossNP", PossNP),
    ("UseSlash", UseSlash),
    ("AdvS", AdvS),
    ("AdjCN", AdjCN),
    ("D_0", D_0),
    ("pot1", pot1),
    ("CompAdv", CompAdv),
    ("BaseAdV", BaseAdV),
    ("whatSg_IP", whatSg_IP),
    ("everywhere_Adv", everywhere_Adv),
    ("if_Subj", if_Subj),
    ("many_Det", many_Det),
    ("this_Quant", this_Quant),
    ("PositAdvAdj", PositAdvAdj),
    ("CompAP", CompAP),
    ("ConjCN", ConjCN),
    ("nd1000", nd1000),
    ("UseV", UseV),
    ("before_Prep", before_Prep),
    ("pot111", pot111),
    ("QuestVP", QuestVP),
    ("have_V2", have_V2),
    ("UttQS", UttQS),
    ("ConjRS", ConjRS),
    ("ConsS", ConsS),
    ("D_1", D_1),
    ("SSubjS", SSubjS),
    ("dn100", dn100),
    ("BaseNP", BaseNP),
    ("MaleSurname", MaleSurname),
    ("num", num),
    ("NumDigits", NumDigits),
    ("want_VV", want_VV),
    ("dn10", dn10),
    ("RelCl", RelCl),
    ("CompIP", CompIP),
    ("ComplA2", ComplA2),
    ("during_Prep", during_Prep),
    ("TFut", TFut),
    ("TFullStop", TFullStop),
    ("pot1plus", pot1plus),
    ("UseRCl", UseRCl),
    ("much_Det", much_Det),
    ("few_Det", few_Det),
    ("AdAP", AdAP),
    ("PositA", PositA),
    ("AdvVPSlash", AdvVPSlash),
    ("pot0as1", pot0as1),
    ("UseCl", UseCl),
    ("CompNP", CompNP),
    ("pot4plus", pot4plus),
    ("dn1000000c", dn1000000c),
    ("there7from_Adv", there7from_Adv),
    ("OrdNumeral", OrdNumeral),
    ("he_Pron", he_Pron),
    ("SlashV2VNP", SlashV2VNP),
    ("something_NP", something_NP),
    ("TQuestMark", TQuestMark),
    ("SlashVS", SlashVS),
    ("which_IQuant", which_IQuant),
    ("TPres", TPres),
    ("it_Pron", it_Pron),
    ("part_Prep", part_Prep),
    ("there7to_Adv", there7to_Adv),
    ("active2passive", active2passive),
    ("FunRP", FunRP),
    ("she_Pron", she_Pron),
    ("PassV2", PassV2),
    ("pot2plus", pot2plus),
    ("QuestIComp", QuestIComp),
    ("digits2numeral", digits2numeral),
    ("UttImpSg", UttImpSg),
    ("ComplN2", ComplN2),
    ("NoPConj", NoPConj),
    ("ReflVP", ReflVP),
    ("SlashV2Q", SlashV2Q),
    ("ConsAP", ConsAP),
    ("D_3", D_3),
    ("DetNP", DetNP),
    ("FullName", FullName),
    ("ConjAdv", ConjAdv),
    ("possess_Prep", possess_Prep),
    ("RelVP", RelVP),
    ("almost_AdN", almost_AdN),
    ("almost_AdA", almost_AdA),
    ("SelfNP", SelfNP),
    ("ImpersCl", ImpersCl),
    ("dn1000", dn1000),
    ("n3", n3),
    ("from_Prep", from_Prep),
    ("everything_NP", everything_NP),
    ("AdVVPSlash", AdVVPSlash),
    ("CompCN", CompCN),
    ("GenericCl", GenericCl),
    ("UsePN", UsePN),
    ("NumDecimal", NumDecimal),
    ("ProgrVP", ProgrVP),
    ("pot2as3", pot2as3),
    ("RelCN", RelCN),
    ("pot4as5", pot4as5),
    ("everybody_NP", everybody_NP),
    ("UttIP", UttIP),
    ("through_Prep", through_Prep),
    ("all_Predet", all_Predet),
    ("SlashVV", SlashVV),
    ("for_Prep", for_Prep),
    ("not_Predet", not_Predet),
    ("pot5", pot5),
    ("NoVoc", NoVoc),
    ("PlainLN", PlainLN),
    ("on_Prep", on_Prep),
    ("PrepNP", PrepNP),
    ("UseComp", UseComp),
    ("AdvNP", AdvNP),
    ("under_Prep", under_Prep),
    ("pot2", pot2),
    ("yes_Utt", yes_Utt),
    ("AdvIP", AdvIP),
    ("PredetNP", PredetNP),
    ("UttS", UttS),
    ("ConsIAdv", ConsIAdv),
    ("D_4", D_4),
    ("somebody_NP", somebody_NP),
    ("without_Prep", without_Prep),
    ("ConsNP", ConsNP),
    ("DetQuantOrd", DetQuantOrd),
    ("n9", n9),
    ("how8many_IDet", how8many_IDet),
    ("UttInterj", UttInterj),
    ("D_9", D_9),
    ("BaseS", BaseS),
    ("EmbedQS", EmbedQS),
    ("nd", nd),
    ("UseLN", UseLN),
    ("AdjDAP", AdjDAP),
    ("OrdDigits", OrdDigits),
    ("SlashV2A", SlashV2A),
    ("UseN", UseN),
    ("ComplVA", ComplVA),
    ("PosDecimal", PosDecimal),
    ("TCond", TCond),
    ("RelSlash", RelSlash),
    ("ComplN3", ComplN3),
    ("SentAP", SentAP),
    ("with_Prep", with_Prep),
    ("as_CAdv", as_CAdv),
    ("ASimul", ASimul),
    ("ExtAdvVP", ExtAdvVP),
    ("DetQuant", DetQuant),
    ("how8much_IAdv", how8much_IAdv),
    ("ComplVV", ComplVV),
    ("why_IAdv", why_IAdv),
    ("nd1000000", nd1000000),
    ("at_least_AdN", at_least_AdN),
    ("D_2", D_2),
    ("they_Pron", they_Pron),
    ("AdAdv", AdAdv),
    ("above_Prep", above_Prep),
    ("UttCN", UttCN),
    ("pot31", pot31),
    ("ComplVQ", ComplVQ),
    ("no_Quant", no_Quant),
    ("if_then_Conj", if_then_Conj),
    ("dn1000000a", dn1000000a),
    ("ExistIP", ExistIP),
    ("num2digits", num2digits),
    ("UttCard", UttCard),
    ("IdetCN", IdetCN),
    ("AdVVP", AdVVP),
    ("more_CAdv", more_CAdv),
    ("how_IAdv", how_IAdv),
  ]

def sig : GrammarSig where
  grammar := "Grammar"
  startCats := #["S"]
  sourceHash := "7238564362398693196"
  funs := Std.HashMap.ofList funsList

end Algorithms.GF.Generated.ProjectCoreSig
