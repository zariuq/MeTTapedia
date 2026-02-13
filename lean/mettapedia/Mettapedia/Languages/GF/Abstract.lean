/-
# GF Abstract Syntax

Abstract syntax defines the language-independent structure:
- Function signatures (type constructors)
- Tree operations
- Well-formedness conditions

In GF, abstract syntax captures meaning/structure independent of any language.
-/

import Mettapedia.Languages.GF.Core

namespace Mettapedia.Languages.GF.Abstract

open Core

/-! ## Abstract Function Signatures

GF abstract functions are typed constructors that build trees.
For example:
  DetCN : Det → CN → NP      (determiner + common noun → noun phrase)
  UseV : V → VP              (verb → verb phrase)
  PredVP : NP → VP → S       (subject + verb phrase → sentence)
-/

/-- Abstract function signature: name and type -/
structure FunctionSig where
  name : String
  type : Category
  deriving DecidableEq, Repr

namespace FunctionSig

-- Shorthand for building arrow types
private abbrev c := Category.base
private abbrev arr := Category.arrow

/-! ### Noun.gf — Nouns, noun phrases, and determiners (42 functions) -/

-- Noun phrases
def DetCN : FunctionSig :=     ⟨"DetCN",     arr .Det (arr .CN .NP)⟩
def UsePN : FunctionSig :=     ⟨"UsePN",     arr .PN .NP⟩
def UsePron : FunctionSig :=   ⟨"UsePron",   arr .Pron .NP⟩
def PredetNP : FunctionSig :=  ⟨"PredetNP",  arr .Predet (arr .NP .NP)⟩
def PPartNP : FunctionSig :=   ⟨"PPartNP",   arr .NP (arr .V2 .NP)⟩
def AdvNP : FunctionSig :=     ⟨"AdvNP",     arr .NP (arr .Adv .NP)⟩
def ExtAdvNP : FunctionSig :=  ⟨"ExtAdvNP",  arr .NP (arr .Adv .NP)⟩
def RelNP : FunctionSig :=     ⟨"RelNP",     arr .NP (arr .RS .NP)⟩
def DetNP : FunctionSig :=     ⟨"DetNP",     arr .Det .NP⟩

-- Determiners
def DetQuant : FunctionSig :=    ⟨"DetQuant",    arr .Quant (arr .Num .Det)⟩
def DetQuantOrd : FunctionSig := ⟨"DetQuantOrd", arr .Quant (arr .Num (arr .Ord .Det))⟩

-- Number
def NumSg : FunctionSig :=   ⟨"NumSg",   .Num⟩
def NumPl : FunctionSig :=   ⟨"NumPl",   .Num⟩
def NumCard : FunctionSig := ⟨"NumCard", arr .Card .Num⟩

-- Cardinal numbers
def NumDigits : FunctionSig :=  ⟨"NumDigits",  arr .Digits .Card⟩
def NumDecimal : FunctionSig := ⟨"NumDecimal", arr .Decimal .Card⟩
def NumNumeral : FunctionSig := ⟨"NumNumeral", arr .Numeral .Card⟩
def AdNum : FunctionSig :=      ⟨"AdNum",      arr .AdN (arr .Card .Card)⟩

-- Ordinals
def OrdDigits : FunctionSig :=        ⟨"OrdDigits",        arr .Digits .Ord⟩
def OrdNumeral : FunctionSig :=       ⟨"OrdNumeral",       arr .Numeral .Ord⟩
def OrdSuperl : FunctionSig :=        ⟨"OrdSuperl",        arr .A .Ord⟩
def OrdNumeralSuperl : FunctionSig := ⟨"OrdNumeralSuperl", arr .Numeral (arr .A .Ord)⟩

-- Quantifiers
def IndefArt : FunctionSig := ⟨"IndefArt", .Quant⟩
def DefArt : FunctionSig :=   ⟨"DefArt",   .Quant⟩
def MassNP : FunctionSig :=   ⟨"MassNP",   arr .CN .NP⟩
def PossPron : FunctionSig := ⟨"PossPron", arr .Pron .Quant⟩

-- Common nouns
def UseN : FunctionSig :=    ⟨"UseN",    arr .N .CN⟩
def ComplN2 : FunctionSig := ⟨"ComplN2", arr .N2 (arr .NP .CN)⟩
def ComplN3 : FunctionSig := ⟨"ComplN3", arr .N3 (arr .NP .N2)⟩
def UseN2 : FunctionSig :=   ⟨"UseN2",   arr .N2 .CN⟩
def Use2N3 : FunctionSig :=  ⟨"Use2N3",  arr .N3 .N2⟩
def Use3N3 : FunctionSig :=  ⟨"Use3N3",  arr .N3 .N2⟩
def AdjCN : FunctionSig :=   ⟨"AdjCN",   arr .AP (arr .CN .CN)⟩
def RelCN : FunctionSig :=   ⟨"RelCN",   arr .CN (arr .RS .CN)⟩
def AdvCN : FunctionSig :=   ⟨"AdvCN",   arr .CN (arr .Adv .CN)⟩
def SentCN : FunctionSig :=  ⟨"SentCN",  arr .CN (arr .SC .CN)⟩

-- Apposition, possessive, partitive
def ApposCN : FunctionSig :=  ⟨"ApposCN",  arr .CN (arr .NP .CN)⟩
def PossNP : FunctionSig :=   ⟨"PossNP",   arr .CN (arr .NP .CN)⟩
def PartNP : FunctionSig :=   ⟨"PartNP",   arr .CN (arr .NP .CN)⟩
def CountNP : FunctionSig :=  ⟨"CountNP",  arr .Det (arr .NP .NP)⟩
def AdjDAP : FunctionSig :=   ⟨"AdjDAP",   arr .DAP (arr .AP .DAP)⟩
def DetDAP : FunctionSig :=   ⟨"DetDAP",   arr .Det .DAP⟩
def QuantityNP : FunctionSig := ⟨"QuantityNP", arr .Decimal (arr .MU .NP)⟩

/-! ### Verb.gf — Verb phrases (29 functions) -/

-- Complementation
def UseV : FunctionSig :=      ⟨"UseV",      arr .V .VP⟩
def ComplVV : FunctionSig :=   ⟨"ComplVV",   arr .VV (arr .VP .VP)⟩
def ComplVS : FunctionSig :=   ⟨"ComplVS",   arr .VS (arr .S .VP)⟩
def ComplVQ : FunctionSig :=   ⟨"ComplVQ",   arr .VQ (arr .QS .VP)⟩
def ComplVA : FunctionSig :=   ⟨"ComplVA",   arr .VA (arr .AP .VP)⟩
def SlashV2a : FunctionSig :=  ⟨"SlashV2a",  arr .V2 .VPSlash⟩
def Slash2V3 : FunctionSig :=  ⟨"Slash2V3",  arr .V3 (arr .NP .VPSlash)⟩
def Slash3V3 : FunctionSig :=  ⟨"Slash3V3",  arr .V3 (arr .NP .VPSlash)⟩
def SlashV2V : FunctionSig :=  ⟨"SlashV2V",  arr .V2V (arr .VP .VPSlash)⟩
def SlashV2S : FunctionSig :=  ⟨"SlashV2S",  arr .V2S (arr .S .VPSlash)⟩
def SlashV2Q : FunctionSig :=  ⟨"SlashV2Q",  arr .V2Q (arr .QS .VPSlash)⟩
def SlashV2A : FunctionSig :=  ⟨"SlashV2A",  arr .V2A (arr .AP .VPSlash)⟩
def ComplSlash : FunctionSig := ⟨"ComplSlash", arr .VPSlash (arr .NP .VP)⟩
def SlashVV : FunctionSig :=    ⟨"SlashVV",    arr .VV (arr .VPSlash .VPSlash)⟩
def SlashV2VNP : FunctionSig := ⟨"SlashV2VNP", arr .V2V (arr .NP (arr .VPSlash .VPSlash))⟩

-- Reflexive, copula, passive
def ReflVP : FunctionSig :=  ⟨"ReflVP",  arr .VPSlash .VP⟩
def UseComp : FunctionSig := ⟨"UseComp", arr .Comp .VP⟩
def PassV2 : FunctionSig :=  ⟨"PassV2",  arr .V2 .VP⟩

-- Adverbs on VPs
def AdvVP : FunctionSig :=       ⟨"AdvVP",       arr .VP (arr .Adv .VP)⟩
def ExtAdvVP : FunctionSig :=    ⟨"ExtAdvVP",    arr .VP (arr .Adv .VP)⟩
def AdVVP : FunctionSig :=       ⟨"AdVVP",       arr .AdV (arr .VP .VP)⟩
def AdvVPSlash : FunctionSig :=  ⟨"AdvVPSlash",  arr .VPSlash (arr .Adv .VPSlash)⟩
def AdVVPSlash : FunctionSig :=  ⟨"AdVVPSlash",  arr .AdV (arr .VPSlash .VPSlash)⟩
def VPSlashPrep : FunctionSig := ⟨"VPSlashPrep", arr .VP (arr .Prep .VPSlash)⟩

-- Complements to copula
def CompAP : FunctionSig :=  ⟨"CompAP",  arr .AP .Comp⟩
def CompNP : FunctionSig :=  ⟨"CompNP",  arr .NP .Comp⟩
def CompAdv : FunctionSig := ⟨"CompAdv", arr .Adv .Comp⟩
def CompCN : FunctionSig :=  ⟨"CompCN",  arr .CN .Comp⟩

-- Copula alone
def UseCopula : FunctionSig := ⟨"UseCopula", .VP⟩

/-! ### Adjective.gf — Adjectives and adjectival phrases (11 functions) -/

def PositA : FunctionSig :=     ⟨"PositA",     arr .A .AP⟩
def ComparA : FunctionSig :=    ⟨"ComparA",    arr .A (arr .NP .AP)⟩
def ComplA2 : FunctionSig :=    ⟨"ComplA2",    arr .A2 (arr .NP .AP)⟩
def ReflA2 : FunctionSig :=     ⟨"ReflA2",     arr .A2 .AP⟩
def UseA2 : FunctionSig :=      ⟨"UseA2",      arr .A2 .AP⟩
def UseComparA : FunctionSig := ⟨"UseComparA", arr .A .AP⟩
def CAdvAP : FunctionSig :=     ⟨"CAdvAP",     arr .CAdv (arr .AP (arr .NP .AP))⟩
def AdjOrd : FunctionSig :=     ⟨"AdjOrd",     arr .Ord .AP⟩
def SentAP : FunctionSig :=     ⟨"SentAP",     arr .AP (arr .SC .AP)⟩
def AdAP : FunctionSig :=       ⟨"AdAP",       arr .AdA (arr .AP .AP)⟩
def AdvAP : FunctionSig :=      ⟨"AdvAP",      arr .AP (arr .Adv .AP)⟩

/-! ### Sentence.gf — Sentences, clauses, imperatives (19 functions) -/

-- Clauses
def PredVP : FunctionSig :=   ⟨"PredVP",   arr .NP (arr .VP .Cl)⟩
def PredSCVP : FunctionSig := ⟨"PredSCVP", arr .SC (arr .VP .Cl)⟩

-- Slash clauses
def SlashVP : FunctionSig :=  ⟨"SlashVP",  arr .NP (arr .VPSlash .ClSlash)⟩
def AdvSlash : FunctionSig := ⟨"AdvSlash", arr .ClSlash (arr .Adv .ClSlash)⟩
def SlashPrep : FunctionSig := ⟨"SlashPrep", arr .Cl (arr .Prep .ClSlash)⟩
def SlashVS : FunctionSig :=  ⟨"SlashVS",  arr .NP (arr .VS (arr .SSlash .ClSlash))⟩

-- Imperatives
def ImpVP : FunctionSig :=  ⟨"ImpVP",  arr .VP .Imp⟩
def AdvImp : FunctionSig := ⟨"AdvImp", arr .Adv (arr .Imp .Imp)⟩

-- Embedded sentences
def EmbedS : FunctionSig :=  ⟨"EmbedS",  arr .S .SC⟩
def EmbedQS : FunctionSig := ⟨"EmbedQS", arr .QS .SC⟩
def EmbedVP : FunctionSig := ⟨"EmbedVP", arr .VP .SC⟩

-- Sentences (tense/polarity selection)
def UseCl : FunctionSig :=    ⟨"UseCl",    arr .Temp (arr .Pol (arr .Cl .S))⟩
def UseQCl : FunctionSig :=   ⟨"UseQCl",   arr .Temp (arr .Pol (arr .QCl .QS))⟩
def UseRCl : FunctionSig :=   ⟨"UseRCl",   arr .Temp (arr .Pol (arr .RCl .RS))⟩
def UseSlash : FunctionSig := ⟨"UseSlash", arr .Temp (arr .Pol (arr .ClSlash .SSlash))⟩

-- Sentence modifiers
def AdvS : FunctionSig :=    ⟨"AdvS",    arr .Adv (arr .S .S)⟩
def ExtAdvS : FunctionSig := ⟨"ExtAdvS", arr .Adv (arr .S .S)⟩
def SSubjS : FunctionSig :=  ⟨"SSubjS",  arr .S (arr .Subj (arr .S .S))⟩
def RelS : FunctionSig :=    ⟨"RelS",    arr .S (arr .RS .S)⟩

/-! ### Question.gf — Questions and interrogative pronouns (17 functions) -/

def QuestCl : FunctionSig :=    ⟨"QuestCl",    arr .Cl .QCl⟩
def QuestVP : FunctionSig :=    ⟨"QuestVP",    arr .IP (arr .VP .QCl)⟩
def QuestSlash : FunctionSig := ⟨"QuestSlash", arr .IP (arr .ClSlash .QCl)⟩
def QuestIAdv : FunctionSig :=  ⟨"QuestIAdv",  arr .IAdv (arr .Cl .QCl)⟩
def QuestIComp : FunctionSig := ⟨"QuestIComp", arr .IComp (arr .NP .QCl)⟩
def IdetCN : FunctionSig :=    ⟨"IdetCN",    arr .IDet (arr .CN .IP)⟩
def IdetIP : FunctionSig :=    ⟨"IdetIP",    arr .IDet .IP⟩
def AdvIP : FunctionSig :=     ⟨"AdvIP",     arr .IP (arr .Adv .IP)⟩
def IdetQuant : FunctionSig := ⟨"IdetQuant", arr .IQuant (arr .Num .IDet)⟩
def PrepIP : FunctionSig :=    ⟨"PrepIP",    arr .Prep (arr .IP .IAdv)⟩
def AdvIAdv : FunctionSig :=   ⟨"AdvIAdv",   arr .IAdv (arr .Adv .IAdv)⟩
def CompIAdv : FunctionSig :=  ⟨"CompIAdv",  arr .IAdv .IComp⟩
def CompIP : FunctionSig :=    ⟨"CompIP",    arr .IP .IComp⟩

-- Multi-wh questions (Question.gf)
def ComplSlashIP : FunctionSig := ⟨"ComplSlashIP", arr .VPSlash (arr .IP .QVP)⟩
def AdvQVP : FunctionSig :=      ⟨"AdvQVP",      arr .VP (arr .IAdv .QVP)⟩
def AddAdvQVP : FunctionSig :=   ⟨"AddAdvQVP",   arr .QVP (arr .IAdv .QVP)⟩
def QuestQVP : FunctionSig :=    ⟨"QuestQVP",    arr .IP (arr .QVP .QCl)⟩

/-! ### Relative.gf — Relative clauses and pronouns (5 functions) -/

def RelCl_f : FunctionSig :=    ⟨"RelCl",    arr .Cl .RCl⟩
def RelVP : FunctionSig :=      ⟨"RelVP",    arr .RP (arr .VP .RCl)⟩
def RelSlash : FunctionSig :=   ⟨"RelSlash", arr .RP (arr .ClSlash .RCl)⟩
def IdRP : FunctionSig :=       ⟨"IdRP",     .RP⟩
def FunRP : FunctionSig :=      ⟨"FunRP",    arr .Prep (arr .NP (arr .RP .RP))⟩

/-! ### Phrase.gf — Phrases and utterances (19 functions) -/

def PhrUtt : FunctionSig :=    ⟨"PhrUtt",    arr .PConj (arr .Utt (arr .Voc .Phr))⟩
def UttS : FunctionSig :=      ⟨"UttS",      arr .S .Utt⟩
def UttQS : FunctionSig :=     ⟨"UttQS",     arr .QS .Utt⟩
def UttImpSg : FunctionSig :=  ⟨"UttImpSg",  arr .Pol (arr .Imp .Utt)⟩
def UttImpPl : FunctionSig :=  ⟨"UttImpPl",  arr .Pol (arr .Imp .Utt)⟩
def UttImpPol : FunctionSig := ⟨"UttImpPol", arr .Pol (arr .Imp .Utt)⟩
def UttIP : FunctionSig :=     ⟨"UttIP",     arr .IP .Utt⟩
def UttIAdv : FunctionSig :=   ⟨"UttIAdv",   arr .IAdv .Utt⟩
def UttNP : FunctionSig :=     ⟨"UttNP",     arr .NP .Utt⟩
def UttAdv : FunctionSig :=    ⟨"UttAdv",    arr .Adv .Utt⟩
def UttVP : FunctionSig :=     ⟨"UttVP",     arr .VP .Utt⟩
def UttCN : FunctionSig :=     ⟨"UttCN",     arr .CN .Utt⟩
def UttCard : FunctionSig :=   ⟨"UttCard",   arr .Card .Utt⟩
def UttAP : FunctionSig :=     ⟨"UttAP",     arr .AP .Utt⟩
def UttInterj : FunctionSig := ⟨"UttInterj", arr .Interj .Utt⟩
def NoPConj : FunctionSig :=   ⟨"NoPConj",   .PConj⟩
def PConjConj : FunctionSig := ⟨"PConjConj", arr .Conj .PConj⟩
def NoVoc : FunctionSig :=     ⟨"NoVoc",     .Voc⟩
def VocNP : FunctionSig :=     ⟨"VocNP",     arr .NP .Voc⟩

/-! ### Conjunction.gf — Coordination (9 + 18 list constructors = 27 functions) -/

-- Coordination rules
def ConjS : FunctionSig :=    ⟨"ConjS",    arr .Conj (arr .ListS .S)⟩
def ConjRS : FunctionSig :=   ⟨"ConjRS",   arr .Conj (arr .ListRS .RS)⟩
def ConjAP : FunctionSig :=   ⟨"ConjAP",   arr .Conj (arr .ListAP .AP)⟩
def ConjNP : FunctionSig :=   ⟨"ConjNP",   arr .Conj (arr .ListNP .NP)⟩
def ConjAdv : FunctionSig :=  ⟨"ConjAdv",  arr .Conj (arr .ListAdv .Adv)⟩
def ConjAdV : FunctionSig :=  ⟨"ConjAdV",  arr .Conj (arr .ListAdV .AdV)⟩
def ConjIAdv : FunctionSig := ⟨"ConjIAdv", arr .Conj (arr .ListIAdv .IAdv)⟩
def ConjCN : FunctionSig :=   ⟨"ConjCN",   arr .Conj (arr .ListCN .CN)⟩
def ConjDet : FunctionSig :=  ⟨"ConjDet",  arr .Conj (arr .ListDAP .Det)⟩

-- List constructors: BaseC : C → C → ListC, ConsC : C → ListC → ListC
def BaseS : FunctionSig :=    ⟨"BaseS",    arr .S (arr .S .ListS)⟩
def ConsS : FunctionSig :=    ⟨"ConsS",    arr .S (arr .ListS .ListS)⟩
def BaseRS : FunctionSig :=   ⟨"BaseRS",   arr .RS (arr .RS .ListRS)⟩
def ConsRS : FunctionSig :=   ⟨"ConsRS",   arr .RS (arr .ListRS .ListRS)⟩
def BaseAP : FunctionSig :=   ⟨"BaseAP",   arr .AP (arr .AP .ListAP)⟩
def ConsAP : FunctionSig :=   ⟨"ConsAP",   arr .AP (arr .ListAP .ListAP)⟩
def BaseNP : FunctionSig :=   ⟨"BaseNP",   arr .NP (arr .NP .ListNP)⟩
def ConsNP : FunctionSig :=   ⟨"ConsNP",   arr .NP (arr .ListNP .ListNP)⟩
def BaseAdv : FunctionSig :=  ⟨"BaseAdv",  arr .Adv (arr .Adv .ListAdv)⟩
def ConsAdv : FunctionSig :=  ⟨"ConsAdv",  arr .Adv (arr .ListAdv .ListAdv)⟩
def BaseAdV : FunctionSig :=  ⟨"BaseAdV",  arr .AdV (arr .AdV .ListAdV)⟩
def ConsAdV : FunctionSig :=  ⟨"ConsAdV",  arr .AdV (arr .ListAdV .ListAdV)⟩
def BaseIAdv : FunctionSig := ⟨"BaseIAdv", arr .IAdv (arr .IAdv .ListIAdv)⟩
def ConsIAdv : FunctionSig := ⟨"ConsIAdv", arr .IAdv (arr .ListIAdv .ListIAdv)⟩
def BaseCN : FunctionSig :=   ⟨"BaseCN",   arr .CN (arr .CN .ListCN)⟩
def ConsCN : FunctionSig :=   ⟨"ConsCN",   arr .CN (arr .ListCN .ListCN)⟩
def BaseDAP : FunctionSig :=  ⟨"BaseDAP",  arr .DAP (arr .DAP .ListDAP)⟩
def ConsDAP : FunctionSig :=  ⟨"ConsDAP",  arr .DAP (arr .ListDAP .ListDAP)⟩

/-! ### All core grammar functions -/

/-- All 170 core grammar FunctionSigs from the GF RGL
    (Noun + Verb + Adjective + Sentence + Question + Relative + Phrase + Conjunction). -/
def allCoreFunctions : List FunctionSig :=
  -- Noun (42)
  [ DetCN, UsePN, UsePron, PredetNP, PPartNP, AdvNP, ExtAdvNP, RelNP, DetNP
  , DetQuant, DetQuantOrd, NumSg, NumPl, NumCard
  , NumDigits, NumDecimal, NumNumeral, AdNum
  , OrdDigits, OrdNumeral, OrdSuperl, OrdNumeralSuperl
  , IndefArt, DefArt, MassNP, PossPron
  , UseN, ComplN2, ComplN3, UseN2, Use2N3, Use3N3
  , AdjCN, RelCN, AdvCN, SentCN, ApposCN, PossNP, PartNP, CountNP
  , AdjDAP, DetDAP, QuantityNP
  -- Verb (29)
  , UseV, ComplVV, ComplVS, ComplVQ, ComplVA
  , SlashV2a, Slash2V3, Slash3V3, SlashV2V, SlashV2S, SlashV2Q, SlashV2A
  , ComplSlash, SlashVV, SlashV2VNP
  , ReflVP, UseComp, PassV2
  , AdvVP, ExtAdvVP, AdVVP, AdvVPSlash, AdVVPSlash, VPSlashPrep
  , CompAP, CompNP, CompAdv, CompCN, UseCopula
  -- Adjective (11)
  , PositA, ComparA, ComplA2, ReflA2, UseA2, UseComparA
  , CAdvAP, AdjOrd, SentAP, AdAP, AdvAP
  -- Sentence (19)
  , PredVP, PredSCVP, SlashVP, AdvSlash, SlashPrep, SlashVS
  , ImpVP, AdvImp, EmbedS, EmbedQS, EmbedVP
  , UseCl, UseQCl, UseRCl, UseSlash, AdvS, ExtAdvS, SSubjS, RelS
  -- Question (17)
  , QuestCl, QuestVP, QuestSlash, QuestIAdv, QuestIComp
  , IdetCN, IdetIP, AdvIP, IdetQuant, PrepIP, AdvIAdv, CompIAdv, CompIP
  , ComplSlashIP, AdvQVP, AddAdvQVP, QuestQVP
  -- Relative (5)
  , RelCl_f, RelVP, RelSlash, IdRP, FunRP
  -- Phrase (19)
  , PhrUtt, UttS, UttQS, UttImpSg, UttImpPl, UttImpPol
  , UttIP, UttIAdv, UttNP, UttAdv, UttVP, UttCN, UttCard, UttAP, UttInterj
  , NoPConj, PConjConj, NoVoc, VocNP
  -- Conjunction (27)
  , ConjS, ConjRS, ConjAP, ConjNP, ConjAdv, ConjAdV, ConjIAdv, ConjCN, ConjDet
  , BaseS, ConsS, BaseRS, ConsRS, BaseAP, ConsAP, BaseNP, ConsNP
  , BaseAdv, ConsAdv, BaseAdV, ConsAdV, BaseIAdv, ConsIAdv, BaseCN, ConsCN
  , BaseDAP, ConsDAP ]

/-! ### Adverb.gf — Adverbs and adverbial phrases (8 functions) -/

def PositAdvAdj : FunctionSig :=  ⟨"PositAdvAdj",  arr .A .Adv⟩
def PrepNP : FunctionSig :=      ⟨"PrepNP",      arr .Prep (arr .NP .Adv)⟩
def ComparAdvAdj : FunctionSig := ⟨"ComparAdvAdj", arr .CAdv (arr .A (arr .NP .Adv))⟩
def ComparAdvAdjS : FunctionSig := ⟨"ComparAdvAdjS", arr .CAdv (arr .A (arr .S .Adv))⟩
def AdAdv : FunctionSig :=       ⟨"AdAdv",       arr .AdA (arr .Adv .Adv)⟩
def PositAdAAdj : FunctionSig := ⟨"PositAdAAdj", arr .A .AdA⟩
def SubjS : FunctionSig :=       ⟨"SubjS",       arr .Subj (arr .S .Adv)⟩
def AdnCAdv : FunctionSig :=     ⟨"AdnCAdv",     arr .CAdv .AdN⟩

/-- All Adverb module functions. -/
def adverbFunctions : List FunctionSig :=
  [PositAdvAdj, PrepNP, ComparAdvAdj, ComparAdvAdjS, AdAdv, PositAdAAdj, SubjS, AdnCAdv]

/-! ### Tense.gf — Tense, polarity, anteriority (9 functions) -/

def TTAnt : FunctionSig :=  ⟨"TTAnt",  arr .Tense (arr .Ant .Temp)⟩
def PPos : FunctionSig :=   ⟨"PPos",   .Pol⟩
def PNeg : FunctionSig :=   ⟨"PNeg",   .Pol⟩
def TPres : FunctionSig :=  ⟨"TPres",  .Tense⟩
def ASimul : FunctionSig := ⟨"ASimul", .Ant⟩
def TPast : FunctionSig :=  ⟨"TPast",  .Tense⟩
def TFut : FunctionSig :=   ⟨"TFut",   .Tense⟩
def TCond : FunctionSig :=  ⟨"TCond",  .Tense⟩
def AAnter : FunctionSig := ⟨"AAnter", .Ant⟩

/-- All Tense module functions. -/
def tenseFunctions : List FunctionSig :=
  [TTAnt, PPos, PNeg, TPres, ASimul, TPast, TFut, TCond, AAnter]

/-! ### Text.gf — Text building (4 functions) -/

def TEmpty : FunctionSig :=     ⟨"TEmpty",     .Text⟩
def TFullStop : FunctionSig :=  ⟨"TFullStop",  arr .Phr (arr .Text .Text)⟩
def TQuestMark : FunctionSig := ⟨"TQuestMark", arr .Phr (arr .Text .Text)⟩
def TExclMark : FunctionSig :=  ⟨"TExclMark",  arr .Phr (arr .Text .Text)⟩

/-- All Text module functions. -/
def textFunctions : List FunctionSig :=
  [TEmpty, TFullStop, TQuestMark, TExclMark]

/-! ### Idiom.gf — Idiomatic expressions (14 functions) -/

def ImpersCl : FunctionSig :=  ⟨"ImpersCl",  arr .VP .Cl⟩
def GenericCl : FunctionSig := ⟨"GenericCl", arr .VP .Cl⟩
def CleftNP : FunctionSig :=   ⟨"CleftNP",   arr .NP (arr .RS .Cl)⟩
def CleftAdv : FunctionSig :=  ⟨"CleftAdv",  arr .Adv (arr .S .Cl)⟩
def ExistNP : FunctionSig :=   ⟨"ExistNP",   arr .NP .Cl⟩
def ExistIP : FunctionSig :=   ⟨"ExistIP",   arr .IP .QCl⟩
def ExistNPAdv : FunctionSig := ⟨"ExistNPAdv", arr .NP (arr .Adv .Cl)⟩
def ExistIPAdv : FunctionSig := ⟨"ExistIPAdv", arr .IP (arr .Adv .QCl)⟩
def ProgrVP : FunctionSig :=   ⟨"ProgrVP",   arr .VP .VP⟩
def ImpPl1 : FunctionSig :=    ⟨"ImpPl1",    arr .VP .Utt⟩
def ImpP3 : FunctionSig :=     ⟨"ImpP3",     arr .NP (arr .VP .Utt)⟩
def SelfAdvVP : FunctionSig := ⟨"SelfAdvVP", arr .VP .VP⟩
def SelfAdVVP : FunctionSig := ⟨"SelfAdVVP", arr .VP .VP⟩
def SelfNP : FunctionSig :=    ⟨"SelfNP",    arr .NP .NP⟩

/-- All Idiom module functions. -/
def idiomFunctions : List FunctionSig :=
  [ ImpersCl, GenericCl, CleftNP, CleftAdv, ExistNP, ExistIP
  , ExistNPAdv, ExistIPAdv, ProgrVP, ImpPl1, ImpP3
  , SelfAdvVP, SelfAdVVP, SelfNP ]

/-! ### Numeral.gf — Numeral construction (48 data constructors) -/

def num_f : FunctionSig :=    ⟨"num",    arr .Sub1000000 .Numeral⟩
def n2_f : FunctionSig :=     ⟨"n2",     .Digit⟩
def n3_f : FunctionSig :=     ⟨"n3",     .Digit⟩
def n4_f : FunctionSig :=     ⟨"n4",     .Digit⟩
def n5_f : FunctionSig :=     ⟨"n5",     .Digit⟩
def n6_f : FunctionSig :=     ⟨"n6",     .Digit⟩
def n7_f : FunctionSig :=     ⟨"n7",     .Digit⟩
def n8_f : FunctionSig :=     ⟨"n8",     .Digit⟩
def n9_f : FunctionSig :=     ⟨"n9",     .Digit⟩
def pot01 : FunctionSig :=    ⟨"pot01",    .Sub10⟩
def pot0 : FunctionSig :=     ⟨"pot0",     arr .Digit .Sub10⟩
def pot0as1 : FunctionSig :=  ⟨"pot0as1",  arr .Sub10 .Sub100⟩
def pot110 : FunctionSig :=   ⟨"pot110",   .Sub100⟩
def pot111 : FunctionSig :=   ⟨"pot111",   .Sub100⟩
def pot1to19 : FunctionSig := ⟨"pot1to19", arr .Digit .Sub100⟩
def pot1 : FunctionSig :=     ⟨"pot1",     arr .Digit .Sub100⟩
def pot1plus : FunctionSig := ⟨"pot1plus", arr .Digit (arr .Sub10 .Sub100)⟩
def pot1as2 : FunctionSig :=  ⟨"pot1as2",  arr .Sub100 .Sub1000⟩
def pot21 : FunctionSig :=    ⟨"pot21",    .Sub1000⟩
def pot2 : FunctionSig :=     ⟨"pot2",     arr .Sub10 .Sub1000⟩
def pot2plus : FunctionSig := ⟨"pot2plus", arr .Sub10 (arr .Sub100 .Sub1000)⟩
def pot2as3 : FunctionSig :=  ⟨"pot2as3",  arr .Sub1000 .Sub1000000⟩
def pot31 : FunctionSig :=    ⟨"pot31",    .Sub1000000⟩
def pot3 : FunctionSig :=     ⟨"pot3",     arr .Sub1000 .Sub1000000⟩
def pot3plus : FunctionSig := ⟨"pot3plus", arr .Sub1000 (arr .Sub1000 .Sub1000000)⟩
def pot3as4 : FunctionSig :=  ⟨"pot3as4",  arr .Sub1000000 .Sub1000000000⟩
def pot3decimal : FunctionSig := ⟨"pot3decimal", arr .Decimal .Sub1000000⟩
def pot41 : FunctionSig :=    ⟨"pot41",    .Sub1000000000⟩
def pot4 : FunctionSig :=     ⟨"pot4",     arr .Sub1000 .Sub1000000000⟩
def pot4plus : FunctionSig := ⟨"pot4plus", arr .Sub1000 (arr .Sub1000000 .Sub1000000000)⟩
def pot4as5 : FunctionSig :=  ⟨"pot4as5",  arr .Sub1000000000 .Sub1000000000000⟩
def pot4decimal : FunctionSig := ⟨"pot4decimal", arr .Decimal .Sub1000000000⟩
def pot51 : FunctionSig :=    ⟨"pot51",    .Sub1000000000000⟩
def pot5 : FunctionSig :=     ⟨"pot5",     arr .Sub1000 .Sub1000000000000⟩
def pot5plus : FunctionSig := ⟨"pot5plus", arr .Sub1000 (arr .Sub1000000000 .Sub1000000000000)⟩
def pot5decimal : FunctionSig := ⟨"pot5decimal", arr .Decimal .Sub1000000000000⟩
def IDig_f : FunctionSig :=   ⟨"IDig",   arr .Dig .Digits⟩
def IIDig : FunctionSig :=    ⟨"IIDig",  arr .Dig (arr .Digits .Digits)⟩
def D_0 : FunctionSig := ⟨"D_0", .Dig⟩
def D_1 : FunctionSig := ⟨"D_1", .Dig⟩
def D_2 : FunctionSig := ⟨"D_2", .Dig⟩
def D_3 : FunctionSig := ⟨"D_3", .Dig⟩
def D_4 : FunctionSig := ⟨"D_4", .Dig⟩
def D_5 : FunctionSig := ⟨"D_5", .Dig⟩
def D_6 : FunctionSig := ⟨"D_6", .Dig⟩
def D_7 : FunctionSig := ⟨"D_7", .Dig⟩
def D_8 : FunctionSig := ⟨"D_8", .Dig⟩
def D_9 : FunctionSig := ⟨"D_9", .Dig⟩
def PosDecimal : FunctionSig := ⟨"PosDecimal", arr .Digits .Decimal⟩
def NegDecimal : FunctionSig := ⟨"NegDecimal", arr .Digits .Decimal⟩
def IFrac : FunctionSig :=      ⟨"IFrac",      arr .Decimal (arr .Dig .Decimal)⟩

/-- All Numeral module functions. -/
def numeralFunctions : List FunctionSig :=
  [ num_f, n2_f, n3_f, n4_f, n5_f, n6_f, n7_f, n8_f, n9_f
  , pot01, pot0, pot0as1, pot110, pot111, pot1to19, pot1, pot1plus, pot1as2
  , pot21, pot2, pot2plus, pot2as3, pot31, pot3, pot3plus, pot3as4, pot3decimal
  , pot41, pot4, pot4plus, pot4as5, pot4decimal
  , pot51, pot5, pot5plus, pot5decimal
  , IDig_f, IIDig
  , D_0, D_1, D_2, D_3, D_4, D_5, D_6, D_7, D_8, D_9
  , PosDecimal, NegDecimal, IFrac ]

/-! ### Structural.gf — Structural words (101 lexical constants) -/

-- Prepositions
def above_Prep : FunctionSig :=    ⟨"above_Prep", .Prep⟩
def after_Prep : FunctionSig :=    ⟨"after_Prep", .Prep⟩
def before_Prep : FunctionSig :=   ⟨"before_Prep", .Prep⟩
def behind_Prep : FunctionSig :=   ⟨"behind_Prep", .Prep⟩
def between_Prep : FunctionSig :=  ⟨"between_Prep", .Prep⟩
def by8agent_Prep : FunctionSig := ⟨"by8agent_Prep", .Prep⟩
def by8means_Prep : FunctionSig := ⟨"by8means_Prep", .Prep⟩
def during_Prep : FunctionSig :=   ⟨"during_Prep", .Prep⟩
def except_Prep : FunctionSig :=   ⟨"except_Prep", .Prep⟩
def for_Prep : FunctionSig :=      ⟨"for_Prep", .Prep⟩
def from_Prep : FunctionSig :=     ⟨"from_Prep", .Prep⟩
def in8front_Prep : FunctionSig := ⟨"in8front_Prep", .Prep⟩
def in_Prep : FunctionSig :=       ⟨"in_Prep", .Prep⟩
def on_Prep : FunctionSig :=       ⟨"on_Prep", .Prep⟩
def part_Prep : FunctionSig :=     ⟨"part_Prep", .Prep⟩
def possess_Prep : FunctionSig :=  ⟨"possess_Prep", .Prep⟩
def through_Prep : FunctionSig :=  ⟨"through_Prep", .Prep⟩
def to_Prep : FunctionSig :=       ⟨"to_Prep", .Prep⟩
def under_Prep : FunctionSig :=    ⟨"under_Prep", .Prep⟩
def with_Prep : FunctionSig :=     ⟨"with_Prep", .Prep⟩
def without_Prep : FunctionSig :=  ⟨"without_Prep", .Prep⟩

-- Subjunctions
def although_Subj : FunctionSig := ⟨"although_Subj", .Subj⟩
def because_Subj : FunctionSig :=  ⟨"because_Subj", .Subj⟩
def if_Subj : FunctionSig :=       ⟨"if_Subj", .Subj⟩
def that_Subj : FunctionSig :=     ⟨"that_Subj", .Subj⟩
def when_Subj : FunctionSig :=     ⟨"when_Subj", .Subj⟩

-- Conjunctions
def and_Conj : FunctionSig :=          ⟨"and_Conj", .Conj⟩
def both7and_DConj : FunctionSig :=    ⟨"both7and_DConj", .Conj⟩
def either7or_DConj : FunctionSig :=   ⟨"either7or_DConj", .Conj⟩
def if_then_Conj : FunctionSig :=      ⟨"if_then_Conj", .Conj⟩
def or_Conj : FunctionSig :=           ⟨"or_Conj", .Conj⟩

-- Pronouns
def he_Pron : FunctionSig :=      ⟨"he_Pron", .Pron⟩
def i_Pron : FunctionSig :=       ⟨"i_Pron", .Pron⟩
def it_Pron : FunctionSig :=      ⟨"it_Pron", .Pron⟩
def she_Pron : FunctionSig :=     ⟨"she_Pron", .Pron⟩
def they_Pron : FunctionSig :=    ⟨"they_Pron", .Pron⟩
def we_Pron : FunctionSig :=      ⟨"we_Pron", .Pron⟩
def youSg_Pron : FunctionSig :=   ⟨"youSg_Pron", .Pron⟩
def youPl_Pron : FunctionSig :=   ⟨"youPl_Pron", .Pron⟩
def youPol_Pron : FunctionSig :=  ⟨"youPol_Pron", .Pron⟩

-- Determiners
def every_Det : FunctionSig :=  ⟨"every_Det", .Det⟩
def few_Det : FunctionSig :=    ⟨"few_Det", .Det⟩
def many_Det : FunctionSig :=   ⟨"many_Det", .Det⟩
def much_Det : FunctionSig :=   ⟨"much_Det", .Det⟩
def someSg_Det : FunctionSig := ⟨"someSg_Det", .Det⟩
def somePl_Det : FunctionSig := ⟨"somePl_Det", .Det⟩

-- Quantifiers
def no_Quant : FunctionSig :=   ⟨"no_Quant", .Quant⟩
def that_Quant : FunctionSig := ⟨"that_Quant", .Quant⟩
def this_Quant : FunctionSig := ⟨"this_Quant", .Quant⟩

-- Predeterminers
def all_Predet : FunctionSig :=  ⟨"all_Predet", .Predet⟩
def most_Predet : FunctionSig := ⟨"most_Predet", .Predet⟩
def not_Predet : FunctionSig :=  ⟨"not_Predet", .Predet⟩
def only_Predet : FunctionSig := ⟨"only_Predet", .Predet⟩

-- NPs
def everybody_NP : FunctionSig :=  ⟨"everybody_NP", .NP⟩
def everything_NP : FunctionSig := ⟨"everything_NP", .NP⟩
def nobody_NP : FunctionSig :=     ⟨"nobody_NP", .NP⟩
def nothing_NP : FunctionSig :=    ⟨"nothing_NP", .NP⟩
def somebody_NP : FunctionSig :=   ⟨"somebody_NP", .NP⟩
def something_NP : FunctionSig :=  ⟨"something_NP", .NP⟩

-- Adverbs
def everywhere_Adv : FunctionSig := ⟨"everywhere_Adv", .Adv⟩
def here_Adv : FunctionSig :=       ⟨"here_Adv", .Adv⟩
def here7to_Adv : FunctionSig :=    ⟨"here7to_Adv", .Adv⟩
def here7from_Adv : FunctionSig :=  ⟨"here7from_Adv", .Adv⟩
def somewhere_Adv : FunctionSig :=  ⟨"somewhere_Adv", .Adv⟩
def there_Adv : FunctionSig :=      ⟨"there_Adv", .Adv⟩
def there7to_Adv : FunctionSig :=   ⟨"there7to_Adv", .Adv⟩
def there7from_Adv : FunctionSig := ⟨"there7from_Adv", .Adv⟩

-- AdA (adverb modifying adjective)
def almost_AdA : FunctionSig := ⟨"almost_AdA", .AdA⟩
def quite_Adv_f : FunctionSig := ⟨"quite_Adv", .AdA⟩  -- GF: quite_Adv : AdA
def so_AdA : FunctionSig :=     ⟨"so_AdA", .AdA⟩
def too_AdA : FunctionSig :=    ⟨"too_AdA", .AdA⟩
def very_AdA : FunctionSig :=   ⟨"very_AdA", .AdA⟩

-- AdN, AdV
def almost_AdN : FunctionSig :=  ⟨"almost_AdN", .AdN⟩
def at_least_AdN : FunctionSig := ⟨"at_least_AdN", .AdN⟩
def at_most_AdN : FunctionSig :=  ⟨"at_most_AdN", .AdN⟩
def always_AdV : FunctionSig :=   ⟨"always_AdV", .AdV⟩

-- CAdv
def as_CAdv : FunctionSig :=   ⟨"as_CAdv", .CAdv⟩
def less_CAdv : FunctionSig := ⟨"less_CAdv", .CAdv⟩
def more_CAdv : FunctionSig := ⟨"more_CAdv", .CAdv⟩

-- Interrogatives
def how_IAdv : FunctionSig :=       ⟨"how_IAdv", .IAdv⟩
def how8much_IAdv : FunctionSig :=  ⟨"how8much_IAdv", .IAdv⟩
def when_IAdv : FunctionSig :=      ⟨"when_IAdv", .IAdv⟩
def where_IAdv : FunctionSig :=     ⟨"where_IAdv", .IAdv⟩
def why_IAdv : FunctionSig :=       ⟨"why_IAdv", .IAdv⟩
def how8many_IDet : FunctionSig :=  ⟨"how8many_IDet", .IDet⟩
def which_IQuant : FunctionSig :=   ⟨"which_IQuant", .IQuant⟩
def whatPl_IP : FunctionSig :=      ⟨"whatPl_IP", .IP⟩
def whatSg_IP : FunctionSig :=      ⟨"whatSg_IP", .IP⟩
def whoPl_IP : FunctionSig :=       ⟨"whoPl_IP", .IP⟩
def whoSg_IP : FunctionSig :=       ⟨"whoSg_IP", .IP⟩

-- VV
def can8know_VV : FunctionSig := ⟨"can8know_VV", .VV⟩
def can_VV : FunctionSig :=      ⟨"can_VV", .VV⟩
def must_VV : FunctionSig :=     ⟨"must_VV", .VV⟩
def want_VV : FunctionSig :=     ⟨"want_VV", .VV⟩

-- PConj, Utt, Voc, V2
def but_PConj : FunctionSig :=       ⟨"but_PConj", .PConj⟩
def otherwise_PConj : FunctionSig := ⟨"otherwise_PConj", .PConj⟩
def therefore_PConj : FunctionSig := ⟨"therefore_PConj", .PConj⟩
def no_Utt : FunctionSig :=          ⟨"no_Utt", .Utt⟩
def yes_Utt : FunctionSig :=         ⟨"yes_Utt", .Utt⟩
def language_title_Utt : FunctionSig := ⟨"language_title_Utt", .Utt⟩
def please_Voc : FunctionSig :=      ⟨"please_Voc", .Voc⟩
def have_V2 : FunctionSig :=         ⟨"have_V2", .V2⟩

/-- All Structural module functions (101). -/
def structuralFunctions : List FunctionSig :=
  [ above_Prep, after_Prep, before_Prep, behind_Prep, between_Prep
  , by8agent_Prep, by8means_Prep, during_Prep, except_Prep, for_Prep
  , from_Prep, in8front_Prep, in_Prep, on_Prep, part_Prep, possess_Prep
  , through_Prep, to_Prep, under_Prep, with_Prep, without_Prep
  , although_Subj, because_Subj, if_Subj, that_Subj, when_Subj
  , and_Conj, both7and_DConj, either7or_DConj, if_then_Conj, or_Conj
  , he_Pron, i_Pron, it_Pron, she_Pron, they_Pron, we_Pron
  , youSg_Pron, youPl_Pron, youPol_Pron
  , every_Det, few_Det, many_Det, much_Det, someSg_Det, somePl_Det
  , no_Quant, that_Quant, this_Quant
  , all_Predet, most_Predet, not_Predet, only_Predet
  , everybody_NP, everything_NP, nobody_NP, nothing_NP, somebody_NP, something_NP
  , everywhere_Adv, here_Adv, here7to_Adv, here7from_Adv
  , somewhere_Adv, there_Adv, there7to_Adv, there7from_Adv
  , almost_AdA, quite_Adv_f, so_AdA, too_AdA, very_AdA
  , almost_AdN, at_least_AdN, at_most_AdN, always_AdV
  , as_CAdv, less_CAdv, more_CAdv
  , how_IAdv, how8much_IAdv, when_IAdv, where_IAdv, why_IAdv
  , how8many_IDet, which_IQuant
  , whatPl_IP, whatSg_IP, whoPl_IP, whoSg_IP
  , can8know_VV, can_VV, must_VV, want_VV
  , but_PConj, otherwise_PConj, therefore_PConj
  , no_Utt, yes_Utt, language_title_Utt, please_Voc, have_V2 ]

/-! ### Extend.gf — Extended syntax (126 functions) -/

-- Genitives
def GenNP : FunctionSig :=    ⟨"GenNP",    arr .NP .Quant⟩
def GenIP : FunctionSig :=    ⟨"GenIP",    arr .IP .IQuant⟩
def GenRP : FunctionSig :=    ⟨"GenRP",    arr .Num (arr .CN .RP)⟩
def GenModNP : FunctionSig := ⟨"GenModNP", arr .Num (arr .NP (arr .CN .NP))⟩
def GenModIP : FunctionSig := ⟨"GenModIP", arr .Num (arr .IP (arr .CN .IP))⟩
def CompBareCN : FunctionSig := ⟨"CompBareCN", arr .CN .Comp⟩

-- Pied-piping and stranding
def PiedPipingQuestSlash : FunctionSig := ⟨"PiedPipingQuestSlash", arr .IP (arr .ClSlash .QCl)⟩
def PiedPipingRelSlash : FunctionSig :=   ⟨"PiedPipingRelSlash", arr .RP (arr .ClSlash .RCl)⟩
def StrandQuestSlash : FunctionSig :=     ⟨"StrandQuestSlash", arr .IP (arr .ClSlash .QCl)⟩
def StrandRelSlash : FunctionSig :=       ⟨"StrandRelSlash", arr .RP (arr .ClSlash .RCl)⟩
def EmptyRelSlash : FunctionSig :=        ⟨"EmptyRelSlash", arr .ClSlash .RCl⟩

-- VPS (finite VP conjunction)
def MkVPS : FunctionSig :=   ⟨"MkVPS",   arr .Temp (arr .Pol (arr .VP .VPS))⟩
def ConjVPS : FunctionSig := ⟨"ConjVPS", arr .Conj (arr .ListVPS .VPS)⟩
def PredVPS : FunctionSig := ⟨"PredVPS", arr .NP (arr .VPS .S)⟩
def SQuestVPS : FunctionSig := ⟨"SQuestVPS", arr .NP (arr .VPS .QS)⟩
def QuestVPS : FunctionSig := ⟨"QuestVPS", arr .IP (arr .VPS .QS)⟩
def RelVPS : FunctionSig :=  ⟨"RelVPS", arr .RP (arr .VPS .RS)⟩
def BaseVPS : FunctionSig := ⟨"BaseVPS", arr .VPS (arr .VPS .ListVPS)⟩
def ConsVPS : FunctionSig := ⟨"ConsVPS", arr .VPS (arr .ListVPS .ListVPS)⟩

-- Existentials
def ExistS : FunctionSig :=     ⟨"ExistS",     arr .Temp (arr .Pol (arr .NP .S))⟩
def ExistNPQS : FunctionSig :=  ⟨"ExistNPQS",  arr .Temp (arr .Pol (arr .NP .QS))⟩
def ExistIPQS : FunctionSig :=  ⟨"ExistIPQS",  arr .Temp (arr .Pol (arr .IP .QS))⟩

-- VPI (infinitive VP conjunction)
def MkVPI : FunctionSig :=      ⟨"MkVPI",      arr .VP .VPI⟩
def ConjVPI : FunctionSig :=    ⟨"ConjVPI",    arr .Conj (arr .ListVPI .VPI)⟩
def ComplVPIVV : FunctionSig := ⟨"ComplVPIVV", arr .VV (arr .VPI .VP)⟩
def BaseVPI : FunctionSig :=    ⟨"BaseVPI", arr .VPI (arr .VPI .ListVPI)⟩
def ConsVPI : FunctionSig :=    ⟨"ConsVPI", arr .VPI (arr .ListVPI .ListVPI)⟩

-- VPS2/VPI2 (binary versions)
def MkVPS2 : FunctionSig :=    ⟨"MkVPS2",    arr .Temp (arr .Pol (arr .VPSlash .VPS2))⟩
def ConjVPS2 : FunctionSig :=  ⟨"ConjVPS2",  arr .Conj (arr .ListVPS2 .VPS2)⟩
def ComplVPS2 : FunctionSig := ⟨"ComplVPS2", arr .VPS2 (arr .NP .VPS)⟩
def ReflVPS2 : FunctionSig :=  ⟨"ReflVPS2",  arr .VPS2 (arr .RNP .VPS)⟩
def BaseVPS2 : FunctionSig :=  ⟨"BaseVPS2", arr .VPS2 (arr .VPS2 .ListVPS2)⟩
def ConsVPS2 : FunctionSig :=  ⟨"ConsVPS2", arr .VPS2 (arr .ListVPS2 .ListVPS2)⟩
def MkVPI2 : FunctionSig :=    ⟨"MkVPI2",    arr .VPSlash .VPI2⟩
def ConjVPI2 : FunctionSig :=  ⟨"ConjVPI2",  arr .Conj (arr .ListVPI2 .VPI2)⟩
def ComplVPI2 : FunctionSig := ⟨"ComplVPI2", arr .VPI2 (arr .NP .VPI)⟩
def BaseVPI2 : FunctionSig :=  ⟨"BaseVPI2", arr .VPI2 (arr .VPI2 .ListVPI2)⟩
def ConsVPI2 : FunctionSig :=  ⟨"ConsVPI2", arr .VPI2 (arr .ListVPI2 .ListVPI2)⟩

-- Conjunction of Comp, Imp
def ConjComp : FunctionSig :=  ⟨"ConjComp", arr .Conj (arr .ListComp .Comp)⟩
def BaseComp : FunctionSig :=  ⟨"BaseComp", arr .Comp (arr .Comp .ListComp)⟩
def ConsComp : FunctionSig :=  ⟨"ConsComp", arr .Comp (arr .ListComp .ListComp)⟩
def ConjImp : FunctionSig :=   ⟨"ConjImp",  arr .Conj (arr .ListImp .Imp)⟩
def BaseImp : FunctionSig :=   ⟨"BaseImp",  arr .Imp (arr .Imp .ListImp)⟩
def ConsImp : FunctionSig :=   ⟨"ConsImp",  arr .Imp (arr .ListImp .ListImp)⟩

-- Miscellaneous
def ProDrop : FunctionSig :=     ⟨"ProDrop",     arr .Pron .Pron⟩
def ICompAP : FunctionSig :=    ⟨"ICompAP",    arr .AP .IComp⟩
def IAdvAdv : FunctionSig :=    ⟨"IAdvAdv",    arr .Adv .IAdv⟩
def CompIQuant : FunctionSig := ⟨"CompIQuant", arr .IQuant .IComp⟩
def PrepCN : FunctionSig :=     ⟨"PrepCN",     arr .Prep (arr .CN .Adv)⟩

-- Fronted/focal constructions
def FocusObj : FunctionSig := ⟨"FocusObj", arr .NP (arr .SSlash .Utt)⟩
def FocusAdv : FunctionSig := ⟨"FocusAdv", arr .Adv (arr .S .Utt)⟩
def FocusAdV : FunctionSig := ⟨"FocusAdV", arr .AdV (arr .S .Utt)⟩
def FocusAP : FunctionSig :=  ⟨"FocusAP",  arr .AP (arr .NP .Utt)⟩

-- Participles
def PresPartAP : FunctionSig :=      ⟨"PresPartAP",      arr .VP .AP⟩
def EmbedPresPart : FunctionSig :=   ⟨"EmbedPresPart",   arr .VP .SC⟩
def PastPartAP : FunctionSig :=      ⟨"PastPartAP",      arr .VPSlash .AP⟩
def PastPartAgentAP : FunctionSig := ⟨"PastPartAgentAP", arr .VPSlash (arr .NP .AP)⟩
def PassVPSlash : FunctionSig :=     ⟨"PassVPSlash",     arr .VPSlash .VP⟩
def PassAgentVPSlash : FunctionSig := ⟨"PassAgentVPSlash", arr .VPSlash (arr .NP .VP)⟩
def NominalizeVPSlashNP : FunctionSig := ⟨"NominalizeVPSlashNP", arr .VPSlash (arr .NP .NP)⟩
def ProgrVPSlash : FunctionSig :=    ⟨"ProgrVPSlash", arr .VPSlash .VPSlash⟩
def A2VPSlash : FunctionSig :=       ⟨"A2VPSlash", arr .A2 .VPSlash⟩
def N2VPSlash : FunctionSig :=       ⟨"N2VPSlash", arr .N2 .VPSlash⟩

-- Existentials
def ExistsNP : FunctionSig :=      ⟨"ExistsNP",      arr .NP .Cl⟩
def ExistCN : FunctionSig :=       ⟨"ExistCN",       arr .CN .Cl⟩
def ExistMassCN : FunctionSig :=   ⟨"ExistMassCN",   arr .CN .Cl⟩
def ExistPluralCN : FunctionSig := ⟨"ExistPluralCN", arr .CN .Cl⟩
def AdvIsNP : FunctionSig :=       ⟨"AdvIsNP",       arr .Adv (arr .NP .Cl)⟩
def AdvIsNPAP : FunctionSig :=     ⟨"AdvIsNPAP",     arr .Adv (arr .NP (arr .AP .Cl))⟩
def PurposeVP : FunctionSig :=     ⟨"PurposeVP",     arr .VP .Adv⟩

-- Bare complements
def ComplBareVS : FunctionSig :=  ⟨"ComplBareVS",  arr .VS (arr .S .VP)⟩
def SlashBareV2S : FunctionSig := ⟨"SlashBareV2S", arr .V2S (arr .S .VPSlash)⟩
def ComplDirectVS : FunctionSig := ⟨"ComplDirectVS", arr .VS (arr .Utt .VP)⟩
def ComplDirectVQ : FunctionSig := ⟨"ComplDirectVQ", arr .VQ (arr .Utt .VP)⟩
def FrontComplDirectVS : FunctionSig := ⟨"FrontComplDirectVS", arr .NP (arr .VS (arr .Utt .Cl))⟩
def FrontComplDirectVQ : FunctionSig := ⟨"FrontComplDirectVQ", arr .NP (arr .VQ (arr .Utt .Cl))⟩
def PredAPVP : FunctionSig :=  ⟨"PredAPVP",  arr .AP (arr .VP .Cl)⟩
def AdjAsCN : FunctionSig :=   ⟨"AdjAsCN",   arr .AP .CN⟩
def AdjAsNP : FunctionSig :=   ⟨"AdjAsNP",   arr .AP .NP⟩
def PredIAdvVP : FunctionSig := ⟨"PredIAdvVP", arr .IAdv (arr .VP .QCl)⟩
def EmbedSSlash : FunctionSig := ⟨"EmbedSSlash", arr .SSlash .SC⟩

-- Reflexive NPs
def ReflRNP : FunctionSig :=       ⟨"ReflRNP",       arr .VPSlash (arr .RNP .VP)⟩
def ReflPron : FunctionSig :=      ⟨"ReflPron",      .RNP⟩
def ReflPoss : FunctionSig :=      ⟨"ReflPoss",      arr .Num (arr .CN .RNP)⟩
def PredetRNP : FunctionSig :=     ⟨"PredetRNP",     arr .Predet (arr .RNP .RNP)⟩
def AdvRNP : FunctionSig :=        ⟨"AdvRNP",        arr .NP (arr .Prep (arr .RNP .RNP))⟩
def AdvRVP : FunctionSig :=        ⟨"AdvRVP",        arr .VP (arr .Prep (arr .RNP .VP))⟩
def AdvRAP : FunctionSig :=        ⟨"AdvRAP",        arr .AP (arr .Prep (arr .RNP .AP))⟩
def ReflA2RNP : FunctionSig :=     ⟨"ReflA2RNP",     arr .A2 (arr .RNP .AP)⟩
def PossPronRNP : FunctionSig :=   ⟨"PossPronRNP", arr .Pron (arr .Num (arr .CN (arr .RNP .NP)))⟩
def ConjRNP : FunctionSig :=       ⟨"ConjRNP",       arr .Conj (arr .RNPList .RNP)⟩
def Base_rr_RNP : FunctionSig :=   ⟨"Base_rr_RNP",   arr .RNP (arr .RNP .RNPList)⟩
def Base_nr_RNP : FunctionSig :=   ⟨"Base_nr_RNP",   arr .NP (arr .RNP .RNPList)⟩
def Base_rn_RNP : FunctionSig :=   ⟨"Base_rn_RNP",   arr .RNP (arr .NP .RNPList)⟩
def Cons_rr_RNP : FunctionSig :=   ⟨"Cons_rr_RNP",   arr .RNP (arr .RNPList .RNPList)⟩
def Cons_nr_RNP : FunctionSig :=   ⟨"Cons_nr_RNP",   arr .NP (arr .RNPList .RNPList)⟩
def ReflPossPron : FunctionSig :=  ⟨"ReflPossPron",  .Quant⟩

-- Extensions (from Extensions.gf)
def ComplGenVV : FunctionSig :=  ⟨"ComplGenVV",  arr .VV (arr .Ant (arr .Pol (arr .VP .VP)))⟩
def CompoundN : FunctionSig :=   ⟨"CompoundN",   arr .N (arr .N .N)⟩
def CompoundAP : FunctionSig :=  ⟨"CompoundAP",  arr .N (arr .A .AP)⟩
def GerundCN : FunctionSig :=    ⟨"GerundCN",    arr .VP .CN⟩
def GerundNP : FunctionSig :=    ⟨"GerundNP",    arr .VP .NP⟩
def GerundAdv : FunctionSig :=   ⟨"GerundAdv",   arr .VP .Adv⟩
def WithoutVP : FunctionSig :=   ⟨"WithoutVP",   arr .VP .Adv⟩
def ByVP : FunctionSig :=        ⟨"ByVP",        arr .VP .Adv⟩
def InOrderToVP : FunctionSig := ⟨"InOrderToVP", arr .VP .Adv⟩
def ApposNP : FunctionSig :=     ⟨"ApposNP",     arr .NP (arr .NP .NP)⟩
def AdAdV_f : FunctionSig :=     ⟨"AdAdV",       arr .AdA (arr .AdV .AdV)⟩
def UttAdV_f : FunctionSig :=    ⟨"UttAdV",      arr .AdV .Utt⟩
def PositAdVAdj : FunctionSig := ⟨"PositAdVAdj", arr .A .AdV⟩
def CompS : FunctionSig :=       ⟨"CompS",       arr .S .Comp⟩
def CompQS : FunctionSig :=      ⟨"CompQS",      arr .QS .Comp⟩
def CompVP : FunctionSig :=      ⟨"CompVP",      arr .Ant (arr .Pol (arr .VP .Comp))⟩

-- Language-specific extensions
def UncontractedNeg : FunctionSig :=    ⟨"UncontractedNeg", .Pol⟩
def UttVPShort : FunctionSig :=         ⟨"UttVPShort", arr .VP .Utt⟩
def ComplSlashPartLast : FunctionSig := ⟨"ComplSlashPartLast", arr .VPSlash (arr .NP .VP)⟩
def DetNPMasc : FunctionSig :=          ⟨"DetNPMasc", arr .Det .NP⟩
def DetNPFem : FunctionSig :=           ⟨"DetNPFem",  arr .Det .NP⟩
def UseComp_estar : FunctionSig :=      ⟨"UseComp_estar", arr .Comp .VP⟩
def UseComp_ser : FunctionSig :=        ⟨"UseComp_ser", arr .Comp .VP⟩
def SubjRelNP : FunctionSig :=          ⟨"SubjRelNP", arr .NP (arr .RS .NP)⟩
def iFem_Pron : FunctionSig :=          ⟨"iFem_Pron", .Pron⟩
def youFem_Pron : FunctionSig :=        ⟨"youFem_Pron", .Pron⟩
def weFem_Pron : FunctionSig :=         ⟨"weFem_Pron", .Pron⟩
def youPlFem_Pron : FunctionSig :=      ⟨"youPlFem_Pron", .Pron⟩
def theyFem_Pron : FunctionSig :=       ⟨"theyFem_Pron", .Pron⟩
def theyNeutr_Pron : FunctionSig :=     ⟨"theyNeutr_Pron", .Pron⟩
def youPolFem_Pron : FunctionSig :=     ⟨"youPolFem_Pron", .Pron⟩
def youPolPl_Pron : FunctionSig :=      ⟨"youPolPl_Pron", .Pron⟩
def youPolPlFem_Pron : FunctionSig :=   ⟨"youPolPlFem_Pron", .Pron⟩
def UttAccNP : FunctionSig := ⟨"UttAccNP", arr .NP .Utt⟩
def UttDatNP : FunctionSig := ⟨"UttDatNP", arr .NP .Utt⟩
def UttAccIP : FunctionSig := ⟨"UttAccIP", arr .IP .Utt⟩
def UttDatIP : FunctionSig := ⟨"UttDatIP", arr .IP .Utt⟩
def UseDAP : FunctionSig :=     ⟨"UseDAP",     arr .DAP .NP⟩
def UseDAPMasc : FunctionSig := ⟨"UseDAPMasc", arr .DAP .NP⟩
def UseDAPFem : FunctionSig :=  ⟨"UseDAPFem",  arr .DAP .NP⟩
def CardCNCard : FunctionSig := ⟨"CardCNCard", arr .Card (arr .CN .Card)⟩
def TPastSimple : FunctionSig := ⟨"TPastSimple", .Tense⟩
def SubjunctRelCN : FunctionSig := ⟨"SubjunctRelCN", arr .CN (arr .RS .CN)⟩

/-- All Extend module functions. -/
def extendFunctions : List FunctionSig :=
  [ GenNP, GenIP, GenRP, GenModNP, GenModIP, CompBareCN
  , PiedPipingQuestSlash, PiedPipingRelSlash, StrandQuestSlash, StrandRelSlash, EmptyRelSlash
  , MkVPS, ConjVPS, PredVPS, SQuestVPS, QuestVPS, RelVPS, BaseVPS, ConsVPS
  , ExistS, ExistNPQS, ExistIPQS
  , MkVPI, ConjVPI, ComplVPIVV, BaseVPI, ConsVPI
  , MkVPS2, ConjVPS2, ComplVPS2, ReflVPS2, BaseVPS2, ConsVPS2
  , MkVPI2, ConjVPI2, ComplVPI2, BaseVPI2, ConsVPI2
  , ConjComp, BaseComp, ConsComp, ConjImp, BaseImp, ConsImp
  , ProDrop, ICompAP, IAdvAdv, CompIQuant, PrepCN
  , FocusObj, FocusAdv, FocusAdV, FocusAP
  , PresPartAP, EmbedPresPart, PastPartAP, PastPartAgentAP
  , PassVPSlash, PassAgentVPSlash, NominalizeVPSlashNP, ProgrVPSlash
  , A2VPSlash, N2VPSlash
  , ExistsNP, ExistCN, ExistMassCN, ExistPluralCN, AdvIsNP, AdvIsNPAP, PurposeVP
  , ComplBareVS, SlashBareV2S, ComplDirectVS, ComplDirectVQ
  , FrontComplDirectVS, FrontComplDirectVQ, PredAPVP, AdjAsCN, AdjAsNP
  , PredIAdvVP, EmbedSSlash
  , ReflRNP, ReflPron, ReflPoss, PredetRNP, AdvRNP, AdvRVP, AdvRAP
  , ReflA2RNP, PossPronRNP, ConjRNP
  , Base_rr_RNP, Base_nr_RNP, Base_rn_RNP, Cons_rr_RNP, Cons_nr_RNP
  , ReflPossPron, ComplGenVV, CompoundN, CompoundAP
  , GerundCN, GerundNP, GerundAdv, WithoutVP, ByVP, InOrderToVP
  , ApposNP, AdAdV_f, UttAdV_f, PositAdVAdj, CompS, CompQS, CompVP
  , UncontractedNeg, UttVPShort, ComplSlashPartLast
  , DetNPMasc, DetNPFem, UseComp_estar, UseComp_ser, SubjRelNP
  , iFem_Pron, youFem_Pron, weFem_Pron, youPlFem_Pron
  , theyFem_Pron, theyNeutr_Pron, youPolFem_Pron, youPolPl_Pron, youPolPlFem_Pron
  , UttAccNP, UttDatNP, UttAccIP, UttDatIP
  , UseDAP, UseDAPMasc, UseDAPFem, CardCNCard, TPastSimple, SubjunctRelCN ]

/-! ### Idiom + Construction + Symbol functions -/

-- Construction.gf — Construction grammar
def hungry_VP : FunctionSig :=    ⟨"hungry_VP", .VP⟩
def thirsty_VP : FunctionSig :=   ⟨"thirsty_VP", .VP⟩
def tired_VP : FunctionSig :=     ⟨"tired_VP", .VP⟩
def scared_VP : FunctionSig :=    ⟨"scared_VP", .VP⟩
def ill_VP : FunctionSig :=       ⟨"ill_VP", .VP⟩
def ready_VP : FunctionSig :=     ⟨"ready_VP", .VP⟩
def has_age_VP : FunctionSig :=   ⟨"has_age_VP", arr .Card .VP⟩
def have_name_Cl : FunctionSig := ⟨"have_name_Cl", arr .NP (arr .NP .Cl)⟩
def married_Cl : FunctionSig :=   ⟨"married_Cl", arr .NP (arr .NP .Cl)⟩
def what_name_QCl : FunctionSig := ⟨"what_name_QCl", arr .NP .QCl⟩
def how_old_QCl : FunctionSig :=   ⟨"how_old_QCl", arr .NP .QCl⟩
def how_far_QCl : FunctionSig :=   ⟨"how_far_QCl", arr .NP .QCl⟩
def weather_adjCl : FunctionSig := ⟨"weather_adjCl", arr .AP .Cl⟩
def is_right_VP : FunctionSig :=   ⟨"is_right_VP", .VP⟩
def is_wrong_VP : FunctionSig :=   ⟨"is_wrong_VP", .VP⟩
def n_units_AP : FunctionSig :=    ⟨"n_units_AP", arr .Card (arr .CN (arr .A .AP))⟩
def n_units_of_NP : FunctionSig := ⟨"n_units_of_NP", arr .Card (arr .CN (arr .NP .NP))⟩
def n_unit_CN : FunctionSig :=     ⟨"n_unit_CN", arr .Card (arr .CN (arr .CN .CN))⟩
def bottle_of_CN : FunctionSig :=  ⟨"bottle_of_CN", arr .NP .CN⟩
def cup_of_CN : FunctionSig :=     ⟨"cup_of_CN", arr .NP .CN⟩
def glass_of_CN : FunctionSig :=   ⟨"glass_of_CN", arr .NP .CN⟩
def few_X_short_of_Y : FunctionSig := ⟨"few_X_short_of_Y", arr .NP (arr .CN (arr .CN .S))⟩
def timeunitAdv : FunctionSig :=      ⟨"timeunitAdv", arr .Card (arr .Timeunit .Adv)⟩
def timeunitRange : FunctionSig :=    ⟨"timeunitRange", arr .Card (arr .Card (arr .Timeunit .Adv))⟩
def timeHour : FunctionSig :=         ⟨"timeHour", arr .Hour .Adv⟩
def timeHourMinute : FunctionSig :=   ⟨"timeHourMinute", arr .Hour (arr .Card .Adv)⟩
def weekdayPunctualAdv : FunctionSig := ⟨"weekdayPunctualAdv", arr .Weekday .Adv⟩
def weekdayHabitualAdv : FunctionSig := ⟨"weekdayHabitualAdv", arr .Weekday .Adv⟩
def weekdayLastAdv : FunctionSig :=     ⟨"weekdayLastAdv", arr .Weekday .Adv⟩
def weekdayNextAdv : FunctionSig :=     ⟨"weekdayNextAdv", arr .Weekday .Adv⟩
def monthAdv : FunctionSig :=           ⟨"monthAdv", arr .Month .Adv⟩
def yearAdv : FunctionSig :=            ⟨"yearAdv", arr .Year .Adv⟩
def dayMonthAdv : FunctionSig :=        ⟨"dayMonthAdv", arr .Monthday (arr .Month .Adv)⟩
def monthYearAdv : FunctionSig :=       ⟨"monthYearAdv", arr .Month (arr .Year .Adv)⟩
def dayMonthYearAdv : FunctionSig :=    ⟨"dayMonthYearAdv", arr .Monthday (arr .Month (arr .Year .Adv))⟩
def intYear : FunctionSig :=     ⟨"intYear", arr (c "Int") .Year⟩
def intMonthday : FunctionSig := ⟨"intMonthday", arr (c "Int") .Monthday⟩
def InLanguage : FunctionSig :=  ⟨"InLanguage", arr .Language .Adv⟩
def weekdayN : FunctionSig :=    ⟨"weekdayN",  arr .Weekday .N⟩
def monthN : FunctionSig :=      ⟨"monthN",    arr .Month .N⟩
def weekdayPN : FunctionSig :=   ⟨"weekdayPN", arr .Weekday .PN⟩
def monthPN : FunctionSig :=     ⟨"monthPN",   arr .Month .PN⟩
def languageNP : FunctionSig :=  ⟨"languageNP", arr .Language .NP⟩
def languageCN : FunctionSig :=  ⟨"languageCN", arr .Language .CN⟩

-- Construction: time unit constants
def second_Timeunit : FunctionSig :=  ⟨"second_Timeunit", .Timeunit⟩
def minute_Timeunit : FunctionSig :=  ⟨"minute_Timeunit", .Timeunit⟩
def hour_Timeunit : FunctionSig :=    ⟨"hour_Timeunit", .Timeunit⟩
def day_Timeunit : FunctionSig :=     ⟨"day_Timeunit", .Timeunit⟩
def week_Timeunit : FunctionSig :=    ⟨"week_Timeunit", .Timeunit⟩
def month_Timeunit : FunctionSig :=   ⟨"month_Timeunit", .Timeunit⟩
def year_Timeunit : FunctionSig :=    ⟨"year_Timeunit", .Timeunit⟩

-- Construction: weekdays
def monday_Weekday : FunctionSig :=    ⟨"monday_Weekday", .Weekday⟩
def tuesday_Weekday : FunctionSig :=   ⟨"tuesday_Weekday", .Weekday⟩
def wednesday_Weekday : FunctionSig := ⟨"wednesday_Weekday", .Weekday⟩
def thursday_Weekday : FunctionSig :=  ⟨"thursday_Weekday", .Weekday⟩
def friday_Weekday : FunctionSig :=    ⟨"friday_Weekday", .Weekday⟩
def saturday_Weekday : FunctionSig :=  ⟨"saturday_Weekday", .Weekday⟩
def sunday_Weekday : FunctionSig :=    ⟨"sunday_Weekday", .Weekday⟩

-- Construction: months
def january_Month : FunctionSig :=   ⟨"january_Month", .Month⟩
def february_Month : FunctionSig :=  ⟨"february_Month", .Month⟩
def march_Month : FunctionSig :=     ⟨"march_Month", .Month⟩
def april_Month : FunctionSig :=     ⟨"april_Month", .Month⟩
def may_Month : FunctionSig :=       ⟨"may_Month", .Month⟩
def june_Month : FunctionSig :=      ⟨"june_Month", .Month⟩
def july_Month : FunctionSig :=      ⟨"july_Month", .Month⟩
def august_Month : FunctionSig :=    ⟨"august_Month", .Month⟩
def september_Month : FunctionSig := ⟨"september_Month", .Month⟩
def october_Month : FunctionSig :=   ⟨"october_Month", .Month⟩
def november_Month : FunctionSig :=  ⟨"november_Month", .Month⟩
def december_Month : FunctionSig :=  ⟨"december_Month", .Month⟩

-- Construction: hours (1–24)
def oneHour : FunctionSig :=         ⟨"oneHour", .Hour⟩
def twoHour : FunctionSig :=         ⟨"twoHour", .Hour⟩
def threeHour : FunctionSig :=       ⟨"threeHour", .Hour⟩
def fourHour : FunctionSig :=        ⟨"fourHour", .Hour⟩
def fiveHour : FunctionSig :=        ⟨"fiveHour", .Hour⟩
def sixHour : FunctionSig :=         ⟨"sixHour", .Hour⟩
def sevenHour : FunctionSig :=       ⟨"sevenHour", .Hour⟩
def eightHour : FunctionSig :=       ⟨"eightHour", .Hour⟩
def nineHour : FunctionSig :=        ⟨"nineHour", .Hour⟩
def tenHour : FunctionSig :=         ⟨"tenHour", .Hour⟩
def elevenHour : FunctionSig :=      ⟨"elevenHour", .Hour⟩
def twelveHour : FunctionSig :=      ⟨"twelveHour", .Hour⟩
def thirteenHour : FunctionSig :=    ⟨"thirteenHour", .Hour⟩
def fourteenHour : FunctionSig :=    ⟨"fourteenHour", .Hour⟩
def fifteenHour : FunctionSig :=     ⟨"fifteenHour", .Hour⟩
def sixteenHour : FunctionSig :=     ⟨"sixteenHour", .Hour⟩
def seventeenHour : FunctionSig :=   ⟨"seventeenHour", .Hour⟩
def eighteenHour : FunctionSig :=    ⟨"eighteenHour", .Hour⟩
def nineteenHour : FunctionSig :=    ⟨"nineteenHour", .Hour⟩
def twentyHour : FunctionSig :=      ⟨"twentyHour", .Hour⟩
def twentyOneHour : FunctionSig :=   ⟨"twentyOneHour", .Hour⟩
def twentyTwoHour : FunctionSig :=   ⟨"twentyTwoHour", .Hour⟩
def twentyThreeHour : FunctionSig := ⟨"twentyThreeHour", .Hour⟩
def twentyFourHour : FunctionSig :=  ⟨"twentyFourHour", .Hour⟩

-- Construction: languages (34)
def afrikaans_Language : FunctionSig :=  ⟨"afrikaans_Language", .Language⟩
def amharic_Language : FunctionSig :=    ⟨"amharic_Language", .Language⟩
def arabic_Language : FunctionSig :=     ⟨"arabic_Language", .Language⟩
def bulgarian_Language : FunctionSig :=  ⟨"bulgarian_Language", .Language⟩
def catalan_Language : FunctionSig :=    ⟨"catalan_Language", .Language⟩
def chinese_Language : FunctionSig :=    ⟨"chinese_Language", .Language⟩
def danish_Language : FunctionSig :=     ⟨"danish_Language", .Language⟩
def dutch_Language : FunctionSig :=      ⟨"dutch_Language", .Language⟩
def english_Language : FunctionSig :=    ⟨"english_Language", .Language⟩
def estonian_Language : FunctionSig :=   ⟨"estonian_Language", .Language⟩
def finnish_Language : FunctionSig :=    ⟨"finnish_Language", .Language⟩
def french_Language : FunctionSig :=     ⟨"french_Language", .Language⟩
def german_Language : FunctionSig :=     ⟨"german_Language", .Language⟩
def greek_Language : FunctionSig :=      ⟨"greek_Language", .Language⟩
def hebrew_Language : FunctionSig :=     ⟨"hebrew_Language", .Language⟩
def hindi_Language : FunctionSig :=      ⟨"hindi_Language", .Language⟩
def japanese_Language : FunctionSig :=   ⟨"japanese_Language", .Language⟩
def italian_Language : FunctionSig :=    ⟨"italian_Language", .Language⟩
def latin_Language : FunctionSig :=      ⟨"latin_Language", .Language⟩
def latvian_Language : FunctionSig :=    ⟨"latvian_Language", .Language⟩
def maltese_Language : FunctionSig :=    ⟨"maltese_Language", .Language⟩
def nepali_Language : FunctionSig :=     ⟨"nepali_Language", .Language⟩
def norwegian_Language : FunctionSig :=  ⟨"norwegian_Language", .Language⟩
def persian_Language : FunctionSig :=    ⟨"persian_Language", .Language⟩
def polish_Language : FunctionSig :=     ⟨"polish_Language", .Language⟩
def punjabi_Language : FunctionSig :=    ⟨"punjabi_Language", .Language⟩
def romanian_Language : FunctionSig :=   ⟨"romanian_Language", .Language⟩
def russian_Language : FunctionSig :=    ⟨"russian_Language", .Language⟩
def sindhi_Language : FunctionSig :=     ⟨"sindhi_Language", .Language⟩
def spanish_Language : FunctionSig :=    ⟨"spanish_Language", .Language⟩
def swahili_Language : FunctionSig :=    ⟨"swahili_Language", .Language⟩
def swedish_Language : FunctionSig :=    ⟨"swedish_Language", .Language⟩
def thai_Language : FunctionSig :=       ⟨"thai_Language", .Language⟩
def turkish_Language : FunctionSig :=    ⟨"turkish_Language", .Language⟩
def urdu_Language : FunctionSig :=       ⟨"urdu_Language", .Language⟩

/-- All Construction module functions. -/
def constructionFunctions : List FunctionSig :=
  [ hungry_VP, thirsty_VP, tired_VP, scared_VP, ill_VP, ready_VP, has_age_VP
  , have_name_Cl, married_Cl, what_name_QCl, how_old_QCl, how_far_QCl
  , weather_adjCl, is_right_VP, is_wrong_VP
  , n_units_AP, n_units_of_NP, n_unit_CN
  , bottle_of_CN, cup_of_CN, glass_of_CN, few_X_short_of_Y
  , timeunitAdv, timeunitRange, timeHour, timeHourMinute
  , weekdayPunctualAdv, weekdayHabitualAdv, weekdayLastAdv, weekdayNextAdv
  , monthAdv, yearAdv, dayMonthAdv, monthYearAdv, dayMonthYearAdv
  , intYear, intMonthday, InLanguage
  , weekdayN, monthN, weekdayPN, monthPN, languageNP, languageCN
  , second_Timeunit, minute_Timeunit, hour_Timeunit, day_Timeunit
  , week_Timeunit, month_Timeunit, year_Timeunit
  , monday_Weekday, tuesday_Weekday, wednesday_Weekday, thursday_Weekday
  , friday_Weekday, saturday_Weekday, sunday_Weekday
  , january_Month, february_Month, march_Month, april_Month
  , may_Month, june_Month, july_Month, august_Month
  , september_Month, october_Month, november_Month, december_Month
  , oneHour, twoHour, threeHour, fourHour, fiveHour, sixHour
  , sevenHour, eightHour, nineHour, tenHour, elevenHour, twelveHour
  , thirteenHour, fourteenHour, fifteenHour, sixteenHour
  , seventeenHour, eighteenHour, nineteenHour, twentyHour
  , twentyOneHour, twentyTwoHour, twentyThreeHour, twentyFourHour
  , afrikaans_Language, amharic_Language, arabic_Language, bulgarian_Language
  , catalan_Language, chinese_Language, danish_Language, dutch_Language
  , english_Language, estonian_Language, finnish_Language, french_Language
  , german_Language, greek_Language, hebrew_Language, hindi_Language
  , japanese_Language, italian_Language, latin_Language, latvian_Language
  , maltese_Language, nepali_Language, norwegian_Language, persian_Language
  , polish_Language, punjabi_Language, romanian_Language, russian_Language
  , sindhi_Language, spanish_Language, swahili_Language, swedish_Language
  , thai_Language, turkish_Language, urdu_Language ]

-- Symbol.gf — Symbolic expressions
def SymbPN : FunctionSig :=   ⟨"SymbPN",   arr .Symb .PN⟩
def IntPN : FunctionSig :=    ⟨"IntPN",    arr (c "Int") .PN⟩
def FloatPN : FunctionSig :=  ⟨"FloatPN",  arr (c "Float") .PN⟩
def NumPN : FunctionSig :=    ⟨"NumPN",    arr .Card .PN⟩
def CNNumNP : FunctionSig :=  ⟨"CNNumNP",  arr .CN (arr .Card .NP)⟩
def CNSymbNP : FunctionSig := ⟨"CNSymbNP", arr .Det (arr .CN (arr .ListSymb .NP))⟩
def SymbS : FunctionSig :=    ⟨"SymbS",    arr .Symb .S⟩
def SymbNum : FunctionSig :=  ⟨"SymbNum",  arr .Symb .Card⟩
def SymbOrd : FunctionSig :=  ⟨"SymbOrd",  arr .Symb .Ord⟩
def MkSymb : FunctionSig :=   ⟨"MkSymb",   arr (c "String") .Symb⟩
def CNIntNP : FunctionSig :=  ⟨"CNIntNP",  arr .CN (arr (c "Int") .NP)⟩
def BaseSymb : FunctionSig := ⟨"BaseSymb", arr .Symb (arr .Symb .ListSymb)⟩
def ConsSymb : FunctionSig := ⟨"ConsSymb", arr .Symb (arr .ListSymb .ListSymb)⟩

/-- All Symbol module functions. -/
def symbolFunctions : List FunctionSig :=
  [ SymbPN, IntPN, FloatPN, NumPN, CNNumNP, CNSymbNP
  , SymbS, SymbNum, SymbOrd, MkSymb, CNIntNP, BaseSymb, ConsSymb ]

/-! ### Lexicon.gf — Basic vocabulary (348 lexical constants) -/

-- Nouns (N)
def airplane_N : FunctionSig := ⟨"airplane_N", .N⟩
def animal_N : FunctionSig :=   ⟨"animal_N", .N⟩
def apartment_N : FunctionSig := ⟨"apartment_N", .N⟩
def apple_N : FunctionSig :=    ⟨"apple_N", .N⟩
def art_N : FunctionSig :=      ⟨"art_N", .N⟩
def ashes_N : FunctionSig :=    ⟨"ashes_N", .N⟩
def baby_N : FunctionSig :=     ⟨"baby_N", .N⟩
def back_N : FunctionSig :=     ⟨"back_N", .N⟩
def bank_N : FunctionSig :=     ⟨"bank_N", .N⟩
def bark_N : FunctionSig :=     ⟨"bark_N", .N⟩
def belly_N : FunctionSig :=    ⟨"belly_N", .N⟩
def bike_N : FunctionSig :=     ⟨"bike_N", .N⟩
def bird_N : FunctionSig :=     ⟨"bird_N", .N⟩
def blood_N : FunctionSig :=    ⟨"blood_N", .N⟩
def boat_N : FunctionSig :=     ⟨"boat_N", .N⟩
def bone_N : FunctionSig :=     ⟨"bone_N", .N⟩
def book_N : FunctionSig :=     ⟨"book_N", .N⟩
def boot_N : FunctionSig :=     ⟨"boot_N", .N⟩
def boss_N : FunctionSig :=     ⟨"boss_N", .N⟩
def boy_N : FunctionSig :=      ⟨"boy_N", .N⟩
def bread_N : FunctionSig :=    ⟨"bread_N", .N⟩
def breast_N : FunctionSig :=   ⟨"breast_N", .N⟩
def butter_N : FunctionSig :=   ⟨"butter_N", .N⟩
def camera_N : FunctionSig :=   ⟨"camera_N", .N⟩
def cap_N : FunctionSig :=      ⟨"cap_N", .N⟩
def car_N : FunctionSig :=      ⟨"car_N", .N⟩
def carpet_N : FunctionSig :=   ⟨"carpet_N", .N⟩
def cat_N : FunctionSig :=      ⟨"cat_N", .N⟩
def ceiling_N : FunctionSig :=  ⟨"ceiling_N", .N⟩
def chair_N : FunctionSig :=    ⟨"chair_N", .N⟩
def cheese_N : FunctionSig :=   ⟨"cheese_N", .N⟩
def child_N : FunctionSig :=    ⟨"child_N", .N⟩
def church_N : FunctionSig :=   ⟨"church_N", .N⟩
def city_N : FunctionSig :=     ⟨"city_N", .N⟩
def cloud_N : FunctionSig :=    ⟨"cloud_N", .N⟩
def coat_N : FunctionSig :=     ⟨"coat_N", .N⟩
def computer_N : FunctionSig := ⟨"computer_N", .N⟩
def country_N : FunctionSig :=  ⟨"country_N", .N⟩
def cousin_N : FunctionSig :=   ⟨"cousin_N", .N⟩
def cow_N : FunctionSig :=      ⟨"cow_N", .N⟩
def day_N : FunctionSig :=      ⟨"day_N", .N⟩
def doctor_N : FunctionSig :=   ⟨"doctor_N", .N⟩
def dog_N : FunctionSig :=      ⟨"dog_N", .N⟩
def door_N : FunctionSig :=     ⟨"door_N", .N⟩
def dust_N : FunctionSig :=     ⟨"dust_N", .N⟩
def ear_N : FunctionSig :=      ⟨"ear_N", .N⟩
def earth_N : FunctionSig :=    ⟨"earth_N", .N⟩
def egg_N : FunctionSig :=      ⟨"egg_N", .N⟩
def enemy_N : FunctionSig :=    ⟨"enemy_N", .N⟩
def eye_N : FunctionSig :=      ⟨"eye_N", .N⟩
def factory_N : FunctionSig :=  ⟨"factory_N", .N⟩
def fat_N : FunctionSig :=      ⟨"fat_N", .N⟩
def feather_N : FunctionSig :=  ⟨"feather_N", .N⟩
def fingernail_N : FunctionSig := ⟨"fingernail_N", .N⟩
def fire_N : FunctionSig :=     ⟨"fire_N", .N⟩
def fish_N : FunctionSig :=     ⟨"fish_N", .N⟩
def floor_N : FunctionSig :=    ⟨"floor_N", .N⟩
def flower_N : FunctionSig :=   ⟨"flower_N", .N⟩
def fog_N : FunctionSig :=      ⟨"fog_N", .N⟩
def foot_N : FunctionSig :=     ⟨"foot_N", .N⟩
def forest_N : FunctionSig :=   ⟨"forest_N", .N⟩
def fridge_N : FunctionSig :=   ⟨"fridge_N", .N⟩
def friend_N : FunctionSig :=   ⟨"friend_N", .N⟩
def fruit_N : FunctionSig :=    ⟨"fruit_N", .N⟩
def garden_N : FunctionSig :=   ⟨"garden_N", .N⟩
def girl_N : FunctionSig :=     ⟨"girl_N", .N⟩
def glove_N : FunctionSig :=    ⟨"glove_N", .N⟩
def gold_N : FunctionSig :=     ⟨"gold_N", .N⟩
def grammar_N : FunctionSig :=  ⟨"grammar_N", .N⟩
def grass_N : FunctionSig :=    ⟨"grass_N", .N⟩
def guts_N : FunctionSig :=     ⟨"guts_N", .N⟩
def hair_N : FunctionSig :=     ⟨"hair_N", .N⟩
def hand_N : FunctionSig :=     ⟨"hand_N", .N⟩
def harbour_N : FunctionSig :=  ⟨"harbour_N", .N⟩
def hat_N : FunctionSig :=      ⟨"hat_N", .N⟩
def head_N : FunctionSig :=     ⟨"head_N", .N⟩
def heart_N : FunctionSig :=    ⟨"heart_N", .N⟩
def hill_N : FunctionSig :=     ⟨"hill_N", .N⟩
def horn_N : FunctionSig :=     ⟨"horn_N", .N⟩
def horse_N : FunctionSig :=    ⟨"horse_N", .N⟩
def house_N : FunctionSig :=    ⟨"house_N", .N⟩
def husband_N : FunctionSig :=  ⟨"husband_N", .N⟩
def ice_N : FunctionSig :=      ⟨"ice_N", .N⟩
def industry_N : FunctionSig := ⟨"industry_N", .N⟩
def iron_N : FunctionSig :=     ⟨"iron_N", .N⟩
def king_N : FunctionSig :=     ⟨"king_N", .N⟩
def knee_N : FunctionSig :=     ⟨"knee_N", .N⟩
def lake_N : FunctionSig :=     ⟨"lake_N", .N⟩
def lamp_N : FunctionSig :=     ⟨"lamp_N", .N⟩
def language_N : FunctionSig := ⟨"language_N", .N⟩
def leaf_N : FunctionSig :=     ⟨"leaf_N", .N⟩
def leather_N : FunctionSig :=  ⟨"leather_N", .N⟩
def leg_N : FunctionSig :=      ⟨"leg_N", .N⟩
def liver_N : FunctionSig :=    ⟨"liver_N", .N⟩
def louse_N : FunctionSig :=    ⟨"louse_N", .N⟩
def love_N : FunctionSig :=     ⟨"love_N", .N⟩
def man_N : FunctionSig :=      ⟨"man_N", .N⟩
def meat_N : FunctionSig :=     ⟨"meat_N", .N⟩
def milk_N : FunctionSig :=     ⟨"milk_N", .N⟩
def moon_N : FunctionSig :=     ⟨"moon_N", .N⟩
def mountain_N : FunctionSig := ⟨"mountain_N", .N⟩
def mouth_N : FunctionSig :=    ⟨"mouth_N", .N⟩
def music_N : FunctionSig :=    ⟨"music_N", .N⟩
def name_N : FunctionSig :=     ⟨"name_N", .N⟩
def neck_N : FunctionSig :=     ⟨"neck_N", .N⟩
def newspaper_N : FunctionSig := ⟨"newspaper_N", .N⟩
def night_N : FunctionSig :=    ⟨"night_N", .N⟩
def nose_N : FunctionSig :=     ⟨"nose_N", .N⟩
def number_N : FunctionSig :=   ⟨"number_N", .N⟩
def oil_N : FunctionSig :=      ⟨"oil_N", .N⟩
def paper_N : FunctionSig :=    ⟨"paper_N", .N⟩
def peace_N : FunctionSig :=    ⟨"peace_N", .N⟩
def pen_N : FunctionSig :=      ⟨"pen_N", .N⟩
def person_N : FunctionSig :=   ⟨"person_N", .N⟩
def planet_N : FunctionSig :=   ⟨"planet_N", .N⟩
def plastic_N : FunctionSig :=  ⟨"plastic_N", .N⟩
def queen_N : FunctionSig :=    ⟨"queen_N", .N⟩
def question_N : FunctionSig := ⟨"question_N", .N⟩
def radio_N : FunctionSig :=    ⟨"radio_N", .N⟩
def rain_N : FunctionSig :=     ⟨"rain_N", .N⟩
def reason_N : FunctionSig :=   ⟨"reason_N", .N⟩
def religion_N : FunctionSig := ⟨"religion_N", .N⟩
def restaurant_N : FunctionSig := ⟨"restaurant_N", .N⟩
def river_N : FunctionSig :=    ⟨"river_N", .N⟩
def road_N : FunctionSig :=     ⟨"road_N", .N⟩
def rock_N : FunctionSig :=     ⟨"rock_N", .N⟩
def roof_N : FunctionSig :=     ⟨"roof_N", .N⟩
def root_N : FunctionSig :=     ⟨"root_N", .N⟩
def rope_N : FunctionSig :=     ⟨"rope_N", .N⟩
def rubber_N : FunctionSig :=   ⟨"rubber_N", .N⟩
def rule_N : FunctionSig :=     ⟨"rule_N", .N⟩
def salt_N : FunctionSig :=     ⟨"salt_N", .N⟩
def sand_N : FunctionSig :=     ⟨"sand_N", .N⟩
def school_N : FunctionSig :=   ⟨"school_N", .N⟩
def science_N : FunctionSig :=  ⟨"science_N", .N⟩
def sea_N : FunctionSig :=      ⟨"sea_N", .N⟩
def seed_N : FunctionSig :=     ⟨"seed_N", .N⟩
def sheep_N : FunctionSig :=    ⟨"sheep_N", .N⟩
def ship_N : FunctionSig :=     ⟨"ship_N", .N⟩
def shirt_N : FunctionSig :=    ⟨"shirt_N", .N⟩
def shoe_N : FunctionSig :=     ⟨"shoe_N", .N⟩
def shop_N : FunctionSig :=     ⟨"shop_N", .N⟩
def silver_N : FunctionSig :=   ⟨"silver_N", .N⟩
def sister_N : FunctionSig :=   ⟨"sister_N", .N⟩
def skin_N : FunctionSig :=     ⟨"skin_N", .N⟩
def sky_N : FunctionSig :=      ⟨"sky_N", .N⟩
def smoke_N : FunctionSig :=    ⟨"smoke_N", .N⟩
def snake_N : FunctionSig :=    ⟨"snake_N", .N⟩
def snow_N : FunctionSig :=     ⟨"snow_N", .N⟩
def sock_N : FunctionSig :=     ⟨"sock_N", .N⟩
def song_N : FunctionSig :=     ⟨"song_N", .N⟩
def star_N : FunctionSig :=     ⟨"star_N", .N⟩
def steel_N : FunctionSig :=    ⟨"steel_N", .N⟩
def stick_N : FunctionSig :=    ⟨"stick_N", .N⟩
def stone_N : FunctionSig :=    ⟨"stone_N", .N⟩
def stove_N : FunctionSig :=    ⟨"stove_N", .N⟩
def student_N : FunctionSig :=  ⟨"student_N", .N⟩
def sun_N : FunctionSig :=      ⟨"sun_N", .N⟩
def table_N : FunctionSig :=    ⟨"table_N", .N⟩
def tail_N : FunctionSig :=     ⟨"tail_N", .N⟩
def teacher_N : FunctionSig :=  ⟨"teacher_N", .N⟩
def television_N : FunctionSig := ⟨"television_N", .N⟩
def tongue_N : FunctionSig :=   ⟨"tongue_N", .N⟩
def tooth_N : FunctionSig :=    ⟨"tooth_N", .N⟩
def train_N : FunctionSig :=    ⟨"train_N", .N⟩
def tree_N : FunctionSig :=     ⟨"tree_N", .N⟩
def university_N : FunctionSig := ⟨"university_N", .N⟩
def village_N : FunctionSig :=  ⟨"village_N", .N⟩
def war_N : FunctionSig :=      ⟨"war_N", .N⟩
def water_N : FunctionSig :=    ⟨"water_N", .N⟩
def wife_N : FunctionSig :=     ⟨"wife_N", .N⟩
def wind_N : FunctionSig :=     ⟨"wind_N", .N⟩
def window_N : FunctionSig :=   ⟨"window_N", .N⟩
def wine_N : FunctionSig :=     ⟨"wine_N", .N⟩
def wing_N : FunctionSig :=     ⟨"wing_N", .N⟩
def woman_N : FunctionSig :=    ⟨"woman_N", .N⟩
def wood_N : FunctionSig :=     ⟨"wood_N", .N⟩
def worm_N : FunctionSig :=     ⟨"worm_N", .N⟩
def year_N : FunctionSig :=     ⟨"year_N", .N⟩

-- Relational nouns (N2, N3), proper names (PN)
def brother_N2 : FunctionSig :=  ⟨"brother_N2", .N2⟩
def father_N2 : FunctionSig :=   ⟨"father_N2", .N2⟩
def mother_N2 : FunctionSig :=   ⟨"mother_N2", .N2⟩
def distance_N3 : FunctionSig := ⟨"distance_N3", .N3⟩
def john_PN : FunctionSig :=     ⟨"john_PN", .PN⟩
def paris_PN : FunctionSig :=    ⟨"paris_PN", .PN⟩

-- Adjectives (A, A2)
def bad_A : FunctionSig :=       ⟨"bad_A", .A⟩
def beautiful_A : FunctionSig := ⟨"beautiful_A", .A⟩
def big_A : FunctionSig :=       ⟨"big_A", .A⟩
def black_A : FunctionSig :=     ⟨"black_A", .A⟩
def blue_A : FunctionSig :=      ⟨"blue_A", .A⟩
def broad_A : FunctionSig :=     ⟨"broad_A", .A⟩
def brown_A : FunctionSig :=     ⟨"brown_A", .A⟩
def clean_A : FunctionSig :=     ⟨"clean_A", .A⟩
def clever_A : FunctionSig :=    ⟨"clever_A", .A⟩
def cold_A : FunctionSig :=      ⟨"cold_A", .A⟩
def correct_A : FunctionSig :=   ⟨"correct_A", .A⟩
def dirty_A : FunctionSig :=     ⟨"dirty_A", .A⟩
def dry_A : FunctionSig :=       ⟨"dry_A", .A⟩
def dull_A : FunctionSig :=      ⟨"dull_A", .A⟩
def empty_A : FunctionSig :=     ⟨"empty_A", .A⟩
def full_A : FunctionSig :=      ⟨"full_A", .A⟩
def fun_AV : FunctionSig :=      ⟨"fun_AV", .A⟩
def good_A : FunctionSig :=      ⟨"good_A", .A⟩
def green_A : FunctionSig :=     ⟨"green_A", .A⟩
def heavy_A : FunctionSig :=     ⟨"heavy_A", .A⟩
def hot_A : FunctionSig :=       ⟨"hot_A", .A⟩
def important_A : FunctionSig := ⟨"important_A", .A⟩
def long_A : FunctionSig :=      ⟨"long_A", .A⟩
def narrow_A : FunctionSig :=    ⟨"narrow_A", .A⟩
def near_A : FunctionSig :=      ⟨"near_A", .A⟩
def new_A : FunctionSig :=       ⟨"new_A", .A⟩
def old_A : FunctionSig :=       ⟨"old_A", .A⟩
def ready_A : FunctionSig :=     ⟨"ready_A", .A⟩
def red_A : FunctionSig :=       ⟨"red_A", .A⟩
def rotten_A : FunctionSig :=    ⟨"rotten_A", .A⟩
def round_A : FunctionSig :=     ⟨"round_A", .A⟩
def sharp_A : FunctionSig :=     ⟨"sharp_A", .A⟩
def short_A : FunctionSig :=     ⟨"short_A", .A⟩
def small_A : FunctionSig :=     ⟨"small_A", .A⟩
def smooth_A : FunctionSig :=    ⟨"smooth_A", .A⟩
def straight_A : FunctionSig :=  ⟨"straight_A", .A⟩
def stupid_A : FunctionSig :=    ⟨"stupid_A", .A⟩
def thick_A : FunctionSig :=     ⟨"thick_A", .A⟩
def thin_A : FunctionSig :=      ⟨"thin_A", .A⟩
def ugly_A : FunctionSig :=      ⟨"ugly_A", .A⟩
def uncertain_A : FunctionSig := ⟨"uncertain_A", .A⟩
def warm_A : FunctionSig :=      ⟨"warm_A", .A⟩
def wet_A : FunctionSig :=       ⟨"wet_A", .A⟩
def white_A : FunctionSig :=     ⟨"white_A", .A⟩
def wide_A : FunctionSig :=      ⟨"wide_A", .A⟩
def yellow_A : FunctionSig :=    ⟨"yellow_A", .A⟩
def young_A : FunctionSig :=     ⟨"young_A", .A⟩
def easy_A2V : FunctionSig :=    ⟨"easy_A2V", .A2⟩
def married_A2 : FunctionSig :=  ⟨"married_A2", .A2⟩
def probable_AS : FunctionSig := ⟨"probable_AS", .A⟩

-- Verbs
def become_VA : FunctionSig :=  ⟨"become_VA", .VA⟩
def blow_V : FunctionSig :=     ⟨"blow_V", .V⟩
def breathe_V : FunctionSig :=  ⟨"breathe_V", .V⟩
def burn_V : FunctionSig :=     ⟨"burn_V", .V⟩
def come_V : FunctionSig :=     ⟨"come_V", .V⟩
def die_V : FunctionSig :=      ⟨"die_V", .V⟩
def dig_V : FunctionSig :=      ⟨"dig_V", .V⟩
def fall_V : FunctionSig :=     ⟨"fall_V", .V⟩
def float_V : FunctionSig :=    ⟨"float_V", .V⟩
def flow_V : FunctionSig :=     ⟨"flow_V", .V⟩
def fly_V : FunctionSig :=      ⟨"fly_V", .V⟩
def freeze_V : FunctionSig :=   ⟨"freeze_V", .V⟩
def go_V : FunctionSig :=       ⟨"go_V", .V⟩
def jump_V : FunctionSig :=     ⟨"jump_V", .V⟩
def laugh_V : FunctionSig :=    ⟨"laugh_V", .V⟩
def lie_V : FunctionSig :=      ⟨"lie_V", .V⟩
def live_V : FunctionSig :=     ⟨"live_V", .V⟩
def play_V : FunctionSig :=     ⟨"play_V", .V⟩
def rain_V0 : FunctionSig :=    ⟨"rain_V0", .V⟩
def run_V : FunctionSig :=      ⟨"run_V", .V⟩
def sew_V : FunctionSig :=      ⟨"sew_V", .V⟩
def sing_V : FunctionSig :=     ⟨"sing_V", .V⟩
def sit_V : FunctionSig :=      ⟨"sit_V", .V⟩
def sleep_V : FunctionSig :=    ⟨"sleep_V", .V⟩
def smell_V : FunctionSig :=    ⟨"smell_V", .V⟩
def spit_V : FunctionSig :=     ⟨"spit_V", .V⟩
def stand_V : FunctionSig :=    ⟨"stand_V", .V⟩
def stop_V : FunctionSig :=     ⟨"stop_V", .V⟩
def swell_V : FunctionSig :=    ⟨"swell_V", .V⟩
def swim_V : FunctionSig :=     ⟨"swim_V", .V⟩
def think_V : FunctionSig :=    ⟨"think_V", .V⟩
def travel_V : FunctionSig :=   ⟨"travel_V", .V⟩
def turn_V : FunctionSig :=     ⟨"turn_V", .V⟩
def vomit_V : FunctionSig :=    ⟨"vomit_V", .V⟩
def walk_V : FunctionSig :=     ⟨"walk_V", .V⟩
-- V2
def bite_V2 : FunctionSig :=      ⟨"bite_V2", .V2⟩
def break_V2 : FunctionSig :=     ⟨"break_V2", .V2⟩
def buy_V2 : FunctionSig :=       ⟨"buy_V2", .V2⟩
def close_V2 : FunctionSig :=     ⟨"close_V2", .V2⟩
def count_V2 : FunctionSig :=     ⟨"count_V2", .V2⟩
def cut_V2 : FunctionSig :=       ⟨"cut_V2", .V2⟩
def do_V2 : FunctionSig :=        ⟨"do_V2", .V2⟩
def drink_V2 : FunctionSig :=     ⟨"drink_V2", .V2⟩
def eat_V2 : FunctionSig :=       ⟨"eat_V2", .V2⟩
def fear_V2 : FunctionSig :=      ⟨"fear_V2", .V2⟩
def fight_V2 : FunctionSig :=     ⟨"fight_V2", .V2⟩
def find_V2 : FunctionSig :=      ⟨"find_V2", .V2⟩
def forget_V2 : FunctionSig :=    ⟨"forget_V2", .V2⟩
def hate_V2 : FunctionSig :=      ⟨"hate_V2", .V2⟩
def hear_V2 : FunctionSig :=      ⟨"hear_V2", .V2⟩
def hit_V2 : FunctionSig :=       ⟨"hit_V2", .V2⟩
def hold_V2 : FunctionSig :=      ⟨"hold_V2", .V2⟩
def hunt_V2 : FunctionSig :=      ⟨"hunt_V2", .V2⟩
def kill_V2 : FunctionSig :=      ⟨"kill_V2", .V2⟩
def know_V2 : FunctionSig :=      ⟨"know_V2", .V2⟩
def learn_V2 : FunctionSig :=     ⟨"learn_V2", .V2⟩
def leave_V2 : FunctionSig :=     ⟨"leave_V2", .V2⟩
def like_V2 : FunctionSig :=      ⟨"like_V2", .V2⟩
def listen_V2 : FunctionSig :=    ⟨"listen_V2", .V2⟩
def lose_V2 : FunctionSig :=      ⟨"lose_V2", .V2⟩
def love_V2 : FunctionSig :=      ⟨"love_V2", .V2⟩
def open_V2 : FunctionSig :=      ⟨"open_V2", .V2⟩
def play_V2 : FunctionSig :=      ⟨"play_V2", .V2⟩
def pull_V2 : FunctionSig :=      ⟨"pull_V2", .V2⟩
def push_V2 : FunctionSig :=      ⟨"push_V2", .V2⟩
def put_V2 : FunctionSig :=       ⟨"put_V2", .V2⟩
def read_V2 : FunctionSig :=      ⟨"read_V2", .V2⟩
def rub_V2 : FunctionSig :=       ⟨"rub_V2", .V2⟩
def scratch_V2 : FunctionSig :=   ⟨"scratch_V2", .V2⟩
def see_V2 : FunctionSig :=       ⟨"see_V2", .V2⟩
def seek_V2 : FunctionSig :=      ⟨"seek_V2", .V2⟩
def speak_V2 : FunctionSig :=     ⟨"speak_V2", .V2⟩
def split_V2 : FunctionSig :=     ⟨"split_V2", .V2⟩
def squeeze_V2 : FunctionSig :=   ⟨"squeeze_V2", .V2⟩
def stab_V2 : FunctionSig :=      ⟨"stab_V2", .V2⟩
def suck_V2 : FunctionSig :=      ⟨"suck_V2", .V2⟩
def switch8off_V2 : FunctionSig := ⟨"switch8off_V2", .V2⟩
def switch8on_V2 : FunctionSig :=  ⟨"switch8on_V2", .V2⟩
def teach_V2 : FunctionSig :=     ⟨"teach_V2", .V2⟩
def throw_V2 : FunctionSig :=     ⟨"throw_V2", .V2⟩
def tie_V2 : FunctionSig :=       ⟨"tie_V2", .V2⟩
def understand_V2 : FunctionSig := ⟨"understand_V2", .V2⟩
def wait_V2 : FunctionSig :=      ⟨"wait_V2", .V2⟩
def wash_V2 : FunctionSig :=      ⟨"wash_V2", .V2⟩
def watch_V2 : FunctionSig :=     ⟨"watch_V2", .V2⟩
def win_V2 : FunctionSig :=       ⟨"win_V2", .V2⟩
def wipe_V2 : FunctionSig :=      ⟨"wipe_V2", .V2⟩
def write_V2 : FunctionSig :=     ⟨"write_V2", .V2⟩
-- V3, VS, VQ, V2S, V2Q, V2A, V2V
def add_V3 : FunctionSig :=     ⟨"add_V3", .V3⟩
def give_V3 : FunctionSig :=    ⟨"give_V3", .V3⟩
def sell_V3 : FunctionSig :=    ⟨"sell_V3", .V3⟩
def send_V3 : FunctionSig :=    ⟨"send_V3", .V3⟩
def talk_V3 : FunctionSig :=    ⟨"talk_V3", .V3⟩
def fear_VS : FunctionSig :=    ⟨"fear_VS", .VS⟩
def hope_VS : FunctionSig :=    ⟨"hope_VS", .VS⟩
def know_VS : FunctionSig :=    ⟨"know_VS", .VS⟩
def say_VS : FunctionSig :=     ⟨"say_VS", .VS⟩
def know_VQ : FunctionSig :=    ⟨"know_VQ", .VQ⟩
def wonder_VQ : FunctionSig :=  ⟨"wonder_VQ", .VQ⟩
def answer_V2S : FunctionSig := ⟨"answer_V2S", .V2S⟩
def ask_V2Q : FunctionSig :=    ⟨"ask_V2Q", .V2Q⟩
def paint_V2A : FunctionSig :=  ⟨"paint_V2A", .V2A⟩
def beg_V2V : FunctionSig :=    ⟨"beg_V2V", .V2V⟩
-- Adverbs, ordinals, interjections
def already_Adv : FunctionSig := ⟨"already_Adv", .Adv⟩
def far_Adv : FunctionSig :=     ⟨"far_Adv", .Adv⟩
def now_Adv : FunctionSig :=     ⟨"now_Adv", .Adv⟩
def today_Adv : FunctionSig :=   ⟨"today_Adv", .Adv⟩
def left_Ord : FunctionSig :=    ⟨"left_Ord", .Ord⟩
def right_Ord : FunctionSig :=   ⟨"right_Ord", .Ord⟩
def alas_Interj : FunctionSig := ⟨"alas_Interj", .Interj⟩

/-- All Lexicon module functions (348). -/
def lexiconFunctions : List FunctionSig :=
  -- N (165)
  [ airplane_N, animal_N, apartment_N, apple_N, art_N, ashes_N
  , baby_N, back_N, bank_N, bark_N, belly_N, bike_N, bird_N, blood_N
  , boat_N, bone_N, book_N, boot_N, boss_N, boy_N, bread_N, breast_N
  , butter_N, camera_N, cap_N, car_N, carpet_N, cat_N, ceiling_N, chair_N
  , cheese_N, child_N, church_N, city_N, cloud_N, coat_N, computer_N
  , country_N, cousin_N, cow_N, day_N, doctor_N, dog_N, door_N, dust_N
  , ear_N, earth_N, egg_N, enemy_N, eye_N, factory_N, fat_N, feather_N
  , fingernail_N, fire_N, fish_N, floor_N, flower_N, fog_N, foot_N
  , forest_N, fridge_N, friend_N, fruit_N, garden_N, girl_N, glove_N
  , gold_N, grammar_N, grass_N, guts_N, hair_N, hand_N, harbour_N
  , hat_N, head_N, heart_N, hill_N, horn_N, horse_N, house_N, husband_N
  , ice_N, industry_N, iron_N, king_N, knee_N, lake_N, lamp_N, language_N
  , leaf_N, leather_N, leg_N, liver_N, louse_N, love_N, man_N, meat_N
  , milk_N, moon_N, mountain_N, mouth_N, music_N, name_N, neck_N
  , newspaper_N, night_N, nose_N, number_N, oil_N, paper_N, peace_N
  , pen_N, person_N, planet_N, plastic_N, queen_N, question_N, radio_N
  , rain_N, reason_N, religion_N, restaurant_N, river_N, road_N, rock_N
  , roof_N, root_N, rope_N, rubber_N, rule_N, salt_N, sand_N, school_N
  , science_N, sea_N, seed_N, sheep_N, ship_N, shirt_N, shoe_N, shop_N
  , silver_N, sister_N, skin_N, sky_N, smoke_N, snake_N, snow_N, sock_N
  , song_N, star_N, steel_N, stick_N, stone_N, stove_N, student_N, sun_N
  , table_N, tail_N, teacher_N, television_N, tongue_N, tooth_N, train_N
  , tree_N, university_N, village_N, war_N, water_N, wife_N, wind_N
  , window_N, wine_N, wing_N, woman_N, wood_N, worm_N, year_N
  -- N2, N3, PN
  , brother_N2, father_N2, mother_N2, distance_N3, john_PN, paris_PN
  -- A, A2
  , bad_A, beautiful_A, big_A, black_A, blue_A, broad_A, brown_A
  , clean_A, clever_A, cold_A, correct_A, dirty_A, dry_A, dull_A
  , empty_A, full_A, fun_AV, good_A, green_A, heavy_A, hot_A
  , important_A, long_A, narrow_A, near_A, new_A, old_A, ready_A
  , red_A, rotten_A, round_A, sharp_A, short_A, small_A, smooth_A
  , straight_A, stupid_A, thick_A, thin_A, ugly_A, uncertain_A
  , warm_A, wet_A, white_A, wide_A, yellow_A, young_A
  , easy_A2V, married_A2, probable_AS
  -- V
  , become_VA, blow_V, breathe_V, burn_V, come_V, die_V, dig_V
  , fall_V, float_V, flow_V, fly_V, freeze_V, go_V, jump_V, laugh_V
  , lie_V, live_V, play_V, rain_V0, run_V, sew_V, sing_V, sit_V
  , sleep_V, smell_V, spit_V, stand_V, stop_V, swell_V, swim_V
  , think_V, travel_V, turn_V, vomit_V, walk_V
  -- V2
  , bite_V2, break_V2, buy_V2, close_V2, count_V2, cut_V2, do_V2
  , drink_V2, eat_V2, fear_V2, fight_V2, find_V2, forget_V2, hate_V2
  , hear_V2, hit_V2, hold_V2, hunt_V2, kill_V2, know_V2, learn_V2
  , leave_V2, like_V2, listen_V2, lose_V2, love_V2, open_V2, play_V2
  , pull_V2, push_V2, put_V2, read_V2, rub_V2, scratch_V2, see_V2
  , seek_V2, speak_V2, split_V2, squeeze_V2, stab_V2, suck_V2
  , switch8off_V2, switch8on_V2, teach_V2, throw_V2, tie_V2
  , understand_V2, wait_V2, wash_V2, watch_V2, win_V2, wipe_V2, write_V2
  -- V3, VS, VQ, V2S, V2Q, V2A, V2V
  , add_V3, give_V3, sell_V3, send_V3, talk_V3
  , fear_VS, hope_VS, know_VS, say_VS, know_VQ, wonder_VQ
  , answer_V2S, ask_V2Q, paint_V2A, beg_V2V
  -- Adv, Ord, Interj
  , already_Adv, far_Adv, now_Adv, today_Adv
  , left_Ord, right_Ord, alas_Interj ]

/-! ### Master list: All GF RGL abstract functions -/

/-- All GF RGL abstract functions (core + adverb + tense + text + idiom + numeral +
    structural + extend + construction + symbol + lexicon). -/
def allFunctions : List FunctionSig :=
  allCoreFunctions ++ adverbFunctions ++ tenseFunctions ++ textFunctions ++
  idiomFunctions ++ numeralFunctions ++ structuralFunctions ++
  extendFunctions ++ constructionFunctions ++ symbolFunctions ++ lexiconFunctions

end FunctionSig

/-! ## Abstract Tree Construction

Abstract trees with constructor applications.
For MVP, we use simplified representation.
-/

/-- Abstract tree node with function application -/
inductive AbstractNode where
  | leaf : String → Category → AbstractNode
  | apply : FunctionSig → List AbstractNode → AbstractNode
  deriving Repr

namespace AbstractNode

/-- Extract result category from function type -/
def extractResultCategory : Category → Category
  | Category.base s => Category.base s
  | Category.arrow _ result => extractResultCategory result

/-- Get the category of an abstract node -/
def category : AbstractNode → Category
  | leaf _ cat => cat
  | apply f _ => extractResultCategory f.type

end AbstractNode

/-! ## Well-formedness

Abstract trees must respect type signatures.
-/

/-- Check if arguments match function type -/
def argumentsMatch (funType : Category) (args : List Category) : Bool :=
  match funType, args with
  | Category.base _, [] => true
  | Category.arrow dom rest, arg :: args' =>
      dom == arg && argumentsMatch rest args'
  | _, _ => false

/-- Check if abstract tree is well-formed -/
partial def isWellFormed : AbstractNode → Bool
  | AbstractNode.leaf _ _ => true
  | AbstractNode.apply f args =>
      let argCats := args.map AbstractNode.category
      argumentsMatch f.type argCats &&
      args.all isWellFormed

/-! ## Example Abstract Trees

These demonstrate well-formed abstract syntax trees.
-/

namespace Examples

open AbstractNode FunctionSig

/-- Example: simple noun phrase "the house"
    DetCN the_Det house_CN
-/
def theHouse : AbstractNode :=
  apply DetCN [
    leaf "the_Det" Category.Det,
    leaf "house_CN" Category.CN
  ]

/-- Example: modified noun "big house"
    DetCN the_Det (AdjCN (PositA big_A) house_CN)
-/
def bigHouse : AbstractNode :=
  apply DetCN [
    leaf "the_Det" Category.Det,
    apply AdjCN [
      apply PositA [leaf "big_A" Category.A],
      leaf "house_CN" Category.CN
    ]
  ]

end Examples

/-! ## Node Equivalence

Two abstract nodes are equivalent if they linearize identically for all parameters.
Unlike the old `AbstractEquiv` (which was vacuous), this compares actual tree
structure through a linearization function, making it meaningful.
-/

/-- Linearization function for abstract nodes -/
def NodeLinearize (Params : Type) := AbstractNode → Params → String

/-- Two nodes are equivalent under a linearization if they produce identical output -/
def NodeEquiv {Params : Type} (lin : NodeLinearize Params)
    (n₁ n₂ : AbstractNode) : Prop :=
  ∀ params : Params, lin n₁ params = lin n₂ params

namespace NodeEquiv

theorem refl {Params : Type} (lin : NodeLinearize Params) (n : AbstractNode) :
    NodeEquiv lin n n :=
  fun _ => Eq.refl _

theorem symm {Params : Type} {lin : NodeLinearize Params} {n₁ n₂ : AbstractNode} :
    NodeEquiv lin n₁ n₂ → NodeEquiv lin n₂ n₁ :=
  fun h params => (h params).symm

theorem trans {Params : Type} {lin : NodeLinearize Params} {n₁ n₂ n₃ : AbstractNode} :
    NodeEquiv lin n₁ n₂ → NodeEquiv lin n₂ n₃ → NodeEquiv lin n₁ n₃ :=
  fun h12 h23 params => (h12 params).trans (h23 params)

theorem is_equivalence {Params : Type} (lin : NodeLinearize Params) :
    Equivalence (NodeEquiv lin) :=
  ⟨refl lin, symm, trans⟩

end NodeEquiv

end Mettapedia.Languages.GF.Abstract
