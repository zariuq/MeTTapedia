import Mettapedia.Languages.GF.English.Linearization

namespace Mettapedia.Languages.GF.English.Linearization

open Mettapedia.Languages.GF
open Core Abstract

/-- Function names with explicit typed semantics in `dispatchApply`. -/
def explicitApplyFunctionNames : List String :=
  [ "UseN", "AdNum", "OrdNumeralSuperl", "ComplN2", "ComplN3", "UseN2", "Use2N3", "Use3N3"
  , "SentCN", "ApposCN", "PossNP", "PartNP", "AdjDAP", "DetDAP"
  , "ComplA2", "ReflA2", "UseA2", "UseComparA", "CAdvAP", "AdjOrd", "SentAP", "AdAP", "AdvAP"
  , "PositAdvAdj", "ComparAdvAdj", "ComparAdvAdjS", "AdAdv", "PositAdAAdj", "SubjS", "AdnCAdv"
  , "TEmpty", "TFullStop", "TQuestMark", "TExclMark", "no_Utt", "yes_Utt", "language_title_Utt", "FunRP"
  , "DetCN", "DetQuant", "DetQuantOrd", "PredetNP", "PPartNP", "AdvNP", "ExtAdvNP"
  , "RelNP", "CountNP", "QuantityNP", "MassNP", "UsePron", "UsePN", "AdjCN", "AdvCN"
  , "DefArt", "IndefArt", "DetNP", "NumSg", "NumPl", "NumCard", "NumDigits", "NumDecimal"
  , "NumNumeral", "num", "pot01", "pot0", "pot0as1", "pot110", "pot111", "pot1to19", "pot1"
  , "pot1plus", "pot1as2", "pot21", "pot2", "pot2plus", "pot2as3", "pot31", "pot3", "pot3plus"
  , "pot3as4", "pot3decimal", "pot41", "pot4", "pot4plus", "pot4as5", "pot4decimal", "pot51"
  , "pot5", "pot5plus", "pot5decimal", "IDig", "IIDig", "PosDecimal", "NegDecimal", "IFrac"
  , "OrdDigits", "OrdNumeral", "OrdSuperl", "PossPron"
  , "PositA", "ComparA", "UseV", "ComplVV", "ComplVS", "ComplVQ", "ComplVA", "PassV2"
  , "SlashVV", "SlashV2VNP", "ReflVP", "ExtAdvVP", "AdVVP", "CompNP", "CompAP", "CompAdv", "CompCN"
  , "UseComp", "UseCopula", "SlashV2a", "AdvVPSlash", "AdVVPSlash", "VPSlashPrep"
  , "Slash2V3", "Slash3V3", "SlashV2V", "SlashV2S", "SlashV2Q", "SlashV2A", "ComplSlash", "AdvVP"
  , "ImpersCl", "GenericCl", "CleftNP", "CleftAdv", "ExistNP", "ExistIP", "ExistNPAdv", "ExistIPAdv"
  , "ProgrVP", "ImpPl1", "ImpP3", "SelfAdvVP", "SelfAdVVP", "SelfNP"
  , "PredVP", "PredSCVP", "SlashVP", "AdvSlash", "SlashPrep"
  , "QuestCl", "QuestVP", "QuestSlash", "PiedPipingQuestSlash", "StrandQuestSlash"
  , "QuestIAdv", "QuestIComp", "IdetCN", "IdetIP", "AdvIP", "IdetQuant"
  , "PrepIP", "AdvIAdv", "CompIAdv", "CompIP", "ICompAP", "IAdvAdv", "CompIQuant", "GenIP"
  , "ExistS", "ExistNPQS", "ExistIPQS", "ComplSlashIP", "AdvQVP", "AddAdvQVP", "QuestQVP"
  , "TTAnt", "PPos", "PNeg", "TPres", "TPast", "TFut"
  , "TCond", "ASimul", "AAnter", "ImpVP", "AdvImp", "EmbedS", "EmbedQS", "EmbedVP", "UseSlash", "SlashVS"
  , "AdvS", "ExtAdvS", "RelS", "UseCl", "UseQCl"
  , "IdRP", "RelCl", "RelVP", "RelSlash", "PiedPipingRelSlash", "StrandRelSlash", "EmptyRelSlash"
  , "UseRCl", "RelCN", "GenRP", "PrepNP", "SSubjS"
  , "NoPConj", "PConjConj", "NoVoc", "VocNP", "PhrUtt", "UttS", "UttQS", "UttImpSg", "UttImpPl", "UttImpPol"
  , "UttIP", "UttIAdv", "UttNP", "UttAdv", "UttVP", "UttCN", "UttCard", "UttAP", "UttInterj"
  , "GenNP", "GenModNP", "GenModIP", "CompBareCN", "ProDrop", "PrepCN"
  , "FocusObj", "FocusAdv", "FocusAdV", "FocusAP", "PresPartAP", "EmbedPresPart", "PastPartAP"
  , "PastPartAgentAP", "PassVPSlash", "PassAgentVPSlash", "NominalizeVPSlashNP"
  , "MkVPS", "ConjVPS", "PredVPS", "SQuestVPS", "QuestVPS", "RelVPS", "BaseVPS", "ConsVPS"
  , "MkVPI", "ConjVPI", "ComplVPIVV", "BaseVPI", "ConsVPI"
  , "MkVPS2", "ConjVPS2", "ComplVPS2", "ReflVPS2", "BaseVPS2", "ConsVPS2"
  , "MkVPI2", "ConjVPI2", "ComplVPI2", "BaseVPI2", "ConsVPI2"
  , "ConjComp", "BaseComp", "ConsComp", "ConjImp", "BaseImp", "ConsImp"
  , "MkSymb", "BaseSymb", "ConsSymb", "SymbPN", "IntPN", "FloatPN", "NumPN"
  , "CNNumNP", "CNIntNP", "CNSymbNP", "SymbS", "SymbNum", "SymbOrd"
  , "BaseNP", "ConsNP", "ConjNP", "BaseCN", "ConsCN", "ConjCN", "BaseRS", "ConsRS", "ConjRS"
  , "BaseAdv", "ConsAdv", "ConjAdv", "BaseAdV", "ConsAdV", "ConjAdV"
  , "BaseIAdv", "ConsIAdv", "ConjIAdv", "BaseDAP", "ConsDAP", "ConjDet"
  , "BaseAP", "ConsAP", "ConjAP", "BaseS", "ConsS", "ConjS" ]

/-- Result categories that are typed by `evalLeafValue` (not raw fallback). -/
def typedLeafResultCategories : List Category :=
  [ Category.base "N", Category.base "CN", Category.base "N2", Category.base "N3"
  , Category.base "A", Category.base "A2", Category.base "Predet", Category.base "AdA", Category.base "AdN", Category.base "CAdv"
  , Category.base "V", Category.base "V2"
  , Category.base "VV", Category.base "VS", Category.base "VQ", Category.base "VA"
  , Category.base "V3", Category.base "V2V", Category.base "V2S", Category.base "V2Q", Category.base "V2A"
  , Category.base "Quant", Category.base "Num", Category.base "Card", Category.base "Ord"
  , Category.base "Digit", Category.base "Dig", Category.base "Digits", Category.base "Decimal", Category.base "Numeral"
  , Category.base "Sub10", Category.base "Sub100", Category.base "Sub1000", Category.base "Sub1000000"
  , Category.base "Sub1000000000", Category.base "Sub1000000000000"
  , Category.base "Det", Category.base "DAP", Category.base "Pron", Category.base "NP"
  , Category.base "Adv", Category.base "AdV", Category.base "IAdv"
  , Category.base "Text"
  , Category.base "IP", Category.base "IComp", Category.base "IDet", Category.base "IQuant", Category.base "RP"
  , Category.base "Prep", Category.base "Conj", Category.base "Subj", Category.base "Interj"
  , Category.base "PConj", Category.base "Voc"
  , Category.base "Tense", Category.base "Ant", Category.base "Pol" ]

/-- Zero-arity constructors handled by typed leaf linearization. -/
def typedLeafFunctionNames : List String :=
  FunctionSig.allFunctions.foldl
    (fun acc f =>
      if f.arity = 0 && typedLeafResultCategories.contains (FunctionSig.resultCategory f.type) then
        f.name :: acc
      else
        acc)
    []

/-- Complete typed-handler set: explicit apply handlers + typed leaf handlers. -/
def explicitlyHandledFunctionNames : List String :=
  (explicitApplyFunctionNames ++ typedLeafFunctionNames).eraseDups

/-- Non-lexical GF abstract functions (core grammar constructors only).
Excludes lexicon entries to provide a meaningful grammar-coverage signal. -/
def nonLexicalFunctionNames : List String :=
  ( FunctionSig.allCoreFunctions ++ FunctionSig.adverbFunctions ++ FunctionSig.tenseFunctions
    ++ FunctionSig.textFunctions ++ FunctionSig.idiomFunctions ++ FunctionSig.numeralFunctions
    ++ FunctionSig.structuralFunctions ++ FunctionSig.extendFunctions
    ++ FunctionSig.constructionFunctions ++ FunctionSig.symbolFunctions
  ).map (·.name)

/-- Explicitly handled non-lexical function names. -/
def explicitlyHandledNonLexicalFunctionNames : List String :=
  nonLexicalFunctionNames.filter (fun name => explicitlyHandledFunctionNames.contains name)

/-- Non-lexical function names still without explicit typed handlers. -/
def uncoveredNonLexicalFunctionNames : List String :=
  nonLexicalFunctionNames.filter (fun name => !(explicitlyHandledFunctionNames.contains name))

/-- Number of GF abstract functions with explicit typed handlers. -/
def explicitCoverageCount : Nat :=
  FunctionSig.allFunctions.foldl
    (fun acc f => if explicitlyHandledFunctionNames.contains f.name then acc + 1 else acc)
    0

/-- Number of functions with explicit `dispatchApply` handlers. -/
def explicitApplyCoverageCount : Nat :=
  FunctionSig.allFunctions.foldl
    (fun acc f => if explicitApplyFunctionNames.contains f.name then acc + 1 else acc)
    0

/-- Number of zero-arity functions covered by typed leaf linearization. -/
def typedLeafCoverageCount : Nat :=
  FunctionSig.allFunctions.foldl
    (fun acc f => if typedLeafFunctionNames.contains f.name then acc + 1 else acc)
    0

/-- Number of names that are both explicit apply handlers and typed leaf handlers. -/
def applyLeafOverlapCount : Nat :=
  explicitApplyFunctionNames.foldl
    (fun acc name => if typedLeafFunctionNames.contains name then acc + 1 else acc)
    0

/-- Number of non-lexical GF abstract functions. -/
def nonLexicalFunctionCount : Nat :=
  nonLexicalFunctionNames.length

/-- Number of non-lexical functions with explicit typed handlers. -/
def explicitNonLexicalCoverageCount : Nat :=
  explicitlyHandledNonLexicalFunctionNames.length

/-- Explicit non-lexical semantic coverage ratio in percentage points. -/
def explicitNonLexicalCoveragePercent : Float :=
  if nonLexicalFunctionCount = 0 then 0.0
  else (Float.ofNat explicitNonLexicalCoverageCount / Float.ofNat nonLexicalFunctionCount) * 100.0

/-- Total number of GF abstract functions declared in `Abstract.lean`. -/
def totalFunctionCount : Nat := FunctionSig.allFunctions.length

/-- Explicit semantic coverage ratio in percentage points. -/
def explicitCoveragePercent : Float :=
  if totalFunctionCount = 0 then 0.0
  else (Float.ofNat explicitCoverageCount / Float.ofNat totalFunctionCount) * 100.0

/-- GF abstract function names without explicit typed handlers.
They still linearize through deterministic symbolic fallback. -/
def uncoveredFunctionNames : List String :=
  FunctionSig.allFunctionNames.filter
    (fun name => !(explicitlyHandledFunctionNames.contains name))

end Mettapedia.Languages.GF.English.Linearization
