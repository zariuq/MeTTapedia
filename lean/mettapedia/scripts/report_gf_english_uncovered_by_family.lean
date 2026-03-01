import Mettapedia.Languages.GF.Abstract
import Mettapedia.Languages.GF.English.Linearization

open Mettapedia.Languages.GF
open Mettapedia.Languages.GF.Abstract
open Mettapedia.Languages.GF.Abstract.FunctionSig
open Mettapedia.Languages.GF.English.Linearization

private def preview (xs : List String) (k : Nat) : String :=
  String.intercalate "," (xs.take k)

private def familyTable : List (String × List FunctionSig) :=
  [ ("core", allCoreFunctions)
  , ("adverb", adverbFunctions)
  , ("tense", tenseFunctions)
  , ("text", textFunctions)
  , ("idiom", idiomFunctions)
  , ("numeral", numeralFunctions)
  , ("structural", structuralFunctions)
  , ("extend", extendFunctions)
  , ("construction", constructionFunctions)
  , ("symbol", symbolFunctions)
  ]

private def uncoveredByFamily (fns : List FunctionSig) : List String :=
  (fns.map (·.name)).filter (fun nm => !(explicitlyHandledFunctionNames.contains nm))


def main : IO Unit := do
  for (family, fns) in familyTable do
    let names := fns.map (·.name)
    let uncovered := uncoveredByFamily fns
    let explicit := names.length - uncovered.length
    IO.println s!"gf_en_linearization.family.{family}.total={names.length}"
    IO.println s!"gf_en_linearization.family.{family}.explicit={explicit}"
    IO.println s!"gf_en_linearization.family.{family}.uncovered={uncovered.length}"
    IO.println s!"gf_en_linearization.family.{family}.preview_uncovered_csv={preview uncovered 60}"
