import Mettapedia.Languages.GF.Abstract
import Mettapedia.Languages.GF.English.Linearization

open Mettapedia.Languages.GF
open Mettapedia.Languages.GF.Abstract
open Mettapedia.Languages.GF.Abstract.FunctionSig
open Mettapedia.Languages.GF.English.Linearization

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

private def shapeKey (f : FunctionSig) : String :=
  s!"arity={f.arity};result={repr (FunctionSig.resultCategory f.type)}"

private def addToBucket (buckets : List (String × List FunctionSig)) (key : String) (f : FunctionSig) : List (String × List FunctionSig) :=
  match buckets with
  | [] => [(key, [f])]
  | (k, fs) :: rest =>
    if k = key then (k, f :: fs) :: rest
    else (k, fs) :: addToBucket rest key f

private def bucketsByShape (fs : List FunctionSig) : List (String × List FunctionSig) :=
  fs.foldl (fun acc f => addToBucket acc (shapeKey f) f) []

private def argPattern (arity : Nat) : String :=
  match arity with
  | 0 => "[]"
  | 1 => "[a1]"
  | 2 => "[a1, a2]"
  | 3 => "[a1, a2, a3]"
  | 4 => "[a1, a2, a3, a4]"
  | _ => "args"

private def emitStubArm (family bucket : String) (f : FunctionSig) : String :=
  let pat := argPattern f.arity
  s!"| \"{f.name}\", {pat} =>\n  -- TODO [{family}] [{bucket}]\n  none\n"

private def emitFamilySection (family : String) (fs : List FunctionSig) : String :=
  let uncovered := fs.filter (fun f => !(explicitlyHandledFunctionNames.contains f.name))
  let buckets := bucketsByShape uncovered
  let header := s!"\n-- ===== FAMILY: {family} =====\n"
  let body :=
    buckets.foldl
      (fun acc (bucket, bfs) =>
        let title := s!"\n-- Bucket {bucket} ({bfs.length} constructors)\n"
        let arms := String.intercalate "" (bfs.reverse.map (emitStubArm family bucket))
        acc ++ title ++ arms)
      ""
  header ++ body

private def emitAll : String :=
  let pre :=
"-- AUTO-GENERATED STUB SKELETONS FOR dispatchApply\n\
-- Source: scripts/generate_gf_english_handler_stubs.lean\n\
-- Paste selected arms into Mettapedia/Languages/GF/English/Linearization.lean\n\
-- and replace `none` with typed semantics.\n"
  pre ++ String.intercalate "" (familyTable.map (fun (fam, fs) => emitFamilySection fam fs))


def main : IO Unit := do
  let out := emitAll
  IO.println out
