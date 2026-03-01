import Mettapedia.Languages.GF.Abstract
import Mettapedia.Languages.GF.English.Linearization

open Mettapedia.Languages.GF
open Mettapedia.Languages.GF.Core
open Mettapedia.Languages.GF.Abstract
open Mettapedia.Languages.GF.Abstract.FunctionSig
open Mettapedia.Languages.GF.English.Linearization

private def keyOf (f : FunctionSig) : String :=
  let rc := FunctionSig.resultCategory f.type
  s!"arity={f.arity};result={repr rc}"

private def addCount (m : List (String × Nat)) (k : String) : List (String × Nat) :=
  match m with
  | [] => [(k, 1)]
  | (k0, n0) :: rest =>
    if k = k0 then (k0, n0 + 1) :: rest
    else (k0, n0) :: addCount rest k

private def accumulate (keys : List String) : List (String × Nat) :=
  keys.foldl (fun acc k => addCount acc k) []

def main : IO Unit := do
  let uncovered := FunctionSig.allFunctions.filter (fun f => !(explicitlyHandledFunctionNames.contains f.name))
  let counts := accumulate (uncovered.map keyOf)
  IO.println s!"gf_en_linearization.uncovered_shape_bucket_count={counts.length}"
  IO.println s!"gf_en_linearization.uncovered_total={uncovered.length}"
  for (k, n) in counts.take 40 do
    IO.println s!"gf_en_linearization.uncovered_shape.{k}={n}"
