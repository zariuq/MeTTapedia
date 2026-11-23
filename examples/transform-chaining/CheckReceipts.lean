import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.TransformChain

/-! Decode runtime receipts for the finite family vocabulary and pass their
actual endpoints and proof trees to the existing MIL materializer. Occurrence
and source labels travel alongside the derivation. -/

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.Logic.MetaInterpretiveLearning.CumulativeTheory
open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
open MILCheckedChain MILCheckedNativePrograms

private def entity : String → Option Pattern
  | "alice" => some alice
  | "bob" => some bob
  | "carol" => some carol
  | _ => none

private def primitive : String → Option RawProof
  | "mother-proof" => some motherProof
  | "father-proof" => some fatherProof
  | _ => none

private def checkReceipt (bank : List (List String)) (fields : List String) : Option String := do
  let [r, s, x, y, z, i, j, lp, rp, ls, rs] := fields | none
  let source ← entity x
  let middle ← entity y
  let target ← entity z
  let left : TransformChain.Premise := ⟨source, middle, ⟨i, ← primitive lp, [ls]⟩⟩
  let right : TransformChain.Premise := ⟨middle, target, ⟨j, ← primitive rp, [rs]⟩⟩
  let term ← MILNativeMaterialization.materialize? FormedQuotationCanary.quotation source target
    (TransformChain.tree left right)
  guard (term == MILNativeMaterialization.Examples.grandparentNative)
  if !(bank.contains [r, x, y, i, lp, ls] && bank.contains [s, y, z, j, rp, rs]) then
    return "invalid-occurrence"
  return String.intercalate " " ["accepted", i, j, ls, rs]

def main : IO Unit := do
  let input ← IO.getStdin
  let mut bank : List (List String) := []
  repeat
    let line ← input.getLine
    if line.isEmpty then break
    match line.trimAscii.toString.splitOn "\t" with
    | "premise" :: fields => bank := fields :: bank
    | "check" :: fields => IO.println ((checkReceipt bank fields).getD "rejected")
    | _ => throw (IO.userError "expected a premise or a check")
