import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.TransformChain
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.TransformChainTransport

/-! Decode runtime receipts at the family or transport declaration and
materialize the submitted proof. Occurrence and source labels travel
alongside the derivation. -/

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.Logic.MetaInterpretiveLearning.CumulativeTheory
open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
open Mettapedia.Machines.Specialization.RelationComposition (Row Proof)
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

private def stop : String → Option TransformChainTransport.Stop
  | "east" => some .east
  | "hub" => some .hub
  | "west" => some .west
  | _ => none

private def transportPrimitive : String → Option RawProof
  | "rail-proof" => some TransformChainTransport.railProof
  | "ferry-proof" => some TransformChainTransport.ferryProof
  | _ => none

open TransformChainTransport (Stop schema definition journey) in
private def materializeTransport (x y z lp rp : String) : Option Unit := do
  let source ← stop x
  let middle ← stop y
  let target ← stop z
  let row : Row Stop (Proof Stop RawProof) :=
    ⟨source, target, .via middle (.leaf (← transportPrimitive lp)) (.leaf (← transportPrimitive rp))⟩
  let checked ← schema.materialize? definition id journey row
  guard (checkRaw definition (schema.judgment journey source target) checked.erase)

private def checkReceipt (bank : List (List String)) (fields : List String) : Option String := do
  let [r, s, x, y, z, i, j, lp, rp, ls, rs] := fields | none
  match r, s with
  | "mother", "father" =>
    let source ← entity x
    let middle ← entity y
    let target ← entity z
    let left : TransformChain.Premise := ⟨source, middle, ⟨i, ← primitive lp, [ls]⟩⟩
    let right : TransformChain.Premise := ⟨middle, target, ⟨j, ← primitive rp, [rs]⟩⟩
    let term ← MILNativeMaterialization.materialize? FormedQuotationCanary.quotation source target
      (TransformChain.tree left right)
    guard (term == MILNativeMaterialization.Examples.grandparentNative)
  | "rail", "ferry" => materializeTransport x y z lp rp
  | _, _ => none
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
