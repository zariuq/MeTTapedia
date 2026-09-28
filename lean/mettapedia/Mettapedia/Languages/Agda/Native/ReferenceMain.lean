import Mettapedia.Languages.Agda.Native.Selection
import Mettapedia.Languages.Agda.Native.ProofCodec
import Mettapedia.OSLF.Syntax.FiniteRuleProofData
import Mettapedia.OSLF.Syntax.BindingWireJson

/-! Untrusted JSON transport for the structural proof-producing reference.
The mathematical soundness boundary is the producer and its returned native
tree. JSON parsing and presentation belong to the external transport layer. -/

set_option autoImplicit false

open Lean
open Mettapedia.OSLF.Binding.WireCodec
open Mettapedia.OSLF.Binding.FiniteRuleSearch
open Mettapedia.Languages.Agda.Structural
open Statics

private def field (request : Json) (name : String) : Except String Json :=
  request.getObjVal? name

private def readInput (request : Json) : Except String AdministrativeStatics.Judgment := do
  let entries ← request.getObj?
  unless entries.toList.all (fun entry => ["profile", "scope", "term", "type"].contains entry.1) do
    throw "unrecognized request metadata"
  let profile ← (← field request "profile").getStr?
  unless profile = "finite-set-relevant-pi-v1" do throw "unsupported profile"
  let scope ← (← field request "scope").getNat?
  unless scope = 0 do throw "this entry point requires a closed input"
  let some term := (Mettapedia.Languages.Agda.Native.Codec.rawTerm 0 .term).ofJson (← field request "term")
    | throw "malformed term scope, sort, operator or arity"
  let some type := (Mettapedia.Languages.Agda.Native.Codec.rawTerm 0 .type).ofJson (← field request "type")
    | throw "malformed type scope, sort, operator or arity"
  return .core (typed .nil term type)

private def nodeCount {j : AdministrativeStatics.Judgment}
    (tree : AdministrativeStatics.Derivation j) : Nat :=
  match tree with
  | .roll _ children => 1 + (List.ofFn (fun p => nodeCount (children p))).sum
termination_by structural tree

private def result (fuel : Nat) (request : Json) : Json :=
  match readInput request with
  | .error reason => Json.mkObj [("status",toJson "OutsideFragment"),("reason",toJson reason)]
  | .ok j => match Mettapedia.Languages.Agda.Native.Production.run fuel j with
    | .established tree => Json.mkObj [("status",toJson "Established"),
        ("proof_nodes",toJson (nodeCount tree)),
        ("proof",Mettapedia.OSLF.Binding.FiniteRuleLabelledProofWire.dataWireCodec.toJson (Mettapedia.Languages.Agda.Native.Codec.encode tree))]
    | .refuted _ => Json.mkObj [("status",toJson "Refuted")]
    | .incomplete => Json.mkObj [("status",toJson "Incomplete"),("rule_depth",toJson fuel),
        ("reason",toJson "candidate selection or depth budget did not produce a proof")]

private def replay (packet : Json) : Json :=
  let checked : Except String Json := do
    let request ← field packet "request"
    let j ← readInput request
    let encoded ← field packet "proof"
    let some wire := Mettapedia.OSLF.Binding.FiniteRuleLabelledProofWire.dataWireCodec.ofJson encoded
      | throw "malformed proof-wire data"
    match Mettapedia.Languages.Agda.Native.Codec.decodeAt j wire with
    | some tree => return Json.mkObj [("status",toJson "Established"),
        ("proof_nodes",toJson (nodeCount tree))]
    | none => return Json.mkObj [("status",toJson "RejectedProof"),
        ("reason",toJson "proof does not reconstruct the requested judgment")]
  match checked with
  | .ok result => result
  | .error reason => Json.mkObj [("status",toJson "RejectedProof"),("reason",toJson reason)]

def Mettapedia.Languages.Agda.Native.referenceMain (arguments : List String) : IO UInt32 := do
  let [mode, input, depth] := arguments
    | throw (IO.userError "expected produce/replay, JSON file, and rule depth")
  unless mode = "produce" || mode = "replay" do throw (IO.userError "unsupported operation")
  let some fuel := depth.toNat? | throw (IO.userError "rule depth must be a natural number")
  let source ← IO.FS.readFile input
  let requests ← IO.ofExcept (Json.parse source >>= Json.getArr?)
  let stdout ← IO.getStdout
  for request in requests do
    stdout.putStrLn (if mode = "produce" then result fuel request else replay request).compress
  return 0
