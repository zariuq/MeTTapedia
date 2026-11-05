import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CettaWireAtomRead
import Mettapedia.GSLT.LanguageDef.CettaWireData
import Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceCatalogueCertifiedVerification
import Mettapedia.GSLT.LanguageDef.ModuleFormat.Value
import Mettapedia.Data.HexBytes

/-! Language-independent parts of the in-process source compiler protocol:
the reply envelope, physical data payloads, module-value payloads and the
independent source-catalogue verification request. Each language package
supplies its own source reader, preparation and observation. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceCompilerProtocol

open Lean
open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL

abbrev HostAtom := Mettapedia.Languages.MeTTa.OSLFCore.Atom

/-- Every provider reply is one compact JSON object. -/
def answer (result : Except String Json) : String :=
  (match result with
   | .ok value => Json.mkObj [("ok", .bool true), ("value", value)]
   | .error message => Json.mkObj [("ok", .bool false), ("message", .str message)]).compress

/-- A physical payload is exactly one wire term written as host source. -/
def physical (text : String) : Except String CettaWire.Term := do
  let .ok [host] := SpaceSemantics.readSource text | .error "expected one data payload"
  let some value := CettaWireAtom.decode? host | .error "invalid data carrier"
  pure value

def renderValue (value : Value) : String := CettaWireData.render (Value.Wire.encode value)

def value? (text : String) : Except String Value := do
  let some value := Value.Wire.decode? (← physical text) | .error "invalid module value carrier"
  pure value

def evidenceBytes (text : String) : Except String (List UInt8) := do
  let some bytes := Mettapedia.Data.HexBytes.decode? text
    | .error "expected hexadecimal parser evidence bytes"
  pure bytes

structure SourceEvidence where
  packets : List HostAtom
  forest : List UInt8
  identity : List UInt8
  rounds : Nat

def readSourceEvidence (packet forest identity allowance : String) : Except String SourceEvidence := do
  let .ok [.expression (.symbol "SourceValuesV1" :: packets)] := SpaceSemantics.readSource packet
    | .error "expected a whole-input syntax catalogue"
  let forestBytes ← evidenceBytes forest
  let identityBytes ← evidenceBytes identity
  let some rounds := allowance.toNat? | .error "expected a natural verification allowance"
  pure ⟨packets, forestBytes, identityBytes, rounds⟩

def verificationReply : Option Bool → Except String Json
  | none => .ok (Json.mkObj [("status", .str "pending")])
  | some false => .error "source forest or selected catalogue failed independent verification"
  | some true => .ok (Json.mkObj [("status", .str "verified")])

/-- Coverage and catalogue checking are independent of the recognizer; the
coverage reference is certified in one pass. An unfinished check asks for
another allowance; it never admits a packet. -/
def verifySource (spec : Portable.SyntaxDescription) (filters : List SourceSyntax.FamilyFilter)
    (source packet forest identity allowance : String) : Except String Json := do
  let evidence ← readSourceEvidence packet forest identity allowance
  match SourceCatalogueCertifiedVerification.verify? spec filters
      source evidence.forest evidence.identity evidence.packets evidence.rounds with
  | some false => .error (refusal spec source evidence)
  | result => verificationReply result
where
  /-- The first refusing check, named for the diagnostic. -/
  refusal (spec : Portable.SyntaxDescription) (source : String) (evidence : SourceEvidence) : String :=
    if !SourceSyntaxForest.check spec source evidence.forest evidence.identity then
      "native forest does not exactly represent source grammar derivations"
    else match SourceSyntaxExport.plan? spec with
      | none => "source grammar has no parser plan"
      | some plan =>
        if (SourceCatalogue.certificates? plan (source.toList.map Char.toNat) evidence.packets).isNone then
          "selected source packets have no grammar certificates"
        else match SourceCatalogueCertifiedVerification.complete? spec source evidence.forest evidence.identity
            evidence.rounds with
          | some false => "native forest failed independent whole-input coverage"
          | _ => "selected source catalogue failed independent validation"

/-- Entry prefixes name emitted definitions; they are never host code. -/
def entryValid (entry : String) : Bool :=
  let letter := fun c => ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z') || c == '_'
  match entry.toList with
  | [] => false
  | first :: rest => letter first && rest.all (fun c =>
      letter c || ('0' ≤ c && c ≤ '9') || c == ':' || c == '-')

example : entryValid "lang:compiled" = true := by decide +kernel
example : entryValid "bad) !(inject)" = false := by decide +kernel

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceCompilerProtocol
