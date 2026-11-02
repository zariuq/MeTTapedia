import Mettapedia.Languages.HOLLight.RecordedSourceImport

/-!
# Source record framing and provenance controls

The records build a real reflexive proof, a closed identity definition and a
transitivity step using the same parent twice. Malformed rows and extra
premises cannot be silently discarded by the intake adapter.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.HOLLight.RecordedSourceImport.Controls
open Lean Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight

def arr (items : List Json) : Json := toJson items

def types : Array Json := #[
  arr [toJson "op",toJson "bool",arr []],
  arr [toJson "op",toJson "fun",toJson ([0,0] : List Nat)],
  arr [toJson "op",toJson "fun",toJson ([0,1] : List Nat)],
  arr [toJson "op",toJson "fun",toJson ([1,0] : List Nat)],
  arr [toJson "op",toJson "fun",toJson ([1,3] : List Nat)]]

def terms : Array Json := #[
  arr [toJson "var",toJson "x",toJson (0:Nat)],
  arr [toJson "const",toJson "=",toJson (2:Nat)],
  arr [toJson "app",toJson (1:Nat),toJson (0:Nat)],
  arr [toJson "app",toJson (2:Nat),toJson (0:Nat)],
  arr [toJson "abs",toJson (0:Nat),toJson (0:Nat)],
  arr [toJson "var",toJson "f",toJson (1:Nat)],
  arr [toJson "const",toJson "=",toJson (4:Nat)],
  arr [toJson "app",toJson (6:Nat),toJson (5:Nat)],
  arr [toJson "app",toJson (7:Nat),toJson (4:Nat)],
  arr [toJson "const",toJson "f",toJson (1:Nat)],
  arr [toJson "app",toJson (6:Nat),toJson (9:Nat)],
  arr [toJson "app",toJson (10:Nat),toJson (4:Nat)]]

def initial : Reading :=
  ⟨⟨types,terms,#[]⟩,Array.replicate types.size none,Array.replicate terms.size none,
    SourceProfile.primitiveBasis.received,SourceProfile.primitiveBasis.symbols,{},[],0⟩

def event (serial : Nat) (rule : String) (payload : List Json) (parents : List Nat)
    (source conclusion : Nat) : Json := Json.mkObj [
  ("event",toJson serial),("rule",toJson rule),("payload",toJson payload),("parents",toJson parents),
  ("outputs",arr [Json.mkObj [("id",toJson source),("hypotheses",arr []),("conclusion",toJson conclusion)]])]

def reflexivity := event 0 "REFL" [toJson (0:Nat)] [] 0 3
def definition := event 1 "DEFINITION" [toJson (8:Nat)] [] 1 11
def duplicateParents := event 2 "TRANS" [] [0,0] 2 3

def run : Except String Reading := do
  let (_, first) ← (receiveEvent reflexivity).run initial
  let (_, second) ← (receiveEvent definition).run first
  let (_, third) ← (receiveEvent duplicateParents).run second
  return third

def refused (state : Reading) (record : Json) : Bool := !((receiveEvent record).run state).isOk

def malformedRow : Reading := {initial with input := {initial.input with
  terms := terms.set! 0 (arr [toJson "var",toJson "x",toJson (0:Nat),toJson "extra"])}}

def controls : List (String × Bool) :=
  let positive := run.isOk
  let state := run.toOption.getD initial
  let beforeDefinition := ((receiveEvent reflexivity).run initial).toOption.map (·.2) |>.getD initial
  [("real-source-commands",positive),
   ("three-theorem-occurrences",state.registered.registered.cache.size == 3),
   ("extra-definition-parent",refused beforeDefinition (event 1 "DEFINITION" [toJson (8:Nat)] [0] 1 11)),
   ("extra-reflexivity-payload",refused state (event 3 "REFL" [toJson (0:Nat),toJson (0:Nat)] [] 3 3)),
   ("missing-transitivity-parent",refused state (event 3 "TRANS" [] [0] 3 3)),
   ("extra-transitivity-payload",refused state (event 3 "TRANS" [toJson (0:Nat)] [0,0] 3 3)),
   ("reused-source-identity",refused state (event 3 "REFL" [toJson (0:Nat)] [] 0 3)),
   ("future-parent",refused state (event 3 "TRANS" [] [0,999] 3 3)),
   ("malformed-term-row",refused malformedRow reflexivity),
   ("malformed-substitution-row",refused state (event 3 "INST" [arr [toJson (0:Nat)]] [0] 3 3)),
   ("extra-substitution-component",refused state (event 3 "INST"
      [toJson ([0,0,0] : List Nat)] [0] 3 3)),
   ("wrong-output-formula",refused state (event 3 "REFL" [toJson (0:Nat)] [] 3 0))]

def main : IO UInt32 := do
  for (label, passed) in controls do
    IO.println s!"{label}: {passed}"
    unless passed do throw (IO.userError ("failed control: " ++ label))
  return 0
end Mettapedia.Languages.HOLLight.RecordedSourceImport.Controls
