import Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaConstraintReadoutControls

/-! Execute different source/runtime representatives and re-enter actual
streaming callers with the full branch packet. Corrupted packets must differ. -/

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open EagerDFS
open Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaConstraintReadoutControls

def transportedValues (packet : AnswerReadout.BranchPacket) (body : Atom) : IO (List Atom) := do
  match Streaming.run program 40 (StreamingAnswerTransport.resume base packet (caller body) []) with
  | .complete reached => pure (Streaming.values reached)
  | _ => throw (IO.userError "transport did not complete")

def main : IO Unit := do
  let source ← match Destination.resolve constraints with
    | some model => pure model
    | none => throw (IO.userError "source orientation refused")
  let native ← match Unifying.unify [] y x with
    | .ok bindings => pure bindings
    | _ => throw (IO.userError "runtime orientation did not answer")
  unless Destination.read source x != Unifying.resolve native x do
    throw (IO.userError "representative control did not distinguish the actual names")
  IO.println "representatives: different"
  let sourceValues := [x,y,z].map (Destination.read source)
  let nativeValues := [x,y,z].map (Unifying.resolve native)
  let joint := Mettapedia.Languages.ProcessCalculi.MORK.VariantReadout.joint
  unless joint sourceValues == joint nativeValues && joint nativeValues == joint [x,x,z] do
    throw (IO.userError "joint observation lost sharing")
  IO.println "joint: same"
  let packet := AnswerReadout.packAnswers [answer]
  let resumed ← transportedValues packet (.var "result")
  unless resumed == [a] do throw (IO.userError "restored caller lost the value")
  IO.println "caller: a"
  unless returnedValues displayedOnly (.var "result") == some [.var "0"] do
    throw (IO.userError "corrupted display-only packet was not distinguished")
  IO.println "labels-without-inverse: changed"
  unless returnedValues [⟨Effects.boolean true,[("x",a)]⟩] x == some [a] &&
      returnedValues [⟨Effects.boolean true,[]⟩] x == some [x] do
    throw (IO.userError "lost binding was not observed by the caller")
  IO.println "bindings-without-state: changed"
  let earlier := Atom.expression [.symbol "marker",.symbol "earlier"]
  let routed := Atom.expression [.symbol "routed",a]
  let state ← match Effects.insert Effects.empty .self earlier with
    | some state => pure state
    | none => throw (IO.userError "earlier addition refused")
  let body := OutputPlan.call "add-atom"
    [.symbol "&self",.expression [.symbol "routed",.var "result"]]
  let effectBase : Streaming.State := {base with world := {base.world with state}}
  match Streaming.run program 40 (StreamingAnswerTransport.resume effectBase packet (caller body) []) with
  | .complete reached =>
      unless reached.world.state.core.count earlier == 1 && reached.world.state.core.count routed == 1 do
        throw (IO.userError "transport lost or duplicated caller effects")
  | _ => throw (IO.userError "effectful caller did not complete")
  IO.println "caller-effects: earlier=1 routed=1"
