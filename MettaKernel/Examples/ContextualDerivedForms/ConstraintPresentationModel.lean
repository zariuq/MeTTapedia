import Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaConstraintPresentationControls
import Mettapedia.Languages.ProcessCalculi.MORK.VariantReadout

/-! Execute the actual runtime unifier and independent destination source
solver, comparing ordered joint observations and explicit refusal. -/

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.Languages.MeTTa.PeTTa
open EagerDFS
open UnifyingConstraintPresentation

def joint (values : List Atom) : Atom :=
  Mettapedia.Languages.ProcessCalculi.MORK.VariantReadout.normalize (.expression values)

def check (label : String) (bindings : Subst) (left right : Atom) (observations : List Atom)
    (expected : Option (List Atom)) : IO Unit := do
  let source := Destination.refine (presentation bindings) left right
  match Unifying.unify bindings left (Unifying.resolve bindings right),source,expected with
  | .ok bound,some after,some wanted =>
      let model ← match Destination.resolve after with
        | some model => pure model
        | none => throw (IO.userError s!"{label}: accepted source has no model")
      let nativeView := joint (observations.map (Unifying.resolve bound))
      let sourceView := joint (observations.map (Destination.read model))
      unless nativeView == joint wanted && sourceView == joint wanted do
        throw (IO.userError s!"{label}: readback disagreement: {nativeView} / {sourceView}")
      IO.println s!"{label}: accepted"
  | .clash,none,none => IO.println s!"{label}: refused"
  | .exhausted,_,_ => throw (IO.userError s!"{label}: unserved runtime work")
  | _,_,_ => throw (IO.userError s!"{label}: source/runtime outcome disagreement")

def main : IO Unit := do
  let x := Atom.var "x"
  let y := Atom.var "y"
  let z := Atom.var "z"
  let a := Atom.symbol "a"
  let b := Atom.symbol "b"
  let pair := fun first second => Atom.expression [.symbol "pair",first,second]
  check "ground" [] (pair x y) (pair a b) [x,y] (some [a,b])
  check "sharing" [] x y [x,y,z] (some [x,x,z])
  check "retained" [("x",a)] y x [x,y] (some [a,a])
  check "shadow" [("x",a),("x",b)] x a [x] (some [a])
  check "literal-conflict" [] a b [] none
  check "occurs" [] x (.expression [.symbol "f",x]) [] none
  check "shared-conflict" [] (pair x x) (pair a b) [] none
  check "retained-conflict" [("x",a)] x b [] none
  unless Unifying.unifyTerms 0 [] x a == .exhausted && (Destination.refine [] x a).isSome do
    throw (IO.userError "interruption was confused with source refusal")
  IO.println "interruption: source-enabled"
  let earlier := Atom.expression [.symbol "event",.symbol "earlier"]
  let forbidden := Atom.expression [.symbol "event",.symbol "forbidden"]
  let state ← match Effects.insert Effects.empty .self earlier with
    | some state => pure state
    | none => throw (IO.userError "earlier write failed")
  let program : SpaceSemantics.Program := {equations := [],declarations := []}
  let base : Streaming.State := {world := {state},agenda := []}
  let falseResult := Effects.boolean false
  let trueResult := Effects.boolean true
  let continuation := OutputPlan.call "add-atom" [.symbol "&self",forbidden]
  let reached := Streaming.advance program 4
    (OutputPlan.focused base [] (OutputPlan.equate falseResult trueResult continuation) [] [])
  let cursor : Destination.Cursor String :=
    {world := OutputPlan.ConstraintAdmission.sourceWorld base.world
     control := {bindings := [],goals := [.equate falseResult trueResult,
       .invoke "add-atom" [.symbol "&self",forbidden] trueResult],destination := .var "out"}
     context := "caller"}
  match (Destination.machine .relational program).step cursor with
  | some (.finish (.noValue _,sourceReached)) =>
      unless sourceReached.world.state.core.count earlier == 1 &&
          sourceReached.world.state.core.count forbidden == 0 &&
          reached.world.state.core.count earlier == 1 && reached.world.state.core.count forbidden == 0 &&
          reached.agenda.isEmpty do throw (IO.userError "gate refusal changed earlier effects or ran the body")
  | _ => throw (IO.userError "source gate did not refuse")
  IO.println "gate: earlier=1 forbidden=0"
