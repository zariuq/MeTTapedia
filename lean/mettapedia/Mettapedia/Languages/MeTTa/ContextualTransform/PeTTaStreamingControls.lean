import Mettapedia.Languages.MeTTa.PeTTa.StreamingDemand
import Mettapedia.Languages.MeTTa.PeTTa.LambdaStagingDepth
import Lean.Elab.Tactic.Cbv

/-!
# Streaming demand, caught scope and marker association controls

The expected observations are source-level effects and answers. Missing scope
markers refuse; matching a different marker kind or updating another scope is
not accepted as successful delivery. Generic prefix laws retain the paid state.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaStreamingControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa

def call (head : String) (arguments : List Atom) : Atom := .expression (.symbol head :: arguments)
def registry : SpaceSemantics.Program := {equations := [],declarations := []}
def mark (name : String) : Atom := call "mark" [.symbol name]
def effect (name : String) (body : Atom) : Atom :=
  call "let" [.var ("ignored-" ++ name),call "add-atom" [.symbol "&self",mark name],body]
def alternatives : Atom := call "superpose" [.expression
  [effect "silent" (call "empty" []),effect "chosen" (call "record" [.symbol "a"]),
   effect "forbidden" (call "record" [.symbol "b"])]]
def requested : Atom := call "collapse" [call "once" [alternatives]]

def preparedStart (expression : Atom) : Streaming.State :=
  let compiled := LambdaStaging.stage registry ∅ {} expression
  Streaming.enter {state := Effects.empty,privateCode := compiled.table.code} compiled.expression

def result : Streaming.State := Streaming.advance registry 1000 (preparedStart requested)

theorem once_keeps_answerless_effect_and_stops_the_tail :
    Streaming.values result = [Atom.expression [call "record" [.symbol "a"]]] ∧
      result.world.state.core.count (mark "silent") = 1 ∧
      result.world.state.core.count (mark "chosen") = 1 ∧
      result.world.state.core.count (mark "forbidden") = 0 ∧
      result.agenda = [] := by
  decide +kernel

def callerFault : Atom := call "let"
  [.var "f",call "|->" [.expression [],.symbol "a"],
    call "let" [.var "x",.expression [.var "f"],call "+" [.symbol "bad-value",.grounded (.int 3)]]]

def callerCompiled : LambdaStaging.Result :=
  ⟨⟨[⟨"lambda_1",[],.symbol "a"⟩],1,{"lambda_1"}⟩,
    call "let" [.var "f",.symbol "lambda_1",
      call "let" [.var "x",.expression [.var "f"],call "+" [.symbol "bad-value",.grounded (.int 3)]]]⟩

private theorem first_name :
    Mettapedia.FirstFreshName.choose LambdaLifting.name LambdaLifting.name_injective ∅ 1 = 1 := by
  apply (Mettapedia.FirstFreshName.choose_eq_iff _ _ _ _ _).mpr
  exact ⟨by omega,by simp,fun earlier lower upper => by omega⟩

private theorem name_one : LambdaLifting.name 1 = "lambda_1" := by decide

theorem caller_prepared : LambdaStaging.prepare registry ∅ 20 {} callerFault = some callerCompiled := by
  simp [ConstructorDataHeads.emit,ConstructorDataHeads.shouldFreeze,ConstructorDataHeads.namedCallable,
    ConstructorDataHeads.construct,ConstructorDataHeads.frozen,Unifying.sourceControlForm,
    LambdaStaging.prepare,LambdaStaging.perform,LambdaStaging.classify,LambdaStaging.visitArguments,
    LambdaStaging.heldArgument,LambdaStaging.reserve,LambdaLifting.occupied,first_name,name_one,
    LambdaStaging.finish,LambdaLifting.equation,LambdaLifting.value,LambdaLifting.captures,LambdaLifting.scan,
    Mettapedia.Languages.ProcessCalculi.MORK.atomFreeVars,
    Mettapedia.Languages.ProcessCalculi.MORK.atomFreeVars.atomFreeVarsList,
    Unifying.codeRegistry,Eval.argumentIsRaw,Eval.ioHead,StdLib.known,
    callerFault,callerCompiled,call,registry,bind,pure]

def faultReason : Streaming.Outcome → Option Effects.Fault
  | .fault reason _ => some reason
  | _ => none

def invalidArgumentHead : Streaming.Outcome → Option String
  | .fault (.invalidArguments head) _ => some head
  | _ => none

theorem invalidArgumentHead_some (outcome : Streaming.Outcome) (head : String) :
    invalidArgumentHead outcome = some head ↔ faultReason outcome = some (.invalidArguments head) := by
  cases outcome with
  | complete _ | suspended _ => simp [invalidArgumentHead,faultReason]
  | fault reason state => cases reason <;> simp [invalidArgumentHead,faultReason]

theorem returning_from_a_callee_does_not_catch_the_callers_error :
    faultReason (Streaming.run registry 1000 (preparedStart callerFault)) =
      some (.invalidArguments "+") := by
  simp only [preparedStart,LambdaStaging.stage_eq_of_prepared caller_prepared]
  exact (invalidArgumentHead_some _ _).mp (by decide +kernel)

theorem a_missing_first_marker_is_not_an_empty_success :
    Streaming.returnAnswer registry {world := {state := Effects.empty},agenda := []}
      ⟨.symbol "a",[]⟩ [.first 3] [] = none := rfl

theorem a_collection_marker_is_not_an_exception_marker :
    Streaming.handlerMarker 3 (.collect 3 [] [] []) = false := rfl

theorem recording_uses_the_selected_scope_and_retains_the_other_marker :
    Streaming.collectAnswer 2 ⟨.symbol "kept",[]⟩
      [.collect 1 [] [] [⟨.symbol "other",[]⟩],.collect 2 [] [] []] =
      some [.collect 1 [] [] [⟨.symbol "other",[]⟩],.collect 2 [] [] [⟨.symbol "kept",[]⟩]] := rfl

theorem a_missing_collection_marker_does_not_update_another_scope :
    Streaming.collectAnswer 2 ⟨.symbol "kept",[]⟩ [.collect 1 [] [] []] = none := rfl

theorem partial_execution_resumes_the_actual_frontier (first second : Nat) :
    Streaming.advance registry (first + second) (preparedStart requested) =
      Streaming.advance registry second (Streaming.advance registry first (preparedStart requested)) :=
  Streaming.advance_add registry first second (preparedStart requested)

end Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaStreamingControls
