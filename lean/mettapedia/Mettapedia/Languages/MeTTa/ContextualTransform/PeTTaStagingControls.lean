import Mettapedia.Languages.MeTTa.PeTTa.LambdaStaging
import Mettapedia.Languages.MeTTa.PeTTa.UnifyingComputation
import Lean.Elab.Tactic.Cbv

/-!
# Recursive lambda preparation consumed by the actual source machine

The controls exercise nested private clauses, original capture order, held
payloads, unselected effects and retained data-head decisions with operands.
The generic completed-schedule connection is separate from full compiler adequacy.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaStagingControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Unifying

def registry : SpaceSemantics.Program := {equations := [],declarations := []}
def call (head : String) (arguments : List Atom) : Atom := .expression (.symbol head :: arguments)
def lambda (arguments : List Atom) (body : Atom) : Atom := call "|->" [.expression arguments,body]

private theorem first_name :
    Mettapedia.FirstFreshName.choose LambdaLifting.name LambdaLifting.name_injective ∅ 1 = 1 := by
  apply (Mettapedia.FirstFreshName.choose_eq_iff _ _ _ _ _).mpr
  exact ⟨by omega,by simp,fun earlier lower upper => by omega⟩

private theorem second_name :
    Mettapedia.FirstFreshName.choose LambdaLifting.name LambdaLifting.name_injective {"lambda_1"} 2 = 2 := by
  apply (Mettapedia.FirstFreshName.choose_eq_iff _ _ _ _ _).mpr
  exact ⟨by omega,by decide,fun earlier lower upper => by omega⟩

private theorem name_one : LambdaLifting.name 1 = "lambda_1" := by decide
private theorem name_two : LambdaLifting.name 2 = "lambda_2" := by decide

def nested : Atom :=
  call "let" [.var "f",
    lambda [.var "x"]
      (call "let" [.var "g",lambda [.var "y"] (call "pair" [.var "x",.var "y"]),
        .expression [.var "g",.symbol "b"]]),
    .expression [.var "f",.symbol "a"]]

def innerEquation : SpaceSemantics.Equation :=
  ⟨"lambda_2",[.var "x",.var "y"],ConstructorSpine.build [.symbol "pair",.var "x",.var "y"]⟩

def outerEquation : SpaceSemantics.Equation :=
  ⟨"lambda_1",[.var "g",.var "y",.var "x"],
    call "let" [.var "g",Eval.partialValue "lambda_2" [.var "x"],.expression [.var "g",.symbol "b"]]⟩

def nestedResult : LambdaStaging.Result :=
  ⟨⟨[innerEquation,outerEquation],2,{"lambda_2","lambda_1"}⟩,
    call "let" [.var "f",Eval.partialValue "lambda_1" [.var "g",.var "y"],
      .expression [.var "f",.symbol "a"]]⟩

theorem nested_prepared : LambdaStaging.prepare registry ∅ 20 {} nested = some nestedResult := by
  simp [ConstructorDataHeads.emit,ConstructorDataHeads.shouldFreeze,ConstructorDataHeads.namedCallable,
    ConstructorDataHeads.construct,ConstructorDataHeads.frozen,ConstructorSpine.build,ConstructorSpine.cons,
    ConstructorSpine.empty,Unifying.sourceControlForm,
    LambdaStaging.prepare,LambdaStaging.perform,LambdaStaging.classify,LambdaStaging.visitArguments,
    LambdaStaging.heldArgument,LambdaStaging.reserve,LambdaLifting.occupied,first_name,second_name,name_one,name_two,
    LambdaStaging.finish,LambdaLifting.equation,LambdaLifting.value,LambdaLifting.captures,LambdaLifting.scan,
    Mettapedia.Languages.ProcessCalculi.MORK.atomFreeVars,
    Mettapedia.Languages.ProcessCalculi.MORK.atomFreeVars.atomFreeVarsList,
    Unifying.codeRegistry,Eval.argumentIsRaw,Eval.ioHead,StdLib.known,
    nested,lambda,call,registry,nestedResult,innerEquation,outerEquation,bind,pure]

def runPrepared (expression : Atom) : Option Outcome :=
  (LambdaStaging.prepare registry ∅ 20 {} expression).map fun translated =>
    run registry 100 (ScopedSource.enter 0 translated.table.code Effects.empty translated.expression)

theorem nested_lambda_runs_in_actual_source :
    (runPrepared nested).map observed = some (.answers [call "pair" [.symbol "a",.symbol "b"]]) := by
  simp only [runPrepared,nested_prepared,Option.map_some]
  apply congrArg some
  simp only [nestedResult,innerEquation,outerEquation,call,ScopedSource.enter]
  unifying_run

theorem outer_reserved_first_inner_installed_first :
    (LambdaStaging.prepare registry ∅ 20 {} nested).map
      (fun result => (result.table.code.map (·.head),result.table.cursor)) =
      some (["lambda_2","lambda_1"],2) := by rw [nested_prepared]; rfl

theorem captures_come_from_original_bodies :
    (LambdaStaging.prepare registry ∅ 20 {} nested).map
      (fun result => result.table.code.map (·.arguments)) =
      some [[.var "x",.var "y"],[.var "g",.var "y",.var "x"]] := by rw [nested_prepared]; rfl

def quoted : Atom := call "quote" [lambda [.var "x"] (call "pair" [.var "x",.var "x"])]

theorem quotation_does_not_install_its_lambda :
    (LambdaStaging.prepare registry ∅ 20 {} quoted).map
      (fun result => (result.table.code,result.expression)) = some ([],quoted) := by cbv

def unused : Atom :=
  call "if" [Effects.boolean true,.symbol "safe",lambda [] (call "println!" [.symbol "unwanted"])]

def unusedResult : LambdaStaging.Result :=
  ⟨⟨[⟨"lambda_1",[],call "println!" [.symbol "unwanted"]⟩],1,{"lambda_1"}⟩,
    call "if" [Effects.boolean true,.symbol "safe",.symbol "lambda_1"]⟩

theorem unused_prepared : LambdaStaging.prepare registry ∅ 20 {} unused = some unusedResult := by
  simp only [unused,unusedResult,Effects.boolean]
  simp [ConstructorDataHeads.emit,ConstructorDataHeads.shouldFreeze,ConstructorDataHeads.namedCallable,
    ConstructorDataHeads.construct,ConstructorDataHeads.frozen,ConstructorSpine.build,ConstructorSpine.cons,
    ConstructorSpine.empty,Unifying.sourceControlForm,
    LambdaStaging.prepare,LambdaStaging.perform,LambdaStaging.classify,LambdaStaging.visitArguments,
    LambdaStaging.heldArgument,LambdaStaging.reserve,LambdaLifting.occupied,first_name,name_one,
    LambdaStaging.finish,LambdaLifting.equation,LambdaLifting.value,LambdaLifting.captures,LambdaLifting.scan,
    Mettapedia.Languages.ProcessCalculi.MORK.atomFreeVars,
    Mettapedia.Languages.ProcessCalculi.MORK.atomFreeVars.atomFreeVarsList,
    Unifying.codeRegistry,Eval.argumentIsRaw,Eval.ioHead,StdLib.known,
    lambda,call,registry,bind,pure]

theorem preparing_an_unselected_body_does_not_execute_it :
    (runPrepared unused).map shown = some (.printed [] [.symbol "safe"]) := by
  simp only [runPrepared,unused_prepared,Option.map_some]
  apply congrArg some
  simp only [unusedResult,call,ScopedSource.enter]
  unifying_run

def held : Atom :=
  call "let" [.var "_",
    call "add-atom" [.symbol "&self",call "saved" [lambda [.var "z"] (call "println!" [.var "z"])]],
    call "match" [.symbol "&self",call "saved" [lambda [.var "w"] (call "println!" [.var "w"])],
      .symbol "held"]]

theorem held_prepared : LambdaStaging.prepare registry ∅ 20 {} held = some ⟨{},held⟩ := by
  simp [ConstructorDataHeads.emit,ConstructorDataHeads.shouldFreeze,ConstructorDataHeads.namedCallable,
    ConstructorDataHeads.construct,ConstructorDataHeads.frozen,ConstructorSpine.build,ConstructorSpine.cons,
    ConstructorSpine.empty,Unifying.sourceControlForm,
    held,call,lambda,LambdaStaging.prepare,LambdaStaging.perform,LambdaStaging.classify,
    LambdaStaging.visitArguments,LambdaStaging.heldArgument,registry,Eval.argumentIsRaw,Eval.ioHead,
    StdLib.known,StdLib.rawArgument,Unifying.codeRegistry,bind,pure]

theorem held_payloads_are_not_lambda_authoring_sites :
    (LambdaStaging.prepare registry ∅ 20 {} held).map (fun result => result.table.code) = some [] ∧
      (runPrepared held).map observed = some (.answers [.symbol "held"]) := by
  constructor
  · rw [held_prepared]; rfl
  · simp only [runPrepared,held_prepared,Option.map_some]
    apply congrArg some
    simp only [held,call,lambda,ScopedSource.enter]
    unifying_run

def futureHead : Atom := .expression [lambda [] (call "lambda_1" [])]

def futureResult : LambdaStaging.Result :=
  ⟨⟨[⟨"lambda_1",[],call "quote" [call "lambda_1" []]⟩],1,{"lambda_1"}⟩,
    call "lambda_1" []⟩

theorem future_prepared : LambdaStaging.prepare registry ∅ 20 {} futureHead = some futureResult := by
  simp [LambdaStaging.prepare,LambdaStaging.perform,LambdaStaging.classify,
    LambdaStaging.reserve,LambdaLifting.occupied,first_name,name_one,
    LambdaStaging.finish,LambdaLifting.equation,LambdaLifting.value,LambdaLifting.captures,LambdaLifting.scan,
    Mettapedia.Languages.ProcessCalculi.MORK.atomFreeVars,
    Mettapedia.Languages.ProcessCalculi.MORK.atomFreeVars.atomFreeVarsList,
    ConstructorDataHeads.emit,ConstructorDataHeads.shouldFreeze,ConstructorDataHeads.namedCallable,
    ConstructorDataHeads.construct,ConstructorDataHeads.frozen,Unifying.sourceControlForm,Unifying.codeRegistry,Eval.ioHead,StdLib.known,
    futureHead,futureResult,lambda,call,registry,bind,pure]

/-- SWI's cold source fixture returns (lambda_1). The compiled quotation
retains that decision after the generated name becomes callable. -/
theorem compiled_future_head_remains_data :
    (runPrepared futureHead).map observed = some (.answers [call "lambda_1" []]) := by
  simp only [runPrepared,future_prepared,Option.map_some]
  apply congrArg some
  simp only [futureResult,call,ScopedSource.enter]
  unifying_run

def futureArguments : Atom := .expression [lambda [.var "x"] (call "lambda_1" [.var "x"]),.symbol "a"]

def futureArgumentsResult : LambdaStaging.Result :=
  ⟨⟨[⟨"lambda_1",[.var "x"],ConstructorSpine.build [.symbol "lambda_1",.var "x"]⟩],1,{"lambda_1"}⟩,
    call "lambda_1" [.symbol "a"]⟩

theorem future_arguments_prepared :
    LambdaStaging.prepare registry ∅ 20 {} futureArguments = some futureArgumentsResult := by
  simp [ConstructorDataHeads.emit,ConstructorDataHeads.shouldFreeze,ConstructorDataHeads.namedCallable,
    ConstructorDataHeads.construct,ConstructorDataHeads.frozen,ConstructorSpine.build,ConstructorSpine.cons,
    ConstructorSpine.empty,Unifying.sourceControlForm,
    LambdaStaging.prepare,LambdaStaging.perform,LambdaStaging.classify,LambdaStaging.visitArguments,
    LambdaStaging.heldArgument,LambdaStaging.reserve,LambdaLifting.occupied,first_name,name_one,
    LambdaStaging.finish,LambdaLifting.equation,LambdaLifting.value,LambdaLifting.captures,LambdaLifting.scan,
    Mettapedia.Languages.ProcessCalculi.MORK.atomFreeVars,
    Mettapedia.Languages.ProcessCalculi.MORK.atomFreeVars.atomFreeVarsList,
    Unifying.codeRegistry,Eval.argumentIsRaw,Eval.ioHead,StdLib.known,
    futureArguments,futureArgumentsResult,lambda,call,registry,bind,pure]

/-- The cold source fixture returns (lambda_1 a). Its operand evaluation
must be retained when the earlier data-head decision is lowered. -/
theorem compiled_argument_head_remains_data :
    (runPrepared futureArguments).map observed = some (.answers [call "lambda_1" [.symbol "a"]]) := by
  simp only [runPrepared,future_arguments_prepared,Option.map_some]
  apply congrArg some
  simp only [futureArgumentsResult,call,ScopedSource.enter]
  unifying_run

end Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaStagingControls
