import Mettapedia.Languages.MeTTa.PeTTa.LambdaLifting
import Mettapedia.Languages.MeTTa.PeTTa.UnifyingPrefixes
import Mettapedia.Languages.MeTTa.PeTTa.UnifyingComputation
import Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaCallCache

/-!
# Actual execution of lifted private lambda clauses

The ordinary clause profile is exercised through the real unifying machine,
including unresolved captures, held code, ordinary source effects and public
space observation. The source fixture separately calibrates lambda authoring
in SWI; these controls do not supply a recursive source-compiler theorem.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaLambdaControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Unifying

def registry : SpaceSemantics.Program := {equations := [],declarations := []}

def call (head : String) (arguments : List Atom) : Atom := .expression (.symbol head :: arguments)
def bind (name : String) (value body : Atom) : Atom := call "let" [.var name,value,body]

private theorem first_empty_name :
    Mettapedia.FirstFreshName.choose LambdaLifting.name LambdaLifting.name_injective ∅ 1 = 1 := by
  apply (Mettapedia.FirstFreshName.choose_eq_iff _ _ _ _ _).mpr
  exact ⟨by omega,by simp,fun earlier lower upper => by omega⟩

def sourceBody : Atom := call "pair" [.var "saved",.var "x"]

def lifted : LambdaLifting.Lifted :=
  LambdaLifting.lift {} registry ∅ [.var "x"] sourceBody sourceBody

def installed : SpaceSemantics.Equation :=
  ⟨"lambda_1",[.var "saved",.var "x"],sourceBody⟩

theorem lifted_exact :
    lifted = ⟨⟨[installed],1,{"lambda_1"}⟩,1,["saved"],installed,
      Eval.partialValue "lambda_1" [.var "saved"]⟩ := by
  simp [lifted,LambdaLifting.lift,LambdaLifting.occupied,registry,first_empty_name,
    LambdaLifting.captures,LambdaLifting.scan,sourceBody,call,
    Mettapedia.Languages.ProcessCalculi.MORK.atomFreeVars,
    Mettapedia.Languages.ProcessCalculi.MORK.atomFreeVars.atomFreeVarsList,
    LambdaLifting.name,LambdaLifting.equation,LambdaLifting.value,installed]
  decide

def request : Atom :=
  bind "saved" (.symbol "a")
    (bind "f" lifted.closure (.expression [.var "f",.symbol "b"]))

def heldRequest : Atom :=
  bind "saved" (call "quote" [call "println!" [.grounded (.int 9)]])
    (bind "f" lifted.closure (.expression [.var "f",.symbol "b"]))

def lateCaptureRequest : Atom :=
  bind "f" lifted.closure
    (bind "saved" (.symbol "a") (.expression [.var "f",.symbol "b"]))

def runLifted (expression : Atom) : Outcome :=
  run registry 100 (LambdaLifting.enter lifted Effects.empty expression)

theorem captured_value_runs_in_actual_source :
    observed (runLifted request) = .answers [call "pair" [.symbol "a",.symbol "b"]] := by
  simp only [runLifted,request,lifted_exact,LambdaLifting.enter,bind,call]
  unifying_run

theorem captured_code_is_not_evaluated_again :
    shown (runLifted heldRequest) = .printed []
      [call "pair" [call "println!" [.grounded (.int 9)],.symbol "b"]] := by
  simp only [runLifted,heldRequest,lifted_exact,LambdaLifting.enter,bind,call]
  unifying_run

theorem capture_can_be_bound_after_closure_creation :
    observed (runLifted lateCaptureRequest) = .answers [call "pair" [.symbol "a",.symbol "b"]] := by
  simp only [runLifted,lateCaptureRequest,lifted_exact,LambdaLifting.enter,bind,call]
  unifying_run

theorem private_clause_is_not_a_public_atom :
    observed (runLifted (call "collapse" [call "get-atoms" [.symbol "&self"]])) =
      .answers [.expression []] := by
  simp only [runLifted,lifted_exact,LambdaLifting.enter,call]
  unifying_run

def publicized : Effects.State := {Effects.empty with core := [installed.toAtom]}

def oldNegativeCache : PeTTaCallCache.Cache :=
  PeTTaCallCache.warm registry PeTTaCallCache.empty "lambda_1"

theorem private_installation_changes_the_cache_dependency :
    PeTTaCallCache.lookup (codeRegistry registry [installed]) oldNegativeCache "lambda_1" = false ∧
      PeTTaActivation.callable (codeRegistry registry [installed]) "lambda_1" = true ∧
      PeTTaCallCache.lookup (codeRegistry registry [installed])
        (PeTTaCallCache.transfer registry (codeRegistry registry [installed]) oldNegativeCache)
        "lambda_1" = true := by decide

/-- Publishing the same generated clause as a stored atom changes the real
space primitive's answer. Keeping code private is observable, not cosmetic. -/
theorem publicizing_code_changes_space_observation :
    StdLib.apply Effects.empty "get-atoms" [.symbol "&self"] = .ok (Effects.empty,[]) ∧
      StdLib.apply publicized "get-atoms" [.symbol "&self"] = .ok (publicized,[installed.toAtom]) := by
  constructor <;> rfl

def removeThenCall : Atom :=
  bind "removed" (call "remove-atom" [.symbol "&self",installed.toAtom]) request

theorem public_removal_does_not_remove_private_code :
    observed (runLifted removeThenCall) = .answers [call "pair" [.symbol "a",.symbol "b"]] := by
  simp only [runLifted,removeThenCall,request,lifted_exact,LambdaLifting.enter,bind,call,installed,
    SpaceSemantics.Equation.toAtom,sourceBody]
  unifying_run

def closed : LambdaLifting.Lifted :=
  LambdaLifting.lift {} registry ∅ [.var "x"] (.var "x") (.var "x")

theorem closed_exact :
    closed = ⟨⟨[⟨"lambda_1",[.var "x"],.var "x"⟩],1,{"lambda_1"}⟩,1,[],
      ⟨"lambda_1",[.var "x"],.var "x"⟩,.symbol "lambda_1"⟩ := by
  simp [closed,LambdaLifting.lift,LambdaLifting.occupied,registry,first_empty_name,
    LambdaLifting.captures,LambdaLifting.scan,Mettapedia.Languages.ProcessCalculi.MORK.atomFreeVars,
    Mettapedia.Languages.ProcessCalculi.MORK.atomFreeVars.atomFreeVarsList,
    LambdaLifting.name,LambdaLifting.equation,LambdaLifting.value]
  decide

theorem closed_lambda_uses_private_written_call :
    observed (run registry 100 (LambdaLifting.enter closed Effects.empty
      (.expression [closed.closure,.symbol "a"]))) = .answers [.symbol "a"] := by
  simp only [closed_exact,LambdaLifting.enter]
  unifying_run

theorem captures_keep_first_occurrence_and_exclude_formals :
    LambdaLifting.captures [.var "x"]
      (call "row" [.var "b",.var "a",.var "b",.var "x",.var "a"]) = ["b","a"] := by decide

theorem raw_partial_syntax_is_not_the_private_carrier :
    partial? (call "partial" [.symbol "lambda_1",.expression [.symbol "a"]]) = none := by decide

def suffixCollision : Atom :=
  bind "x#0" (.symbol "a") (bind "f" closed.closure (.expression [.var "f",.symbol "b"]))

/-- A retained negative control for bypassing source admission. Suffix
spelling alone cannot standardize a clause apart from every legal caller name. -/
theorem literal_suffix_can_capture_caller_binding :
    observed (run registry 100 (startWithCode closed.table.code Effects.empty suffixCollision)) =
      .answers [] := by
  simp only [closed_exact,suffixCollision,bind,call]
  unifying_run

theorem scoped_literal_suffix_preserves_the_source_answer :
    observed (run registry 100 (LambdaLifting.enter closed Effects.empty suffixCollision)) =
      .answers [.symbol "b"] := by
  simp only [closed_exact,LambdaLifting.enter,suffixCollision,bind,call]
  unifying_run

end Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaLambdaControls
