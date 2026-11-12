import Mettapedia.Languages.MeTTa.PeTTa.ConstructorFaults
import Mettapedia.Languages.MeTTa.PeTTa.ConstructorContinuations
import Mettapedia.Languages.MeTTa.PeTTa.LambdaStagingDepth
import Mettapedia.Languages.MeTTa.PeTTa.UnifyingComputation

/-!
# Completed root prefixes through constructor errors

The independent source fixture keeps its first root answer before a later
error. Nested root collectors retain that prefix through a singleton clause
wrapper. Argument waiters still discard tentative packets. These controls do
not establish general streaming through unfinished operand continuations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaConstructorFaultControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Unifying

def call (head : String) (arguments : List Atom) : Atom := .expression (.symbol head :: arguments)
def registry : SpaceSemantics.Program := {equations := [],declarations := []}
def marker : Atom := call "mark" [.symbol "caught"]
def kept : Atom := call "record" [.symbol "kept"]
def body : Atom := call "superpose" [.expression
  [kept,call "record" [call "let" [.var "ignored",
    call "add-atom" [.symbol "&self",marker],
    call "+" [.symbol "bad-value",.grounded (.int 3)]]]]]
def expanded : Atom := (LambdaStaging.stage registry ∅ {} body).expression

def root (expression : Atom) : Configuration :=
  {state := Effects.empty,control := .evaluate [] expression,frames := [.dynamicCall]}

def wrapped (expression : Atom) : Configuration :=
  {state := Effects.empty,control := .sequence [.evaluate [] expression] [],frames := [.dynamicCall]}

def answersAndMarks : Outcome → Option (List Atom × Nat)
  | .complete state answers _ _ => some (answers,state.core.count marker)
  | _ => none

theorem bare_root_keeps_the_answer :
    answersAndMarks (run registry 500 (root body)) = some ([kept],1) := by
  decide +kernel

theorem unexpanded_singleton_wrapper_keeps_the_answer :
    answersAndMarks (run registry 500 (wrapped body)) = some ([kept],1) := by
  decide +kernel

theorem expanded_singleton_wrapper_keeps_the_answer :
    answersAndMarks (run registry 500 (wrapped expanded)) = some ([kept],1) := by
  decide +kernel

theorem singleton_wrapper_preserves_this_root_prefix :
    answersAndMarks (run registry 500 (root body)) =
      answersAndMarks (run registry 500 (wrapped body)) := by
  rw [bare_root_keeps_the_answer,unexpanded_singleton_wrapper_keeps_the_answer]

theorem argument_waiter_discards_tentative_answers :
    recoverDynamic [⟨.symbol "unfinished",[]⟩]
      [.argument .data [] [] 0,.dynamicCall] = some ([],[]) := rfl

theorem nested_root_collectors_keep_discovery_order :
    recoverDynamic []
      [.sequence [] [⟨.symbol "later",[]⟩],
       .sequence [] [⟨.symbol "earlier",[]⟩],.dynamicCall] =
        some ([⟨.symbol "earlier",[]⟩,⟨.symbol "later",[]⟩],[]) := rfl

end Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaConstructorFaultControls
