import Mettapedia.Languages.MeTTa.PeTTa.ConstructorDataHeads
import Mettapedia.Languages.MeTTa.PeTTa.UnifyingLocalProjection
import Mettapedia.Languages.MeTTa.PeTTa.UnifyingComputation
import Lean.Elab.Tactic.Cbv

/-!
# Retained data heads, logical cutoffs and fresh binding controls

The same constructor stays data after registration, while an ordinary known
call still executes. Control and I/O heads remain operations. Fresh locals
preserve source bindings; a captured existing key can instead make a bind fail.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaConstructorControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Unifying

def emptyProgram : SpaceSemantics.Program := {equations := [],declarations := []}
def lateProgram : SpaceSemantics.Program :=
  {equations := [⟨"late",[],.symbol "called"⟩],declarations := [],layout := [.equation]}
def call (head : String) (arguments : List Atom) : Atom := .expression (.symbol head :: arguments)
def frozenLate : Atom := ConstructorDataHeads.emit emptyProgram (.symbol "late") []

theorem frozen_late_exact : frozenLate = call "quote" [call "late" []] := by decide

def execute (registry : SpaceSemantics.Program) (fuel : Nat) (expression : Atom) : Outcome :=
  run registry fuel (ScopedSource.enter 0 [] (Effects.loaded registry) expression)

theorem later_registration_keeps_compiled_data :
    observed (execute lateProgram 100 frozenLate) = .answers [call "late" []] := by
  simp only [execute,frozen_late_exact,call,ScopedSource.enter]
  unifying_run

theorem known_call_still_executes :
    observed (execute lateProgram 100 (call "late" [])) = .answers [.symbol "called"] := by
  simp only [execute,call,ScopedSource.enter]
  unifying_run

theorem cutoff_difference_is_explicit :
    observed (execute emptyProgram 1 (call "late" [])) = .other ∧
      observed (execute emptyProgram 1 frozenLate) = .answers [call "late" []] := by
  constructor <;> decide +kernel

theorem empty_is_not_turned_into_data :
    observed (execute emptyProgram 100
      (ConstructorDataHeads.emit emptyProgram (.symbol "empty") [])) = .answers [] := by cbv

def inputRequest : Configuration :=
  {ScopedSource.enter 0 [] Effects.empty
    (ConstructorDataHeads.emit emptyProgram (.symbol "readln!") []) with input := [.symbol "token"]}

theorem input_operation_is_not_turned_into_data :
    observed (run emptyProgram 100 inputRequest) = .answers [.symbol "token"] := by cbv

def original : Subst := [("source",.symbol "a")]

theorem actual_local_binding_keeps_the_source_substitution :
    unifyBinding original (.var "local") (.var "source") =
      .ok [("local",.symbol "a"),("source",.symbol "a")] ∧
      eraseLocal "local" [("local",.symbol "a"),("source",.symbol "a")] = original := by decide

theorem colliding_binder_does_not_act_like_a_fresh_temporary :
    unifyBinding [("local",.symbol "old")] (.var "local") (.symbol "new") = .clash := by decide

end Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaConstructorControls
