import Mathlib.Data.List.Basic

/-!
# Prefix behavior of success-priority error selection

This is a pure observation over already-produced visible replies. It neither
changes branch scheduling nor classifies raised exceptions as error data.
Successes remain valid under extension; an error-only prefix may lose every
reply after a later success. Eagerly gathering all successful replies is
therefore not forced by this observation policy, while publishing a provisional
error before completion is generally unsound.

Preservation of effects, demand, fairness and faults under an actual streaming
implementation is a separate operational obligation.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.RuntimePlumbing.SuccessPriority

variable {Reply : Type}

def successes (isError : Reply → Bool) (replies : List Reply) : List Reply :=
  replies.filter (fun reply => !isError reply)

def select (isError : Reply → Bool) (replies : List Reply) : List Reply :=
  match successes isError replies with
  | [] => replies
  | first :: rest => first :: rest

theorem successes_append (isError : Reply → Bool) (front back : List Reply) :
    successes isError (front ++ back) =
      successes isError front ++ successes isError back := by
  simp [successes]

theorem select_of_success (isError : Reply → Bool) (replies : List Reply)
    (present : successes isError replies ≠ []) :
    select isError replies = successes isError replies := by
  cases found : successes isError replies with
  | nil => exact False.elim (present found)
  | cons first rest => simp [select, found]

/-- After success appears, extensions only append further successes. -/
theorem select_append_of_success (isError : Reply → Bool) (front back : List Reply)
    (present : successes isError front ≠ []) :
    select isError (front ++ back) =
      successes isError front ++ successes isError back := by
  cases found : successes isError front with
  | nil => exact False.elim (present found)
  | cons first rest => simp [select, successes_append, found]

namespace Controls

inductive Sample where
  | value (payload : Nat)
  | error (reason : Nat)
  deriving DecidableEq, Repr

def isError : Sample → Bool
  | .error _ => true
  | .value _ => false

theorem an_error_prefix_cannot_be_published_irrevocably :
    select isError [.error 3] = [.error 3] ∧
      select isError ([.error 3] ++ [.value 7]) = [.value 7] := by decide

theorem successful_replies_do_not_require_the_later_error :
    select isError ([.value 7] ++ [.error 3]) = [.value 7] ∧
      select isError ([.value 7] ++ [.error 3, .value 8]) = [.value 7, .value 8] := by decide

theorem success_multiplicity_is_retained :
    select isError [.value 7, .error 3, .value 7] = [.value 7, .value 7] := by decide

theorem error_only_completion_retains_errors :
    select isError [.error 3, .error 4] = [.error 3, .error 4] := by decide

end Controls

end Mettapedia.Machines.RuntimePlumbing.SuccessPriority
