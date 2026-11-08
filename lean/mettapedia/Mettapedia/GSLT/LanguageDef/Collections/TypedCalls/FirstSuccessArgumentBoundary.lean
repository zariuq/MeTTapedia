import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.FirstSuccessBoundary
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEReturns

/-! # Scalar argument stopping at the retained HE boundary -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.FirstSuccessArgumentBoundary

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)

theorem grounded_not_stopped (value : GroundedValue) (original : Atom) :
    ((Atom.grounded value != original) && isEmptyOrError (.grounded value)) = false := by
  simp [isEmptyOrError, isEmptyAtom, isErrorAtom, Atom.empty]

theorem numeric_self_equal (n : Int) :
    ((Atom.grounded (.int n)) == (Atom.grounded (.int n))) = true := by simp

theorem numeric_cast (space : Space) (bindings : Bindings) (n : Int) (depth : Nat) :
    typeCast (.grounded (.int n)) (.symbol "Number") space bindings (depth + 2) =
      [(.grounded (.int n), bindings)] := by
  exact CompletedDelivery.typeCast_checked rfl
    (HEReturns.argumentChecked_grounded space (.int n) rfl) bindings (by change 1 ≤ depth + 2; omega)

theorem numeric_cast_covered (space : Space) (bindings : Bindings) (n : Int) (depth : Nat) :
    typeCastCovered (.grounded (.int n)) (.symbol "Number") space bindings (depth + 2) = true := by
  rw [FirstSuccessScopedAdequacy.UniversalScopedCastAndHeadBoundary.typeCastCovered_of_singleton_lookup
    (.grounded (.int n)) (.symbol "Number") (.symbol "Number") space bindings (depth + 2)
    (rawTypeLookup space) rfl]
  cbv

/-- A delivered scalar continues with the saved tail and its own binding
record. Testing whether it differs from the original source is unnecessary
because the scalar is neither Empty nor Error. -/
theorem grounded_argument_entry (space : Space) (dispatch : GroundedDispatch)
    (lookup : TypeLookup) (original : Atom) (remaining types : List Atom)
    (depth : Nat) (value : GroundedValue) (bindings : Bindings)
    (alternatives : ResultSet) (live : List Atom) :
    RecursiveMachine.enter space dispatch
      (.argumentHeads original remaining types depth ((.grounded value, bindings) :: alternatives) live) lookup =
        (.work (.args remaining types bindings depth (.grounded value :: live)),
         [.argumentTail (.grounded value),
          .append (.argumentHeads original remaining types depth alternatives live)]) := by
  simp only [RecursiveMachine.enter, grounded_not_stopped, Bool.false_eq_true, if_false]

/-- The checked worker's corresponding step is independent of the lookup
policy; this argument-head phase performs no new type query. -/
theorem checked_grounded_argument_step (space : Space) (dispatch : GroundedDispatch)
    (policy : FirstSuccessRecursiveExecution.TypePolicy)
    (original : Atom) (remaining types : List Atom) (depth : Nat) (value : GroundedValue)
    (bindings : Bindings) (alternatives : ResultSet) (live : List Atom)
    (stack : List RecursiveTasks.Frame) (emitted : ResultSet) :
    (FirstSuccessRecursiveExecution.Checked.machine dispatch policy).step
      ⟨space, .work (.argumentHeads original remaining types depth
        ((.grounded value, bindings) :: alternatives) live), stack, emitted⟩ =
      some (.silent ⟨space, .work (.args remaining types bindings depth (.grounded value :: live)),
        [.argumentTail (.grounded value),
          .append (.argumentHeads original remaining types depth alternatives live)] ++ stack, emitted⟩) := by
  simp [FirstSuccessRecursiveExecution.Checked.machine, RecursiveMachine.Checked.guardMachine,
    FirstSuccessRecursiveExecution.Checked.blocked, FirstSuccessRecursiveStrategy.taskReady,
    RecursiveMachine.Checked.taskReady, FirstSuccessRecursiveExecution.machine,
    FirstSuccessRecursiveExecution.next, FirstSuccessRecursiveStrategy.enter,
    grounded_argument_entry, Mettapedia.GSLT.Distinction.ProductiveBlocks.Transition.relabel]

attribute [local cbv_eval] numeric_self_equal

theorem numeric_self_inequality_false (n : Int) :
    ((Atom.grounded (.int n)) != (Atom.grounded (.int n))) = false := by cbv

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.FirstSuccessArgumentBoundary
