import Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangMailboxEmissionAgreement
import Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangValueCanonical

/-! Source-order, duplicate-occurrence, closure-payload and local-wait
controls for the joined mailbox proofs. Wrong normal answers are rejected
by universal completed-target reflection, not only bounded exploration. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangMailbox.Execution.AgreementControls

open Mettapedia.OSLF.MeTTaIL Syntax CanonicalBags
open Mettapedia.Languages.Erlang

abbrev encode := ErlangCompilation.value

def first : Value := .closure 1 (.lambda 4) [.pid 3, .literal (.integer 7)]
def second : Value := .closure 1 (.recursive 17 1) [.tuple [first, .literal (.atom "captured")]]
def rotating : Mailbox Value := ⟨[second], [], [second, first]⟩
def duplicates : Mailbox Value := ⟨[second, first], [first, first], [second]⟩

def peekRequest : Pattern := node "ErPeek" [mailbox encode rotating]
def peekExpected : Pattern := node "ErPeekValue" [encode first, mailbox encode rotating.normalize]
def peekWrong : Pattern := node "ErPeekValue" [encode second, mailbox encode rotating.normalize]

def removeRequest : Pattern := node "ErRemove" [mailbox encode duplicates]
def removeExpected : Pattern := node "ErRemoved" [mailbox encode ⟨[], [first, second, first], [second]⟩]
def removeWrong : Pattern := node "ErRemoved" [mailbox encode ⟨[], [first, second], [second]⟩]

theorem peek_correct : Settles Runner.base peekRequest peekExpected := by
  simpa [peekRequest, peekExpected, rotating, peekAnswer, Mailbox.peek, Mailbox.unread, Mailbox.normalize] using
    peek Runner.base encode rotating

theorem remove_correct : Settles Runner.base removeRequest removeExpected := by
  simpa [removeRequest, removeExpected, duplicates] using
    remove Runner.base encode (box := duplicates)
      (result := ⟨[], [first, second, first], [second]⟩) (by rfl)

theorem peek_wrong_unreachable : ¬ Path Runner.base peekRequest peekWrong := by
  intro path
  have same := peek_correct.exact peekWrong path
    (answer_no_step Runner.base "ErPeekValue" _ (by simp))
  exact (by decide +kernel : peekWrong ≠ peekExpected) same

theorem remove_wrong_unreachable : ¬ Path Runner.base removeRequest removeWrong := by
  intro path
  have same := remove_correct.exact removeWrong path
    (answer_no_step Runner.base "ErRemoved" _ (by simp))
  exact (by decide +kernel : removeWrong ≠ removeExpected) same

theorem incoming_does_not_authorize_raw_next (target : Pattern) :
    ¬ ContextualStep.Step Runner.base language (node "ErNext" [mailbox encode rotating]) target :=
  empty_next_no_step Runner.base _ _ target

theorem waiting_is_not_a_step (target : Pattern) :
    ¬ ContextualStep.Step Runner.base language (node "ErWaiting" [mailbox encode rotating]) target :=
  answer_no_step Runner.base "ErWaiting" _ (by simp) target

theorem peek_canonical : canon peekRequest = peekRequest := by
  simp only [peekRequest, node, canon_apply, List.map_cons, List.map_nil,
    ErlangCompilation.mailbox_canonical]

theorem remove_canonical : canon removeRequest = removeRequest := by
  simp only [removeRequest, node, canon_apply, List.map_cons, List.map_nil,
    ErlangCompilation.mailbox_canonical]

theorem peek_sorted : Model.Sorted peekRequest :=
  (Mettapedia.GSLT.LanguageDef.WellSorted.checkOpenPatternWellSorted_eq_true_iff _ _ _ _ _).mp (by decide +kernel)

theorem remove_sorted : Model.Sorted removeRequest :=
  (Mettapedia.GSLT.LanguageDef.WellSorted.checkOpenPatternWellSorted_eq_true_iff _ _ _ _ _).mp (by decide +kernel)

theorem completed_peek (ticks quantum : Nat) (done : (Runner.run peekRequest ticks quantum).phase = .done) :
    (Runner.run peekRequest ticks quantum).state = peekExpected :=
  Runner.done_value peek_correct peek_canonical peek_sorted ticks quantum done

theorem completed_remove (ticks quantum : Nat) (done : (Runner.run removeRequest ticks quantum).phase = .done) :
    (Runner.run removeRequest ticks quantum).state = removeExpected :=
  Runner.done_value remove_correct remove_canonical remove_sorted ticks quantum done

end Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangMailbox.Execution.AgreementControls
