import Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiSumStore
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiSumPrenexControls

/-!
# Controls: the store of the π-calculus with sums

The modal decider of the π-calculus with sums on its store (`PiSumStore.decider`), its successors read off by the
generic store plan instantiated with the calculus's keys and firing (`SumsStore.plan`):

- **A choice is resolved** (`choice_resolved_by_store`), and a silent alternative can be taken instead
  (`silent_alternative_by_store`).
- **Different channels do not communicate** (`channels_apart_by_store`, negative), and a private channel stays private
  (`private_channel_stuck_by_store`, negative).
- **A server serves once and stays** (`server_by_store`), and the forwarder steps back to itself
  (`forwarder_by_store`).
- **A refutation over every successor**: a server offering a choice and three clients, one of them with a silent
  alternative, never reach inaction within three steps (`busy_never_inaction`).
- **Copies with a restriction**: `!(νa)[x⟨a⟩.0]` copies a block with a restriction, so the store gives no list and
  the decider no answer (`restricted_copies_unanswered`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiSumStoreControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiSumStore
open PiControls (zero par restrict replicate)
open PiSumPrenexControls (choice receive send silent x w z twoInputs silentAlternative apart serving forwarder private_)

/-- **A choice is resolved**, by the store. -/
theorem choice_resolved_by_store : frontDoor.sat Env.closed (.possibly .any (.is zero)) twoInputs :=
  decided_holds (by decide +kernel)

/-- **A silent alternative can be taken instead**, leaving the output on `x` waiting, by the store. -/
theorem silent_alternative_by_store :
    frontDoor.sat Env.closed (.possibly .any (.is (par [choice [send z w zero], choice [send x w zero]])))
      silentAlternative :=
  decided_holds (by decide +kernel)

/-- **Different channels do not communicate**, by the store. -/
theorem channels_apart_by_store : ¬ frontDoor.sat Env.closed (.possibly .any .top) apart :=
  decided_fails (by decide +kernel)

/-- **A private channel stays private**, by the store. -/
theorem private_channel_stuck_by_store : ¬ frontDoor.sat Env.closed (.possibly .any .top) private_ :=
  decided_fails (by decide +kernel)

/-- **A server serves once and stays**, by the store. -/
theorem server_by_store :
    frontDoor.sat Env.closed (.possibly .any (.is (replicate (choice [receive x zero])))) serving :=
  decided_holds (by decide +kernel)

/-- **The forwarder steps back to itself**, by the store. -/
theorem forwarder_by_store : frontDoor.sat Env.closed (.possibly .any (.is forwarder)) forwarder :=
  decided_holds (by decide +kernel)

/-- `![x(y).0 + z(y).0] | [x⟨w⟩.0] | [z⟨w⟩.0] | [x⟨w⟩.0 + τ.0]`. -/
def busy : Pattern := par
  [replicate (choice [receive x zero, receive z zero]), choice [send x w zero], choice [send z w zero],
    choice [send x w zero, silent zero]]

/-- **A server offering a choice and three clients never reach inaction within three steps**: the server stays. -/
theorem busy_never_inaction :
    ¬ frontDoor.sat Env.closed (.possibly .any (.possibly .any (.possibly .any (.is zero)))) busy :=
  decided_fails (by decide +kernel)

/-- `!(νa)[x⟨a⟩.0] | [x(y).[y⟨w⟩.0]]`. -/
def restrictedCopies : Pattern :=
  par [replicate (restrict (choice [send x (.bvar 0) zero])), choice [receive x (choice [send (.bvar 0) w zero])]]

/-- **Copies with a restriction**: the store gives no list there, and the decider no answer. -/
theorem restricted_copies_unanswered : decider.decide (.possibly .any .top) restrictedCopies = none := by
  decide +kernel

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiSumStoreControls
