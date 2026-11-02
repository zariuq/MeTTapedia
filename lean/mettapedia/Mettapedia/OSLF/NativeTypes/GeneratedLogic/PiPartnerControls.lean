import Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiPartnerAdequacy
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiPrenexControls

/-!
# Controls: π's parallel partners through the front door

The step modalities of `piCalc` under partners' labels, decided at the listed successors (`PiPartners.decider`):

- An input on `x` has no step of its own, steps beside an output on `x` (`receiver_steps_beside_sender`), and not
  beside an output on another channel (`receiver_stuck_beside_other`).
- Beside `x⟨w⟩`, `(νa)(x(y).a⟨y⟩)` reaches `(νa) a⟨w⟩`, extruding its restriction to communicate
  (`guarded_reaches_beside_sender`).
- A private channel stays private beside any output on a public one (`private_stuck_beside_sender`).
- **The labels see beyond plain steps**: `x(y).0` and `0` have the same plain steps, none, and the partner `x⟨w⟩`
  separates them. So they are not saturated reduction bisimilar (`receiver_not_saturated_inaction`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiPartnerControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiPartners
open PiControls (input output zero restrict)
open PiPrenexControls (x w)

/-- The partner `□` beside a process. -/
abbrev beside (partner : Pattern) : StepLabel := partnerLabel "hole" partner

def receiver : Pattern := input x zero
def sender : Pattern := output x w

/-- **An input on `x` has no step of its own.** -/
theorem receiver_alone_stuck : ¬ frontDoor.sat Env.closed (.possibly .any .top) receiver :=
  decided_fails (by decide +kernel)

/-- **Beside an output on `x` it steps.** -/
theorem receiver_steps_beside_sender : frontDoor.sat Env.closed (.possibly (beside sender) .top) receiver :=
  decided_holds (by decide +kernel)

/-- **Beside an output on `w` it does not.** -/
theorem receiver_stuck_beside_other : ¬ frontDoor.sat Env.closed (.possibly (beside (output w w)) .top) receiver :=
  decided_fails (by decide +kernel)

/-- `(νa)(x(y).a⟨y⟩)`. -/
def guarded : Pattern := restrict (input x (output (.bvar 1) (.bvar 0)))

/-- **Beside `x⟨w⟩`, the guarded restriction extrudes and reaches `(νa) a⟨w⟩`.** -/
theorem guarded_reaches_beside_sender :
    frontDoor.sat Env.closed (.possibly (beside sender) (.is (restrict (output (.bvar 0) w)))) guarded :=
  decided_holds (by decide +kernel)

/-- `(νa) a(y).0`. -/
def private_ : Pattern := restrict (input (.bvar 0) zero)

/-- **A private channel stays private** beside an output on a public channel. -/
theorem private_stuck_beside_sender : ¬ frontDoor.sat Env.closed (.possibly (beside sender) .top) private_ :=
  decided_fails (by decide +kernel)

/-- **Inaction has no step of its own either.** -/
theorem inaction_alone_stuck : ¬ frontDoor.sat Env.closed (.possibly .any .top) zero :=
  decided_fails (by decide +kernel)

theorem inaction_stuck_beside_sender : ¬ frontDoor.sat Env.closed (.possibly (beside sender) .top) zero :=
  decided_fails (by decide +kernel)

/-- **`x(y).0` and `0` are not saturated reduction bisimilar**: the partner `x⟨w⟩` separates them, though neither has
a step of its own. -/
theorem receiver_not_saturated_inaction : ¬ SaturatedReductionBisimilar receiver zero := by
  intro bisimilar
  have receiverIn : processes receiver := by decide +kernel
  have zeroIn : processes zero := by decide +kernel
  have agree := (agree_iff_saturated receiverIn zeroIn).mpr bisimilar
  have forward : (Formula.possibly (beside sender) .top : Formula 0).forwardOn isPartnerLabel = true := by
    decide +kernel
  exact inaction_stuck_beside_sender ((agree _ forward).mp receiver_steps_beside_sender)

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiPartnerControls
