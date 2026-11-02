import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CCSPartnerAdequacy
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CCSControls

/-!
# Controls: CCS's parallel partners through the front door

The step modalities of `ccsCalc` under partners' labels, decided at the listed successors (`CCSPartners.decider`):

- An action on `a` has no step of its own; beside the co-action on `a` it reacts, to inaction
  (`action_reacts_beside_coaction`), and beside a co-action on another name it does not (`action_stuck_beside_other`).
- Beside `~a.0`, `(νx)(a.0 | x.0)` reacts on its free name and keeps its restriction (`restricted_reacts`), while
  `(νx) x.0` has no reaction: a private name is no partner's (`private_stuck`).
- A choice resolved by a partner: beside `~b.0`, `a.0 + b.a.0` reaches `a.0` (`choice_resolved_by_partner`) and not
  inaction, the summand `a.0` being discarded (`choice_discards_beside_partner`).
- **The labels see beyond plain steps**: `a.0` and `0` have the same plain steps, none, and the partner `~a.0`
  separates them (`action_not_saturated_inaction`).
- **The labels see branching**: `a.(b.0 + c.0)` and `a.b.0 + a.c.0` have no plain steps and the same traces; after
  a reaction with `~a.0` the first can always react with `~b.0`, while the second may have resolved its choice to
  `c.0`. So they are not saturated reduction bisimilar (`branching_separated`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.CCSPartnerControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.NativeTypes.GeneratedLogic.CCSPartners
open Mettapedia.Languages.ProcessCalculi.CCS (nil sum nu act coact)
open CCSControls (a b)

/-- The partner `□` beside a process. -/
abbrev beside (partner : Pattern) : StepLabel := partnerLabel "hole" partner

/-- The free name `c`. -/
def c : Pattern := .fvar "c"

/-- `a.0`. -/
def action : Pattern := sum [act a nil]

/-- `~a.0`. -/
def coaction : Pattern := sum [coact a nil]

/-! ## Reactions with a partner -/

/-- **An action has no step of its own.** -/
theorem action_alone_stuck : ¬ frontDoor.sat Env.closed (.possibly .any .top) action :=
  decided_fails (by decide +kernel)

/-- **Beside the co-action on its name it steps.** -/
theorem action_steps_beside_coaction : frontDoor.sat Env.closed (.possibly (beside coaction) .top) action :=
  decided_holds (by decide +kernel)

/-- **It reacts to inaction.** -/
theorem action_reacts_beside_coaction : frontDoor.sat Env.closed (.possibly (beside coaction) (.is nil)) action :=
  decided_holds (by decide +kernel)

/-- **Beside a co-action on another name it does not step.** -/
theorem action_stuck_beside_other :
    ¬ frontDoor.sat Env.closed (.possibly (beside (sum [coact b nil])) .top) action :=
  decided_fails (by decide +kernel)

/-! ## Restriction -/

/-- `(νx)(a.0 | x.0)`. -/
def restricted : Pattern := nu (par (sum [act a nil]) (sum [act (.bvar 0) nil]))

/-- **A restricted process reacts on its free name and keeps its restriction**: beside `~a.0` it reaches
`(νx) x.0`. -/
theorem restricted_reacts :
    frontDoor.sat Env.closed (.possibly (beside coaction) (.is (nu (sum [act (.bvar 0) nil])))) restricted :=
  decided_holds (by decide +kernel)

/-- `(νx) x.0`. -/
def private_ : Pattern := nu (sum [act (.bvar 0) nil])

/-- **A private name is no partner's**: `(νx) x.0` has no reaction beside `~a.0`. -/
theorem private_stuck : ¬ frontDoor.sat Env.closed (.possibly (beside coaction) .top) private_ :=
  decided_fails (by decide +kernel)

/-! ## Choice -/

/-- `a.0 + b.a.0`. -/
def choice : Pattern := sum [act a nil, act b (sum [act a nil])]

/-- **A partner resolves a choice**: beside `~b.0`, `a.0 + b.a.0` reaches `a.0`. -/
theorem choice_resolved_by_partner :
    frontDoor.sat Env.closed (.possibly (beside (sum [coact b nil])) (.is action)) choice :=
  decided_holds (by decide +kernel)

/-- **The other summand is discarded**: beside `~b.0` it does not reach inaction. -/
theorem choice_discards_beside_partner :
    ¬ frontDoor.sat Env.closed (.possibly (beside (sum [coact b nil])) (.is nil)) choice :=
  decided_fails (by decide +kernel)

/-! ## What the labels separate -/

/-- **Inaction has no step beside `~a.0`.** -/
theorem inaction_stuck_beside_coaction : ¬ frontDoor.sat Env.closed (.possibly (beside coaction) .top) nil :=
  decided_fails (by decide +kernel)

/-- **`a.0` and `0` are not saturated reduction bisimilar**: the partner `~a.0` separates them, though neither has a
step of its own. -/
theorem action_not_saturated_inaction : ¬ SaturatedReductionBisimilar action nil := by
  intro bisimilar
  have actionIn : processes action := by decide +kernel
  have nilIn : processes nil := by decide +kernel
  have agree := (agree_iff_saturated actionIn nilIn).mpr bisimilar
  have forward : (Formula.possibly (beside coaction) .top : Formula 0).forwardOn isPartnerLabel = true := by
    decide +kernel
  exact inaction_stuck_beside_coaction ((agree _ forward).mp action_steps_beside_coaction)

/-- `a.(b.0 + c.0)`: the choice is made after the action. -/
def late : Pattern := sum [act a (sum [act b nil, act c nil])]

/-- `a.b.0 + a.c.0`: the choice is made with the action. -/
def early : Pattern := sum [act a (sum [act b nil]), act a (sum [act c nil])]

/-- After every reaction with `~a.0`, a reaction with `~b.0` is available. -/
def keepsChoice : Formula 0 := .necessarily (beside coaction) (.possibly (beside (sum [coact b nil])) .top)

/-- **Neither has a plain step.** -/
theorem late_stuck : ¬ frontDoor.sat Env.closed (.possibly .any .top) late :=
  decided_fails (by decide +kernel)

theorem early_stuck : ¬ frontDoor.sat Env.closed (.possibly .any .top) early :=
  decided_fails (by decide +kernel)

/-- **The late choice keeps both options after the action.** -/
theorem late_keepsChoice : frontDoor.sat Env.closed keepsChoice late := decided_holds (by decide +kernel)

/-- **The early choice may have dropped one.** -/
theorem early_not_keepsChoice : ¬ frontDoor.sat Env.closed keepsChoice early := decided_fails (by decide +kernel)

/-- **`a.(b.0 + c.0)` and `a.b.0 + a.c.0` are not saturated reduction bisimilar.** -/
theorem branching_separated : ¬ SaturatedReductionBisimilar late early := by
  intro bisimilar
  have lateIn : processes late := by decide +kernel
  have earlyIn : processes early := by decide +kernel
  have agree := (agree_iff_saturated lateIn earlyIn).mpr bisimilar
  have forward : keepsChoice.forwardOn isPartnerLabel = true := by decide +kernel
  exact early_not_keepsChoice ((agree _ forward).mp late_keepsChoice)

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.CCSPartnerControls
