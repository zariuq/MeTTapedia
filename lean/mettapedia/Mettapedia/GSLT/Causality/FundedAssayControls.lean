import Mettapedia.GSLT.Causality.FundedAssayCompletion

/-!
# Funded assay controls

Complete computed outcomes retain session, origin and received payload.
Underfunding and unfinished scheduling are distinguished from falsity, and
erasing origins loses distinctions present in the complete receipt readout.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.ComplementaryAssay.Controls

open ResourceInteraction OccurrenceHistory

def testingPrice : Bool → Nat
  | true => 2
  | false => 3

def confirms : Multiset (Nat × Verdict × Nat × Bool) := { (5, .confirm, 7, true) }
def refutes : Multiset (Nat × Verdict × Nat × Bool) := { (5, .refute, 7, false) }

theorem funded_confirmation : observed id testingPrice 5 7 (some true) 4 = confirms := by decide

theorem funded_refutation : observed id testingPrice 5 7 (some false) 4 = refutes := by decide

theorem exact_price_is_sufficient :
    observed id testingPrice 5 7 (some true) 2 = confirms := by decide

theorem absent_message_no_verdict : observed id testingPrice 5 7 none 4 = 0 := by decide

theorem delivered_underfunded_no_verdict :
    Resource.message 5 false ∈ ready (Origins := Nat) 5 7 false ∧
      observed id testingPrice 5 7 (some false) 2 = 0 := by
  constructor
  · decide
  · decide

theorem unspent_purse_readout :
    rightPart (execute id testingPrice 5 7 (some true) 4).1 = purse 2 := by decide

theorem budget_account :
    4 = (rightPart (completed id testingPrice 5 7 true 4)).card + testingPrice true :=
  paidRun_conserved id testingPrice 5 7 true 4 (by decide)

def unfinished : OccurrencePath (paid (Origins := Nat) id testingPrice).presentation
    (marking (ready 5 7 true) (purse 4)) (marking (ready 5 7 true) (purse 4)) := .refl _

theorem unfinished_arrival_is_not_a_refutation :
    outputs (leftPart (marking (ready 5 7 true) (purse 4))) = 0 ∧
      (paid id testingPrice).Enables (marking (ready 5 7 true) (purse 4))
        (selected id 5 7 true) ∧
      (paid id testingPrice).pathEntries unfinished = [] := by
  exact ⟨by rw [leftPart_marking, outputs_ready],
    (paid_selected_enabled_iff id testingPrice 5 7 true 4).2 (by decide), rfl⟩

theorem unfinished_is_not_maximal :
    ¬ Maximal id testingPrice (marking (ready 5 7 true) (purse 4)) := by
  intro maximal
  exact maximal (selected id 5 7 true)
    ((paid_selected_enabled_iff id testingPrice 5 7 true 4).2 (by decide))

theorem wrong_guard_cannot_accept :
    ¬ ∃ firing : Firing Nat (id : Bool → Bool) .refute, firing.value = true := by
  rintro ⟨firing, sameValue⟩
  have checked := firing.guard
  rw [sameValue] at checked
  exact Bool.noConfusion checked

def publicReadout (readout : Multiset (Nat × Verdict × Nat × Bool)) : Multiset (Verdict × Bool) :=
  readout.map fun result => (result.2.1, result.2.2.2)

theorem same_public_verdict_different_retained_origins :
    publicReadout (observed id testingPrice 5 7 (some true) 4) =
      publicReadout (observed id testingPrice 5 8 (some true) 4) ∧
    observed id testingPrice 5 7 (some true) 4 ≠
      observed id testingPrice 5 8 (some true) 4 := by decide

theorem every_completed_prefix_retains_confirmation
    {target : Multiset (Resource Bool Nat ⊕ Unit)}
    (path : OccurrencePath (paid id testingPrice).presentation
      (marking (ready 5 7 true) (purse 4)) target)
    (maximal : Maximal id testingPrice target) :
    outputs (leftPart target) = confirms ∧
      ((paid id testingPrice).pathEntries path).length = 1 :=
  maximal_affordable_verdict id testingPrice 5 7 true 4 (by decide) path maximal

end Mettapedia.GSLT.Causality.ComplementaryAssay.Controls
