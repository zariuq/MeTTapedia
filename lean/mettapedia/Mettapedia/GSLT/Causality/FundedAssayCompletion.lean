import Mettapedia.GSLT.Causality.FundedAssay

/-!
# Complete funded assay prefixes and scheduling qualifications

Every finite prefix from one delivered session either has not fired or
contains exactly its unique funded verdict firing. A maximal prefix must
have fired when the testing price is available. A pending session cannot
produce a verdict, while an underfunded delivered session is also stuck.
Thus absence of a verdict is not itself evidence that the environment failed
to answer or that the hypothesis was false.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.ComplementaryAssay

open ResourceInteraction OccurrenceHistory

universe u v w z

variable {X : Type u} {Origins : Type v}
variable [DecidableEq X] [DecidableEq Origins]

omit [DecidableEq X] [DecidableEq Origins] in
theorem path_of_stuck {R : Type w} [DecidableEq R] (S : System.{w, z} R)
    : ∀ {source target : Multiset R} (path : OccurrencePath S.presentation source target),
      (∀ {site : S.Site} (firing : S.Instance site), ¬ S.Enables source firing) →
      target = source ∧ S.pathEntries path = []
  | _, _, .refl _, _ => ⟨rfl, rfl⟩
  | _, _, .cons occurrence _, stuck =>
      False.elim (stuck occurrence.evidence.val occurrence.evidence.property.1)

theorem paid_path_cases (test : X → Bool) (cost : X → Nat)
    (session : Nat) (origin : Origins) (value : X) (budget : Nat)
    : ∀ {target : Multiset (Resource X Origins ⊕ Unit)}
      (path : OccurrencePath (paid test cost).presentation
        (marking (ready session origin value) (purse budget)) target),
    (target = marking (ready session origin value) (purse budget) ∧
      (paid test cost).pathEntries path = []) ∨
    (target = completed test cost session origin value budget ∧
      ((paid test cost).pathEntries path).length = 1 ∧ cost value ≤ budget)
  | _, .refl _ => .inl ⟨rfl, rfl⟩
  | _, @OccurrencePath.cons _ _ _ middle _ occurrence rest => by
    have step : (paid test cost).theory.rewrites
        (marking (ready session origin value) (purse budget)) middle :=
      ⟨occurrence.site, occurrence.evidence.val,
        occurrence.evidence.property.1, occurrence.evidence.property.2⟩
    obtain ⟨affordable, endOfFirst⟩ :=
      (paid_ready_step_iff test cost session origin value budget middle).1 step
    have stuck : ∀ {site : (paid (Origins := Origins) test cost).Site}
        (firing : (paid test cost).Instance site),
        ¬ (paid test cost).Enables middle firing := by
      intro site firing
      rw [endOfFirst]
      exact paid_finished_stuck test cost session origin value
        (purse budget - purse (cost value)) firing
    obtain ⟨sameEnd, noEntries⟩ := path_of_stuck (paid test cost) rest stuck
    refine .inr ⟨sameEnd.trans endOfFirst, ?_, affordable⟩
    change (⟨occurrence.site, occurrence.evidence.val⟩ :: (paid test cost).pathEntries rest).length = 1
    rw [noEntries]
    rfl

/-- Maximality states that the supplied endpoint has no further admitted firing. -/
def Maximal (test : X → Bool) (cost : X → Nat)
    (target : Multiset (Resource X Origins ⊕ Unit)) : Prop :=
  ∀ {site : (paid (Origins := Origins) test cost).Site}
    (firing : (paid test cost).Instance site), ¬ (paid test cost).Enables target firing

theorem maximal_affordable_verdict (test : X → Bool) (cost : X → Nat)
    (session : Nat) (origin : Origins) (value : X) (budget : Nat)
    (affordable : cost value ≤ budget) {target : Multiset (Resource X Origins ⊕ Unit)}
    (path : OccurrencePath (paid test cost).presentation
      (marking (ready session origin value) (purse budget)) target)
    (maximal : Maximal test cost target) :
    outputs (leftPart target) = { (session, verdictOf (test value), origin, value) } ∧
      ((paid test cost).pathEntries path).length = 1 := by
  rcases paid_path_cases test cost session origin value budget path with
    ⟨sameEnd, _⟩ | ⟨sameEnd, oneEntry, _⟩
  · have disabled := maximal (selected test session origin value)
    rw [sameEnd] at disabled
    exact False.elim (disabled
      ((paid_selected_enabled_iff test cost session origin value budget).2 affordable))
  · exact ⟨by rw [sameEnd, completed, leftPart_marking, outputs_finished], oneEntry⟩

theorem underfunded_prefix_quiet (test : X → Bool) (cost : X → Nat)
    (session : Nat) (origin : Origins) (value : X) (budget : Nat)
    (underfunded : budget < cost value) {target : Multiset (Resource X Origins ⊕ Unit)}
    (path : OccurrencePath (paid test cost).presentation
      (marking (ready session origin value) (purse budget)) target) :
    target = marking (ready session origin value) (purse budget) ∧
      outputs (leftPart target) = 0 ∧ (paid test cost).pathEntries path = [] := by
  rcases paid_path_cases test cost session origin value budget path with
    ⟨sameEnd, noEntries⟩ | ⟨_, _, affordable⟩
  · exact ⟨sameEnd, by rw [sameEnd, leftPart_marking, outputs_ready], noEntries⟩
  · omega

theorem pending_prefix_quiet (test : X → Bool) (cost : X → Nat)
    (session : Nat) (origin : Origins) (budget : Nat)
    {target : Multiset (Resource X Origins ⊕ Unit)}
    (path : OccurrencePath (paid test cost).presentation
      (marking (pending (X := X) session origin) (purse budget)) target) :
    target = marking (pending session origin) (purse budget) ∧
      outputs (leftPart target) = 0 ∧ (paid test cost).pathEntries path = [] := by
  obtain ⟨sameEnd, noEntries⟩ := path_of_stuck (paid test cost) path
    (paid_pending_stuck test cost session origin (purse budget))
  exact ⟨sameEnd, by rw [sameEnd, leftPart_marking, outputs_pending], noEntries⟩

end Mettapedia.GSLT.Causality.ComplementaryAssay
