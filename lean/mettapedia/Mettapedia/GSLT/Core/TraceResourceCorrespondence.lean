import Mettapedia.GSLT.Core.ResourceAwareControl

/-!
# Total additive trace grades as exact resource demand

A total additive event valuation and an additive resource demand may share the
same event-to-account map without sharing authority.  This module proves their
numerical correspondence: the valuation of a chronological history is exactly
the positional resource demand of that history.

The correspondence constructs an exact purse only when the source account is
explicitly supplied as that demand.  Merely reading a trace grade does not mint
such a source.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Core.TraceResourceCorrespondence

open Mettapedia.GSLT.Core.ResourceAwareControl
open Mettapedia.GSLT.Dynamics.IndexedEventValuation

universe uEvent uAccount

theorem batchDemand_append
    {Event : Type uEvent} {Account : Type uAccount} [AddMonoid Account]
    (demand : Event -> Account) (first second : List Event) :
    batchDemand demand (first ++ second) =
      batchDemand demand first + batchDemand demand second := by
  simp [batchDemand]

/-- Folding a total additive valuation and summing the matching positional
resource demand are the same computation. -/
theorem additive_historyGrade_eq_batchDemand
    {Event : Type uEvent} {Account : Type uAccount} [AddMonoid Account]
    (demand : Event -> Account) (events : List Event) :
    (additive demand).historyGrade events =
      some (batchDemand demand events) := by
  induction events with
  | nil => rfl
  | cons event rest inductionHypothesis =>
      simp only [Valuation.historyGrade_cons, inductionHypothesis]
      rfl

/-- The exact positional demand funds its own finite history with no retained
frame.  The source account is explicit data, not a consequence of valuation. -/
def exactFunding
    {Event : Type uEvent} {Account : Type uAccount} [AddMonoid Account]
    (demand : Event -> Account) (events : List Event) :
    BatchSeparation Account demand (batchDemand demand events) events where
  frame := 0
  source_eq := by simp

/-! ## Positive and negative authority controls -/

namespace Canary

inductive Event where
  | left
  | right
deriving DecidableEq

def demand : Event -> Nat
  | .left => 2
  | .right => 3

theorem additive_trace_is_positional_sum :
    (additive demand).historyGrade [.left, .right] = some 5 := by
  decide

theorem zero_source_does_not_follow_from_grade :
    (additive demand).historyGrade [.left] = some 2 /\
      ¬ Nonempty (BatchSeparation Nat demand 0 [.left]) := by
  constructor
  · decide
  · rintro ⟨funding⟩
    have source := funding.source_eq
    simp [batchDemand, demand] at source
    omega

end Canary

#print axioms batchDemand_append
#print axioms additive_historyGrade_eq_batchDemand
#print axioms Canary.additive_trace_is_positional_sum
#print axioms Canary.zero_source_does_not_follow_from_grade

end Mettapedia.GSLT.Core.TraceResourceCorrespondence
