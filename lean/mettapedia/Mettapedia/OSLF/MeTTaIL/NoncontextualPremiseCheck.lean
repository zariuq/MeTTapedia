import Mettapedia.OSLF.MeTTaIL.ContextualStep

/-! Classify premise lists at the boundary with recursive language steps. -/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.ContextualStep

open Mettapedia.OSLF.MeTTaIL.Syntax

/-- Top-level dispatch to the base premise interpreter. A quantified
premise has the semantics supplied by that interpreter. -/
def noncontextualPremise : Premise → Bool
  | .freshness _ | .relationQuery _ _ | .forAll _ _ _ => true
  | .congruence _ _ | .scopedStep _ => false

theorem check_noncontextualPremises_iff (premises : List Premise) :
    premises.all noncontextualPremise = true ↔ NoncontextualPremises premises := by
  constructor
  · induction premises with
    | nil => exact fun _ => .nil
    | cons premise rest ih =>
      intro accepted
      cases premise with
      | freshness condition => exact .freshness (ih accepted)
      | relationQuery relation arguments => exact .relationQuery (ih accepted)
      | forAll collection binder body => exact .forAll (ih accepted)
      | congruence lhs rhs => cases accepted
      | scopedStep request => cases accepted
  · intro declared
    induction declared with
    | nil => rfl
    | freshness _ checked | relationQuery _ checked | forAll _ checked =>
      exact checked

/-- Reflect a check of the actual rule list into the premise guard of the
root-executor equivalence. -/
theorem check_noncontextualRules_iff (rules : List RewriteRule) :
    rules.all (fun rule => rule.premises.all noncontextualPremise) = true ↔
      ∀ rule ∈ rules, NoncontextualPremises rule.premises := by
  rw [List.all_eq_true]
  exact ⟨fun checked rule member => (check_noncontextualPremises_iff _).mp (checked rule member),
    fun guarded rule member => (check_noncontextualPremises_iff _).mpr (guarded rule member)⟩

end Mettapedia.OSLF.MeTTaIL.ContextualStep
