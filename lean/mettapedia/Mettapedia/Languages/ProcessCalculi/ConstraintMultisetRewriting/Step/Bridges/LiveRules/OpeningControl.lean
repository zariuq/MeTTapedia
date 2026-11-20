import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.LiveRules.OriginCards
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.Doubling

/-!
# Infinite unused openings do not erase the canonical origin fibres

The candidate's first-order link admits infinitely many irrelevant opening
assignments. Its existing event bisimulation can identify one held copy with
two by rearranging those assignments. Over a specified complete base run,
the canonical projection still has one origin run versus `2 ^ count`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.LiveRules.OpeningControl

open RuleSyntax RuleSyntax.RuleOccurrences Origins
open Examples (Tm X E)

theorem origin_card (ids : Finset Nat) (state : State Tm Nat)
    (firing : (baseEvents X E (P := ∅) (Q := Doubling.linkProgram)).Choice state) :
    Nat.card (Uses X E (ids := ids) (code := Doubling.code) Doubling.zone state firing) = ids.card := by
  rw [held_uses_card]
  apply Nat.subtype_card ids
  intro identity
  simp only [Doubling.code, Doubling.rule_eq firing.val, and_true]

theorem run_origin_card {ids : Finset Nat} {identity : Nat} (present : identity ∈ ids)
    (state : State Tm Nat) (count : Nat)
    (base : BaseRuns X E (P := ∅) (Q := Doubling.linkProgram) state count) :
    Nat.card {run : HeldRuns X E (P := ∅) (ids := ids) (code := Doubling.code) Doubling.zone state count //
      projectRun X E Doubling.zone (Doubling.offers_link ids present) state count run = base} =
        ids.card ^ count := by
  rw [run_fibre_card]
  exact ways_constant X E Doubling.zone ids.card (origin_card ids) _

theorem bisimilar_with_different_run_fibres (state : State Tm Nat) (count : Nat)
    (base : BaseRuns X E (P := ∅) (Q := Doubling.linkProgram) state count) :
    EventMultiplicity.Bisimilar
      (byRule Nat Unit X E (∅ : Program Tm)) (holding state {0} Doubling.code Doubling.zone)
      (byRule Nat Unit X E (∅ : Program Tm)) (Doubling.twice state) ∧
    Nat.card {run : HeldRuns X E (P := ∅) (ids := {0}) (code := Doubling.code) Doubling.zone state count //
      projectRun X E Doubling.zone (Doubling.offers_link {0} (Finset.mem_singleton_self 0)) state count run = base} = 1 ∧
    Nat.card {run : HeldRuns X E (P := ∅) (ids := {0, 1}) (code := Doubling.code) Doubling.zone state count //
      projectRun X E Doubling.zone (Doubling.offers_link {0, 1} (Finset.mem_insert_self 0 {1})) state count run = base} =
        2 ^ count := by
  refine ⟨Doubling.one_two_bisimilar state, ?_, ?_⟩
  · simpa using run_origin_card (Finset.mem_singleton_self 0) state count base
  · simpa using run_origin_card (Finset.mem_insert_self 0 {1}) state count base

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.LiveRules.OpeningControl
