import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ModuleReading.CoalescedGroundDemands
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ModuleReading.Choice

/-!
# Two alternatives stay with their tagged call

Reuse the module-reading toss fixture. The general demand contains
both the callable toss and a constructor with no rule. Both toss
answers survive batching; neither is attributed to the uncallable
constructor just because the result table contains it.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ModuleReading
namespace CoalescedGroundDemandControls

open Mettapedia.Logic.LP (Term)
open Toss

private def roots : Finset T := {coin, toss coin}

private theorem rootsGround : ∀ root ∈ roots, root.isGround := by
  intro r member
  simp only [roots, Finset.mem_insert, Finset.mem_singleton] at member
  rcases member with rfl | rfl
  · intro slot
    exact Fin.elim0 slot
  · exact ground

theorem two_answers_survive :
    valueRow (toss coin) heads ∈ coalescedRows module rows roots ∧
      valueRow (toss coin) tails ∈ coalescedRows module rows roots := by
  have covered : toss coin ∈ roots := by simp [roots]
  exact ⟨(coalesced_value_iff_variant roots rangeRestricted rootsGround rows_ground covered heads).mpr
    two_values.1,
    (coalesced_value_iff_variant roots rangeRestricted rootsGround rows_ground covered tails).mpr
      two_values.2.1⟩

private theorem coin_does_not_derive (value : T) : ¬ Derives module ↑rows coin value := by
  intro derivesCoin
  obtain ⟨label, θ, source, _, _⟩ := derives_iff.mp derivesCoin
  cases label
  all_goals
    have same : Head.con Con.coin = Head.con Con.toss := (Term.app.inj source).1
    cases Head.con.inj same

theorem untagged_projection_would_add_an_answer :
    (∃ tag, valueRow tag heads ∈ coalescedRows module rows roots) ∧
      valueRow coin heads ∉ coalescedRows module rows roots :=
  forgetting_call_can_add_answer roots rangeRestricted rootsGround rows_ground (by simp [roots])
    (by simp [roots]) (derives .heads coin) (coin_does_not_derive _)

#print axioms two_answers_survive
#print axioms untagged_projection_would_add_an_answer

end CoalescedGroundDemandControls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ModuleReading
