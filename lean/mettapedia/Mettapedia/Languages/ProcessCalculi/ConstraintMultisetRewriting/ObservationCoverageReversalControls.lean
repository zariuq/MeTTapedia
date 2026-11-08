import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ObservationCoverageReversals
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FirstOrderChecksControls

/-! A real first-order constraint model separates equality of absence
verdicts from preservation of all physical matching occurrences. -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ObservationCoverageReversalControls

open Mettapedia.Logic.LP
open ConstraintMultisetRewriting.Controls (signature zero)

def constantLabel (_ : Nat) : Term signature := .const 0

theorem absence_agrees_in_every_substitution :
    ∀ σ : Subst signature,
      (Check.absent (.const 0)).Holds (FirstOrder.action signature) σ constantLabel {1} ↔
      (Check.absent (.const 0)).Holds (FirstOrder.action signature) σ constantLabel {1, 4} := by
  intro σ
  constructor
  · intro absent
    exact False.elim (absent 1 (by simp) rfl)
  · intro absent
    exact False.elim (absent 1 (by simp) rfl)

theorem empty_equations_have_a_model : (FirstOrder.action signature).Models zero [] := by
  intro equation member
  cases member

theorem agreement_does_not_supply_coverage :
    ¬ Check.CoversMatches (FirstOrder.action signature) [] constantLabel {1} {1, 4} (.const 0) := by
  intro covers
  have impossible := covers zero empty_equations_have_a_model 4 (by simp) rfl
  simp at impossible

theorem exact_counts_disagree :
    (Check.matches (FirstOrder.action signature) zero constantLabel {1} (.const 0)).card = 1 ∧
      (Check.matches (FirstOrder.action signature) zero constantLabel {1, 4} (.const 0)).card = 2 := by
  simp [Check.matches, constantLabel, FirstOrder.action]

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ObservationCoverageReversalControls
