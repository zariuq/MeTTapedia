import Mettapedia.Algebra.Collections.FlatBagBasis

/-! End-to-end controls for actual finite flat-bag basis selection. The
kernel laws are distinguished from executable enumeration-size checks. -/

set_option autoImplicit false

namespace Mettapedia.Algebra.Collections.FlatBagBasis.Controls

open FlatElementEncoding (Element)
open FlatBagUnifiers (Answer Family Instance MoreGeneral)

def leftVariable : List (Element Nat (Fin 2)) := [.inr 0]
def rightVariable : List (Element Nat (Fin 2)) := [.inr 1]

-- Independent rest and element-identification families are both necessary.
#guard (executable leftVariable rightVariable).length == 2

def repeated : List (Element Nat (Fin 1)) := [.inr 0, .inr 0]

-- Distinct occurrence matchings can describe equivalent families.
#guard (FlatBagUnifiers.families repeated repeated).length > 1
#guard (executable repeated repeated).length == 1

theorem repeated_problem_has_an_irredundant_complete_basis :
    Unification.IsMinimalComplete (Unifier repeated repeated) MoreGeneral
      {family | family ∈ executable repeated repeated} := executable_irredundant repeated repeated

theorem different_constants_keep_the_compensating_solution :
    ∃ family ∈ executable ([.inl 1] : List (Element Nat (Fin 1))) [.inl 2],
      Instance family FlatBagUnifiers.Controls.compensated := by
  apply (executable_complete _ _ _).mp
  change ({Sum.inl 1} : Multiset (Element Nat (Fin 1))) + {.inl 2} = {.inl 2} + {.inl 1}
  exact add_comm _ _

theorem aliased_rests_still_reject_distinct_constants
    (answer : Answer Nat (Fin 1)) (sameRest : answer.rest .left = answer.rest .right) :
    ¬ ∃ family ∈ executable ([.inl 1] : List (Element Nat (Fin 1))) [.inl 2], Instance family answer := by
  intro represented
  have solved := (executable_complete _ _ answer).mpr represented
  exact FlatBagUnifiers.Controls.shared_rest_cannot_compensate_distinct_constants 1 2 (by decide) answer sameRest solved

theorem bag_permutation_preserves_all_answers (answer : Answer Nat (Fin 1)) :
    (∃ family ∈ executable ([.inl 1, .inl 2] : List (Element Nat (Fin 1))) [.inr 0], Instance family answer) ↔
      ∃ family ∈ executable ([.inl 2, .inl 1] : List (Element Nat (Fin 1))) [.inr 0], Instance family answer := by
  exact permutation_preserves_solutions _ _ _ _ (List.Perm.swap _ _ []) (List.Perm.refl _) answer

end Mettapedia.Algebra.Collections.FlatBagBasis.Controls
