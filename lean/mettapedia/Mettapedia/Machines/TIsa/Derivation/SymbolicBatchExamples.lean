import Mettapedia.Machines.TIsa.Derivation.SymbolicBatch
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.Knowledge

/-!
# A joint firing that neither member can justify on its own

The source example supplies the two symbolic readings and their
shared tell problem. This runs the derived batch test for the three
boundaries that differ on those tells.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.Derivation.SymbolicBatch.Examples

open Mettapedia.Logic.LP
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open RuleSyntax.JointFirings
open RuleSyntax.Controls (atoms)
open Knowledge (start both first second v)
open SymbolicFiring (act)

private def prepared : Prepared (program := Knowledge.program) start :=
  ⟨both, List.cons_ne_nil _ _, Knowledge.both_fits⟩

theorem joint_publication_succeeds :
    (evaluate .joint prepared).isSome = true := by
  obtain ⟨answer, fires⟩ := admitted_has_result .joint prepared Knowledge.both_admitted
  rw [fires]
  rfl

theorem testing_members_alone_loses_the_joint_step :
    evaluate .memberOwn prepared = none :=
  (refuses_exactly_when_not_admitted .memberOwn prepared).mpr Knowledge.both_refused_own

private theorem notBefore : ¬ both.AdmitsBeforeTells (act atoms) start := by
  intro early
  let onlyFive : Subst atoms := fun _ => .const (5 : ℕ)
  have solved : (act atoms).Models (a := PUnit.unit) (b := PUnit.unit) onlyFive
      (both.askInformation (act atoms) start) := by
    intro equation found
    change equation ∈ [(v 2, v 0), (v 3, v 1), (v 4, v 0), (v 5, v 1)] at found
    simp only [List.mem_cons, List.not_mem_nil, or_false] at found
    rcases found with rfl | rfl | rfl | rfl <;> rfl
  have check := (early.2.2.2 PUnit.unit onlyFive solved first List.mem_cons_self).1
    (Check.equal (v 3) (.const (6 : ℕ))) List.mem_cons_self
  have impossible : (Term.const (5 : ℕ) : Term atoms) = .const (6 : ℕ) := check
  exact (by decide +kernel : (5 : ℕ) ≠ 6) (Term.const.inj impossible)

theorem before_tells_cannot_use_the_joint_solution_as_a_guard :
    evaluate .beforeTells prepared = none :=
  (refuses_exactly_when_not_admitted .beforeTells prepared).mpr notBefore

end Mettapedia.Machines.TIsa.Derivation.SymbolicBatch.Examples
