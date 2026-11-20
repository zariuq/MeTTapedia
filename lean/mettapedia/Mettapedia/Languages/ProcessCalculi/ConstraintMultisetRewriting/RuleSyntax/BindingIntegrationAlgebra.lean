import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflQuotientControls

/-!
# Equality and observation at a transform instance

The existing quotient frame supplies a substitution-stable ACU congruence,
including inside unquoted terms. It admits actual firings. What cannot be
transported through that equality is an observer that always returns the
written left operand of a parallel pair. The obstruction concerns that
observer, rather than the availability of rewriting modulo equations.

The positive control below uses the quotient frame's actual COMM rule,
opening, occurrence selection and admission. No executable AC solver or
correspondence with another language is inferred from semantic admission.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.BindingIntegration.Algebra

open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus (par)
open MeTTaCalculus.Corrected.BagControls (atomA atomB)
open StepWeb.ReflQuotient

/-- The selected congruence is respected by every structural substitution,
including for open, unquoted parallel terms. -/
theorem ac_substitution (assignment : MeTTaOperationsComm.PSubst) (left right : Pattern) :
    BagLaws (MeTTaOperationsComm.psubst assignment (par left right))
      (MeTTaOperationsComm.psubst assignment (par right left)) :=
  bagLaws_psubst assignment (bagLaws_par_comm left right)

/-- An order-sensitive choice cannot be read from an AC-equivalence class.
Other observers, canonical representatives and relational match enumeration
are not ruled out. -/
theorem no_written_left_projection :
    ¬ ∃ project : Pattern → Pattern,
      (∀ {left right}, BagLaws left right → BagLaws (project left) (project right)) ∧
      (∀ left right, project (par left right) = left) := by
  rintro ⟨project, respects, written⟩
  have same := respects (bagLaws_par_comm atomA atomB)
  rw [written, written] at same
  have different : ¬ BagLaws atomA atomB := by decide +kernel
  exact different same

/-- A real quotient-frame firing exists although the written-left observer
has no interpretation at that equality. -/
theorem actual_ac_firing_and_observer_boundary :
    (RuleSyntax.step QX ℕ QE StepWeb.FiniteProgram.program).Admits
      (s := OneFrame.embed StepWeb.ReflQuotient.Controls.rowsNames
        StepWeb.Comm.Controls.start)
      (quotientFiring (StepWeb.FiniteProgram.commAt
        (StepWeb.Comm.renameBy StepWeb.FiniteProgram.Controls.rename) 0 1 2 3)) ∧
    ¬ ∃ project : Pattern → Pattern,
      (∀ {left right}, BagLaws left right → BagLaws (project left) (project right)) ∧
      (∀ left right, project (par left right) = left) :=
  ⟨StepWeb.ReflQuotient.Controls.names_admitted_at_quotient, no_written_left_projection⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.BindingIntegration.Algebra
