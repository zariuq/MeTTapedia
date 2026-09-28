import Mettapedia.OSLF.Syntax.BindingSubstitutionAlgebra
import Mettapedia.OSLF.Syntax.RhoCommunicationSchema

/-!
# A rho binder control for semantic environment lifting

The actual rho input binder adds one name before the caller's ambient names.
The semantic substitution lift retains an older name past that binder. The
selected control is an open value: it rules out the corresponding capture.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.BindingSubstitutionAlgebra.RhoExample

open Mettapedia.OSLF.Binding.RhoSchema

/-- In the target context, the supplied name is the second ambient name. -/
def chooseSecondName : Sub sig [Srt.nm] [Srt.nm, Srt.nm]
  | _, .zero => .var (.succ .zero)

/-- The name newly bound by input is index zero. The supplied ambient name
remains beyond it, at index two in the extended target context. -/
theorem supplied_name_survives_input :
    (terms sig).liftEnvironment chooseSecondName [Srt.nm] Srt.nm
      (Var.succ Var.zero) =
        (Term.var (S := sig) (Var.succ (Var.succ Var.zero))) := rfl

theorem supplied_name_not_captured :
    (terms sig).liftEnvironment chooseSecondName [Srt.nm] Srt.nm
      (Var.succ Var.zero) ≠
        (Term.var (S := sig) Var.zero) := by
  rw [supplied_name_survives_input]
  intro equality
  cases equality

end Mettapedia.OSLF.Binding.BindingSubstitutionAlgebra.RhoExample
