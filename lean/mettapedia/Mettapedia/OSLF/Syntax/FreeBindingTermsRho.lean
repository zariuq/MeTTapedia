import Mettapedia.OSLF.Syntax.FreeBindingTerms
import Mettapedia.OSLF.Syntax.RhoCommunicationSchema

/-!
# The rho binding signature inhabits the free raw-term construction

The generic initial algebra reads rho's actual declared input binder. Its
independent operator-count interpretation distinguishes a process with a
name-bound continuation from the null process. The example concerns the raw
term rung; rho's equations and COMM rule are further presentation data.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.FreeBindingTerms.RhoExample

open Mettapedia.OSLF.Binding.RhoSchema

/-- The input continuation drops the name bound by this input. -/
def boundDrop : Term sig [Srt.nm] Srt.pr :=
  .op Op.drp (.cons (.var .zero) .nil)

def boundInput : Term sig [] Srt.pr :=
  .op Op.inp (.cons chan (.cons boundDrop .nil))

theorem count_null : countTerm nilP = 1 := rfl

theorem count_bound_input : countTerm boundInput = 4 := rfl

/-- The fold witnesses a genuine distinction in the authored binder-bearing
syntax, independently of later equations and operational rules. -/
theorem bound_input_ne_null : boundInput ≠ nilP := by
  intro equality
  have counted := congrArg countTerm equality
  rw [count_bound_input, count_null] at counted
  omega

end Mettapedia.OSLF.Binding.FreeBindingTerms.RhoExample
