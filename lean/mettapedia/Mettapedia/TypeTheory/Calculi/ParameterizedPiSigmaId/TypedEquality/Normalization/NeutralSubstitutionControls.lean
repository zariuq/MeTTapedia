import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.NeutralSubstitution
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.HeadFormControls

/-!
# Substituting neutral terms: a head-form inspection creates a redex

In the toy package of the head-form controls, the type case `tcase X d`
inspects `X` for a head form. At a variable it is neutral and weak-head
normal, since a variable is no head form. The rigid constant `k` is neutral,
and a head form: substituting it for the variable gives `tcase k d`, which
steps to `d`. So substituting neutral terms creates a weak-head redex in that
package (`headForm_not_neutralReflecting`), whose type case inspects a head
form rather than a constructor form.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization
namespace HeadFormControls

/-- The rigid constant `k` for the one variable. -/
def rigidSub : Sub Unit 1 0 := fun _ => .const k

/-- The rigid constant is neutral. -/
theorem rigidSub_neutral : NeutralSub roles rigidSub :=
  fun _ => .rigid (args := []) roles_k

/-- Substituting the rigid constant for the variable of the stuck type case
gives a redex. -/
theorem rigidSub_tcase_step :
    WhStep rules roles
      (Presentation.subst rigidSub (appSpine (.const tcase) [.var 0, .var 0])) (.const k) :=
  .root ⟨_, _, rfl, ⟨_, k_headView []⟩, rfl⟩

/-- **Substituting a neutral term creates a weak-head redex at a head-form
inspection**: the type case at a variable is weak-head normal, while its
instance at the rigid constant steps. -/
theorem headForm_not_neutralReflecting : ¬ NeutralReflecting rules roles := by
  intro reflecting
  obtain ⟨t', step⟩ := reflecting rigidSub_neutral rigidSub_tcase_step
  exact tcase_var_whnf 0 (.var 0) t' step

end HeadFormControls
end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
