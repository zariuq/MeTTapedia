import Mettapedia.Languages.LambdaCalculus.NamePassingEnvironment

/-!
# Persistent environment and scope controls

The closed self-application program fetches its definition, calls the released
function and fetches the same definition again. Nested definitions keep their
fresh reference distinct from the original one. The controls concern the
independently specified source semantics.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.LambdaCalculus.NamePassing.Environment.Controls

open Mettapedia.OSLF.Binding

abbrev Term (Γ : List Unit) := Expr () Γ

def omegaValue : Term [] := .lam (.app (.var .zero) .zero)
def loopingDefinition : Term [] := .defn omegaValue (.app (.var .zero) .zero)
def releasedCall : Term [] :=
  .defn omegaValue (.app (NamePassing.weaken omegaValue) .zero)

theorem first_fetch : Step .environmentFetch loopingDefinition releasedCall :=
  .environmentFetch omegaValue (.app .zero (.here .zero (NamePassing.weaken omegaValue)))

theorem retained_reference_called : Step .beta releasedCall loopingDefinition :=
  .defn omegaValue (.beta (.app (.var .zero) .zero) .zero)

/-- The same retained definition can service another fetch. -/
theorem second_fetch : Step .environmentFetch loopingDefinition releasedCall := first_fetch

/-- An enclosing definition can be fetched below a fresh nested definition;
the old reference occupies slot one, and the fresh one occupies slot zero. -/
theorem nested_definition_outer_fetch (stored : Term [()]) :
    FetchAt (.zero : Var [()] ()) (NamePassing.weaken omegaValue)
      (.defn stored (.var (.succ .zero)))
      (.defn stored (NamePassing.weaken (NamePassing.weaken omegaValue))) :=
  .defn stored (.here (.succ .zero) (NamePassing.weaken (NamePassing.weaken omegaValue)))

theorem fresh_reference_does_not_fetch_outer {target : Term [(), ()]} :
    ¬ FetchAt (.succ .zero) (NamePassing.weaken (NamePassing.weaken omegaValue))
      (.var .zero) target := by
  apply fetch_distinct_variable
  intro equal
  cases equal

theorem stored_lambda_remains_suspended {target : Term [()]} :
    ¬ FetchAt (.zero : Var [()] ()) (NamePassing.weaken omegaValue)
      (NamePassing.weaken omegaValue) target :=
  fetch_not_under_lambda _ _ _

theorem no_lambda_body_communication {kind : Action} {target : Term []} :
    ¬ Step kind omegaValue target := lambda_no_step _

end Mettapedia.Languages.LambdaCalculus.NamePassing.Environment.Controls
