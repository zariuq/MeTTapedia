import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentFullNonVacuityInstance

/-!
# The multi-frame instance in the point package: controls

The firings of `DependentFull.NonVacuity`, translated into the dependent full step:

* **Positive** (`take_translated_admitted`, `take_translated_results`): the take `m(x)` on the row
  `n(x)` is admitted by the dependent full step at the translated state; the decision comes from the
  actual run of the full solver, with no endomorphism condition, and the results correspond.
* **Negative** (`outside_translated_refused`): the take `F(x)` on the row `y` is refused by the
  dependent full step; the refutation comes from the actual run.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
namespace DependentFull.NonVacuity

open ContextualDependentFibre ContextualDependentFibre.Controls Translation
open PointPackage

/-- **The translated take is admitted by the dependent full step**, through the solver's run. -/
theorem take_translated_admitted :
    (step setting.levels Nat).Admits
      (translateEquationFiring (S := setting) facts roots heads church names realization takeFiring) :=
  (translateEquation_admits_iff_of_full (S := setting) facts roots heads church names realization takeFiring
    rigid complete algebra declared choices reducer (fun _ => none) point_normalizes certifyNormal
    headTypingUnique sortInjective point_closed @operatorInjective 16 2 take_decided).mp
    take_admitted_second_order

/-- **The results correspond.** -/
theorem take_translated_results :
    (step setting.levels Nat).result
        (translateEquationFiring (S := setting) facts roots heads church names realization takeFiring)
        take_translated_admitted =
      translateLocal (S := setting) facts roots heads church names realization
        (second.result takeFiring take_admitted_second_order) :=
  translateEquation_result (S := setting) facts roots heads church names realization takeFiring
    take_admitted_second_order take_translated_admitted

/-- **The translated take `F(x)` on the row `y` is refused by the dependent full step.** -/
theorem outside_translated_refused :
    ¬ (step setting.levels Nat).Admits
      (translateEquationFiring (S := setting) facts roots heads church names realization outsideFiring) :=
  fun admitted => refuted_case_refused.2.1
    ((translateEquation_admits_iff_of_full (S := setting) facts roots heads church names realization outsideFiring
      rigid complete algebra declared choices reducer (fun _ => none) point_normalizes certifyNormal
      headTypingUnique sortInjective point_closed @operatorInjective 16 2 outside_decided).mpr admitted)

end DependentFull.NonVacuity

#print axioms DependentFull.NonVacuity.take_translated_admitted
#print axioms DependentFull.NonVacuity.take_translated_results
#print axioms DependentFull.NonVacuity.outside_translated_refused

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
