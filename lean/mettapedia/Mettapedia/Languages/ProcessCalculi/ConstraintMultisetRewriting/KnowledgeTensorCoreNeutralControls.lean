import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.KnowledgeTensorCoreFirstOrderPairing
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.KnowledgeTensorCoreControls

/-!
# Controls for neutral states and for the checks of a word

* `the_reads_word_passes_beside_nine`, `the_absence_word_fails_beside_nine`: the checks of a
  word beside the occurrence `9` pass for the run that reads and fail for the firing that checks
  the absence of `9`.
* `the_absence_run_beside_nothing_and_nine`: beside the pair of the empty configuration and the
  occurrence `9` the absence run is not in its grade; the law of pairs reduces this to the run
  placed beside the empty configuration.

* `the_reads_run_is_in_its_grade_beside_nothing`: beside the empty configuration the run that
  reads is in its own grade.
* `the_absence_run_is_in_its_grade_beside_nothing`: so is the firing that checks the absence of
  the occurrence `9`.
* `nine_is_not_neutral`: the configuration that holds the occurrence `9` is not neutral: the
  firing that checks its absence is admitted alone and refused beside it.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.KnowledgeTensorCore.Controls

open AnnotatedRuns (Firing firstOrder firstOrderTransport)
open FirstOrderNativeRuns
open KnowledgeTensorFirstOrderControls (plain one)

theorem the_reads_run_is_in_its_grade_beside_nothing :
    (contextualRunInterpretation plain id).Checks (left := one)
      (right := AnnotatedRuns.unitConfiguration) PUnit.unit readsRun :=
  checks_of_neutral (FirstOrder.unit_neutral plain id) PUnit.unit readsRun

theorem the_absence_run_is_in_its_grade_beside_nothing :
    (contextualRunInterpretation plain id).Checks (left := one)
      (right := AnnotatedRuns.unitConfiguration) PUnit.unit unlessNineRun :=
  checks_of_neutral (FirstOrder.unit_neutral plain id) PUnit.unit unlessNineRun

/-- **A state that a check can see is not neutral.** -/
theorem nine_is_not_neutral : ¬ Neutral (contextualRunInterpretation plain id) nine :=
  fun neutral => unless_nine_refused_beside_nine
    ((valid_tensor_iff plain id unlessNineFiring unless_nine_admitted).mpr
      (neutral (left := one) PUnit.unit unlessNineFiring unless_nine_admitted).2)

theorem the_reads_word_passes_beside_nine :
    FirstOrder.WordChecks plain id nine one (sites plain id readsRun) :=
  (FirstOrder.checks_iff_wordChecks plain id nine readsRun).mp
    ((exists_places_iff_checks (contextualRunInterpretation plain id) (left := one) (right := nine)
      PUnit.unit readsRun).mp reads_has_a_placed_run)

theorem the_absence_word_fails_beside_nine :
    ¬ FirstOrder.WordChecks plain id nine one (sites plain id unlessNineRun) :=
  fun passes => absence_grade_is_not_structural.2
    ((FirstOrder.checks_iff_wordChecks plain id nine unlessNineRun).mpr passes)

/-- **The law of pairs at the absence check.** Beside the pair of the empty configuration and the
occurrence `9` the absence run is not in its grade. -/
theorem the_absence_run_beside_nothing_and_nine :
    ¬ (contextualRunInterpretation plain id).Checks (left := one)
      (right := AnnotatedRuns.tensor AnnotatedRuns.unitConfiguration nine) PUnit.unit
      unlessNineRun := by
  rw [AnnotatedRuns.tensor_unit_left]
  exact absence_grade_is_not_structural.2

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.KnowledgeTensorCore.Controls
