import Mettapedia.Languages.MM0.Presentation.AdmissionChecks

/-! # Checked storage updates and complete MM0 admission runs -/

set_option autoImplicit false
set_option maxRecDepth 2048

namespace Mettapedia.Languages.MM0.Presentation.ComputationalAdmission

open Kernel ComputationalContext ComputationalDeclaration
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

local notation "P" => admissionProgram
local notation "A" => admissionEquations
local notation "H" => dataEqualityHost

/-- This internal operation constructs the candidate update. Its caller checks
authorization before reaching it. -/
theorem publish_computes (theory : Theory) (admission : Admission) :
    Applies P H "mm0:admission-publish" [encodeTheory theory, encodeAdmission admission]
      (encodeTheoryResult (some (admission.insert theory))) := by
  cases admission <;> exact ⟨5, by rw [admission_apply _ (by decide)]; rfl⟩

theorem checked_computes (allowed : Bool) (theory : Theory) (admission : Admission) :
    Applies P H "mm0:admission-checked" [boolean allowed, encodeTheory theory, encodeAdmission admission]
      (encodeTheoryResult (if allowed then some (admission.insert theory) else none)) := by
  cases allowed with
  | false => exact ⟨1, by rw [admission_apply _ (by decide)]; rfl⟩
  | true =>
      refine admission_equation (equation := A[11]) (by decide) (by rfl) (by rfl) ?_
      exact Evaluates.call (by simp [Special])
        (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) (publish_computes theory admission)

theorem step_computes (theory : Theory) (admission : Admission) :
    Applies P H "mm0:admission-step" [encodeTheory theory, encodeAdmission admission]
      (encodeTheoryResult (theory.step? admission)) := by
  refine admission_equation (equation := A[9]) (by decide) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special])
    (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))
    (checked_computes (admission.check theory) theory admission)
  exact Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) (check_computes theory admission)

private theorem run_start (theory : Theory) (admissions : List Admission) (result : Term)
    (next : Applies P H "mm0:admission-run-view"
      [listView (admissions.map encodeAdmission), encodeTheory theory] result) :
    Applies P H "mm0:admission-run" [encodeTheory theory, encodeAdmissions admissions] result := by
  refine admission_equation (equation := A[17]) (by decide) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special]) (.cons ?_ (.cons (.variable (by rfl)) .nil)) next
  exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil) (.primitive (by rfl) (by rfl))

private theorem run_next (theory : Theory) (admissions : List Admission) (result : Term)
    (next : Applies P H "mm0:admission-run" [encodeTheory theory, encodeAdmissions admissions] result) :
    Applies P H "mm0:admission-run-next" [encodeTheoryResult (some theory), encodeAdmissions admissions] result := by
  refine admission_equation (equation := A[21]) (by decide) (by rfl) (by rfl) ?_
  exact Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) next

theorem run_computes (theory : Theory) (admissions : List Admission) :
    Applies P H "mm0:admission-run" [encodeTheory theory, encodeAdmissions admissions]
      (encodeTheoryResult (theory.run? admissions)) := by
  induction admissions generalizing theory with
  | nil =>
      apply run_start
      exact ⟨2, by rw [admission_apply _ (by decide)]; rfl⟩
  | cons first rest ih =>
      apply run_start
      refine admission_equation (equation := A[19]) (by decide) (by rfl) (by rfl) ?_
      refine Evaluates.call
        (values := [encodeTheoryResult (theory.step? first), encodeAdmissions rest])
        (by simp [Special]) (.cons ?_ (.cons (.variable (by rfl)) .nil)) ?_
      · exact Evaluates.call (by simp [Special])
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) (step_computes theory first)
      · cases computed : theory.step? first with
        | none =>
            simp only [computed, Theory.run?, encodeTheoryResult, Option.map_none, encodeLookupResult]
            exact ⟨1, by rw [admission_apply _ (by decide)]; rfl⟩
        | some next =>
            simpa [Theory.run?, computed] using run_next next rest _ (ih next)

theorem start_computes (admissions : List Admission) :
    Applies P H "mm0:admission-start" [encodeAdmissions admissions]
      (encodeTheoryResult (Theory.run? {} admissions)) := by
  refine admission_equation (equation := A[22]) (by decide) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special]) (.cons ?_ (.cons (.variable (by rfl)) .nil)) (run_computes {} admissions)
  exact Evaluates.list (.cons (.symbol _ _ _ _)
    (.cons (Evaluates.list .nil) (.cons (Evaluates.list .nil) (.cons (Evaluates.list .nil) (.cons (Evaluates.list .nil) .nil)))))

end Mettapedia.Languages.MM0.Presentation.ComputationalAdmission
