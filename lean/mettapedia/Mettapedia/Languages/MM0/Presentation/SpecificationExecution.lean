import Mettapedia.Languages.MM0.Presentation.SpecificationMatching

/-! # Specification alignment executes the actual sequential admission checks -/

set_option autoImplicit false
set_option maxRecDepth 2048

namespace Mettapedia.Languages.MM0.Presentation.ComputationalSpecification

open Kernel ComputationalAdmission
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

local notation "P" => specificationProgram
local notation "A" => specificationEquations
local notation "H" => dataEqualityHost

private theorem admitted_computes (theory : Option Theory) (pending : List SpecificationEntry) :
    Applies P H "mm0:spec-admitted" [encodeTheoryResult theory, encodeEntries pending]
      (encodeStateResult (do
        let next ← theory
        pure ⟨next, pending⟩)) := by
  cases theory <;> exact ⟨3, by rw [specification_apply _ (by decide)]; rfl⟩

private theorem permitted_computes (pending : Option (List SpecificationEntry))
    (theory : Theory) (admission : Admission) :
    Applies P H "mm0:spec-permitted" [encodePendingResult pending, encodeTheory theory, encodeAdmission admission]
      (encodeStateResult (do
        let remaining ← pending
        let next ← theory.step? admission
        pure ⟨next, remaining⟩)) := by
  cases pending with
  | none => exact ⟨1, by rw [specification_apply _ (by decide)]; rfl⟩
  | some remaining =>
      refine specification_equation (equation := A[19]) (by decide) (by rfl) (by rfl) ?_
      refine Evaluates.call (by simp [Special]) (.cons ?_ (.cons (.variable (by rfl)) .nil))
        (admitted_computes (theory.step? admission) remaining)
      exact Evaluates.call (by simp [Special])
        (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))
        (admission_suffix_reused _ (by decide) _ _ (ComputationalAdmission.step_computes theory admission))

theorem step_computes (state : SpecificationAdmission.State) (declaration : ProofDeclaration) :
    Applies P H "mm0:spec-step" [encodeState state, encodeProofDeclaration declaration]
      (encodeStateResult (SpecificationAdmission.step? state declaration)) := by
  let pending : Option (List SpecificationEntry) := if declaration.isLocal then
      if ProofDeclaration.auxiliary declaration.admission then some state.pending else none
    else match state.pending with
      | [] => none
      | expected :: remaining => if expected.checkMatch declaration.admission then some remaining else none
  have same : SpecificationAdmission.step? state declaration = (do
      let remaining ← pending
      let next ← state.theory.step? declaration.admission
      pure ⟨next, remaining⟩) := by
    cases flag : declaration.isLocal <;> cases rest : state.pending <;>
      simp [SpecificationAdmission.step?, pending, flag, rest]
    all_goals split <;> simp_all
  rw [same]
  refine specification_equation (equation := A[17]) (by decide) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special])
    (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))
    (permitted_computes pending state.theory declaration.admission)
  exact Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))
    (pending_computes state.pending declaration)

private theorem run_start (state : SpecificationAdmission.State) (declarations : List ProofDeclaration)
    (result : Term)
    (next : Applies P H "mm0:spec-run-view"
      [listView (declarations.map encodeProofDeclaration), encodeState state] result) :
    Applies P H "mm0:spec-run" [encodeState state, encodeProofDeclarations declarations] result := by
  refine specification_equation (equation := A[22]) (by decide) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special]) (.cons ?_ (.cons (.variable (by rfl)) .nil)) next
  exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil) (.primitive (by rfl) (by rfl))

private theorem run_next (state : SpecificationAdmission.State) (declarations : List ProofDeclaration)
    (result : Term)
    (next : Applies P H "mm0:spec-run" [encodeState state, encodeProofDeclarations declarations] result) :
    Applies P H "mm0:spec-run-next" [encodeStateResult (some state), encodeProofDeclarations declarations] result := by
  refine specification_equation (equation := A[26]) (by decide) (by rfl) (by rfl) ?_
  exact Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) next

theorem run_computes (state : SpecificationAdmission.State) (declarations : List ProofDeclaration) :
    Applies P H "mm0:spec-run" [encodeState state, encodeProofDeclarations declarations]
      (encodeStateResult (SpecificationAdmission.run? state declarations)) := by
  induction declarations generalizing state with
  | nil =>
      apply run_start
      exact ⟨2, by rw [specification_apply _ (by decide)]; rfl⟩
  | cons first rest ih =>
      apply run_start
      refine specification_equation (equation := A[24]) (by decide) (by rfl) (by rfl) ?_
      refine Evaluates.call
        (values := [encodeStateResult (SpecificationAdmission.step? state first), encodeProofDeclarations rest])
        (by simp [Special]) (.cons ?_ (.cons (.variable (by rfl)) .nil)) ?_
      · exact Evaluates.call (by simp [Special])
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) (step_computes state first)
      · cases computed : SpecificationAdmission.step? state first with
        | none =>
            simp only [computed, SpecificationAdmission.run?, encodeStateResult, Option.map_none, encodeLookupResult]
            exact ⟨1, by rw [specification_apply _ (by decide)]; rfl⟩
        | some next =>
            simpa [SpecificationAdmission.run?, computed] using run_next next rest _ (ih next)

private theorem finished_computes (pending : List SpecificationEntry) (theory : Theory) :
    Applies P H "mm0:spec-finished" [listView (pending.map encodeEntry), encodeTheory theory]
      (encodeTheoryResult (if pending.isEmpty then some theory else none)) := by
  cases pending <;> exact ⟨2, by rw [specification_apply _ (by decide)]; rfl⟩

private theorem finish_computes (state : Option SpecificationAdmission.State) :
    Applies P H "mm0:spec-finish" [encodeStateResult state]
      (encodeTheoryResult (do
        let result ← state
        if result.pending.isEmpty then some result.theory else none)) := by
  cases state with
  | none => exact ⟨1, by rw [specification_apply _ (by decide)]; rfl⟩
  | some state =>
      refine specification_equation (equation := A[29]) (by decide) (by rfl) (by rfl) ?_
      refine Evaluates.call (by simp [Special]) (.cons ?_ (.cons (.variable (by rfl)) .nil))
        (finished_computes state.pending state.theory)
      exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil) (.primitive (by rfl) (by rfl))

theorem verify_computes (specification : List SpecificationEntry) (declarations : List ProofDeclaration) :
    Applies P H "mm0:spec-verify" [encodeEntries specification, encodeProofDeclarations declarations]
      (encodeTheoryResult (SpecificationAdmission.verify? specification declarations)) := by
  refine specification_equation (equation := A[27]) (by decide) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special]) (.cons ?_ .nil)
    (finish_computes (SpecificationAdmission.run? ⟨{}, specification⟩ declarations))
  refine Evaluates.call (by simp [Special]) (.cons ?_ (.cons (.variable (by rfl)) .nil))
    (run_computes ⟨{}, specification⟩ declarations)
  refine Evaluates.list (.cons (.symbol _ _ _ _) (.cons ?_ (.cons (.variable (by rfl)) .nil)))
  exact Evaluates.list (.cons (.symbol _ _ _ _)
    (.cons (Evaluates.list .nil) (.cons (Evaluates.list .nil) (.cons (Evaluates.list .nil) (.cons (Evaluates.list .nil) .nil)))))

end Mettapedia.Languages.MM0.Presentation.ComputationalSpecification
