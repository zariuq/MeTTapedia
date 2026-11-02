import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceTraceNaturality
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceSelectedApplication
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceBoardReindexingControls

/-! # An actual request/server trace with a nonidentity physical permutation -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceTraceNaturalityControls

open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.GSLT.LanguageDef.CertificateGSLT.OpenApplicationControls (a b definition)
open InferenceSchemaActivation (action)
open InferenceSchemaKernel (locatedAction)
open InferenceRequestExecution (label)
open InferenceJudgmentBoards
open InferenceTraceClassifying
open InferenceProjectionControls.BoardControls
open InferenceBoardReindexingControls
open _root_.CategoryTheory

/-- The chosen physical second row is retained as the premise even when
the board is reversed. The canonical initial and terminal physical
permutations make the full real trace square commute. -/
theorem actual_trace_reindexes :
    ∃ after, ∃ trace : SelectedRun definition doubled [false, true] after,
      (doubledBoard.reorder reversedBoard).interpret definition ≫
          (trace.project reversedBoard).2 =
        (trace.project doubledBoard).2 ≫
          ((trace.project doubledBoard).1.reorder (trace.project reversedBoard).1).interpret definition ∧
      Nonempty (OpenDerivation definition [a, a] b) := by
  have background : locatedAction.Consistent doubled.equations :=
    ⟨action.identity, locatedAction.models_nil _⟩
  obtain ⟨middle, after, client, server, _, _, _, _, output, present, readback⟩ :=
    InferenceSelectedApplication.application_runs_with_reads definition first_application doubled background
      [secondRow] (by
        intro occurrence member
        have same : occurrence = secondRow := List.mem_singleton.mp member
        subst occurrence
        simp [doubled]) rfl
  let trace : SelectedRun definition doubled [false, true] after :=
    .cons client (.cons server (.nil after))
  refine ⟨after, trace, InferenceTraceNaturality.trace_conjugacy trace doubledBoard reversedBoard, ?_⟩
  exact ⟨trace.derive doubledBoard output present (congrArg Prod.fst readback) b readback⟩

/-- The commuting square above cannot be replaced with identity maps just
because the two initial judgment labels happen to agree. -/
theorem initial_comparison_is_genuinely_nonidentity :
    (doubledBoard.reorder reversedBoard).interpret definition ≠
      𝟙 (doubledBoard.context definition) := permutation_is_not_identity

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceTraceNaturalityControls
