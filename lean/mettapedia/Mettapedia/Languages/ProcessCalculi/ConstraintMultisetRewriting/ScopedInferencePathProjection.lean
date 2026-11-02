import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceScopedExecution
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceTracePaths

/-!
# Returned scoped inference receipts supply actual classifying paths

The situated data retain the entire native receipt and an initial physical
board. The receipt's concrete returned worklist answer supplies the existing
ordinary selected firing; the qualified path functor maps that exact edge.
External caller equations and the scope inventory remain on the retained
native receipt, even though the protected proof view erases them.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ScopedInferencePathProjection

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.GSLT.LanguageDef Mettapedia.GSLT.LanguageDef.CertificateGSLT
open ScopedInferenceValues (base)
open InferenceJudgmentBoards InferenceTraceClassifying
open InferenceExecutionPaths InferencePathFunctor InferenceTracePaths
open _root_.CategoryTheory

variable {Local Shared : Type}

structure Situated (definition : ValidatedCalculusLanguageDef)
    (locals : Local → MetaArity base) (captures : Shared → MetaArity base)
    [DecidableEq Local] [DecidableEq Shared] [∀ result, DecidableEq (base.Op result)] where
  native : InferenceScopedExecution.Receipt definition locals captures
  prior : Board (InferenceScopedReturned.legacyBefore native.state)

namespace Situated

variable {definition : ValidatedCalculusLanguageDef}
  {locals : Local → MetaArity base} {captures : Shared → MetaArity base}
  [DecidableEq Local] [DecidableEq Shared] [∀ result, DecidableEq (base.Op result)]
  (situated : Situated definition locals captures)

def source : Vertex definition :=
  ⟨InferenceScopedReturned.legacyBefore situated.native.state, situated.prior⟩

noncomputable def target : Vertex definition :=
  ⟨InferenceScopedReturned.legacyAfter situated.native.state situated.native.readyRule situated.native.selection,
    (situated.native.projection situated.prior).1⟩

noncomputable def edge : Edge situated.source situated.target := ⟨true, situated.native.firing⟩

noncomputable def path : Quiver.Path situated.source situated.target :=
  Quiver.Hom.toPath (V := Vertex definition) situated.edge

theorem actual_origin_inputs_and_rows :
    situated.edge.actor = true ∧ situated.edge.firing.source = .inl situated.native.id ∧
      situated.edge.firing.inputs = .inl situated.native.arguments ∧
      situated.edge.firing.picked = situated.native.selection := by
  exact ⟨rfl, situated.native.source_inputs_selection⟩

theorem recovers_exact_firing : recoverBundle situated.path =
    ⟨[true], .cons situated.native.firing (.nil _)⟩ := rfl

theorem functor_is_actual_projection :
    (InferencePathFunctor.projection definition).map situated.path =
      (situated.native.projection situated.prior).2 := by
  rw [path, projection_single]
  change (situated.native.projection situated.prior).2 ≫
    changeBoard (situated.native.projection situated.prior).1
      (situated.native.projection situated.prior).1 = _
  rw [changeBoard_self]
  exact Category.comp_id
    (show situated.prior.context definition ⟶ (situated.native.projection situated.prior).1.context definition
      from (situated.native.projection situated.prior).2)

noncomputable def origin := Classical.choice situated.native.firing.kernel_origin

theorem source_instance :
    situated.origin.instance_.ruleId = situated.native.id ∧
      situated.origin.instance_.arguments = situated.native.arguments := by
  exact ⟨Sum.inl.inj (situated.origin.source_eq.symm.trans situated.native.source_inputs_selection.1),
    Sum.inl.inj (situated.origin.inputs_eq.symm.trans situated.native.source_inputs_selection.2.1)⟩

/-- The new categorical path publishes the actual source primitive node;
its premise vector is determined by physical selected occurrences. -/
theorem publishes_source_node :
    (InferencePathFunctor.projection definition).map situated.path ≫
        eqToHom (situated.origin.board_context situated.prior) ≫
        ClassifyingContext.sndProjection (situated.prior.context definition)
          ⟨[situated.origin.conclusion]⟩ =
      OpenDerivationList.cons (.byRule situated.origin.instance_ situated.origin.application
        (situated.origin.picked situated.prior)) .nil :=
  kernel_edge_publishes_source_rule situated.native.firing situated.prior

theorem selected_premise_position (port : Fin situated.origin.premises.length) :
    situated.prior.occurrenceAt (situated.origin.readPosition situated.prior port) =
      situated.origin.readOccurrence port :=
  situated.origin.position_reads_actual_occurrence situated.prior port

end Situated

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ScopedInferencePathProjection
