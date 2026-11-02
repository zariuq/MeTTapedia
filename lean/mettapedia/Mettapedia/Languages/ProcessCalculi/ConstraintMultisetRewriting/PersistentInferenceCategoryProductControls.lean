import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PersistentInferenceCategoryProducts
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PersistentInferenceCategoryControls

/-! # Cartesian observations retain physical theorem identities -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PersistentInferenceCategoryProductControls

open Mettapedia.GSLT.LanguageDef.CertificateGSLT.OpenApplicationControls (a b definition)
open InferenceSchemaActivation (judgment)
open InferenceRequestExecution (Occurrence)
open PersistentInference PersistentInferenceCategoryControls
open _root_.CategoryTheory

theorem first_projection_selects_the_first_physical_row :
    selectedReads (PersistentContext.product firstContext middleContext).board
      (PersistentContext.firstSelection firstContext middleContext) =
      [(0, (.judgments, judgment a))] := rfl

theorem second_projection_selects_the_second_physical_row :
    selectedReads (PersistentContext.product firstContext middleContext).board
      (PersistentContext.secondSelection firstContext middleContext) =
      [(1, (.judgments, judgment b))] := rfl

theorem diagonal_selects_one_occurrence_twice :
    selectedReads firstContext.board firstContext.diagonalSelection =
      [(0, (.judgments, judgment a)), (0, (.judgments, judgment a))] := rfl

theorem diagonal_has_two_ports_and_one_physical_row :
    firstContext.diagonalRepresentative.after.present.card = 1 ∧
      (PersistentContext.product firstContext firstContext).board.judgments.length = 2 :=
  ⟨seed_cardinality firstContext, rfl⟩

theorem weakening_keeps_the_original_physical_store :
    firstContext.toEmptyRepresentative.after = firstContext.state := rfl

theorem no_physical_steps_are_used_for_structural_maps :
    firstContext.diagonalRepresentative.actors = [] ∧
      firstContext.toEmptyRepresentative.actors = [] ∧
      (PersistentContext.firstRepresentative firstContext middleContext).actors = [] ∧
      (PersistentContext.secondRepresentative firstContext middleContext).actors = [] :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem both_diagonal_projections_are_the_actual_identity_morphism :
    firstContext.diagonal ≫ PersistentContext.firstProjection firstContext firstContext = 𝟙 firstContext ∧
      firstContext.diagonal ≫ PersistentContext.secondProjection firstContext firstContext = 𝟙 firstContext :=
  ⟨PersistentContext.diagonal_first firstContext, PersistentContext.diagonal_second firstContext⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PersistentInferenceCategoryProductControls
