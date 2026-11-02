import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceReboarding
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceSelectedApplication
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceBoardReindexingControls

/-!
# Actual request/server paths and a nonidentity natural-isomorphism component

The server selects the second of two equal-valued physical rows. Canonical
embedding and recovery retain its actual actor, source and selected rows.
Reversing the board induces a genuine premise permutation, not an identity
chosen from the coincident judgment labels.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferencePathFunctorControls

open Mettapedia.GSLT.LanguageDef Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.GSLT.LanguageDef.CertificateGSLT.OpenApplicationControls (a b definition)
open InferenceSchemaActivation (action)
open InferenceSchemaKernel (Value locatedAction)
open InferenceRequestExecution (Occurrence label payload system)
open InferenceSelectedFirings InferenceJudgmentBoards InferenceTraceClassifying
open InferenceExecutionPaths InferencePathFunctor InferenceTracePaths InferenceReboarding
open InferenceProjectionControls.BoardControls
open InferenceBoardReindexingControls
open _root_.CategoryTheory

def reverseBoard {state : Configuration Value Occurrence} (board : Board state) : Board state where
  entries := board.entries.reverse
  distinct := by simpa only [List.map_reverse, List.nodup_reverse] using board.distinct
  occupied := by
    intro occurrence
    simpa only [List.map_reverse, List.mem_reverse] using board.occupied occurrence
  readback := fun entry member => board.readback entry (List.mem_reverse.mp member)
  supported := fun entry member => board.supported entry (List.mem_reverse.mp member)

def reverseChoice : Choice definition := fun vertex => reverseBoard vertex.board
def doubledVertex : Vertex definition := ⟨doubled, doubledBoard⟩

theorem natural_iso_component_is_not_identity :
    (boardChoiceIso reverseChoice).hom.app doubledVertex ≠
      𝟙 (doubledBoard.context definition) := by
  change (doubledBoard.reorder reversedBoard).interpret definition ≠ 𝟙 (doubledBoard.context definition)
  exact permutation_is_not_identity

theorem duplicate_identity_cannot_supply_a_vertex_board (vertex : Vertex definition) :
    vertex.board.entries ≠ [(firstRow, a), (firstRow, a)] := by
  intro same
  have distinct := vertex.board.distinct
  rw [same] at distinct
  exact duplicate_identity_is_not_a_board distinct

theorem actual_client_server_path :
    ∃ (middle after : Configuration Value Occurrence)
      (client : SelectedFiring definition false doubled middle)
      (server : SelectedFiring definition true middle after),
      server.source = .inl ⟨"ab"⟩ ∧ server.inputs = .inl [] ∧ server.picked.read = [secondRow] ∧
      let trace : SelectedRun definition doubled [false, true] after := .cons client (.cons server (.nil after))
      ∃ path : Quiver.Path doubledVertex (⟨after, (trace.project doubledBoard).1⟩ : Vertex definition),
        actors path = [false, true] ∧
        recoverBundle path = ⟨[false, true], trace⟩ ∧
        (system definition).Run payload doubled [false, true] after ∧
        (projection definition).map path = (trace.project doubledBoard).2 ∧
        (projection definition).map path ≫
            (boardChoiceIso reverseChoice).hom.app (⟨after, (trace.project doubledBoard).1⟩ : Vertex definition) =
          (boardChoiceIso reverseChoice).hom.app doubledVertex ≫
            (reboarding reverseChoice ⋙ projection definition).map path := by
  have background : locatedAction.Consistent doubled.equations :=
    ⟨action.identity, locatedAction.models_nil _⟩
  obtain ⟨middle, after, client, server, sourceEq, inputsEq, readsEq, _, _⟩ :=
    InferenceSelectedApplication.application_runs_with_reads definition first_application doubled background
      [secondRow] (by
        intro occurrence member
        have same : occurrence = secondRow := List.mem_singleton.mp member
        subst occurrence
        simp [doubled]) rfl
  let trace : SelectedRun definition doubled [false, true] after := .cons client (.cons server (.nil after))
  let path := embed trace doubledBoard
  exact ⟨middle, after, client, server, sourceEq, inputsEq, readsEq,
    path, actors_embed trace doubledBoard,
    recover_embed trace doubledBoard, trace.ordinary, projection_embed trace doubledBoard,
    (boardChoiceIso reverseChoice).hom.naturality path⟩

theorem embedded_actor_order_cannot_be_swapped
    {before after : Configuration Value Occurrence}
    (trace : SelectedRun definition before [false, true] after) (prior : Board before) :
    actors (embed trace prior) ≠ [true, false] := by
  rw [actors_embed]
  decide

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferencePathFunctorControls
