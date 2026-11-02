import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceExecutionPaths
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceTraceNaturality

/-!
# An actual functor from selected physical paths to source proof contexts

The edge arrow is the existing actual-activation projection, followed by
the occurrence-identity reordering to the chosen target board. Mathlib's
free-category lift supplies the functor. Its value on every path agrees
with recovery of the original selected source trace and terminal reordering.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferencePathFunctor

open Mettapedia.GSLT.LanguageDef Mettapedia.GSLT.LanguageDef.CertificateGSLT
open InferenceSchemaKernel (Value)
open InferenceRequestExecution (Occurrence)
open InferenceSelectedFirings InferenceJudgmentBoards InferenceTraceClassifying
open InferenceExecutionPaths
open _root_.CategoryTheory

variable {definition : ValidatedCalculusLanguageDef}

noncomputable def changeBoard {state : Configuration Value Occurrence} (first second : Board state) :
    first.context definition ⟶ second.context definition :=
  (first.reorder second).interpret definition

@[simp] theorem changeBoard_self {state : Configuration Value Occurrence} (board : Board state) :
    changeBoard (definition := definition) board board = 𝟙 (board.context definition) := by
  rw [changeBoard, Board.reorder_self, ContextMap.interpret_id]
  rfl

theorem changeBoard_comp {state : Configuration Value Occurrence} (first second third : Board state) :
    changeBoard (definition := definition) first second ≫ changeBoard second third = changeBoard first third := by
  change (first.reorder second).interpret definition ≫ (second.reorder third).interpret definition = _
  rw [← ContextMap.interpret_comp, Board.reorder_comp]
  rfl

noncomputable def toBoard {before after : Configuration Value Occurrence} {actors : List Bool}
    (trace : SelectedRun definition before actors after) (prior : Board before) (target : Board after) :
    prior.context definition ⟶ target.context definition :=
  (trace.project prior).2 ≫ changeBoard (trace.project prior).1 target

@[simp] theorem toBoard_nil {state : Configuration Value Occurrence} (first second : Board state) :
    toBoard (SelectedRun.nil (definition := definition) state) first second = changeBoard first second := by
  exact Category.id_comp _

private theorem compose_square {C : Type*} [Category* C] {a b c d e f : C}
    (head : a ⟶ b) (upper : b ⟶ c) (vertical : b ⟶ d) (lower : d ⟶ e)
    (right : c ⟶ e) (finish : e ⟶ f) (direct : c ⟶ f)
    (square : vertical ≫ lower = upper ≫ right) (triangle : right ≫ finish = direct) :
    (head ≫ vertical) ≫ (lower ≫ finish) = (head ≫ upper) ≫ direct := by
  calc
    (head ≫ vertical) ≫ (lower ≫ finish) = head ≫ ((vertical ≫ lower) ≫ finish) := by
      simp only [Category.assoc]
    _ = head ≫ ((upper ≫ right) ≫ finish) := by rw [square]
    _ = (head ≫ upper) ≫ (right ≫ finish) := by simp only [Category.assoc]
    _ = (head ≫ upper) ≫ direct := by rw [triangle]

theorem toBoard_append {before middle after : Configuration Value Occurrence}
    {firstActors secondActors : List Bool}
    (first : SelectedRun definition before firstActors middle)
    (second : SelectedRun definition middle secondActors after)
    (prior : Board before) (intermediate : Board middle) (target : Board after) :
    toBoard (first.append second) prior target = toBoard first prior intermediate ≫ toBoard second intermediate target := by
  let left := first.project prior
  let top := second.project left.1
  let bottom := second.project intermediate
  rw [toBoard, SelectedRun.project_append]
  change (left.2 ≫ top.2) ≫ changeBoard top.1 target =
    (left.2 ≫ changeBoard left.1 intermediate) ≫ (bottom.2 ≫ changeBoard bottom.1 target)
  exact (compose_square left.2 top.2 (changeBoard left.1 intermediate) bottom.2
    (changeBoard top.1 bottom.1) (changeBoard bottom.1 target) (changeBoard top.1 target)
    (InferenceTraceNaturality.trace_conjugacy second left.1 intermediate)
    (changeBoard_comp top.1 bottom.1 target)).symm

noncomputable def edgeProjection (definition : ValidatedCalculusLanguageDef) :
    Vertex definition ⥤q ClassifyingContext definition where
  obj vertex := vertex.board.context definition
  map {source} {target} edge :=
    (projectFiring edge.firing source.board).2 ≫
      changeBoard (projectFiring edge.firing source.board).1 target.board

noncomputable def projection (definition : ValidatedCalculusLanguageDef) :
    Paths (Vertex definition) ⥤ ClassifyingContext definition :=
  Paths.lift (edgeProjection definition)

theorem edge_is_original_trace {source target : Vertex definition} (edge : Edge source target) :
    (edgeProjection definition).map edge =
      toBoard (.cons edge.firing (.nil target.state)) source.board target.board := by
  simp only [edgeProjection, toBoard, SelectedRun.project, Category.comp_id]

@[simp] theorem projection_single {source target : Vertex definition} (edge : Edge source target) :
    (projection definition).map (Quiver.Hom.toPath (V := Vertex definition) edge) =
      (edgeProjection definition).map edge :=
  Paths.lift_toPath _ _

theorem projection_recovers {source target : Vertex definition} (path : Quiver.Path source target) :
    (projection definition).map path = toBoard (recover path) source.board target.board := by
  induction path with
  | nil =>
      change 𝟙 _ = (𝟙 _ ≫ changeBoard source.board source.board)
      rw [changeBoard_self, Category.id_comp]
  | @cons middle target past edge earlier =>
      change (Paths.lift (edgeProjection definition)).map (past.cons edge) = _
      rw [Paths.lift_cons]
      change (projection definition).map past ≫ (edgeProjection definition).map edge = _
      rw [earlier, edge_is_original_trace]
      exact (toBoard_append (recover past) (.cons edge.firing (.nil target.state))
        source.board middle.board target.board).symm

/-- The functor appends the original activated source rule, with its actual
selected premise positions. This is an equation of proof vectors. -/
theorem kernel_edge_publishes_source_rule {before after : Configuration Value Occurrence}
    (firing : SelectedFiring definition true before after) (prior : Board before) :
    let origin := Classical.choice firing.kernel_origin
    let edge : Edge (⟨before, prior⟩ : Vertex definition) ⟨after, origin.board prior⟩ := ⟨true, firing⟩
    (projection definition).map (Quiver.Hom.toPath (V := Vertex definition) edge) ≫
        eqToHom (origin.board_context prior) ≫
        ClassifyingContext.sndProjection (prior.context definition) ⟨[origin.conclusion]⟩ =
      OpenDerivationList.cons
        (.byRule origin.instance_ origin.application (origin.picked prior)) .nil := by
  dsimp only
  rw [projection_single]
  let origin := Classical.choice firing.kernel_origin
  change (origin.arrow prior ≫ changeBoard (origin.board prior) (origin.board prior)) ≫
    eqToHom (origin.board_context prior) ≫
      ClassifyingContext.sndProjection (prior.context definition) ⟨[origin.conclusion]⟩ = _
  rw [changeBoard_self, Category.comp_id]
  exact origin.publishes_actual_rule prior

/-- A canonical public-data edge induces the identity on protected proofs. -/
theorem client_edge_identity {before after : Configuration Value Occurrence}
    (firing : SelectedFiring definition false before after) (prior : Board before) :
    let origin := Classical.choice firing.client_origin
    let edge : Edge (⟨before, prior⟩ : Vertex definition) ⟨after, origin.board prior⟩ := ⟨false, firing⟩
    (projection definition).map (Quiver.Hom.toPath (V := Vertex definition) edge) =
      𝟙 (prior.context definition) := by
  dsimp only
  rw [projection_single]
  let origin := Classical.choice firing.client_origin
  change 𝟙 _ ≫ changeBoard (origin.board prior) (origin.board prior) = _
  rw [changeBoard_self, Category.id_comp]
  rfl

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferencePathFunctor
