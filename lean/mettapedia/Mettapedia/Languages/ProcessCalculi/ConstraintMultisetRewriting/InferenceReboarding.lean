import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceTracePaths

/-!
# Physical-board choice induces an actual path functor and natural isomorphism

Reboarding preserves physical configurations and the entire selected firing
at every edge. Its proof comparison is the occurrence-identity permutation,
including nonidentity permutations of equal-valued physical rows.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceReboarding

open Mettapedia.GSLT.LanguageDef Mettapedia.GSLT.LanguageDef.CertificateGSLT
open InferenceJudgmentBoards InferenceTraceClassifying
open InferenceExecutionPaths InferencePathFunctor InferenceTracePaths
open _root_.CategoryTheory

variable {definition : ValidatedCalculusLanguageDef}

abbrev Choice (definition : ValidatedCalculusLanguageDef) :=
  ∀ vertex : Vertex definition, Board vertex.state

def reboard (choose : Choice definition) : Vertex definition ⥤q Vertex definition where
  obj vertex := ⟨vertex.state, choose vertex⟩
  map edge := ⟨edge.actor, edge.firing⟩

@[simp] theorem reboard_identity : reboard (definition := definition) (fun vertex => vertex.board) =
    𝟭q (Vertex definition) := rfl

theorem reboard_comp (first second : Choice definition) :
    reboard first ⋙q reboard second = reboard (fun vertex => second ⟨vertex.state, first vertex⟩) := rfl

def reboarding (choose : Choice definition) : Paths (Vertex definition) ⥤ Paths (Vertex definition) where
  obj vertex := (reboard choose).obj vertex
  map path := (reboard choose).mapPath path
  map_id _ := rfl
  map_comp first second := Prefunctor.mapPath_comp _ first second

set_option backward.isDefEq.respectTransparency.types false in
theorem reboarding_identity : reboarding (definition := definition) (fun vertex => vertex.board) =
    𝟭 (Paths (Vertex definition)) := by
  refine _root_.CategoryTheory.Functor.hext (fun _ => rfl) ?_
  intro source target path
  change HEq ((reboard (fun vertex : Vertex definition => vertex.board)).mapPath path) path
  rw [reboard_identity]
  exact heq_of_eq (Prefunctor.mapPath_id path)

set_option backward.isDefEq.respectTransparency.types false in
theorem reboarding_comp (first second : Choice definition) :
    reboarding first ⋙ reboarding second =
      reboarding (fun vertex => second ⟨vertex.state, first vertex⟩) := by
  refine _root_.CategoryTheory.Functor.hext (fun _ => rfl) ?_
  intro source target path
  exact heq_of_eq (Prefunctor.mapPath_comp_apply (reboard first) (reboard second) path).symm

theorem reboarding_recovers (choose : Choice definition) {source target : Vertex definition}
    (path : Quiver.Path source target) :
    recoverBundle ((reboard choose).mapPath path) = recoverBundle path := by
  induction path with
  | nil => rfl
  | @cons middle target past edge earlier =>
      change InferenceTracePaths.append (recoverBundle ((reboard choose).mapPath past))
          ⟨[edge.actor], .cons edge.firing (.nil target.state)⟩ =
        InferenceTracePaths.append (recoverBundle past)
          ⟨[edge.actor], .cons edge.firing (.nil target.state)⟩
      rw [earlier]
      rfl

theorem edge_square (choose : Choice definition) {source target : Vertex definition}
    (edge : Edge source target) :
    changeBoard source.board (choose source) ≫ (edgeProjection definition).map ((reboard choose).map edge) =
      (edgeProjection definition).map edge ≫ changeBoard target.board (choose target) := by
  let first := projectFiring edge.firing source.board
  let second := projectFiring edge.firing (choose source)
  have afterSquare : changeBoard (definition := definition) first.1 second.1 ≫
      changeBoard second.1 (choose target) =
        changeBoard first.1 target.board ≫ changeBoard target.board (choose target) :=
    (changeBoard_comp first.1 second.1 (choose target)).trans
      (changeBoard_comp first.1 target.board (choose target)).symm
  exact ReadOnlyContextExtension.paste_squares
    (changeBoard source.board (choose source)) (changeBoard first.1 second.1)
    (changeBoard target.board (choose target)) first.2 second.2
    (changeBoard first.1 target.board) (changeBoard second.1 (choose target))
    (InferenceTraceNaturality.firing_conjugacy edge.firing source.board (choose source)) afterSquare

theorem path_square (choose : Choice definition) {source target : Vertex definition}
    (path : Quiver.Path source target) :
    changeBoard source.board (choose source) ≫
        (projection definition).map ((reboard choose).mapPath path) =
      (projection definition).map path ≫ changeBoard target.board (choose target) := by
  induction path with
  | nil =>
      change changeBoard source.board (choose source) ≫ 𝟙 _ =
        𝟙 _ ≫ changeBoard source.board (choose source)
      rw [Category.comp_id, Category.id_comp]
  | @cons middle target past edge earlier =>
      change changeBoard source.board (choose source) ≫
          (Paths.lift (edgeProjection definition)).map
            (((reboard choose).mapPath past).cons ((reboard choose).map edge)) =
        (Paths.lift (edgeProjection definition)).map (past.cons edge) ≫
          changeBoard target.board (choose target)
      rw [Paths.lift_cons, Paths.lift_cons]
      exact ReadOnlyContextExtension.paste_squares
        (changeBoard source.board (choose source)) (changeBoard middle.board (choose middle))
        (changeBoard target.board (choose target))
        ((projection definition).map past)
        ((projection definition).map ((reboard choose).mapPath past))
        ((edgeProjection definition).map edge) ((edgeProjection definition).map ((reboard choose).map edge))
        earlier (edge_square choose edge)

noncomputable def boardChoiceIso (choose : Choice definition) :
    projection definition ≅ reboarding choose ⋙ projection definition :=
  NatIso.ofComponents (fun vertex => vertex.board.reorderingIso definition (choose vertex))
    (fun path => (path_square choose path).symm)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceReboarding
