import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceTraceClassifying
import Mathlib.CategoryTheory.PathCategory.Basic

/-!
# The existing selected physical inference graph and its free paths

Objects pair a physical configuration with a complete protected board.
Edges contain an actor and the existing selected firing, including its
computed source activation, selected rows and authority evidence. Paths use
Mathlib's free category and recover the original selected traces.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceExecutionPaths

open Mettapedia.GSLT.LanguageDef
open InferenceSchemaKernel (Value)
open InferenceRequestExecution (Occurrence payload system)
open InferenceSelectedFirings InferenceJudgmentBoards InferenceTraceClassifying
open _root_.CategoryTheory

structure Vertex (definition : ValidatedCalculusLanguageDef) where
  state : Configuration Value Occurrence
  board : Board state

structure Edge {definition : ValidatedCalculusLanguageDef} (source target : Vertex definition) where
  actor : Bool
  firing : SelectedFiring definition actor source.state target.state

instance graph (definition : ValidatedCalculusLanguageDef) : Quiver (Vertex definition) where
  Hom := Edge

variable {definition : ValidatedCalculusLanguageDef}

def actors {source : Vertex definition} : {target : Vertex definition} → Quiver.Path source target → List Bool
  | _, .nil => []
  | _, .cons past edge => actors past ++ [edge.actor]

def recover {source : Vertex definition} : {target : Vertex definition} →
    (path : Quiver.Path source target) →
      SelectedRun definition source.state (actors path) target.state
  | _, .nil => .nil source.state
  | _, .cons past edge => (recover past).append (.cons edge.firing (.nil _))

theorem ordinary {source target : Vertex definition} (path : Quiver.Path source target) :
    (system definition).Run payload source.state (actors path) target.state :=
  (recover path).ordinary

@[simp] theorem actors_nil (source : Vertex definition) : actors (Quiver.Path.nil (a := source)) = [] := rfl

@[simp] theorem actors_cons {source middle target : Vertex definition}
    (past : Quiver.Path source middle) (edge : Edge middle target) :
    actors (past.cons edge) = actors past ++ [edge.actor] := rfl

theorem actors_comp {source middle target : Vertex definition}
    (first : Quiver.Path source middle) (second : Quiver.Path middle target) :
    actors (first.comp second) = actors first ++ actors second := by
  induction second with
  | nil => simp [Quiver.Path.comp, actors]
  | cons past edge earlier => simp [Quiver.Path.comp, actors, earlier, List.append_assoc]

@[simp] theorem actors_single {source target : Vertex definition} (edge : Edge source target) :
    actors (Quiver.Hom.toPath (V := Vertex definition) edge) = [edge.actor] := rfl

@[simp] theorem recover_single {source target : Vertex definition} (edge : Edge source target) :
    recover (Quiver.Hom.toPath (V := Vertex definition) edge) = .cons edge.firing (.nil target.state) := rfl

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceExecutionPaths
