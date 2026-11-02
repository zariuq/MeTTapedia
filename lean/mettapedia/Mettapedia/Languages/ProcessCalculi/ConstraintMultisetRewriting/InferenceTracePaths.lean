import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferencePathFunctor

/-!
# Canonical path presentation of each existing selected trace

The path retains the actor and the entire original selected firing at each
edge. Recovering its bundled trace is exactly the input trace. Arbitrary
paths may choose other intermediate boards; no converse equality of such
paths or injectivity of the logical projection is asserted.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceTracePaths

open Mettapedia.GSLT.LanguageDef
open InferenceSchemaKernel (Value)
open InferenceRequestExecution (Occurrence)
open InferenceSelectedFirings InferenceJudgmentBoards InferenceTraceClassifying
open InferenceExecutionPaths InferencePathFunctor
open _root_.CategoryTheory

variable {definition : ValidatedCalculusLanguageDef}

abbrev TraceBundle (definition : ValidatedCalculusLanguageDef)
    (before after : Configuration Value Occurrence) :=
  Σ actors : List Bool, SelectedRun definition before actors after

def recoverBundle {source target : Vertex definition} (path : Quiver.Path source target) :
    TraceBundle definition source.state target.state := ⟨actors path, recover path⟩

def prepend {before middle after : Configuration Value Occurrence} {actor : Bool}
    (firing : SelectedFiring definition actor before middle)
    (rest : TraceBundle definition middle after) : TraceBundle definition before after :=
  ⟨actor :: rest.1, .cons firing rest.2⟩

def append {before middle after : Configuration Value Occurrence}
    (first : TraceBundle definition before middle) (second : TraceBundle definition middle after) :
    TraceBundle definition before after :=
  ⟨first.1 ++ second.1, first.2.append second.2⟩

theorem recover_prepend {source middle target : Vertex definition} (edge : Edge source middle)
    (path : Quiver.Path middle target) :
    recoverBundle ((Quiver.Hom.toPath (V := Vertex definition) edge).comp path) =
      prepend edge.firing (recoverBundle path) := by
  induction path with
  | nil => rfl
  | @cons next target past last earlier =>
      change append (recoverBundle ((Quiver.Hom.toPath (V := Vertex definition) edge).comp past))
          ⟨[last.actor], .cons last.firing (.nil target.state)⟩ =
        prepend edge.firing
          (append (recoverBundle past) ⟨[last.actor], .cons last.firing (.nil target.state)⟩)
      rw [earlier]
      rfl

noncomputable def embed : {before after : Configuration Value Occurrence} → {actorList : List Bool} →
    (trace : SelectedRun definition before actorList after) → (prior : Board before) →
      Quiver.Path (⟨before, prior⟩ : Vertex definition)
        ⟨after, (trace.project prior).1⟩
  | _, _, _, .nil _state, _prior => .nil
  | before, _after, _, .cons firing rest, prior =>
      let head := projectFiring firing prior
      let edge : Edge (⟨before, prior⟩ : Vertex definition) ⟨_, head.1⟩ := ⟨_, firing⟩
      (Quiver.Hom.toPath (V := Vertex definition) edge).comp (embed rest head.1)

theorem recover_embed : {before after : Configuration Value Occurrence} → {actorList : List Bool} →
    (trace : SelectedRun definition before actorList after) → (prior : Board before) →
      recoverBundle (embed trace prior) = ⟨actorList, trace⟩
  | _, _, _, .nil _, _prior => rfl
  | before, _after, _, .cons firing rest, prior => by
      let head := projectFiring firing prior
      let edge : Edge (⟨before, prior⟩ : Vertex definition) ⟨_, head.1⟩ := ⟨_, firing⟩
      change recoverBundle ((Quiver.Hom.toPath (V := Vertex definition) edge).comp
        (embed rest head.1)) = _
      rw [recover_prepend, recover_embed rest head.1]
      rfl

theorem actors_embed {before after : Configuration Value Occurrence} {actorList : List Bool}
    (trace : SelectedRun definition before actorList after) (prior : Board before) :
    actors (embed trace prior) = actorList := congrArg Sigma.fst (recover_embed trace prior)

theorem projection_embed {before after : Configuration Value Occurrence} {actorList : List Bool}
    (trace : SelectedRun definition before actorList after) (prior : Board before) :
    (projection definition).map (embed trace prior) = (trace.project prior).2 := by
  have recovered := congrArg
    (fun bundle : TraceBundle definition before after => toBoard bundle.2 prior (trace.project prior).1)
    (recover_embed trace prior)
  rw [projection_recovers]
  exact recovered.trans (by rw [toBoard, changeBoard_self, Category.comp_id])

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceTracePaths
