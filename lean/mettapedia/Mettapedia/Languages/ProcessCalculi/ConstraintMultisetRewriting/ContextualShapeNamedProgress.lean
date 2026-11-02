import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualShapeFreshProgress
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNamedPatternImages
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNamedImitationProgress
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNamedSelfProgress
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNamedFlexProgress

/-!
# Shape progress follows arbitrary named selections

The actual declaration equivalences move shape images and their finite sums
to the selected ports. Fresh-helper answers then compose back to the same
named frame updates used by the executable worklist.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualShapeNamedProgress

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualResidual
open ContextualActiveSupport
open ContextualPatternFragment
open ContextualShapeErasure

variable {S : Signature} {V Next : Type} [DecidableEq V] {source : V → MetaArity S}

theorem imitation (identity : V) {Γ : Ctx S} (rho : Ren S (source identity).1 Γ)
    (operator : S.Op (source identity).2) (fields : Args (signature S source) (S.arity operator) Γ)
    (rest : Problem source) (images : ShapeAssignment S V Next)
    (patterned : ProblemPattern ((observe (rename (S := signature S source) rho (generator source identity)),
      observe (Term.op (.inl operator) fields)) :: rest))
    (models : ShapeModels images ((observe (rename (S := signature S source) rho (generator source identity)),
      observe (Term.op (.inl operator) fields)) :: rest)) :
    let update := ContextualNamedImitation.apply source identity rho operator fields rest
    letI := update.equality
    ∃ remaining : ShapeAssignment S update.Variables Next, ShapeModels remaining update.remaining ∧
      (∀ name, images name = evaluate remaining (update.answer name)) ∧
      ContextualShapePotential.potential remaining (active update.remaining) < ContextualShapePotential.potential images
        (active ((observe (rename (S := signature S source) rho (generator source identity)),
          observe (Term.op (.inl operator) fields)) :: rest)) := by
  let problem := (observe (rename (S := signature S source) rho (generator source identity)),
    observe (Term.op (.inl operator) fields)) :: rest
  let others : ContextualFrameSelection.Remaining identity → MetaArity S := fun other => source other.val
  let selected := ContextualSelectedOccurrences.selected source identity
  let moved : ShapeAssignment S (Unit ⊕ ContextualFrameSelection.Remaining identity) Next :=
    fun name => images ((ContextualFrameSelection.split identity).symm name)
  have movedPattern : ProblemPattern (mapProblem selected problem) :=
    map_patterns selected (ContextualNamedPatternImages.reindex_images _ _) problem patterned
  have movedModels : ShapeModels moved (mapProblem selected problem) :=
    (ContextualShapeTransport.models_reindex_back (ContextualFrameSelection.split identity)
      (ContextualFrameSelection.forward_preserves source identity) problem patterned images).mpr models
  have chosen : (observe (rename (S := signature S (ContextualFrameSelection.declarations source identity)) rho
      (generator (ContextualFrameSelection.declarations source identity) (.inl ()))),
      observe (Term.op (.inl operator) (instantiateArgs selected fields))) ∈ mapProblem selected problem := by
    dsimp only [problem, selected]
    rw [ContextualSelectedOccurrences.selected_rigid_problem]
    exact List.mem_cons_self
  let remaining := ContextualShapeFreshProgress.fieldImages moved (instantiateArgs selected fields)
  have progressed := ContextualShapeFreshProgress.imitation (source identity).1 operator others rho
    (instantiateArgs selected fields) (mapProblem selected problem) chosen moved movedPattern movedModels
  have components := ContextualShapeTransport.components_reindex_back (ContextualFrameSelection.split identity)
    (ContextualFrameSelection.forward_preserves source identity) images
    (ContextualImitation.answer (source identity).1 operator others) remaining progressed.2.1
  have start := ContextualShapePotential.reindex_exact (ContextualFrameSelection.split identity)
    (ContextualFrameSelection.forward_preserves source identity)
    (ContextualFrameSelection.backward_preserves source identity) problem images
  exact ⟨remaining, progressed.1, components, progressed.2.2.trans_eq start⟩

theorem self (identity : V) {Γ : Ctx S} (left right : Ren S (source identity).1 Γ) (different : left ≠ right)
    (rest : Problem source) (images : ShapeAssignment S V Next)
    (patterned : ProblemPattern ((observe (rename (S := signature S source) left (generator source identity)),
      observe (rename (S := signature S source) right (generator source identity))) :: rest))
    (models : ShapeModels images ((observe (rename (S := signature S source) left (generator source identity)),
      observe (rename (S := signature S source) right (generator source identity))) :: rest)) :
    let update := ContextualNamedSelfPair.apply source identity left right rest
    letI := update.equality
    ∃ remaining : ShapeAssignment S update.Variables Next, ShapeModels remaining update.remaining ∧
      (∀ name, images name = evaluate remaining (update.answer name)) ∧
      ContextualShapePotential.potential remaining (active update.remaining) ≤ ContextualShapePotential.potential images
        (active ((observe (rename (S := signature S source) left (generator source identity)),
          observe (rename (S := signature S source) right (generator source identity))) :: rest)) ∧
      ContextualInterfacePotential.cost update.declaration (active update.remaining) < ContextualInterfacePotential.cost source
        (active ((observe (rename (S := signature S source) left (generator source identity)),
          observe (rename (S := signature S source) right (generator source identity))) :: rest)) := by
  let problem := (observe (rename (S := signature S source) left (generator source identity)),
    observe (rename (S := signature S source) right (generator source identity))) :: rest
  let others : ContextualFrameSelection.Remaining identity → MetaArity S := fun other => source other.val
  let selected := ContextualSelectedOccurrences.selected source identity
  let moved : ShapeAssignment S (Unit ⊕ ContextualFrameSelection.Remaining identity) Next :=
    fun name => images ((ContextualFrameSelection.split identity).symm name)
  let equalizer := ScopeEqualizer.Finite.build left right
  let answer := ContextualSelfPair.answer equalizer (source identity).2 others
  have movedPattern : ProblemPattern (mapProblem selected problem) :=
    map_patterns selected (ContextualNamedPatternImages.reindex_images _ _) problem patterned
  have movedModels : ShapeModels moved (mapProblem selected problem) :=
    (ContextualShapeTransport.models_reindex_back (ContextualFrameSelection.split identity)
      (ContextualFrameSelection.forward_preserves source identity) problem patterned images).mpr models
  have chosen : (observe (rename (S := signature S (ContextualFrameSelection.declarations source identity)) left
      (generator (ContextualFrameSelection.declarations source identity) (.inl ()))),
      observe (rename (S := signature S (ContextualFrameSelection.declarations source identity)) right
      (generator (ContextualFrameSelection.declarations source identity) (.inl ())))) ∈ mapProblem selected problem := by
    dsimp only [problem, selected]
    rw [ContextualSelectedOccurrences.selected_problem]
    exact List.mem_cons_self
  have progressed := ContextualShapeFreshProgress.self left right different (source identity).2 others
    (mapProblem selected problem) chosen moved movedPattern movedModels
  have components := ContextualShapeTransport.components_reindex_back (ContextualFrameSelection.split identity)
    (ContextualFrameSelection.forward_preserves source identity) images answer moved progressed.2.1
  have startImages := ContextualShapePotential.reindex_exact (ContextualFrameSelection.split identity)
    (ContextualFrameSelection.forward_preserves source identity)
    (ContextualFrameSelection.backward_preserves source identity) problem images
  have startParameters := ContextualInterfacePotential.reindex_exact source
    (ContextualFrameSelection.declarations source identity) (ContextualFrameSelection.split identity)
    (ContextualFrameSelection.forward_preserves source identity)
    (ContextualFrameSelection.backward_preserves source identity) problem
  have retained : active (mapProblem answer (mapProblem selected rest)) ⊆ active (mapProblem answer (mapProblem selected problem)) :=
    active_tail_subset _ _
  refine ⟨moved, ?_, components, ?_, ?_⟩
  · exact fun equation member => progressed.1 equation (List.mem_cons_of_mem _ member)
  · exact ((ContextualShapePotential.monotone moved retained).trans progressed.2.2.1).trans_eq startImages
  · exact (lt_of_le_of_lt (ContextualInterfacePotential.monotone _ retained) progressed.2.2.2).trans_eq startParameters

theorem flex (first second : V) (different : first ≠ second) (sorts : (source first).2 = (source second).2)
    {Γ : Ctx S} (left : Ren S (source first).1 Γ) (right : Ren S (source second).1 Γ)
    (rest : Problem source) (images : ShapeAssignment S V Next)
    (patterned : ProblemPattern ((observe (rename (S := signature S source) left (generator source first)),
      observe (rename (S := signature S source) right (generator source second))) :: rest))
    (models : ShapeModels images ((observe (rename (S := signature S source) left (generator source first)),
      observe (rename (S := signature S source) right (generator source second))) :: rest)) :
    let update := ContextualNamedFlexPair.apply source first second different sorts left right rest
    letI := update.equality
    ∃ remaining : ShapeAssignment S update.Variables Next, ShapeModels remaining update.remaining ∧
      (∀ name, images name = evaluate remaining (update.answer name)) ∧
      ContextualShapePotential.potential remaining (active update.remaining) < ContextualShapePotential.potential images
        (active ((observe (rename (S := signature S source) left (generator source first)),
          observe (rename (S := signature S source) right (generator source second))) :: rest)) := by
  let problem := (observe (rename (S := signature S source) left (generator source first)),
    observe (rename (S := signature S source) right (generator source second))) :: rest
  let others : ContextualPairSelection.Remaining first second → MetaArity S := fun other => source other.val
  let selected := ContextualSelectedPairs.selected source first second different
  let moved : ShapeAssignment S (Bool ⊕ ContextualPairSelection.Remaining first second) Next :=
    fun name => images ((ContextualPairSelection.split first second different).symm name)
  let answer := ContextualHeterogeneousFlexPair.answer (source first).1 (source second).1 (source first).2 (source second).2
    sorts others left right
  let remaining := ContextualShapeFreshProgress.commonImages moved
  have movedPattern : ProblemPattern (mapProblem selected problem) :=
    map_patterns selected (ContextualNamedPatternImages.reindex_images _ _) problem patterned
  have movedModels : ShapeModels moved (mapProblem selected problem) :=
    (ContextualShapeTransport.models_reindex_back (ContextualPairSelection.split first second different)
      (ContextualPairSelection.forward_preserves source first second different) problem patterned images).mpr models
  have chosen : (observe (rename (S := signature S (ContextualPairSelection.declarations source first second)) left
      (generator (ContextualPairSelection.declarations source first second) (.inl false))),
      observe (rename (S := signature S (ContextualPairSelection.declarations source first second)) right
      (generator (ContextualPairSelection.declarations source first second) (.inl true)))) ∈ mapProblem selected problem := by
    dsimp only [problem, selected]
    rw [ContextualSelectedPairs.selected_problem]
    exact List.mem_cons_self
  have progressed := ContextualShapeFreshProgress.heterogeneous_flex (source first).1 (source second).1
    (source first).2 (source second).2 sorts others left right (mapProblem selected problem) chosen moved movedPattern movedModels
  have components := ContextualShapeTransport.components_reindex_back (ContextualPairSelection.split first second different)
    (ContextualPairSelection.forward_preserves source first second different) images answer remaining progressed.2.1
  have start := ContextualShapePotential.reindex_exact (ContextualPairSelection.split first second different)
    (ContextualPairSelection.forward_preserves source first second different)
    (ContextualPairSelection.backward_preserves source first second different) problem images
  have retained : active (mapProblem answer (mapProblem selected rest)) ⊆ active (mapProblem answer (mapProblem selected problem)) :=
    active_tail_subset _ _
  refine ⟨remaining, ?_, components, ?_⟩
  · exact fun equation member => progressed.1 equation (List.mem_cons_of_mem _ member)
  · exact (lt_of_le_of_lt (ContextualShapePotential.monotone remaining retained) progressed.2.2).trans_eq start

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualShapeNamedProgress
