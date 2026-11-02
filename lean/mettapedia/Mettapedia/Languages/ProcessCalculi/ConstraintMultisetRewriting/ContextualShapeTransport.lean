import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualShapeErasure
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualActiveReindex
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualProblemPermutation

/-!
# Shape models follow actual contextual substitutions

Shape evaluation composes with a substitution on structural inputs. These
laws transport a shape model through the actual answer, including the
declaration equivalences used to select fresh-helper ports.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualShapeTransport

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualResidual
open ContextualPatternFragment
open ContextualShapeErasure

variable {S : Signature} {V W Next : Type} {source : V → MetaArity S} {target : W → MetaArity S}

def compose (images : ShapeAssignment S W Next) (answer : Assignment source target) : ShapeAssignment S V Next :=
  fun identity => evaluate images (answer identity)

theorem models_map (answer : Assignment source target) (images : ShapeAssignment S W Next)
    (problem : Problem source) (patterned : ProblemPattern problem) :
    ShapeModels images (mapProblem answer problem) ↔ ShapeModels (compose images answer) problem := by
  constructor
  · intro models equation member
    have same := models _ (List.mem_map.mpr ⟨equation, member, rfl⟩)
    exact (evaluate_instantiate answer images _ (patterned equation member).1).symm.trans
      (same.trans (evaluate_instantiate answer images _ (patterned equation member).2))
  · intro models equation member
    obtain ⟨original, selected, rfl⟩ := List.mem_map.mp member
    exact (evaluate_instantiate answer images _ (patterned original selected).1).trans
      ((models original selected).trans (evaluate_instantiate answer images _ (patterned original selected).2).symm)

theorem models_of_components (before : ShapeAssignment S V Next) (answer : Assignment source target)
    (after : ShapeAssignment S W Next) (components : ∀ identity, before identity = evaluate after (answer identity))
    (problem : Problem source) (patterned : ProblemPattern problem) :
    ShapeModels after (mapProblem answer problem) ↔ ShapeModels before problem := by
  rw [models_map answer after problem patterned]
  have same : compose after answer = before := (funext components).symm
  rw [same]

theorem evaluate_reindex (forward : V → W) (preserves : ∀ identity, target (forward identity) = source identity)
    (images : ShapeAssignment S W Next) (identity : V) :
    evaluate images (reindex forward preserves identity) = images (forward identity) := by
  rw [reindex, evaluate_cast_body, evaluate_generator]

theorem components_reindex_back {X : Type} {last : X → MetaArity S} (equivalence : V ≃ W)
    (forward : ∀ identity, target (equivalence identity) = source identity)
    (before : ShapeAssignment S V Next) (answer : Assignment target last) (after : ShapeAssignment S X Next)
    (components : ∀ identity, before (equivalence.symm identity) = evaluate after (answer identity)) :
    ∀ identity, before identity = evaluate after (Assignment.compose answer (reindex equivalence forward) identity) := by
  intro identity
  rw [Assignment.compose, instantiate_reindex, evaluate_cast_body]
  simpa only [equivalence.symm_apply_apply] using components (equivalence identity)

theorem compose_associative {X : Type} {last : X → MetaArity S}
    (images : ShapeAssignment S X Next) (second : Assignment target last) (first : Assignment source target)
    (patterned : ∀ identity, Pattern S target (first identity)) :
    compose images (Assignment.compose second first) = compose (compose images second) first := by
  funext identity
  exact evaluate_instantiate second images (first identity) (patterned identity)

theorem models_reindex_back (equivalence : V ≃ W)
    (forward : ∀ identity, target (equivalence identity) = source identity)
    (problem : Problem source) (patterned : ProblemPattern problem) (images : ShapeAssignment S V Next) :
    ShapeModels (fun identity => images (equivalence.symm identity)) (mapProblem (reindex equivalence forward) problem) ↔
      ShapeModels images problem := by
  apply models_of_components images _ _ _ problem patterned
  intro identity
  rw [evaluate_reindex, equivalence.symm_apply_apply]

theorem models_permutation (images : ShapeAssignment S V Next) {first second : Problem source}
    (permuted : first.Perm second) : ShapeModels images first ↔ ShapeModels images second := by
  constructor
  · exact fun models equation member => models equation (permuted.mem_iff.mpr member)
  · exact fun models equation member => models equation (permuted.mem_iff.mp member)

theorem pattern_tail {equation : Equation (Observation S source)} {rest : Problem source}
    (patterned : ProblemPattern (equation :: rest)) : ProblemPattern rest :=
  fun pair member => patterned pair (List.mem_cons_of_mem _ member)

theorem models_tail (images : ShapeAssignment S V Next) {equation : Equation (Observation S source)}
    {rest : Problem source} (models : ShapeModels images (equation :: rest)) : ShapeModels images rest :=
  fun pair member => models pair (List.mem_cons_of_mem _ member)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualShapeTransport
