import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualGuardSemantics
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualComputedFreshFrame

/-!
# All-future contextual asks reflect invertible declaration reindexing

The inverse changes identities without adding equations. Schema locals and
physical regions retain their original matching contract, including count
and absence checks. The result quantifies over arbitrary later families.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualGuardSemantics

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily

universe u
variable {S : Signature} {Local V W : Type} {O : Type u}
  (locals : Local → MetaArity S) {source : V → MetaArity S} {target : W → MetaArity S}

theorem Ask.reindex_iff (forward : V → W) (backward : W → V)
    (forwardPreserves : ∀ identity, target (forward identity) = source identity)
    (backwardPreserves : ∀ identity, source (backward identity) = target identity)
    (leftInverse : Function.LeftInverse backward forward)
    {Γ : Ctx S} {sort : S.Srt}
    (problem : EquationStore (Term (signature S source) Γ sort))
    (rows : O → ContextualStoredRows.Row locals source Γ sort) (world : Finset O)
    (check : Check (Term (signature S source) Γ sort)) :
    Ask locals (ContextualFrameUnifier.mapProblem (reindex forward forwardPreserves) problem)
        (fun occurrence => (rows occurrence).map locals (reindex forward forwardPreserves)) world
        (check.map (instantiate (reindex forward forwardPreserves))) ↔
      Ask locals problem rows world check := by
  have inverse : Assignment.compose (reindex backward backwardPreserves) (reindex forward forwardPreserves) =
      generator source := reindex_left_inverse forward backward forwardPreserves backwardPreserves leftInverse
  constructor
  · intro transported
    have restored := transported.transport locals (reindex backward backwardPreserves)
    have problemRestored : ContextualFrameUnifier.mapProblem (reindex backward backwardPreserves)
        (ContextualFrameUnifier.mapProblem (reindex forward forwardPreserves) problem) = problem := by
      rw [ContextualComputedFreshFrame.map_compose, inverse]
      simp only [ContextualFrameUnifier.mapProblem, instantiate_identity, List.map_id']
    have rowsRestored : (fun occurrence =>
        ((rows occurrence).map locals (reindex forward forwardPreserves)).map locals
          (reindex backward backwardPreserves)) = rows := by
      funext occurrence
      rw [ContextualStoredRows.Row.map_compose, inverse, ContextualStoredRows.Row.map_identity]
    have checkRestored : (check.map (instantiate (reindex forward forwardPreserves))).map
        (instantiate (reindex backward backwardPreserves)) = check := by
      cases check <;> simp only [Check.map,
        instantiate_reindex_inverse forward backward forwardPreserves backwardPreserves leftInverse]
    rw [problemRestored, rowsRestored, checkRestored] at restored
    exact restored
  · intro admitted
    exact admitted.transport locals (reindex forward forwardPreserves)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualGuardSemantics
