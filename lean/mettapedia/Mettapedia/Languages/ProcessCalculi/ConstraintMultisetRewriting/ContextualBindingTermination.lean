import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualBindingSelectionProgress
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualRigidSupport

/-!
# A finite stopping bound for the executable binding phase

Each recoverable binding removes an active declaration, and intervening rigid
normalization introduces none. The existing fuelled driver therefore reaches
either a certified rigid refutation or a queue with no further recoverable
binding within one plus the original active declaration count. Such a queue
may still contain imitation, pruning, flexible pairs or general applications;
stopping this phase does not declare those equations solved or impossible.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualBindingTermination

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualResidual
open ContextualActiveSupport
open ContextualBindingWorklist

variable {S : Signature} {V : Type} [DecidableEq V] [DecidableEq S.Srt]
  [∀ sort, DecidableEq (S.Op sort)] {source : V → MetaArity S}

inductive Finished {problem : Problem source} : ContextualBindingWorklist.Result problem → Prop
  | residual (update : ContextualBindingWorklist.Update problem)
      (noBinding : choose (S := S) (declaration := source) update.remaining = none) : Finished (.residual update)
  | refuted (impossible : ∀ {Next : Type} (next : Next → MetaArity S)
      (candidate : Assignment source next), ¬ Models candidate problem) : Finished (.refuted impossible)

theorem stopping_bound (problem : Problem source) :
    ∃ fuel, fuel ≤ (active problem).card + 1 ∧ Finished (run (S := S) (declaration := source) fuel problem) := by
  induction measure : (active problem).card using Nat.strong_induction_on generalizing problem with
  | h size earlier =>
      cases normalized : ContextualRigidSolver.normalize (S := S) (source := source) problem with
      | none =>
          refine ⟨1, by omega, ?_⟩
          simp only [run]
          split
          · exact .refuted _
          · rename_i remaining computed
            cases normalized.symm.trans computed
      | some remaining =>
          cases selected : choose (S := S) (declaration := source) remaining with
          | none =>
              refine ⟨1, by omega, ?_⟩
              simp only [run]
              split
              · rename_i computed
                cases normalized.symm.trans computed
              · rename_i rest computed
                have same : rest = remaining := Option.some.inj (computed.symm.trans normalized)
                subst rest
                split
                · exact .residual _ selected
                · rename_i update computed
                  cases selected.symm.trans computed
          | some update =>
              have decrease := ContextualBindingSelectionProgress.choose_active_card_progress selected
              have bounded := Finset.card_le_card (ContextualRigidSupport.normalization_active_subset normalized)
              have smaller : (active update.remaining).card < size := by omega
              obtain ⟨fuel, bound, stopped⟩ := earlier _ smaller update.remaining rfl
              refine ⟨fuel + 1, by omega, ?_⟩
              simp only [run]
              split
              · rename_i computed
                cases normalized.symm.trans computed
              · rename_i rest computed
                have same : rest = remaining := Option.some.inj (computed.symm.trans normalized)
                subst rest
                split
                · rename_i computed
                  cases selected.symm.trans computed
                · rename_i chosen computed
                  have same : chosen = update := Option.some.inj (computed.symm.trans selected)
                  subst chosen
                  cases tail : run (S := S) (declaration := source) fuel update.remaining with
                  | residual last =>
                      rw [tail] at stopped
                      cases stopped with
                      | residual _ noBinding => exact .residual _ noBinding
                  | refuted impossible =>
                      refine .refuted ?_
                      intro Next next candidate solved
                      have first := (ContextualRigidSolver.normalization_reduction normalized).compose update.valid
                      obtain ⟨residual, restSolved, _⟩ := first.complete next candidate solved
                      exact impossible next residual restSolved

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualBindingTermination
