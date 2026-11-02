import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualHeterogeneousFlexPair
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFlexPairActive

/-!
# The heterogeneous flexible-pair update strictly decreases active model work

The result-sort equality transports the complete equation before the common
interface is computed. The actual update drops the solved selected equation
and retains every other instantiated equation. Its active potential is at
most that of the full mapped problem, whose strict decrease is proved.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualHeterogeneousFlexProgress

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualResidual
open ContextualActiveSupport
open ContextualHeterogeneousFlexPair

variable {S : Signature} {Other Next : Type} [DecidableEq Other] {next : Next → MetaArity S}

theorem model_progress (L R : Ctx S) (first second : S.Srt) (same : first = second)
    (others : Other → MetaArity S) {Γ : Ctx S} (left : Ren S L Γ) (right : Ren S R Γ)
    (rest : Problem (declarations L R first second others))
    (candidate : Assignment (declarations L R first second others) next)
    (solved : Models candidate
      ((observe (rename (S := signature S (declarations L R first second others)) left
          (generator (declarations L R first second others) (.inl false))),
        observe (rename (S := signature S (declarations L R first second others)) right
          (generator (declarations L R first second others) (.inl true)))) :: rest)) :
    let update := apply L R first second same others left right rest
    letI := update.equality
    ∃ remaining : Assignment update.declaration next, Models remaining update.remaining ∧
      (∀ identity, candidate identity = instantiate remaining (update.answer identity)) ∧
      potential remaining (active update.remaining) < potential candidate
        (active ((observe (rename (S := signature S (declarations L R first second others)) left
            (generator (declarations L R first second others) (.inl false))),
          observe (rename (S := signature S (declarations L R first second others)) right
            (generator (declarations L R first second others) (.inl true)))) :: rest)) := by
  cases same
  let pullback := ScopePullback.Finite.build (S := S) left right
  let selected := (observe (rename (S := signature S (declarations L R first first others)) left
      (generator (declarations L R first first others) (.inl false))),
    observe (rename (S := signature S (declarations L R first first others)) right
      (generator (declarations L R first first others) (.inl true))))
  let answer := ContextualFlexPair.answer pullback first others
  obtain ⟨remaining, models, components, decrease⟩ := ContextualFlexPairActive.model_progress
    pullback first others (selected :: rest) List.mem_cons_self candidate solved
  have tailSolved : Models remaining (mapProblem answer rest) := by
    intro equation member
    exact models equation (List.mem_cons_of_mem _ member)
  have bounded := potential_monotone remaining (active_tail_subset
    (instantiateObservation answer selected.1, instantiateObservation answer selected.2) (mapProblem answer rest))
  exact ⟨remaining, tailSolved, components, lt_of_le_of_lt bounded decrease⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualHeterogeneousFlexProgress
