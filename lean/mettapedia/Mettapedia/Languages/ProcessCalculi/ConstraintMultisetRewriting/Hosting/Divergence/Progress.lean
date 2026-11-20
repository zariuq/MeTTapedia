import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.ArrowHosting

/-!
# Progress: no alternative of the hosted fragments waits

The source language has live alternatives that have not finished and cannot move: `run` without a
principal solution, `check` with mixed readings, a space whose address the store does not determine.
None of these is in the fragments of the hosting theorem.

* `arrow_progress`: **every alternative of the fragment with `let`** (`ret`, `apply`, `let_`, `choice`,
  `fail`) **that has not finished can move**, in every world. A call either has an equation whose copy
  unifies with it (`apply`) or has none (`unmatched`); the case split is classical.
* `plain_progress`: the same for the first fragment.

A move may make no live alternative (`fail`, a `let` whose pattern does not unify with the value): the
alternative then ends without an answer. Progress is of moves, not of answers.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Divergence

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage

variable {S : Signature} {Γ : Ctx S} {star : S.Srt} {κ : Keys S} {D : Discipline S Γ star}
  {P : SourceLanguage.Program κ Γ star D.Ty} {supply : ℕ → Term S Γ star}

/-- **Progress for the fragment with `let`**: an alternative that has not finished can move. -/
theorem arrow_progress {b : Branch κ Γ star D.Ty} (arrow : ArrowBranch b) (unfinished : ¬ b.Finished)
    (w : World κ Γ star) : ∃ w' bs, Move D P supply w b w' bs := by
  classical
  obtain ⟨K, focus, frames, ps⟩ := b
  obtain ⟨framesOk, shape⟩ := arrow
  rcases shape with ⟨c, rfl, arrowC⟩ | ⟨t, rfl⟩
  · cases c with
    | ret t => exact ⟨_, _, .ret w K t frames ps⟩
    | apply t =>
        by_cases matched : ∃ e ∈ P.equations, Solvable (K ++ [(instantiate (copyAt κ w.scope) e.lhs, t)])
        · exact ⟨_, _, .apply w K t frames ps matched⟩
        · exact ⟨_, _, .unmatched w K t frames ps (fun e member live => matched ⟨e, member, live⟩)⟩
    | let_ s p c k => exact ⟨_, _, .letStart w K s p c k frames ps⟩
    | choice c d => exact ⟨_, _, .choice w K c d frames ps⟩
    | fail => exact ⟨_, _, .fail w K frames ps⟩
    | run _ => exact arrowC.elim
    | query _ _ _ => exact arrowC.elim
    | add _ _ _ => exact arrowC.elim
    | remove _ _ _ => exact arrowC.elim
    | new _ _ _ => exact arrowC.elim
    | check _ _ => exact arrowC.elim
    | delay _ _ _ _ => exact arrowC.elim
    | force _ => exact arrowC.elim
  · cases frames with
    | nil => exact absurd ⟨rfl, t, rfl⟩ unfinished
    | cons fr fs =>
        cases fr with
        | bindTo s p k => exact ⟨_, _, .letBind w K t s p k fs ps⟩
        | checkAt _ => exact framesOk.elim
        | memo _ => exact framesOk.elim

/-- **Progress for the first fragment.** -/
theorem plain_progress {b : Branch κ Γ star D.Ty} (plain : PlainBranch b) (unfinished : ¬ b.Finished)
    (w : World κ Γ star) : ∃ w' bs, Move D P supply w b w' bs :=
  arrow_progress (arrowBranch_of_plain plain) unfinished w

#print axioms arrow_progress
#print axioms plain_progress

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Divergence
