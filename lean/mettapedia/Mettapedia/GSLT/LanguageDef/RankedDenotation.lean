import Mettapedia.GSLT.LanguageDef.CompiledContinuationAnswerProducer

/-!
# Denotations of ranked continuation-body machines

The exactness laws for continuation-body machines (`collect?_exact`,
`ContinuationArenaBridge.completed_answers`, and the compiled-machine laws
built on them) quantify over a `Denotation`: an answer function solving the
unfolding equations.  Those laws are only as informative as the existence of
such a solution.

`denotationOfRank` constructs one whenever calls are ranked so that each
call's alternatives consult only the answers of strictly smaller calls
(`RankedBelow`).  Sized search whose budget decreases on every nested call is
of this kind.  The construction is well-founded recursion on the rank, and
`denotationOfRank_unique` shows the solution is the only one: every
denotation of a ranked machine has the same answers.

Without a rank a machine may have no solution in finite answer lists (a call
that unfolds to itself followed by an answer) or several; nothing here claims
otherwise.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RankedDenotation

open CompiledContinuationAnswerProducer

universe u v

variable {State : Type u} {Answer : Type v}

/-- The answers the alternatives of `state` produce, given answers of calls. -/
def unfoldWith (machine : Machine State Answer) (value : State → List Answer)
    (state : State) : List Answer :=
  (machine.branches state).flatMap (Body.answers value)

/-- Each call's alternatives consult only the answers of strictly smaller
calls. -/
def RankedBelow (machine : Machine State Answer) (rank : State → Nat) : Prop :=
  ∀ state (value value' : State → List Answer),
    (∀ other, rank other < rank state → value other = value' other) →
      unfoldWith machine value state = unfoldWith machine value' state

/-- Answers by well-founded recursion on the rank. -/
noncomputable def rankedValue (machine : Machine State Answer) (rank : State → Nat) :
    State → List Answer :=
  (measure rank).wf.fix fun state recurse =>
    unfoldWith machine
      (fun other => if h : rank other < rank state then recurse other h else []) state

theorem rankedValue_unfold (machine : Machine State Answer) (rank : State → Nat)
    (ranked : RankedBelow machine rank) (state : State) :
    rankedValue machine rank state = unfoldWith machine (rankedValue machine rank) state := by
  rw [rankedValue, WellFounded.fix_eq]
  apply ranked
  intro other smaller
  simp only [smaller, dite_true]

/-- A ranked machine has a denotation. -/
noncomputable def denotationOfRank (machine : Machine State Answer) (rank : State → Nat)
    (ranked : RankedBelow machine rank) : Denotation machine where
  value := rankedValue machine rank
  unfold state := rankedValue_unfold machine rank ranked state

/-- The denotation of a ranked machine is unique. -/
theorem denotationOfRank_unique (machine : Machine State Answer) (rank : State → Nat)
    (ranked : RankedBelow machine rank) (denotation : Denotation machine) (state : State) :
    denotation.value state = rankedValue machine rank state := by
  induction h : rank state using Nat.strong_induction_on generalizing state with
  | _ n ih =>
      rw [denotation.unfold state, rankedValue_unfold machine rank ranked state]
      apply ranked
      intro other smaller
      exact ih (rank other) (h ▸ smaller) other rfl

/-! ### A control: an unranked self-call has no finite solution -/

/-- One call state whose single alternative is itself followed by an answer. -/
def selfLoop : Machine Unit Bool where
  branches _ := [.call () fun a => .answer a, .answer true]

/-- No denotation in finite answer lists exists for it: the unfolding
equation would give a list strictly longer than itself. -/
theorem selfLoop_no_denotation (denotation : Denotation selfLoop) : False := by
  have h := denotation.unfold ()
  simp only [selfLoop, List.flatMap_cons, List.flatMap_nil, Body.answers, List.append_nil,
    List.flatMap_singleton'] at h
  have := congrArg List.length h
  simp at this

end Mettapedia.GSLT.LanguageDef.RankedDenotation
