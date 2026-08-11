import Mathlib.Data.Multiset.Basic
import Mettapedia.GSLT.Core.NonFactorization

/-!
# Quiescence is free for a relation and paid for by a totalized function

A semantics given as a **step relation** answers "is anything available here?"
by looking at the relation.  There is nothing to encode and nothing to lose:
quiescence is `¬ ∃ successor`, and that is the definition rather than a derived
datum.

A semantics given as a **total answer function** has to say something at a
subject it cannot interpret.  The usual choice — return the subject itself —
is what an open world wants to *display*, and it is also where the distinction
between *nothing applied* and *something applied and returned the subject*
disappears.

This module separates the two so the loss can be attributed correctly.

* `quiescent_iff_no_successor` — for a relation, quiescence is definitional.
  The proof is `Iff.rfl`: there is nothing to prove because nothing was added.
* `emptiness_factors` — for an untotalized answer function, the status is a
  function of the answers.  Still nothing lost.
* `totalized_singleton_test_conflates` — after totalization, the test "the
  result is the singleton of my input" holds both for a subject with no answers
  and for one whose only answer is itself, while the emptiness test still
  separates them.

So the repair for a totalized semantics is not an extra status datum.  It is to
test the untotalized relation, and to let the fallback live in the observer
where it belongs.  A calculus whose steps are a relation never incurs the debt
in the first place.
-/

namespace Mettapedia.GSLT.Core.TotalizationLoss

open Mettapedia.GSLT.Core.NonFactorization

variable {Subject : Type}

/-! ## The relational reading -/

/-- Nothing is available here. -/
def Quiescent (step : Subject → Subject → Prop) (subject : Subject) : Prop :=
  ¬ ∃ next, step subject next

/-- **For a step relation, quiescence is definitional.**  The proof is
`Iff.rfl` — there is no encoding, so there is nothing to lose. -/
theorem quiescent_iff_no_successor (step : Subject → Subject → Prop)
    (subject : Subject) :
    Quiescent step subject ↔ ¬ ∃ next, step subject next :=
  Iff.rfl

/-! ## The bag reading, before totalization -/

/-- The step relation a bag-valued answer function induces. -/
def stepOf (answers : Subject → Multiset Subject) :
    Subject → Subject → Prop :=
  fun subject next => next ∈ answers subject

/-- **Emptiness is the status, and it is a function of the answers.**  Before
totalization nothing has been lost. -/
theorem emptiness_factors (answers : Subject → Multiset Subject) :
    Factors answers (fun subject => answers subject = 0) :=
  ⟨fun bag => bag = 0, fun _ => rfl⟩

/-- And the bag reading agrees with the relational one. -/
theorem quiescent_stepOf_iff_empty (answers : Subject → Multiset Subject)
    (subject : Subject) :
    Quiescent (stepOf answers) subject ↔ answers subject = 0 := by
  constructor
  · intro noSuccessor
    by_contra nonempty
    obtain ⟨next, member⟩ := Multiset.exists_mem_of_ne_zero nonempty
    exact noSuccessor ⟨next, member⟩
  · rintro empty ⟨next, member⟩
    simp only [stepOf, empty] at member
    simp at member

/-! ## Totalization, and what it costs -/

/-- Make an answer function total by returning the subject when it has no
answers.  This is the open-world display convention. -/
def totalize [DecidableEq Subject] (answers : Subject → Multiset Subject)
    (subject : Subject) : Multiset Subject :=
  if answers subject = 0 then {subject} else answers subject

@[simp] theorem totalize_of_empty [DecidableEq Subject] (answers : Subject → Multiset Subject)
    {subject : Subject} (empty : answers subject = 0) :
    totalize answers subject = {subject} := by
  simp [totalize, empty]

@[simp] theorem totalize_of_nonempty [DecidableEq Subject] (answers : Subject → Multiset Subject)
    {subject : Subject} (nonempty : answers subject ≠ 0) :
    totalize answers subject = answers subject := by
  simp [totalize, nonempty]

/-- **The cost of totalizing.**  A subject with no answers and a subject whose
only answer is itself both satisfy "the result is the singleton of my input",
so a runner using that test conflates ignorance with a genuine self-loop.  The
emptiness test on the untotalized answers still separates them, so the
information was never absent from the semantics — only from the wrapper. -/
theorem totalized_singleton_test_conflates [DecidableEq Subject] (answers : Subject → Multiset Subject)
    {ignorant looping : Subject}
    (noAnswers : answers ignorant = 0)
    (selfLoop : answers looping = {looping}) :
    totalize answers ignorant = {ignorant} ∧
      totalize answers looping = {looping} ∧
      answers ignorant = 0 ∧ answers looping ≠ 0 := by
  refine ⟨totalize_of_empty answers noAnswers, ?_, noAnswers, ?_⟩
  · rw [totalize_of_nonempty answers (by rw [selfLoop]; simp), selfLoop]
  · rw [selfLoop]
    simp

/-- Stated the other way round: on a totalized semantics the singleton test is
not the quiescence test, and the quiescence test is still available underneath
it. -/
theorem quiescence_available_under_totalization
    (answers : Subject → Multiset Subject) (subject : Subject) :
    Quiescent (stepOf answers) subject ↔ answers subject = 0 :=
  quiescent_stepOf_iff_empty answers subject

end Mettapedia.GSLT.Core.TotalizationLoss
