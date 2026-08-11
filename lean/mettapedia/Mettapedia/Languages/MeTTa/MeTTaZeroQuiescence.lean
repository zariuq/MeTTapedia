import Mettapedia.Languages.MeTTa.MeTTaZero
import Mettapedia.GSLT.Core.NonFactorization

/-!
# Where Zero's status information actually goes

`evaluateOne` cannot distinguish ignorance from a genuine self-loop.  That is
true, and it is worth knowing.  This module locates the loss precisely, because
the location changes the repair.

The kernel is

```
interpretedResults S x  =  equationResults S x + groundApply x
```

and it is **total and lossless**: it returns the empty bag exactly when nothing
was interpreted.  `evaluateOne` is that kernel wrapped in a fallback

```
evaluateOne S x  =  if interpretedResults S x = 0 then {x} else interpretedResults S x
```

and the fallback is where ignorance and self-looping become indistinguishable —
both give the singleton of the subject.

So:

* `quiescence_factors_through_kernel` — quiescence **is** a function of
  `interpretedResults`.  The status is right there, unencoded.
* `evaluateOne_singleton_of_quiescent` and `evaluateOne_singleton_of_selfLoop`
  — both cases give `{subject}`, so any runner testing "result equals the
  singleton of my input" conflates them.
* `kernel_separates_quiescent_from_selfLoop` — the kernel does not.

The consequence for design: a runner should test `interpretedResults = 0`, not
inspect `evaluateOne`'s bag.  Under that test, "run to quiescence" is iteration
while the kernel bag is nonempty; ignorance stops, a self-loop does not, and
duplicate occurrences are preserved — with no additional status datum, no
report type, and no change to Zero's semantics.

The inert fallback is then what it always was: an **observer** convention —
*show me the answers, or the subject if there are none* — which is exactly the
open-world reading, sitting one level above the kernel rather than inside it.
-/

namespace Mettapedia.Languages.MeTTa.MeTTaZeroQuiescence

open Mettapedia.Languages.MeTTa.MeTTaZero
open Mettapedia.GSLT.Core.NonFactorization
open Mettapedia.OSLF.MeTTaIL.Syntax

variable {model : Model}

/-- Quiescence read off the kernel: nothing was interpreted.  This is the
open-world "I do not know how to interpret this", and it is a property of
`interpretedResults` alone. -/
def Quiescent (model : Model) (space : model.Space) (subject : Pattern) : Prop :=
  interpretedResults model space subject = 0

/-- **The status is a function of the kernel bag.**  Nothing needs to be added
to Zero to recover it: emptiness of `interpretedResults` *is* the status. -/
theorem quiescence_factors_through_kernel (space : model.Space) :
    Factors (fun subject => interpretedResults model space subject)
      (fun subject => Quiescent model space subject) :=
  ⟨fun results => results = 0, fun _ => rfl⟩

/-! ## Where the fallback loses it -/

/-- Ignorance evaluates to the singleton of the subject. -/
theorem evaluateOne_singleton_of_quiescent (space : model.Space) {subject : Pattern}
    (quiescent : Quiescent model space subject) :
    evaluateOne model space subject = {subject} := by
  simp [evaluateOne, Quiescent] at quiescent ⊢
  simp [quiescent]

/-- A genuine self-loop evaluates to the singleton of the subject as well. -/
theorem evaluateOne_singleton_of_selfLoop (space : model.Space) {subject : Pattern}
    (selfLoop : interpretedResults model space subject = {subject}) :
    evaluateOne model space subject = {subject} := by
  simp [evaluateOne, selfLoop]

/-- **The singleton test conflates them.**  A runner that stops when the result
equals the singleton of its input cannot tell ignorance from a self-loop,
because the fallback makes both produce that singleton. -/
theorem singleton_test_conflates (space : model.Space)
    {ignorant looping : Pattern}
    (isIgnorant : Quiescent model space ignorant)
    (isLooping : interpretedResults model space looping = {looping}) :
    evaluateOne model space ignorant = {ignorant} ∧
      evaluateOne model space looping = {looping} :=
  ⟨evaluateOne_singleton_of_quiescent space isIgnorant,
    evaluateOne_singleton_of_selfLoop space isLooping⟩

/-- **But the kernel separates them.**  The very same two subjects have
different kernel bags — empty against a singleton — so the distinction the
fallback destroys was never absent from the semantics. -/
theorem kernel_separates_quiescent_from_selfLoop (space : model.Space)
    {ignorant looping : Pattern}
    (isIgnorant : Quiescent model space ignorant)
    (isLooping : interpretedResults model space looping = {looping}) :
    Quiescent model space ignorant ∧ ¬ Quiescent model space looping := by
  refine ⟨isIgnorant, ?_⟩
  intro quiescent
  rw [quiescent] at isLooping
  simp at isLooping

/-! ## The repair, stated

Test the kernel, not the wrapper. -/

/-- One productive step: the kernel returned something. -/
def Productive (model : Model) (space : model.Space) (subject : Pattern) : Prop :=
  interpretedResults model space subject ≠ 0

/-- Every subject is exactly one of quiescent or productive, decided by the
kernel bag alone.  That dichotomy is the whole status discipline. -/
theorem quiescent_or_productive (space : model.Space) (subject : Pattern) :
    Quiescent model space subject ↔ ¬ Productive model space subject := by
  unfold Quiescent Productive
  exact (not_not).symm

/-- On productive subjects the fallback never fires, so `evaluateOne` and the
kernel agree.  The wrapper only ever adds information where the kernel had
none — which is precisely where it destroys the distinction. -/
theorem evaluateOne_eq_kernel_of_productive (space : model.Space)
    {subject : Pattern} (productive : Productive model space subject) :
    evaluateOne model space subject = interpretedResults model space subject := by
  simp [evaluateOne, Productive] at productive ⊢
  simp [productive]

end Mettapedia.Languages.MeTTa.MeTTaZeroQuiescence
