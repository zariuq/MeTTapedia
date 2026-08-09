import Mettapedia.Languages.MeTTa.ObserverLattice

/-!
# Which observers can detect absence, and which can reconstruct answers

"Is reification essential?" has been asked as one question.  It is two, and
they have opposite answers.

Four elimination forms are in play, all of which turn a computation's answer
bag into something ordinary:

* **reify** — the bag as a datum (`collapse`);
* **count** — how many answers;
* **first** — the first answer, if any;
* **zero test** — whether there were any.

Each is a view of the bag, so the ordering of `Core.NonFactorization`
applies unchanged: one view determines another exactly when a function
recovers the second from the first, and fails exactly when two bags agree on
the first and differ on the second.

The results:

* **Every one of the four detects absence.**  `count`, `first` and `zeroTest`
  all determine emptiness, and each is provably weaker than reification.  So
  detecting zero does *not* require reification.
* **Only reification reconstructs the answers.**  `zeroTest`, `count` and
  `first` each provably fail to determine the bag, and they are pairwise
  incomparable in the expected places.

So the honest statement is not "reification is the only way to observe zero"
— it is not — but rather: *some* eliminator is needed, because no
continuation will do; and among eliminators, reification is the top of a
strict hierarchy, necessary only if you want the answers back.

## What this settles about expressibility

Failure of determination is the strong direction and it transfers to syntax:
a macro defining one observer from another must in particular agree on every
bag, hence determine it.  So each negative below rules out **every possible
macro**, whatever its shape (`no_macro_of_not_determines`).  The positives do
not transfer automatically — semantic recoverability is necessary but not
sufficient for a local macro definition — and are recorded as candidates.
-/

namespace Mettapedia.Languages.MeTTa.ZeroObservers

open Mettapedia.Languages.MeTTa.Emptiness
open Mettapedia.Languages.MeTTa.RoundTrip
open Mettapedia.GSLT.Core.NonFactorization

/-! ## The four observers -/

/-- Reify the bag as one datum.  This is `collapse`. -/
def reify : List Datum → Datum := encode
/-- How many answers there were. -/
def count : List Datum → Nat := List.length
/-- Whether there were any. -/
def zeroTest : List Datum → Bool := List.isEmpty
/-- The first answer, if any. -/
def firstAnswer : List Datum → Option Datum := List.head?

/-! ## Reification is the top -/

theorem reify_determines_count : Factors reify count :=
  ⟨fun datum => (decode datum).length, fun bag => by
    simp [reify, count, decode_encode]⟩

theorem reify_determines_zeroTest : Factors reify zeroTest :=
  ⟨fun datum => (decode datum).isEmpty, fun bag => by
    simp [reify, zeroTest, decode_encode]⟩

theorem reify_determines_firstAnswer : Factors reify firstAnswer :=
  ⟨fun datum => (decode datum).head?, fun bag => by
    simp [reify, firstAnswer, decode_encode]⟩

/-! ## Every observer detects absence

This is the half that answers "must we reify to see zero?" — no. -/

theorem count_determines_zeroTest : Factors count zeroTest :=
  ⟨fun total => total == 0, fun bag => by cases bag <;> rfl⟩

theorem firstAnswer_determines_zeroTest : Factors firstAnswer zeroTest :=
  ⟨fun answer => answer.isNone, fun bag => by cases bag <;> rfl⟩

/-- **Detecting absence does not require reification.**  Two strictly weaker
observers already decide it. -/
theorem absence_detectable_without_reification :
    Factors count zeroTest ∧ Factors firstAnswer zeroTest :=
  ⟨count_determines_zeroTest, firstAnswer_determines_zeroTest⟩

/-! ## But only reification reconstructs the answers

Each negative is a fibre: two bags agreeing on the coarse view. -/

/-- Two nonempty bags with different contents. -/
def zeroTestFiber : NonTrivialFiber zeroTest reify where
  left := [.unit]
  right := [.nil]
  sameShadow := rfl
  differentValue := by decide

theorem zeroTest_not_determines_reify : ¬ Factors zeroTest reify :=
  zeroTestFiber.not_factors

/-- Two bags of the same size with different contents. -/
def countFiber : NonTrivialFiber count reify where
  left := [.unit]
  right := [.nil]
  sameShadow := rfl
  differentValue := by decide

theorem count_not_determines_reify : ¬ Factors count reify :=
  countFiber.not_factors

/-- Two bags with the same first answer and different tails. -/
def firstAnswerFiber : NonTrivialFiber firstAnswer reify where
  left := [.unit]
  right := [.unit, .nil]
  sameShadow := rfl
  differentValue := by decide

theorem firstAnswer_not_determines_reify : ¬ Factors firstAnswer reify :=
  firstAnswerFiber.not_factors

/-! ## Counting and peeking are incomparable -/

/-- Same count, different first answer. -/
def countVsFirstFiber : NonTrivialFiber count firstAnswer where
  left := [.unit]
  right := [.nil]
  sameShadow := rfl
  differentValue := by decide

theorem count_not_determines_firstAnswer : ¬ Factors count firstAnswer :=
  countVsFirstFiber.not_factors

/-- Same first answer, different count. -/
def firstVsCountFiber : NonTrivialFiber firstAnswer count where
  left := [.unit]
  right := [.unit, .unit]
  sameShadow := rfl
  differentValue := by decide

theorem firstAnswer_not_determines_count : ¬ Factors firstAnswer count :=
  firstVsCountFiber.not_factors

/-! ## The transfer to syntax

A macro defining one observer from another agrees on every bag, so it *is* a
recovery function.  Hence every negative above rules out all macros at once,
which is what makes the semantic lattice an expressibility result rather than
a semantic curiosity. -/

/-- **No macro can beat determination.**  If the fine view does not determine
the coarse one, then no definition of the coarse observer in terms of the
fine one exists, of any shape. -/
theorem no_macro_of_not_determines {Fine Coarse : Type}
    {fine : List Datum → Fine} {coarse : List Datum → Coarse}
    (fails : ¬ Factors fine coarse) :
    ¬ ∃ expansion : Fine → Coarse, ∀ bag, expansion (fine bag) = coarse bag := fails

/-- **The corrected essentiality claim.**  Reification is not needed to
observe absence — weaker eliminators do that — and is needed, unavoidably, to
recover the answers.  The two halves were being asked as one question. -/
theorem reification_essential_for_answers_not_for_absence :
    (Factors count zeroTest ∧ Factors firstAnswer zeroTest) ∧
      (¬ Factors zeroTest reify ∧ ¬ Factors count reify ∧
        ¬ Factors firstAnswer reify) :=
  ⟨absence_detectable_without_reification,
    zeroTest_not_determines_reify, count_not_determines_reify,
    firstAnswer_not_determines_reify⟩

end Mettapedia.Languages.MeTTa.ZeroObservers
