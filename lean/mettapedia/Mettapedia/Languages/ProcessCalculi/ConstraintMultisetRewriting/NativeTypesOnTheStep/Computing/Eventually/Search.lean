import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Eventually.Limits
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.Budgets.Laws

/-!
# The search for the least sufficient budget is total on typed equal pairs

The executable comparison, read at every budget, is a budgeted decider in the sense of the budget laws
(`comparisonDecider`): its answers are certificates, each of which says yes soundly on typed terms of a formed
context. Taking the first certificate found up to the budget makes it a budgeted decision procedure with laws
1 to 3 by construction.

* **Law 4 on typed equal pairs** (`comparison_answeredOn`): on a qualified package, with a reducer that keeps
  its answers and eventually returns a weak-head normal reduct of every typed term, every typed equal pair is
  answered at some budget.
* **The search is total there** (`searchCertificate`): the least budget that answers is found with no budget.
  Below it the verdict is exhausted, from it on it is yes: **exhausted is transient** (`exhausted_transient`).
* **On typed pairs that are not equal it is exhausted at every budget** (`unequal_exhausted_forever`): the
  comparison never says no, so there the search runs forever. That is the price of a comparison without a
  third outcome; a refusal needs one in the function itself.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace NativeTypesOnTheStep.Computing.Eventually

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open ExecutableReduction ExecutableConversion
open UnificationWithLevels.TreeFibre.Budgets

variable {Head L : Type} [UniverseLevel.LevelOrder L]

/-- A comparison question: two terms and a type in a context. -/
structure Question (Head : Type) where
  n : Nat
  context : Ctx Head n
  left : Tm Head n
  right : Tm Head n
  type : Tm Head n

/-- What a certificate establishes: on typed terms of a formed context, equality. -/
def Holds (S : Setting Head L) (q : Question Head) : Prop :=
  CtxFormed S.R q.context → Typed S.R q.context q.left q.type → Typed S.R q.context q.right q.type →
    Equal S.R q.context q.left q.right q.type

/-- The typed equal pairs. -/
def TypedEqual (S : Setting Head L) (q : Question Head) : Prop :=
  CtxFormed S.R q.context ∧ Equal S.R q.context q.left q.right q.type

variable {S : Setting Head L}
variable [DecidableEq Head] [DecidableRel S.R.headEq] [∀ head, Decidable (S.R.isUniverse head)]

/-- **The comparison as a budget-indexed decider**: at each budget a certificate or nothing; a certificate
says yes. -/
def comparisonDecider (qual : Qualified S) (red : Reducer S.R) : Decider (Holds S) where
  Answer q := Certificate S.R (.compare q.context q.left q.right q.type)
  attempt k q := compare S.R red k q.context q.left q.right q.type
  sign _ := true
  yes a _ := fun formed tt tu => Algorithm.sound qual.facts qual.roots qual.heads qual.algebra a.down formed tt tu
  no _ h := absurd h (by decide)

variable (qual : Qualified S) {red : Reducer S.R} (stable : Stable S.R red)
  (eventually : WhnfEventually S red)

include stable eventually in
/-- Typed equal pairs are answered by some budget's attempt. -/
theorem comparison_answered {q : Question Head} (inside : TypedEqual S q) :
    ∃ k a, (comparisonDecider qual red).attempt k q = some a := by
  obtain ⟨fuel, certificate, stable'⟩ :=
    compare_eventually qual.facts qual.roots qual.heads qual.algebra qual.complete stable eventually inside.1
      inside.2
  exact ⟨fuel, certificate, stable' fuel le_rfl⟩

include stable eventually in
/-- **Law 4 on typed equal pairs.** -/
theorem comparison_answeredOn : (comparisonDecider qual red).procedure.AnsweredOn (TypedEqual S) :=
  fun _ inside => (comparisonDecider qual red).answered_iff.mpr (comparison_answered qual stable eventually inside)

/-- **The search with no budget** on a typed equal pair: the certificate of the least budget that answers. -/
def searchCertificate {q : Question Head} (inside : TypedEqual S q) :
    Certificate S.R (.compare q.context q.left q.right q.type) :=
  (comparisonDecider qual red).search (comparison_answered qual stable eventually inside)

include stable eventually in
/-- **The search agrees with every budget that decides**, and below the least such budget the verdict is
exhausted: exhausted is transient on typed equal pairs. -/
theorem exhausted_transient {q : Question Head} (inside : TypedEqual S q) :
    (∀ k, k < (comparisonDecider qual red).leastAnswering (comparison_answered qual stable eventually inside) →
      (comparisonDecider qual red).procedure.verdict k q = .undecided) ∧
    ∀ k, (comparisonDecider qual red).leastAnswering (comparison_answered qual stable eventually inside) ≤ k →
      (comparisonDecider qual red).procedure.verdict k q = .equal := by
  have answered := comparison_answered qual stable eventually inside
  refine ⟨fun k below => (comparisonDecider qual red).verdict_below_least answered below, fun k above => ?_⟩
  have decided : (comparisonDecider qual red).procedure.verdict k q ≠ .undecided := by
    intro undecided
    have none' := (comparisonDecider qual red).verdict_undecided_iff.mp undecided
      ((comparisonDecider qual red).leastAnswering answered) above
    rw [(comparisonDecider qual red).attempt_least answered] at none'
    cases none'
  rw [(comparisonDecider qual red).verdict_eq_search answered decided]
  rfl

/-- **On typed pairs that are not equal the procedure is exhausted at every budget**: the comparison never
says no. -/
theorem unequal_exhausted_forever {q : Question Head} (formed : CtxFormed S.R q.context)
    (tl : Typed S.R q.context q.left q.type) (tr : Typed S.R q.context q.right q.type)
    (different : ¬ Equal S.R q.context q.left q.right q.type) (k : Nat) :
    (comparisonDecider qual red).procedure.verdict k q = .undecided :=
  (comparisonDecider qual red).undecided_of_none fun j _ =>
    compare_none_of_not_equal qual red formed tl tr different j

end NativeTypesOnTheStep.Computing.Eventually

section Audit
open NativeTypesOnTheStep.Computing.Eventually
#print axioms comparisonDecider
#print axioms comparison_answered
#print axioms comparison_answeredOn
#print axioms searchCertificate
#print axioms exhausted_transient
#print axioms unequal_exhausted_forever
end Audit

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
