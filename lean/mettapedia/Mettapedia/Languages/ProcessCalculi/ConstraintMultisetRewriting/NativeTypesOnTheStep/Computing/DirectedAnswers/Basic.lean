import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.TwoReadings
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Eventually.Normalizer

/-!
# The answer of a call, on the directed reduction

A package has two relations on terms.

* **The directed reduction** (`StrongNormalization.Reduces`): β, both projections and the declared
  rows, under every term former. Universe heads take no step. Its normal forms are the directed normal
  forms (`ContextualDependentExecutableJoin.Normal`).
* **Conversion** adds the equality of universe heads, closed under every former, and symmetry and
  transitivity. The package's full reduction (`ConversionCoherence.StepStar`) is the directed one with
  the head steps added; in the tower the head equality is reflexive, so every term with a head has a
  full step to itself.

**The answer of a call** (`DirectedAnswer`) is a directed normal form that the directed reduction
reaches from it. This module proves the facts that need no particular package:

* a directed step is a full step, so an answer is reached by the full reduction and is convertible
  with the call (`stepStar_of_reducesStar`, `DirectedAnswer.conv`);
* **uniqueness on the nose** in every constructor presentation, hence in every qualified package
  (`DirectedAnswer.unique`, `unique_of_qualified`): the directed reduction is confluent there
  (`Eventually.directed_confluent`);
* on the directed reduction the operational and the definitional reading agree: an answer is exactly
  a directed normal form that is convertible with the call by directed steps alone
  (`directedAnswer_iff`);
* **typing**: in a qualified package the answer of a typed call has the call's type and is
  typed-equal to it (`typed_of_qualified`);
* **the relation to normal forms of the full reduction** (`ConstructorSystem.Normal`, which the
  present `Answer` asks for): a directed normal form without heads is a normal form of the full
  reduction (`normal_of_headFree`), so an answer without heads is an `Answer`
  (`DirectedAnswer.answer`); conversely, when every head is related to itself, a normal form of the
  full reduction has no head (`headFree_of_normal`), so every `Answer` is head-free
  (`headFree_of_answer`). That every `Answer` is an answer needs the rows not to look at heads
  (`DirectedAnswers.Heads`);
* **existence under strong normalization** of the directed reduction (`exists_of_sn`,
  `exists_of_typedSN`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace NativeTypesOnTheStep.Computing.DirectedAnswers

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open ConstructorSystem (ConstructorPresentation)
open ConversionCoherence (StepStar)

variable {Head : Type}

/-! ## The definition -/

/-- **The answer of a call**: a directed normal form that the directed reduction reaches from it. -/
def DirectedAnswer (R : Rules Head) {n : Nat} (t v : Tm Head n) : Prop :=
  StrongNormalization.ReducesStar R t v ∧ ContextualDependentExecutableJoin.Normal R v

/-- **No universe head occurs in the term.** -/
def HeadFree : {n : Nat} → Tm Head n → Prop
  | _, .var _ => True
  | _, .const _ => True
  | _, .head _ => False
  | _, .pi A B => HeadFree A ∧ HeadFree B
  | _, .sigma A B => HeadFree A ∧ HeadFree B
  | _, .id A a b => HeadFree A ∧ HeadFree a ∧ HeadFree b
  | _, .lam body => HeadFree body
  | _, .app f a => HeadFree f ∧ HeadFree a
  | _, .pair a b => HeadFree a ∧ HeadFree b
  | _, .fst p => HeadFree p
  | _, .snd p => HeadFree p
  | _, .refl a => HeadFree a

/-! ## Directed steps are full steps -/

section Steps

variable {R : Rules Head}

/-- **A directed step is a step of the package's full reduction.** -/
theorem step_of_reduces {n : Nat} {t u : Tm Head n} (step : StrongNormalization.Reduces R t u) :
    StepCore R.computation R.headEq t u := by
  induction step with
  | betaPi body a => exact .betaPi body a
  | betaSigmaFst a b => exact .betaSigmaFst a b
  | betaSigmaSnd a b => exact .betaSigmaSnd a b
  | head impossible => exact impossible.elim
  | root h => exact .root h
  | congPiDom _ ih => exact .congPiDom ih
  | congPiCod _ ih => exact .congPiCod ih
  | congSigmaDom _ ih => exact .congSigmaDom ih
  | congSigmaCod _ ih => exact .congSigmaCod ih
  | congIdTy _ ih => exact .congIdTy ih
  | congIdLeft _ ih => exact .congIdLeft ih
  | congIdRight _ ih => exact .congIdRight ih
  | congLam _ ih => exact .congLam ih
  | congAppFun _ ih => exact .congAppFun ih
  | congAppArg _ ih => exact .congAppArg ih
  | congPairFst _ ih => exact .congPairFst ih
  | congPairSnd _ ih => exact .congPairSnd ih
  | congFst _ ih => exact .congFst ih
  | congSnd _ ih => exact .congSnd ih
  | congRefl _ ih => exact .congRefl ih

/-- Directed reduction is full reduction. -/
theorem stepStar_of_reducesStar {n : Nat} {t u : Tm Head n}
    (steps : StrongNormalization.ReducesStar R t u) : StepStar R t u := by
  induction steps with
  | refl => exact .refl
  | tail _ step ih => exact .tail ih (step_of_reduces step)

/-- **A full step from a term without heads is a directed step**: a head step needs a head. -/
theorem reduces_of_headFree {n : Nat} {t u : Tm Head n} (step : StepCore R.computation R.headEq t u)
    (free : HeadFree t) : StrongNormalization.Reduces R t u := by
  induction step with
  | betaPi body a => exact .betaPi body a
  | betaSigmaFst a b => exact .betaSigmaFst a b
  | betaSigmaSnd a b => exact .betaSigmaSnd a b
  | head _ => exact free.elim
  | root h => exact .root h
  | congPiDom _ ih => exact .congPiDom (ih free.1)
  | congPiCod _ ih => exact .congPiCod (ih free.2)
  | congSigmaDom _ ih => exact .congSigmaDom (ih free.1)
  | congSigmaCod _ ih => exact .congSigmaCod (ih free.2)
  | congIdTy _ ih => exact .congIdTy (ih free.1)
  | congIdLeft _ ih => exact .congIdLeft (ih free.2.1)
  | congIdRight _ ih => exact .congIdRight (ih free.2.2)
  | congLam _ ih => exact .congLam (ih free)
  | congAppFun _ ih => exact .congAppFun (ih free.1)
  | congAppArg _ ih => exact .congAppArg (ih free.2)
  | congPairFst _ ih => exact .congPairFst (ih free.1)
  | congPairSnd _ ih => exact .congPairSnd (ih free.2)
  | congFst _ ih => exact .congFst (ih free)
  | congSnd _ ih => exact .congSnd (ih free)
  | congRefl _ ih => exact .congRefl (ih free)

/-- A normal form of the full reduction is a directed normal form. -/
theorem directedNormal_of_normal {n : Nat} {v : Tm Head n} (normal : ConstructorSystem.Normal R v) :
    ContextualDependentExecutableJoin.Normal R v :=
  fun _ step => normal (step_of_reduces step)

/-- **A directed normal form without heads is a normal form of the full reduction.** -/
theorem normal_of_headFree {n : Nat} {v : Tm Head n}
    (normal : ContextualDependentExecutableJoin.Normal R v) (free : HeadFree v) :
    ConstructorSystem.Normal R v :=
  fun step => normal _ (reduces_of_headFree step free)

/-- **When every head is related to itself, a normal form of the full reduction has no head**: at a
head the reflexive head step applies. -/
theorem headFree_of_normal (reflexive : ∀ h, R.headEq h h) {n : Nat} {v : Tm Head n}
    (normal : ConstructorSystem.Normal R v) : HeadFree v := by
  induction v with
  | var _ => trivial
  | const _ => trivial
  | head h => exact normal (.head (reflexive h))
  | pi A B ihA ihB => exact ⟨ihA fun s => normal (.congPiDom s), ihB fun s => normal (.congPiCod s)⟩
  | sigma A B ihA ihB =>
      exact ⟨ihA fun s => normal (.congSigmaDom s), ihB fun s => normal (.congSigmaCod s)⟩
  | id A a b ihA iha ihb =>
      exact ⟨ihA fun s => normal (.congIdTy s), iha fun s => normal (.congIdLeft s),
        ihb fun s => normal (.congIdRight s)⟩
  | lam body ih => exact ih fun s => normal (.congLam s)
  | app f a ihf iha => exact ⟨ihf fun s => normal (.congAppFun s), iha fun s => normal (.congAppArg s)⟩
  | pair a b iha ihb =>
      exact ⟨iha fun s => normal (.congPairFst s), ihb fun s => normal (.congPairSnd s)⟩
  | fst p ih => exact ih fun s => normal (.congFst s)
  | snd p ih => exact ih fun s => normal (.congSnd s)
  | refl a ih => exact ih fun s => normal (.congRefl s)

end Steps

/-! ## Answers -/

section Answers

variable {R : Rules Head}

/-- A directed normal form is its own answer. -/
theorem DirectedAnswer.self {n : Nat} {v : Tm Head n}
    (normal : ContextualDependentExecutableJoin.Normal R v) : DirectedAnswer R v v :=
  ⟨.refl, normal⟩

/-- An answer is reached by the full reduction. -/
theorem DirectedAnswer.stepStar {n : Nat} {t v : Tm Head n} (answer : DirectedAnswer R t v) :
    StepStar R t v :=
  stepStar_of_reducesStar answer.1

/-- **An answer is convertible with its call.** -/
theorem DirectedAnswer.conv {n : Nat} {t v : Tm Head n} (answer : DirectedAnswer R t v) :
    Conv R.headEq t v R.computation :=
  conv_of_stepStar answer.stepStar

/-- A directed step before an answer keeps the answer. -/
theorem DirectedAnswer.head {n : Nat} {t u v : Tm Head n} (step : StrongNormalization.Reduces R t u)
    (answer : DirectedAnswer R u v) : DirectedAnswer R t v :=
  ⟨.head step answer.1, answer.2⟩

/-- **An answer without heads is an answer of the full reduction** (`Answer`). -/
theorem DirectedAnswer.answer {n : Nat} {t v : Tm Head n} (answer : DirectedAnswer R t v)
    (free : HeadFree v) : Answer R t v :=
  ⟨answer.stepStar, normal_of_headFree answer.2 free⟩

/-- **When every head is related to itself, an answer of the full reduction has no head.** -/
theorem headFree_of_answer (reflexive : ∀ h, R.headEq h h) {n : Nat} {t v : Tm Head n}
    (answer : Answer R t v) : HeadFree v :=
  headFree_of_normal reflexive answer.2

/-- **Uniqueness on the nose**: in a constructor presentation two answers of one call are equal,
by confluence of the directed reduction. -/
theorem DirectedAnswer.unique (equations : ConstructorPresentation R) {n : Nat} {t v w : Tm Head n}
    (first : DirectedAnswer R t v) (second : DirectedAnswer R t w) : v = w :=
  Eventually.normal_unique equations first.1 second.1 first.2 second.2

/-- **The operational and the definitional reading agree on the directed reduction**: in a
constructor presentation an answer is exactly a directed normal form convertible with the call by
directed steps. -/
theorem directedAnswer_iff (equations : ConstructorPresentation R) {n : Nat} {t v : Tm Head n} :
    DirectedAnswer R t v ↔
      Relation.EqvGen (StrongNormalization.Reduces R) t v ∧ ContextualDependentExecutableJoin.Normal R v := by
  constructor
  · exact fun answer => ⟨ContextualDependentExecutableJoin.star_eqvGen answer.1, answer.2⟩
  · rintro ⟨conversion, normal⟩
    obtain ⟨common, left, right⟩ := (Eventually.directedPresentation equations).churchRosser conversion
    have same : common = v := ContextualDependentExecutableJoin.Normal.star_eq normal right
    subst same
    exact ⟨left, normal⟩

end Answers

/-! ## In a qualified package -/

section Qualified

variable {L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-- **Two answers of one call are equal**, in every qualified package. -/
theorem unique_of_qualified (q : Qualified S) {n : Nat} {t v w : Tm Head n}
    (first : DirectedAnswer S.R t v) (second : DirectedAnswer S.R t w) : v = w :=
  q.constructors.elim fun equations => DirectedAnswer.unique equations first second

/-- **The answer of a typed call has the call's type and is typed-equal to it**, in every qualified
package. -/
theorem typed_of_qualified (q : Qualified S) {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ)
    {t v A : Tm Head n} (typing : Typed S.R Γ t A) (answer : DirectedAnswer S.R t v) :
    Typed S.R Γ v A ∧ Equal S.R Γ t v A :=
  q.subjectReduction formed answer.stepStar typing

end Qualified

/-! ## Existence under strong normalization -/

section Existence

variable {R : Rules Head}

/-- **A strongly normalizing term has an answer.** -/
theorem exists_of_sn {n : Nat} {t : Tm Head n} (sn : StrongNormalization.SN R t) :
    ∃ v, DirectedAnswer R t v := by
  induction sn with
  | intro t _ ih =>
      by_cases normal : ContextualDependentExecutableJoin.Normal R t
      · exact ⟨t, .self normal⟩
      · simp only [ContextualDependentExecutableJoin.Normal, not_forall, not_not] at normal
        obtain ⟨u, step⟩ := normal
        obtain ⟨v, answer⟩ := ih u step
        exact ⟨v, answer.head step⟩

/-- **Under strong normalization of typed terms, every term typed in a formed context has an
answer.** -/
theorem exists_of_typedSN (sn : Eventually.TypedSN R) {n : Nat} {Γ : Ctx Head n} {t A : Tm Head n}
    (formed : CtxFormed R Γ) (typed : Typed R Γ t A) : ∃ v, DirectedAnswer R t v :=
  exists_of_sn (sn formed typed)

end Existence

end NativeTypesOnTheStep.Computing.DirectedAnswers

section Audit
open NativeTypesOnTheStep.Computing.DirectedAnswers
#print axioms step_of_reduces
#print axioms stepStar_of_reducesStar
#print axioms reduces_of_headFree
#print axioms directedNormal_of_normal
#print axioms normal_of_headFree
#print axioms headFree_of_normal
#print axioms DirectedAnswer.conv
#print axioms DirectedAnswer.answer
#print axioms headFree_of_answer
#print axioms DirectedAnswer.unique
#print axioms directedAnswer_iff
#print axioms unique_of_qualified
#print axioms typed_of_qualified
#print axioms exists_of_sn
#print axioms exists_of_typedSN
end Audit

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
