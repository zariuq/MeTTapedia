import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentConversionBudget
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentExecutableJoin
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Qualification

/-!
# The executable normalizer of a package eventually returns the normal form

The tree's executable normalizer (`ExecutableReduction.normalize`) tries the package's root evaluator first,
then β and the projections at the root, then the subterms from left to right. It is a leftmost-outermost
**full** normalizer, and its fuel counts its steps. Its success on a term needs that this strategy's sequence
of steps from the term is finite. Every qualified package has weak-head normal forms for its typed terms
(`Qualified.whnf`); a typed weak-head normal form need not have a normal form the normalizer reaches
(`loopLam_whnf_unnormalized`, in a package outside the qualified class). Strong normalization suffices.

* **The extra hypothesis, stated once** (`TypedSN`): every term typed in a formed context is strongly
  normalizing under the package's directed reduction (β, the projections and the declared rows, under every
  former; universe-head equalities take no step).
* **A complete root evaluator** (`RootComplete`): when it proposes nothing at a term, the package has no
  root step there. Without it the normalizer may stop early at a term that still computes.
* **Eventual success** (`normalize_eventually`, `typed_normalize_eventually`): under the two, the normalizer
  returns a directed normal form reached from the term at some budget, and the same answer at every larger
  budget.
* **The answer is the normal form** on a qualified package (`qualified_normalize_eventually`): the directed
  reduction of a constructor presentation is confluent (`directed_confluent`, through the presentation of the
  same rows with the head equality removed, `directedPresentation`), so a directed normal form reached from
  the term is unique (`normal_unique`). It is typed at the term's type and typed-equal to it there.
* **A directed normal form is a weak-head normal form** (`whnf_of_normal`), so the normalizer's answer is what
  a weak-head comparison needs.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace NativeTypesOnTheStep.Computing.Eventually

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open ExecutableReduction
open ConstructorSystem (ConstructorPresentation)

/-! ## The hypotheses -/

section Hypotheses

variable {Head : Type} (R : Rules Head)

/-- **A complete root evaluator**: when it proposes nothing at a term, the package has no root step
there. -/
def RootComplete (root : RootEvaluator R) : Prop :=
  ∀ {n : Nat} (t : Tm Head n), root t = none → ∀ u, ¬ R.computation.step t u

/-- **Strong normalization of typed terms**: every term typed in a formed context is strongly
normalizing under the package's directed reduction. -/
def TypedSN : Prop :=
  ∀ {n : Nat} {Γ : Ctx Head n} {t A : Tm Head n}, CtxFormed R Γ → Typed R Γ t A →
    StrongNormalization.SN R t

end Hypotheses

/-! ## Directed steps -/

section Directed

variable {Head : Type} (R : Rules Head)

/-- A weak-head step of a package is a weak-head step of its directed package. -/
theorem whStep_toDirected {roles : Roles Head} {n : Nat} {t u : Tm Head n}
    (step : WhStep R roles t u) : WhStep (ContextualDependentExecutableJoin.directed R) roles t u := by
  induction step with
  | beta body a => exact .beta body a
  | fstPair a b => exact .fstPair a b
  | sndPair a b => exact .sndPair a b
  | root s => exact .root s
  | appFun _ ih => exact .appFun ih
  | fst _ ih => exact .fst ih
  | snd _ ih => exact .snd ih
  | scrutinee role length focus _ ih => exact .scrutinee role length focus ih

/-- **A weak-head step is a directed step.** -/
theorem whStep_directed {roles : Roles Head} {n : Nat} {t u : Tm Head n} (step : WhStep R roles t u) :
    StrongNormalization.Reduces R t u :=
  WhStep.stepCore (whStep_toDirected R step)

/-- **A directed normal form is weak-head normal.** -/
theorem whnf_of_normal {roles : Roles Head} {n : Nat} {t : Tm Head n}
    (normal : ContextualDependentExecutableJoin.Normal R t) : Whnf R roles t :=
  fun u step => normal u (whStep_directed R step)

/-- Weak-head reduction from a weak-head normal form stays there. -/
theorem whRed_of_whnf {roles : Roles Head} {n : Nat} {t u : Tm Head n} (normal : Whnf R roles t)
    (red : WhRed R roles t u) : u = t := by
  induction red using Relation.ReflTransGen.head_induction_on with
  | refl => rfl
  | head step _ _ => exact absurd step (normal _)

end Directed

/-! ## Eventual success under strong normalization -/

section Normalizer

variable {Head : Type} (R : Rules Head) (root : RootEvaluator R)

/-- What the normalizer returns is reached by directed steps. -/
theorem normalize_star {n : Nat} : ∀ (fuel : Nat) {term : Tm Head n} {result : Result R term},
    normalize R root fuel term = some result → StrongNormalization.ReducesStar R term result.val
  | 0, _, _, accepted => by cases accepted
  | fuel + 1, term, result, accepted => by
      cases current : step R root term with
      | none =>
          simp only [ExecutableReduction.normalize, current, Option.some.injEq] at accepted
          subst accepted
          exact .refl
      | some next =>
          cases later : normalize R root fuel next.val with
          | none =>
              simp only [ExecutableReduction.normalize, current, later] at accepted
              cases accepted
          | some answer =>
              simp only [ExecutableReduction.normalize, current, later, Option.some.injEq] at accepted
              subst accepted
              exact Relation.ReflTransGen.head
                (ContextualDependentReductionBudget.step_directed R root term next current)
                (normalize_star fuel later)

/-- **Eventual success of the normalizer on a strongly normalizing term**: with a complete root
evaluator it returns a directed normal form reached from the term at some budget, and the same answer at
every larger budget. -/
theorem normalize_eventually (complete : RootComplete R root) {n : Nat} {t : Tm Head n}
    (sn : StrongNormalization.SN R t) :
    ∃ fuel result, ContextualDependentExecutableJoin.Normal R result.val ∧
      StrongNormalization.ReducesStar R t result.val ∧
      ∀ larger, fuel ≤ larger → normalize R root larger t = some result := by
  obtain ⟨fuel, result, stopped, stable⟩ :=
    ContextualDependentReductionBudget.eventually_stable_of_sn R root sn
  exact ⟨fuel, result,
    ContextualDependentReductionBudget.normal_of_stopped R root complete result.val stopped,
    normalize_star R root fuel (stable fuel le_rfl), stable⟩

/-- **Eventual success on typed terms**, under the extra hypothesis. -/
theorem typed_normalize_eventually (sn : TypedSN R) (complete : RootComplete R root) {n : Nat}
    {Γ : Ctx Head n} {t A : Tm Head n} (formed : CtxFormed R Γ) (typed : Typed R Γ t A) :
    ∃ fuel result, ContextualDependentExecutableJoin.Normal R result.val ∧
      StrongNormalization.ReducesStar R t result.val ∧
      ∀ larger, fuel ≤ larger → normalize R root larger t = some result :=
  normalize_eventually R root complete (sn formed typed)

end Normalizer

/-! ## On a qualified package the answer is the normal form -/

section Qualified

variable {Head : Type}

/-- **The directed rows of a constructor presentation**: the same rows, with the head equality
removed, present the package's directed reduction. -/
def directedPresentation {R : Rules Head} (equations : ConstructorPresentation R) :
    ConstructorPresentation (ContextualDependentExecutableJoin.directed R) where
  presentation :=
    ⟨equations.presentation.schema, equations.presentation.sound, equations.presentation.cover⟩
  system := equations.system
  same := equations.same
  symmetric := ⟨fun _ _ h => h⟩

/-- **Confluence of the directed reduction** of a constructor presentation. -/
theorem directed_confluent {R : Rules Head} (equations : ConstructorPresentation R) {n : Nat}
    {a b c : Tm Head n} (first : StrongNormalization.ReducesStar R a b)
    (second : StrongNormalization.ReducesStar R a c) :
    ∃ d, StrongNormalization.ReducesStar R b d ∧ StrongNormalization.ReducesStar R c d :=
  (directedPresentation equations).churchRosser
    (.trans _ _ _ (.symm _ _ (ContextualDependentExecutableJoin.star_eqvGen first))
      (ContextualDependentExecutableJoin.star_eqvGen second))

/-- **A directed normal form reached from a term is unique.** -/
theorem normal_unique {R : Rules Head} (equations : ConstructorPresentation R) {n : Nat}
    {t v w : Tm Head n} (toV : StrongNormalization.ReducesStar R t v)
    (toW : StrongNormalization.ReducesStar R t w) (normalV : ContextualDependentExecutableJoin.Normal R v)
    (normalW : ContextualDependentExecutableJoin.Normal R w) : v = w := by
  obtain ⟨d, vd, wd⟩ := directed_confluent equations toV toW
  exact (ContextualDependentExecutableJoin.Normal.star_eq normalV vd).symm.trans
    (ContextualDependentExecutableJoin.Normal.star_eq normalW wd)

variable {L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-- **Item 2 on a qualified package.** Under strong normalization of typed terms and with a complete
root evaluator, the executable normalizer returns, at some budget and at every larger one, the unique
directed normal form of every typed term; that answer is typed at the term's type and typed-equal to the
term there. -/
theorem qualified_normalize_eventually (q : Qualified S) (sn : TypedSN S.R) (root : RootEvaluator S.R)
    (complete : RootComplete S.R root) {n : Nat} {Γ : Ctx Head n} {t A : Tm Head n}
    (formed : CtxFormed S.R Γ) (typed : Typed S.R Γ t A) :
    ∃ fuel result, ContextualDependentExecutableJoin.Normal S.R result.val ∧
      (∀ v, StrongNormalization.ReducesStar S.R t v → ContextualDependentExecutableJoin.Normal S.R v →
        v = result.val) ∧
      Typed S.R Γ result.val A ∧ Equal S.R Γ t result.val A ∧
      ∀ larger, fuel ≤ larger → normalize S.R root larger t = some result := by
  obtain ⟨fuel, result, normal, star, stable⟩ :=
    typed_normalize_eventually S.R root sn complete formed typed
  obtain ⟨typed', equal⟩ := q.subjectReduction formed result.property typed
  refine ⟨fuel, result, normal, fun v toV normalV => ?_, typed', equal, stable⟩
  exact q.constructors.elim fun equations => normal_unique equations toV star normalV normal

end Qualified

end NativeTypesOnTheStep.Computing.Eventually

section Audit
open NativeTypesOnTheStep.Computing.Eventually
#print axioms whStep_directed
#print axioms whnf_of_normal
#print axioms whRed_of_whnf
#print axioms normalize_star
#print axioms normalize_eventually
#print axioms typed_normalize_eventually
#print axioms directedPresentation
#print axioms directed_confluent
#print axioms normal_unique
#print axioms qualified_normalize_eventually
end Audit

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
