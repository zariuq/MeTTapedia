import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentDynamicFragmentStability
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentPatternSolver

/-!
# The dynamic pattern fragment of an equation store

The declarations of a store's context are its metavariables. A store equation `λ x̄. l ≐ λ x̄. r`
is **opened** by applying both sides to the locals `x̄`, one for each leading abstraction of its
left side; the opened sides live over the metavariables followed by the locals.

An equation is **in the dynamic pattern fragment** when

* its two annotations are equal types, and its annotation is normal, with at least as many leading
  Π binders as the left side has leading abstractions;
* every normal form of each opened side has **Miller occurrences** (every metavariable spine is a
  metavariable applied to distinct locals, never projected), with the locals rigid and the
  metavariables flexible;
* in every such normal form, each metavariable is applied to exactly as many arguments as its
  declared type has leading Π binders (η-long occurrences).

The definition reads only the store. Every equation in the fragment is then one of: a Miller
pattern equation against any side, flex–flex patterns, or rigid–rigid with equal or distinct
heads, whose decomposition stays in the fragment (`classification`).

**Relation to Abel and Pientka's dynamic pattern fragment.** Their condition is the same Miller
condition on normal forms, checked when an equation is considered. Their spines may also project
Σ-typed locals and metavariables; here a metavariable spine is never projected and its arguments
are bare locals. Σ-typed metavariables and arguments are reduced to this form by currying
(`ContextualDependentSigmaExpansion`), and occurrences are η-long, as in their setting. Annotations
are required normal: the normalizing solver's preparation produces such stores
(`ContextualDependentNormalizing.prepared_normal`).

The two agree as conditions on terms, not in their consequences. Their calculus has no cumulative universes; over a
cumulative tower the inclusion of a universe in the next is silent, so an unknown may receive a local of a smaller
universe than the domain it declares, and the fragment then holds `crossStore`, which is solvable and has no
principal answer (`ContextualDependentSweep.Witnesses.fragment_without_principal_answer`). On such a store every run
stops postponed (`UnificationWithLevels.DependentFibre.cross_postponed`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentDynamicFragment

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ExecutableReduction ContextualDependentExecutableJoin
open ContextualDependentGeneralPattern (liftFlexible)

variable {Head : Type}

/-! ## Opening an equation -/

/-- Apply a side to `count` fresh locals. -/
def openCode {n : Nat} : (count : Nat) → Tm Head n → Tm Head (n + count)
  | 0, code => code
  | count + 1, code => .app (Presentation.rename wk (openCode count code)) (.var 0)

/-- The number of leading Π binders of a code. -/
def piCount {n : Nat} : Tm Head n → Nat
  | .pi _ body => piCount body + 1
  | _ => 0

/-- In an opened context, the `count` newest variables are rigid locals; the rest are the
store's metavariables. -/
def openedFlexible {n : Nat} (count : Nat) : Fin n → Bool := fun index => decide (count ≤ index.val)

/-- The arity of a metavariable of an opened context: the number of leading Π binders of its
declaration. -/
def metaArity {n : Nat} (context : Ctx Head n) (count : Nat) (index : Fin (n + count)) : Nat :=
  if h : count ≤ index.val then piCount (Ctx.lookup context ⟨index.val - count, by omega⟩) else 0

/-- **An opened side in the fragment**: Miller occurrences, and every metavariable at its arity. -/
def InFragmentCode {n : Nat} (context : Ctx Head n) (count : Nat) (code : Tm Head (n + count)) : Prop :=
  miller (openedFlexible count) code = true ∧
    arities (openedFlexible count) (metaArity context count) code = true

instance {n : Nat} (context : Ctx Head n) (count : Nat) (code : Tm Head (n + count)) :
    Decidable (InFragmentCode context count code) := by
  unfold InFragmentCode
  infer_instance

variable {rules : Rules Head}

/-- **An equation of the dynamic pattern fragment**, read from the store alone. -/
def InFragment {Θ : Context rules} (equation : Equation (TotalTerm Θ)) : Prop :=
  TypeEq rules Θ.raw equation.1.1.code equation.2.1.code ∧
  Normal rules equation.1.1.code ∧
  ContextualDependentPatternSolver.lamDepth equation.1.2.code ≤ piCount equation.1.1.code ∧
  (∀ code, Star (R := rules) (openCode (ContextualDependentPatternSolver.lamDepth equation.1.2.code) equation.1.2.code)
      code → Normal rules code →
    InFragmentCode Θ.raw (ContextualDependentPatternSolver.lamDepth equation.1.2.code) code) ∧
  (∀ code, Star (R := rules) (openCode (ContextualDependentPatternSolver.lamDepth equation.1.2.code) equation.2.2.code)
      code → Normal rules code →
    InFragmentCode Θ.raw (ContextualDependentPatternSolver.lamDepth equation.1.2.code) code)

/-- **The dynamic pattern fragment** of equation stores. -/
def InFragmentStore {Θ : Context rules} (problem : EquationStore (TotalTerm Θ)) : Prop :=
  ∀ equation ∈ problem, InFragment equation

/-! ## Classification -/

/-- Each side with Miller occurrences is a Miller pattern spine or has a rigid head. -/
theorem side_shape {n : Nat} {flexible : Fin n → Bool} :
    ∀ (t : Tm Head n), miller flexible t = true →
      millerSpine flexible t = true ∨ flexHead flexible (spineHead t) = false
  | .var i, _ => by
      cases flexibleVariable : flexible i
      · exact .inr flexibleVariable
      · left
        simp [millerSpine, readSpine, flexibleVariable]
  | .app f a, holds => by
      by_cases flexibleSpine : flexHead flexible (spineHead f) = true
      · simp only [miller, flexibleSpine, if_true] at holds
        exact .inl holds
      · right
        cases h : flexHead flexible (spineHead f)
        · exact h
        · exact absurd h flexibleSpine
  | .const _, _ => .inr rfl
  | .head _, _ => .inr rfl
  | .pi _ _, _ => .inr rfl
  | .sigma _ _, _ => .inr rfl
  | .id _ _ _, _ => .inr rfl
  | .lam _, _ => .inr rfl
  | .pair _ _, _ => .inr rfl
  | .fst _, _ => .inr rfl
  | .snd _, _ => .inr rfl
  | .refl _, _ => .inr rfl

/-- **The kinds of a fragment equation.** -/
inductive Kind {n : Nat} (flexible : Fin n → Bool) (left right : Tm Head n) : Prop
  /-- A Miller pattern on the left, against any side. -/
  | patternLeft : millerSpine flexible left = true → Kind flexible left right
  /-- A Miller pattern on the right, against any side. -/
  | patternRight : millerSpine flexible right = true → Kind flexible left right
  /-- Two rigid sides with the same head. -/
  | rigidSame : flexHead flexible (spineHead left) = false → flexHead flexible (spineHead right) = false →
      spineHead left = spineHead right → Kind flexible left right
  /-- Two rigid sides with distinct heads. -/
  | rigidDistinct : flexHead flexible (spineHead left) = false → flexHead flexible (spineHead right) = false →
      spineHead left ≠ spineHead right → Kind flexible left right

/-- **Classification**: an opened equation whose sides have Miller occurrences is a pattern
equation (one side a Miller spine, the other anything, flex–flex included), or rigid–rigid with
equal or distinct spine heads. -/
theorem classification [DecidableEq Head] {n : Nat} {flexible : Fin n → Bool} {left right : Tm Head n}
    (leftMiller : miller flexible left = true) (rightMiller : miller flexible right = true) :
    Kind flexible left right := by
  rcases side_shape left leftMiller with pattern | leftRigid
  · exact .patternLeft pattern
  · rcases side_shape right rightMiller with pattern | rightRigid
    · exact .patternRight pattern
    · by_cases same : spineHead left = spineHead right
      · exact .rigidSame leftRigid rightRigid same
      · exact .rigidDistinct leftRigid rightRigid same

/-- **Decomposition stays in the fragment**: the function and argument of a rigid application, and
the components of every other former, keep Miller occurrences. -/
theorem decompose_app {n : Nat} {flexible : Fin n → Bool} {f a : Tm Head n}
    (rigid : flexHead flexible (spineHead f) = false) (holds : miller flexible (.app f a) = true) :
    miller flexible f = true ∧ miller flexible a = true := by
  simp only [miller, rigid, Bool.false_eq_true, if_false, Bool.and_eq_true] at holds
  exact holds

/-! ## Stability of an opened side -/

/-- **An opened side stays in the fragment** after a pattern instantiation followed by
normalization: its instantiation reduces to a normal side in the fragment. -/
theorem side_stable {R : Rules Head} (empty : R.computation = RootComputation.empty) {n n' count count' : Nat}
    {context : Ctx Head n} {context' : Ctx Head n'} {σ : Sub Head (n + count) (n' + count')}
    (inst : Instantiation R (openedFlexible count) (openedFlexible count') σ)
    (known : Arities inst (metaArity context count) (metaArity context' count'))
    {code : Tm Head (n + count)} (inside : InFragmentCode context count code) (normal : Normal R code) :
    ∃ code', Star (R := R) (subst σ code) code' ∧ Normal R code' ∧ InFragmentCode context' count' code' := by
  obtain ⟨code', steps, normal', miller', arities', -⟩ := stable empty code inst known inside.1 inside.2 normal
  exact ⟨code', steps, normal', miller', arities'⟩

/-! ## Membership from a computed normal form -/

section Membership

variable (empty : rules.computation = RootComputation.empty)
include empty

/-- Every normal reduct of a term is its normal form, by confluence. -/
theorem normal_reduct_unique {n : Nat} {x N code : Tm Head n} (toN : Star (R := rules) x N) (normalN : Normal rules N)
    (toCode : Star (R := rules) x code) (normalCode : Normal rules code) : code = N := by
  obtain ⟨common, fromN, fromCode⟩ := confluent empty toN toCode
  rw [normalN.star_eq fromN] at fromCode
  exact (normalCode.star_eq fromCode).symm

/-- **A side is in the fragment once one normal form is**: the condition on every normal form
follows from one computed normal form, by confluence. -/
theorem side_of_normal_form {n : Nat} {context : Ctx Head n} {count : Nat} {x N : Tm Head (n + count)}
    (toN : Star (R := rules) x N) (normalN : Normal rules N) (inside : InFragmentCode context count N) :
    ∀ code, Star (R := rules) x code → Normal rules code → InFragmentCode context count code := by
  intro code toCode normalCode
  rw [normal_reduct_unique empty toN normalN toCode normalCode]
  exact inside

omit empty in
/-- A side is outside the fragment when one of its normal forms is. -/
theorem side_not_of_normal_form {n : Nat} {context : Ctx Head n} {count : Nat} {x N : Tm Head (n + count)}
    (toN : Star (R := rules) x N) (normalN : Normal rules N) (outside : ¬ InFragmentCode context count N) :
    ¬ ∀ code, Star (R := rules) x code → Normal rules code → InFragmentCode context count code :=
  fun inside => outside (inside N toN normalN)

end Membership

end ContextualDependentDynamicFragment
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
