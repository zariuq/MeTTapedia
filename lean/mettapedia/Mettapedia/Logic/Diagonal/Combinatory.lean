import Mathlib.Data.Set.Operations
import Mettapedia.Logic.Diagonal.Lawvere

/-!
# Reflexive structures: codes that run on codes, up to an equivalence

A *reflexive structure* is an applicative carrier with an equivalence that
application respects, a constant combinator, and a code for every polynomial in
one variable, all laws holding up to the equivalence.  The last field is
point-surjectivity of application onto the polynomial maps
(`Reflexive.pointSurjectiveOn`): combinatory completeness in one variable.  The
untyped λ-calculus modulo β-conversion is the motivating instance (see the
reflective bubble module).

**Positive reading.**  Polynomial maps are closed under diagonal composites,
so every polynomial has a fixed point (`Reflexive.fixedPoint_spec`, the
diagonal step of `Mettapedia.Logic.Diagonal`), and so does every element acting
by application (`Reflexive.elementFixedPoint_spec`): the fixed-point
combinator, without a primitive for recursion.

**Negative reading.**  Truth and falsity are the selectors `K` and `K I`.
* No polynomial decides a property that is invariant under the equivalence,
  holds at some `yes` and fails at some `no` (`Reflexive.not_decides`, the
  Scott–Curry theorem in this form); in particular no element decides the
  equivalence itself between two inequivalent elements
  (`Reflexive.no_equality_decider`).
* A *sound* partial decider is undetermined at its own diagonal
  (`Reflexive.sound_undetermined`): its answer there is neither truth nor
  falsity.  This is the partial escape at the level of internal procedures.
* A decider that is exact on a fragment excludes its diagonal from the
  fragment (`Reflexive.diagonal_not_mem_fragment`): internal carve-outs are
  proper.
* Deciding the equivalence internally collapses the structure: if truth and
  falsity are equivalent, all elements are (`Reflexive.trivial_of_truth_equiv`).

**Controls.**  The one-point structure is reflexive and every property on it is
trivial (`unitReflexive`, `unitReflexive_decides`): the negative theorems need
a property that holds somewhere and fails somewhere.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.Diagonal

universe u

/-- Applicative polynomials in one variable over a carrier: the variable,
constants, and application. -/
inductive AppPolynomial (T : Type u) where
  | var : AppPolynomial T
  | const (value : T) : AppPolynomial T
  | app (function argument : AppPolynomial T) : AppPolynomial T

namespace AppPolynomial

variable {T : Type u}

/-- Evaluation at a value of the variable. -/
def eval (apply : T → T → T) : AppPolynomial T → T → T
  | var, value => value
  | const constant, _ => constant
  | app function argument, value => apply (function.eval apply value) (argument.eval apply value)

/-- Substitution of a polynomial for the variable. -/
def subst : AppPolynomial T → AppPolynomial T → AppPolynomial T
  | var, replacement => replacement
  | const constant, _ => const constant
  | app function argument, replacement =>
      app (function.subst replacement) (argument.subst replacement)

theorem eval_subst (apply : T → T → T) (replacement : AppPolynomial T) :
    ∀ (polynomial : AppPolynomial T) (value : T),
      (polynomial.subst replacement).eval apply value =
        polynomial.eval apply (replacement.eval apply value)
  | var, _ => rfl
  | const _, _ => rfl
  | app function argument, value => by
      simp only [subst, eval, eval_subst apply replacement function value,
        eval_subst apply replacement argument value]

/-- Self-application of the variable. -/
def selfApply : AppPolynomial T := app var var

end AppPolynomial

/-- **A reflexive structure**: codes run on codes, point-surjectively onto the
polynomial maps, up to an equivalence that application respects. -/
structure Reflexive (T : Type u) where
  /-- The equivalence up to which the laws hold. -/
  Equiv : T → T → Prop
  equivalence : Equivalence Equiv
  /-- Running one element on another. -/
  apply : T → T → T
  apply_congr : ∀ {function function' argument argument' : T}, Equiv function function' →
    Equiv argument argument' → Equiv (apply function argument) (apply function' argument')
  /-- The constant combinator. -/
  constant : T
  constant_law : ∀ first second, Equiv (apply (apply constant first) second) first
  /-- A code for every polynomial in one variable. -/
  code : AppPolynomial T → T
  code_law : ∀ polynomial value, Equiv (apply (code polynomial) value) (polynomial.eval apply value)

namespace Reflexive

variable {T : Type u} (A : Reflexive T)

theorem refl (value : T) : A.Equiv value value := A.equivalence.refl value

theorem symm {first second : T} (h : A.Equiv first second) : A.Equiv second first :=
  A.equivalence.symm h

theorem trans {first second third : T} (h : A.Equiv first second)
    (h' : A.Equiv second third) : A.Equiv first third :=
  A.equivalence.trans h h'

/-- The polynomial maps. -/
def polynomialMaps : Set (T → T) :=
  Set.range fun polynomial : AppPolynomial T => polynomial.eval A.apply

/-- **Point-surjectivity**: every polynomial map is represented by its code. -/
theorem pointSurjectiveOn : PointSurjectiveOn A.apply A.Equiv A.polynomialMaps := by
  rintro _ ⟨polynomial, rfl⟩
  exact ⟨A.code polynomial, A.code_law polynomial⟩

/-- AppPolynomial maps are closed under diagonal composites. -/
theorem diagonalComposite_mem (polynomial : AppPolynomial T) :
    diagonalComposite A.apply (polynomial.eval A.apply) ∈ A.polynomialMaps :=
  ⟨polynomial.subst AppPolynomial.selfApply, funext fun value =>
    AppPolynomial.eval_subst A.apply AppPolynomial.selfApply polynomial value⟩

/-- The code whose self-application is the fixed point of a polynomial. -/
def diagonalCode (polynomial : AppPolynomial T) : T :=
  A.code (polynomial.subst AppPolynomial.selfApply)

/-- The fixed point of a polynomial: its diagonal code run on itself. -/
def fixedPoint (polynomial : AppPolynomial T) : T :=
  A.apply (A.diagonalCode polynomial) (A.diagonalCode polynomial)

/-- **Every polynomial has a fixed point**, by the diagonal step. -/
theorem fixedPoint_spec (polynomial : AppPolynomial T) :
    A.Equiv (A.fixedPoint polynomial) (polynomial.eval A.apply (A.fixedPoint polynomial)) :=
  diagonal A.apply A.Equiv (polynomial.eval A.apply) fun value => by
    have law := A.code_law (polynomial.subst AppPolynomial.selfApply) value
    rwa [AppPolynomial.eval_subst] at law

/-- The fixed point of an element acting by application. -/
def elementFixedPoint (function : T) : T :=
  A.fixedPoint (.app (.const function) .var)

/-- **Every element has a fixed point**: `X ≈ f X`. -/
theorem elementFixedPoint_spec (function : T) :
    A.Equiv (A.elementFixedPoint function) (A.apply function (A.elementFixedPoint function)) :=
  A.fixedPoint_spec _

/-! ## Truth values -/

/-- The identity. -/
def identity : T := A.code .var

theorem identity_law (value : T) : A.Equiv (A.apply A.identity value) value :=
  A.code_law .var value

/-- Truth selects its first argument. -/
def truth : T := A.constant

/-- Falsity selects its second argument. -/
def falsity : T := A.apply A.constant A.identity

theorem truth_law (first second : T) : A.Equiv (A.apply (A.apply A.truth first) second) first :=
  A.constant_law first second

theorem falsity_law (first second : T) :
    A.Equiv (A.apply (A.apply A.falsity first) second) second :=
  A.trans (A.apply_congr (A.constant_law A.identity first) (A.refl second))
    (A.identity_law second)

/-- Selecting with an answer equivalent to truth gives the first branch. -/
theorem select_of_truth {answer : T} (isTruth : A.Equiv answer A.truth) (first second : T) :
    A.Equiv (A.apply (A.apply answer first) second) first :=
  A.trans (A.apply_congr (A.apply_congr isTruth (A.refl first)) (A.refl second))
    (A.truth_law first second)

/-- Selecting with an answer equivalent to falsity gives the second branch. -/
theorem select_of_falsity {answer : T} (isFalsity : A.Equiv answer A.falsity) (first second : T) :
    A.Equiv (A.apply (A.apply answer first) second) second :=
  A.trans (A.apply_congr (A.apply_congr isFalsity (A.refl first)) (A.refl second))
    (A.falsity_law first second)

/-- **Truth equivalent to falsity collapses the structure.** -/
theorem trivial_of_truth_equiv (collapse : A.Equiv A.truth A.falsity) (first second : T) :
    A.Equiv first second :=
  A.trans (A.symm (A.select_of_truth (A.refl A.truth) first second))
    (A.select_of_falsity collapse first second)

/-! ## Deciders and their diagonal -/

/-- A polynomial decides `P` when its value is truth where `P` holds and falsity
where it fails. -/
def Decides (P : T → Prop) (decider : AppPolynomial T) : Prop :=
  ∀ value, (A.Equiv (decider.eval A.apply value) A.truth ∧ P value) ∨
    (A.Equiv (decider.eval A.apply value) A.falsity ∧ ¬ P value)

/-- A polynomial soundly decides `P` when truth implies `P` and falsity implies
`¬ P`; elsewhere it may answer nothing. -/
def SoundlyDecides (P : T → Prop) (decider : AppPolynomial T) : Prop :=
  ∀ value, (A.Equiv (decider.eval A.apply value) A.truth → P value) ∧
    (A.Equiv (decider.eval A.apply value) A.falsity → ¬ P value)

/-- The swap of a decider, as a polynomial: answer `no` on truth and `yes` on
falsity. -/
def swapPolynomial (decider : AppPolynomial T) (yes no : T) : AppPolynomial T :=
  .app (.app decider (.const no)) (.const yes)

/-- **The diagonal of a decider**: a fixed point of its swap. -/
def decisionDiagonal (decider : AppPolynomial T) (yes no : T) : T :=
  A.fixedPoint (swapPolynomial decider yes no)

theorem decisionDiagonal_spec (decider : AppPolynomial T) (yes no : T) :
    A.Equiv (A.decisionDiagonal decider yes no)
      (A.apply (A.apply (decider.eval A.apply (A.decisionDiagonal decider yes no)) no) yes) :=
  A.fixedPoint_spec (swapPolynomial decider yes no)

variable {A}

/-- At the diagonal, an answer equivalent to truth makes the diagonal
equivalent to `no`. -/
theorem diagonal_equiv_no {decider : AppPolynomial T} {yes no : T}
    (isTruth : A.Equiv (decider.eval A.apply (A.decisionDiagonal decider yes no)) A.truth) :
    A.Equiv (A.decisionDiagonal decider yes no) no :=
  A.trans (A.decisionDiagonal_spec decider yes no) (A.select_of_truth isTruth no yes)

/-- At the diagonal, an answer equivalent to falsity makes the diagonal
equivalent to `yes`. -/
theorem diagonal_equiv_yes {decider : AppPolynomial T} {yes no : T}
    (isFalsity : A.Equiv (decider.eval A.apply (A.decisionDiagonal decider yes no)) A.falsity) :
    A.Equiv (A.decisionDiagonal decider yes no) yes :=
  A.trans (A.decisionDiagonal_spec decider yes no) (A.select_of_falsity isFalsity no yes)

/-- **Sound deciders are undetermined at their diagonal.**  For an invariant
property holding at `yes` and failing at `no`, a sound partial decider answers
neither truth nor falsity at its diagonal. -/
theorem sound_undetermined {P : T → Prop}
    (invariant : ∀ {first second : T}, A.Equiv first second → (P first ↔ P second))
    {yes no : T} (yesHolds : P yes) (noFails : ¬ P no) {decider : AppPolynomial T}
    (sound : A.SoundlyDecides P decider) :
    ¬ A.Equiv (decider.eval A.apply (A.decisionDiagonal decider yes no)) A.truth ∧
      ¬ A.Equiv (decider.eval A.apply (A.decisionDiagonal decider yes no)) A.falsity := by
  constructor
  · intro isTruth
    exact noFails ((invariant (diagonal_equiv_no isTruth)).mp ((sound _).1 isTruth))
  · intro isFalsity
    exact (sound _).2 isFalsity ((invariant (diagonal_equiv_yes isFalsity)).mpr yesHolds)

/-- **The diagonal escapes every fragment on which a decider is exact.** -/
theorem diagonal_not_mem_fragment {P : T → Prop}
    (invariant : ∀ {first second : T}, A.Equiv first second → (P first ↔ P second))
    {yes no : T} (yesHolds : P yes) (noFails : ¬ P no) {decider : AppPolynomial T}
    {Fragment : T → Prop}
    (exact : ∀ value, Fragment value →
      (A.Equiv (decider.eval A.apply value) A.truth ∧ P value) ∨
        (A.Equiv (decider.eval A.apply value) A.falsity ∧ ¬ P value)) :
    ¬ Fragment (A.decisionDiagonal decider yes no) := by
  intro member
  rcases exact _ member with ⟨isTruth, holds⟩ | ⟨isFalsity, fails⟩
  · exact noFails ((invariant (diagonal_equiv_no isTruth)).mp holds)
  · exact fails ((invariant (diagonal_equiv_yes isFalsity)).mpr yesHolds)

/-- **Scott–Curry, in this form**: no polynomial decides an invariant property
that holds at `yes` and fails at `no`. -/
theorem not_decides {P : T → Prop}
    (invariant : ∀ {first second : T}, A.Equiv first second → (P first ↔ P second))
    {yes no : T} (yesHolds : P yes) (noFails : ¬ P no) (decider : AppPolynomial T) :
    ¬ A.Decides P decider := fun decides =>
  diagonal_not_mem_fragment (Fragment := fun _ => True) invariant yesHolds noFails
    (fun value _ => decides value) trivial

/-- A binary decider of the equivalence, as an element. -/
def DecidesEquiv (A : Reflexive T) (decider : T) : Prop :=
  ∀ first second,
    (A.Equiv (A.apply (A.apply decider first) second) A.truth ∧ A.Equiv first second) ∨
      (A.Equiv (A.apply (A.apply decider first) second) A.falsity ∧ ¬ A.Equiv first second)

/-- The unary decider "equivalent to `target`" obtained from a binary one. -/
def equivDecider (decider target : T) : AppPolynomial T :=
  .app (.app (.const decider) .var) (.const target)

/-- **No element decides the equivalence** as soon as two elements are
inequivalent. -/
theorem no_equality_decider {first second : T} (distinct : ¬ A.Equiv first second)
    (decider : T) : ¬ A.DecidesEquiv decider := by
  intro decides
  refine not_decides (A := A) (P := fun value => A.Equiv value first)
    (fun related => ⟨fun held => A.trans (A.symm related) held, fun held => A.trans related held⟩)
    (A.refl first) (fun related => distinct (A.symm related)) (equivDecider decider first) ?_
  intro value
  exact decides value first

/-- **Deciding the equivalence internally collapses the structure.** -/
theorem trivial_of_decidesEquiv {decider : T} (decides : A.DecidesEquiv decider)
    (first second : T) : A.Equiv first second := by
  rcases decides first second with ⟨_, related⟩ | ⟨_, distinct⟩
  · exact related
  · exact absurd decides (no_equality_decider distinct decider)

end Reflexive

/-! ## Control: the one-point structure -/

/-- The one-point reflexive structure. -/
def unitReflexive : Reflexive Unit where
  Equiv _ _ := True
  equivalence := ⟨fun _ => trivial, fun _ => trivial, fun _ _ => trivial⟩
  apply _ _ := ()
  apply_congr _ _ := trivial
  constant := ()
  constant_law _ _ := trivial
  code _ := ()
  code_law _ _ := trivial

/-- **Control.**  On the one-point structure every element decides the
equivalence: the negative theorems need two inequivalent elements. -/
theorem unitReflexive_decides : unitReflexive.DecidesEquiv () :=
  fun _ _ => Or.inl ⟨trivial, trivial⟩

end Mettapedia.Logic.Diagonal
