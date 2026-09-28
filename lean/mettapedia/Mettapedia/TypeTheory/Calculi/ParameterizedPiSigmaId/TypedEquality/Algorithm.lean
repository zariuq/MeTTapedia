import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Judgment

/-!
# The type-directed conversion algorithm, as a relation

This is the relation computed by the kernel's conversion (`regular_conv_at`,
`regular_conv_neutral` and `regular_conv_types` in the C runtime). Reduction
is the contextual step relation of the rule package, without eta. Terms are
compared at a type:

* at a type reducing to a dependent function type, both sides are applied to
  a fresh variable and compared at the codomain;
* at a type reducing to a dependent pair type, their projections are compared;
* at a universe, both sides are compared as types, by their formers;
* at an identity type, two reflexivity proofs are compared by their subjects;
* otherwise both sides reduce to neutral terms with equal heads, and
  arguments are compared at the types the head's type assigns.

Soundness (every related pair is equal in `Equal`) and completeness on the
admissible class are stated against this relation; both need injectivity of
type formers, which comes from the normalization model.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality

variable {Head : Type}

/-- Reduction of the rule package: the reflexive-transitive closure of its
contextual steps. -/
abbrev Reduces (R : Rules Head) {n : Nat} (t u : Tm Head n) : Prop :=
  Relation.ReflTransGen (StepCore R.computation R.headEq) t u

/-- The three comparisons of the algorithm, indexed by one statement type. -/
inductive AlgorithmStatement (Head : Type) : Type where
  /-- `a` and `b` agree at the type `type`. -/
  | compare {n : Nat} (context : Ctx Head n) (left right type : Tm Head n)
  /-- The neutral terms `left` and `right` agree, and `type` is the type the
  head of `left` assigns. -/
  | neutral {n : Nat} (context : Ctx Head n) (left right type : Tm Head n)
  /-- `left` and `right` agree as types. -/
  | types {n : Nat} (context : Ctx Head n) (left right : Tm Head n)

/-- Derivations of the algorithm. -/
inductive Algorithm (R : Rules Head) : AlgorithmStatement Head → Prop where
  | pi {n : Nat} {Γ : Ctx Head n} {a b T A : Tm Head n} {B : Tm Head (n + 1)} :
      Reduces R T (.pi A B) →
      Algorithm R (.compare (.snoc Γ A)
        (.app (rename wk a) (.var 0)) (.app (rename wk b) (.var 0)) B) →
      Algorithm R (.compare Γ a b T)
  | sigma {n : Nat} {Γ : Ctx Head n} {a b T A : Tm Head n}
      {B : Tm Head (n + 1)} :
      Reduces R T (.sigma A B) →
      Algorithm R (.compare Γ (.fst a) (.fst b) A) →
      Algorithm R (.compare Γ (.snd a) (.snd b) (inst0 (.fst a) B)) →
      Algorithm R (.compare Γ a b T)
  | sort {n : Nat} {Γ : Ctx Head n} {a b T : Tm Head n} {u : Head} :
      Reduces R T (.head u) → R.isUniverse u →
      Algorithm R (.types Γ a b) →
      Algorithm R (.compare Γ a b T)
  | reflexivity {n : Nat} {Γ : Ctx Head n} {a b T A x y a' b' : Tm Head n} :
      Reduces R T (.id A x y) →
      Reduces R a (.refl a') → Reduces R b (.refl b') →
      Algorithm R (.compare Γ a' b' A) →
      Algorithm R (.compare Γ a b T)
  | neutralAt {n : Nat} {Γ : Ctx Head n} {a b T a' b' U : Tm Head n} :
      Reduces R a a' → Reduces R b b' →
      Algorithm R (.neutral Γ a' b' U) →
      Algorithm R (.compare Γ a b T)
  | var {n : Nat} {Γ : Ctx Head n} (i : Fin n) :
      Algorithm R (.neutral Γ (.var i) (.var i) (Ctx.lookup Γ i))
  | const {n : Nat} {Γ : Ctx Head n} {name : DeclName} {type : Tm Head 0} :
      R.constantType name = some type →
      Algorithm R (.neutral Γ (.const name) (.const name) (liftClosed type))
  | app {n : Nat} {Γ : Ctx Head n} {f g a b U A : Tm Head n}
      {B : Tm Head (n + 1)} :
      Algorithm R (.neutral Γ f g U) → Reduces R U (.pi A B) →
      Algorithm R (.compare Γ a b A) →
      Algorithm R (.neutral Γ (.app f a) (.app g b) (inst0 a B))
  | fst {n : Nat} {Γ : Ctx Head n} {p q U A : Tm Head n}
      {B : Tm Head (n + 1)} :
      Algorithm R (.neutral Γ p q U) → Reduces R U (.sigma A B) →
      Algorithm R (.neutral Γ (.fst p) (.fst q) A)
  | snd {n : Nat} {Γ : Ctx Head n} {p q U A : Tm Head n}
      {B : Tm Head (n + 1)} :
      Algorithm R (.neutral Γ p q U) → Reduces R U (.sigma A B) →
      Algorithm R (.neutral Γ (.snd p) (.snd q) (inst0 (.fst p) B))
  | heads {n : Nat} {Γ : Ctx Head n} {A B : Tm Head n} {h h' : Head} :
      Reduces R A (.head h) → Reduces R B (.head h') →
      (h = h' ∨ R.headEq h h') →
      Algorithm R (.types Γ A B)
  | piTypes {n : Nat} {Γ : Ctx Head n} {A B A₁ A₂ : Tm Head n}
      {B₁ B₂ : Tm Head (n + 1)} :
      Reduces R A (.pi A₁ B₁) → Reduces R B (.pi A₂ B₂) →
      Algorithm R (.types Γ A₁ A₂) →
      Algorithm R (.types (.snoc Γ A₁) B₁ B₂) →
      Algorithm R (.types Γ A B)
  | sigmaTypes {n : Nat} {Γ : Ctx Head n} {A B A₁ A₂ : Tm Head n}
      {B₁ B₂ : Tm Head (n + 1)} :
      Reduces R A (.sigma A₁ B₁) → Reduces R B (.sigma A₂ B₂) →
      Algorithm R (.types Γ A₁ A₂) →
      Algorithm R (.types (.snoc Γ A₁) B₁ B₂) →
      Algorithm R (.types Γ A B)
  | idTypes {n : Nat} {Γ : Ctx Head n} {A B C C' x x' y y' : Tm Head n} :
      Reduces R A (.id C x y) → Reduces R B (.id C' x' y') →
      Algorithm R (.types Γ C C') →
      Algorithm R (.compare Γ x x' C) → Algorithm R (.compare Γ y y' C) →
      Algorithm R (.types Γ A B)
  | neutralTypes {n : Nat} {Γ : Ctx Head n} {A B A' B' U : Tm Head n} :
      Reduces R A A' → Reduces R B B' →
      Algorithm R (.neutral Γ A' B' U) →
      Algorithm R (.types Γ A B)

end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
