import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveTyping

/-!
# Typed definitional equality with eta for functions and pairs

This is the declarative equality `Γ ⊢ a ≡ b : A` of the parameterized
dependent calculus, defined together with the typing judgment that uses it.
It refines `FormationSensitive.Typing`, whose conversion rule uses the
untyped relation `Conv`, in one respect: types are compared by typed equality
at a universe, and typed equality validates

* beta for functions and both projections of pairs;
* the declared root computations of the rule package (definitions at their
  authored arity, recursors, and the computation rule of an admitted identity
  eliminator), each between two terms of the same type;
* eta for dependent functions, as extensionality: two functions are equal
  when their applications to a fresh variable are equal;
* eta for dependent pairs: two pairs are equal when their projections are;
* the universe-head equalities and cumulativity of the rule package;
* congruence for every term former.

Excluded: eta for a unit type (no unit former is primitive; a declared
one-constructor type has no eta), definitional uniqueness of identity proofs,
equality reflection (identity evidence never makes its endpoints equal), and
any rule acting on quoted syntax, which is not a term former here.

Every computation rule carries typing premises for both of its sides, so the
judgment says nothing about ill-typed redexes. Whether a particular rule
package makes its root steps type-preserving is an admission obligation, not
part of this definition.

The two judgments are one inductive family indexed by a statement, so that
structural metatheory can be proved by ordinary induction.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality

variable {Head : Type}

/-- The two forms of judgment: a term has a type, or two terms are equal at a
type. Each carries its own context length. -/
inductive Statement (Head : Type) : Type where
  | typing {n : Nat} (context : Ctx Head n) (term type : Tm Head n)
  | equality {n : Nat} (context : Ctx Head n) (left right type : Tm Head n)
  /-- A type is usable at another: cumulative subtyping of types. -/
  | sub {n : Nat} (context : Ctx Head n) (lower upper : Tm Head n)

/-- Derivable typing and typed-equality statements for one rule package. -/
inductive Derivable (R : Rules Head) : Statement Head → Prop where
  -- Typing
  | headType {n : Nat} {Γ : Ctx Head n} {h u : Head} :
      R.headTyping h u → Derivable R (.typing Γ (.head h) (.head u))
  | var {n : Nat} {Γ : Ctx Head n} (i : Fin n) :
      Derivable R (.typing Γ (.var i) (Ctx.lookup Γ i))
  | const {n : Nat} {Γ : Ctx Head n} {name : DeclName} {type : Tm Head 0}
      {u : Head} :
      R.constantType name = some type →
      Derivable R (.typing .nil type (.head u)) → R.isUniverse u →
      Derivable R (.typing Γ (.const name) (liftClosed type))
  | piForm {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} {B : Tm Head (n + 1)}
      {u v w : Head} :
      Derivable R (.typing Γ A (.head u)) → R.isUniverse u →
      Derivable R (.typing (.snoc Γ A) B (.head v)) → R.isUniverse v →
      R.join u v w → Derivable R (.typing Γ (.pi A B) (.head w))
  | sigmaForm {n : Nat} {Γ : Ctx Head n} {A : Tm Head n}
      {B : Tm Head (n + 1)} {u v w : Head} :
      Derivable R (.typing Γ A (.head u)) → R.isUniverse u →
      Derivable R (.typing (.snoc Γ A) B (.head v)) → R.isUniverse v →
      R.join u v w → Derivable R (.typing Γ (.sigma A B) (.head w))
  | lamIntro {n : Nat} {Γ : Ctx Head n} {A : Tm Head n}
      {body B : Tm Head (n + 1)} {u : Head} :
      Derivable R (.typing Γ (.pi A B) (.head u)) → R.isUniverse u →
      Derivable R (.typing (.snoc Γ A) body B) →
      Derivable R (.typing Γ (.lam body) (.pi A B))
  | appElim {n : Nat} {Γ : Ctx Head n} {g a A : Tm Head n}
      {B : Tm Head (n + 1)} :
      Derivable R (.typing Γ g (.pi A B)) → Derivable R (.typing Γ a A) →
      Derivable R (.typing Γ (.app g a) (inst0 a B))
  | pairIntro {n : Nat} {Γ : Ctx Head n} {a b A : Tm Head n}
      {B : Tm Head (n + 1)} {u : Head} :
      Derivable R (.typing Γ (.sigma A B) (.head u)) → R.isUniverse u →
      Derivable R (.typing Γ a A) → Derivable R (.typing Γ b (inst0 a B)) →
      Derivable R (.typing Γ (.pair a b) (.sigma A B))
  | fstElim {n : Nat} {Γ : Ctx Head n} {p A : Tm Head n}
      {B : Tm Head (n + 1)} :
      Derivable R (.typing Γ p (.sigma A B)) →
      Derivable R (.typing Γ (.fst p) A)
  | sndElim {n : Nat} {Γ : Ctx Head n} {p A : Tm Head n}
      {B : Tm Head (n + 1)} :
      Derivable R (.typing Γ p (.sigma A B)) →
      Derivable R (.typing Γ (.snd p) (inst0 (.fst p) B))
  | idForm {n : Nat} {Γ : Ctx Head n} {A a b : Tm Head n} {u : Head} :
      Derivable R (.typing Γ A (.head u)) → R.isUniverse u →
      Derivable R (.typing Γ a A) → Derivable R (.typing Γ b A) →
      Derivable R (.typing Γ (.id A a b) (.head u))
  | reflIntro {n : Nat} {Γ : Ctx Head n} {a A : Tm Head n} :
      Derivable R (.typing Γ a A) →
      Derivable R (.typing Γ (.refl a) (.id A a a))
  /-- A term of a type is a term of every type the type is usable at. -/
  | sub {n : Nat} {Γ : Ctx Head n} {t A B : Tm Head n} :
      Derivable R (.typing Γ t A) → Derivable R (.sub Γ A B) → Derivable R (.typing Γ t B)

  /-- Conversion by typed equality of types at a universe. -/
  | conv {n : Nat} {Γ : Ctx Head n} {t A B : Tm Head n} {u : Head} :
      Derivable R (.typing Γ t A) →
      Derivable R (.equality Γ A B (.head u)) → R.isUniverse u →
      Derivable R (.typing Γ t B)
  -- Equivalence and conversion of equality
  | refl {n : Nat} {Γ : Ctx Head n} {a A : Tm Head n} :
      Derivable R (.typing Γ a A) → Derivable R (.equality Γ a a A)
  | symm {n : Nat} {Γ : Ctx Head n} {a b A : Tm Head n} :
      Derivable R (.equality Γ a b A) → Derivable R (.equality Γ b a A)
  | trans {n : Nat} {Γ : Ctx Head n} {a b c A : Tm Head n} :
      Derivable R (.equality Γ a b A) → Derivable R (.equality Γ b c A) →
      Derivable R (.equality Γ a c A)
  | convEq {n : Nat} {Γ : Ctx Head n} {a b A B : Tm Head n} {u : Head} :
      Derivable R (.equality Γ a b A) →
      Derivable R (.equality Γ A B (.head u)) → R.isUniverse u →
      Derivable R (.equality Γ a b B)
  /-- An equality at a type holds at every type the type is usable at. -/
  | subEq {n : Nat} {Γ : Ctx Head n} {a b A B : Tm Head n} :
      Derivable R (.equality Γ a b A) → Derivable R (.sub Γ A B) →
      Derivable R (.equality Γ a b B)
  /-- Universe-head equality of the rule package, between typed heads. -/
  | headEq {n : Nat} {Γ : Ctx Head n} {h h' : Head} {A : Tm Head n} :
      R.headEq h h' →
      Derivable R (.typing Γ (.head h) A) →
      Derivable R (.typing Γ (.head h') A) →
      Derivable R (.equality Γ (.head h) (.head h') A)
  -- Congruence
  | piCong {n : Nat} {Γ : Ctx Head n} {A A' : Tm Head n}
      {B B' : Tm Head (n + 1)} {u v w : Head} :
      Derivable R (.equality Γ A A' (.head u)) → R.isUniverse u →
      Derivable R (.equality (.snoc Γ A) B B' (.head v)) → R.isUniverse v →
      R.join u v w →
      Derivable R (.equality Γ (.pi A B) (.pi A' B') (.head w))
  | sigmaCong {n : Nat} {Γ : Ctx Head n} {A A' : Tm Head n}
      {B B' : Tm Head (n + 1)} {u v w : Head} :
      Derivable R (.equality Γ A A' (.head u)) → R.isUniverse u →
      Derivable R (.equality (.snoc Γ A) B B' (.head v)) → R.isUniverse v →
      R.join u v w →
      Derivable R (.equality Γ (.sigma A B) (.sigma A' B') (.head w))
  | idCong {n : Nat} {Γ : Ctx Head n} {A A' a a' b b' : Tm Head n}
      {u : Head} :
      Derivable R (.equality Γ A A' (.head u)) → R.isUniverse u →
      Derivable R (.equality Γ a a' A) → Derivable R (.equality Γ b b' A) →
      Derivable R (.equality Γ (.id A a b) (.id A' a' b') (.head u))
  | lamCong {n : Nat} {Γ : Ctx Head n} {A : Tm Head n}
      {body body' B : Tm Head (n + 1)} {u : Head} :
      Derivable R (.typing Γ (.pi A B) (.head u)) → R.isUniverse u →
      Derivable R (.equality (.snoc Γ A) body body' B) →
      Derivable R (.equality Γ (.lam body) (.lam body') (.pi A B))
  | appCong {n : Nat} {Γ : Ctx Head n} {f g a b A : Tm Head n}
      {B : Tm Head (n + 1)} :
      Derivable R (.equality Γ f g (.pi A B)) →
      Derivable R (.equality Γ a b A) →
      Derivable R (.equality Γ (.app f a) (.app g b) (inst0 a B))
  | pairCong {n : Nat} {Γ : Ctx Head n} {a a' b b' A : Tm Head n}
      {B : Tm Head (n + 1)} {u : Head} :
      Derivable R (.typing Γ (.sigma A B) (.head u)) → R.isUniverse u →
      Derivable R (.equality Γ a a' A) →
      Derivable R (.equality Γ b b' (inst0 a B)) →
      Derivable R (.equality Γ (.pair a b) (.pair a' b') (.sigma A B))
  | fstCong {n : Nat} {Γ : Ctx Head n} {p q A : Tm Head n}
      {B : Tm Head (n + 1)} :
      Derivable R (.equality Γ p q (.sigma A B)) →
      Derivable R (.equality Γ (.fst p) (.fst q) A)
  | sndCong {n : Nat} {Γ : Ctx Head n} {p q A : Tm Head n}
      {B : Tm Head (n + 1)} :
      Derivable R (.equality Γ p q (.sigma A B)) →
      Derivable R (.equality Γ (.snd p) (.snd q) (inst0 (.fst p) B))
  | reflCong {n : Nat} {Γ : Ctx Head n} {a b A : Tm Head n} :
      Derivable R (.equality Γ a b A) →
      Derivable R (.equality Γ (.refl a) (.refl b) (.id A a a))
  -- Computation
  | betaPi {n : Nat} {Γ : Ctx Head n} {A a : Tm Head n}
      {body B : Tm Head (n + 1)} {u : Head} :
      Derivable R (.typing Γ (.pi A B) (.head u)) → R.isUniverse u →
      Derivable R (.typing (.snoc Γ A) body B) → Derivable R (.typing Γ a A) →
      Derivable R (.equality Γ (.app (.lam body) a) (inst0 a body) (inst0 a B))
  | betaFst {n : Nat} {Γ : Ctx Head n} {A a b : Tm Head n}
      {B : Tm Head (n + 1)} {u : Head} :
      Derivable R (.typing Γ (.sigma A B) (.head u)) → R.isUniverse u →
      Derivable R (.typing Γ a A) → Derivable R (.typing Γ b (inst0 a B)) →
      Derivable R (.equality Γ (.fst (.pair a b)) a A)
  | betaSnd {n : Nat} {Γ : Ctx Head n} {A a b : Tm Head n}
      {B : Tm Head (n + 1)} {u : Head} :
      Derivable R (.typing Γ (.sigma A B) (.head u)) → R.isUniverse u →
      Derivable R (.typing Γ a A) → Derivable R (.typing Γ b (inst0 a B)) →
      Derivable R (.equality Γ (.snd (.pair a b)) b (inst0 a B))
  /-- A declared root computation between two terms of one type. -/
  | root {n : Nat} {Γ : Ctx Head n} {left right A : Tm Head n} :
      R.computation.step left right →
      Derivable R (.typing Γ left A) → Derivable R (.typing Γ right A) →
      Derivable R (.equality Γ left right A)
  -- Eta
  /-- Functions are equal when their applications to a fresh variable are. -/
  | etaPi {n : Nat} {Γ : Ctx Head n} {f g A : Tm Head n}
      {B : Tm Head (n + 1)} :
      Derivable R (.typing Γ f (.pi A B)) →
      Derivable R (.typing Γ g (.pi A B)) →
      Derivable R (.equality (.snoc Γ A)
        (.app (rename wk f) (.var 0)) (.app (rename wk g) (.var 0)) B) →
      Derivable R (.equality Γ f g (.pi A B))
  /-- Pairs are equal when their projections are. -/
  | etaSigma {n : Nat} {Γ : Ctx Head n} {p q A : Tm Head n}
      {B : Tm Head (n + 1)} :
      Derivable R (.typing Γ p (.sigma A B)) →
      Derivable R (.typing Γ q (.sigma A B)) →
      Derivable R (.equality Γ (.fst p) (.fst q) A) →
      Derivable R (.equality Γ (.snd p) (.snd q) (inst0 (.fst p) B)) →
      Derivable R (.equality Γ p q (.sigma A B))
  -- Cumulative subtyping of types: equal types, universes by cumulativity,
  -- dependent function types with equal domains and codomains below, and
  -- dependent pair types with both components below. The Π and Σ cases carry
  -- the well-formedness of both sides, so that inversion never needs the
  -- well-formedness of a middle type.
  | subEqual {n : Nat} {Γ : Ctx Head n} {A B : Tm Head n} {u : Head} :
      Derivable R (.equality Γ A B (.head u)) → R.isUniverse u →
      Derivable R (.sub Γ A B)
  | subUniv {n : Nat} {Γ : Ctx Head n} {u v : Head} :
      R.cumulative u v → Derivable R (.sub Γ (.head u) (.head v))
  | subPi {n : Nat} {Γ : Ctx Head n} {A A' : Tm Head n} {B B' : Tm Head (n + 1)}
      {u u' w : Head} :
      Derivable R (.typing Γ (.pi A B) (.head u)) → R.isUniverse u →
      Derivable R (.typing Γ (.pi A' B') (.head u')) → R.isUniverse u' →
      Derivable R (.equality Γ A A' (.head w)) → R.isUniverse w →
      Derivable R (.sub (.snoc Γ A) B B') →
      Derivable R (.sub Γ (.pi A B) (.pi A' B'))
  | subSigma {n : Nat} {Γ : Ctx Head n} {A A' : Tm Head n} {B B' : Tm Head (n + 1)}
      {u u' : Head} :
      Derivable R (.typing Γ (.sigma A B) (.head u)) → R.isUniverse u →
      Derivable R (.typing Γ (.sigma A' B') (.head u')) → R.isUniverse u' →
      Derivable R (.sub Γ A A') → Derivable R (.sub (.snoc Γ A) B B') →
      Derivable R (.sub Γ (.sigma A B) (.sigma A' B'))
  | subTrans {n : Nat} {Γ : Ctx Head n} {A B C : Tm Head n} :
      Derivable R (.sub Γ A B) → Derivable R (.sub Γ B C) → Derivable R (.sub Γ A C)

/-- `Γ ⊢ t : A`. -/
abbrev Typed (R : Rules Head) {n : Nat} (Γ : Ctx Head n) (t A : Tm Head n) :
    Prop :=
  Derivable R (.typing Γ t A)

/-- `Γ ⊢ a ≡ b : A`. -/
abbrev Equal (R : Rules Head) {n : Nat} (Γ : Ctx Head n) (a b A : Tm Head n) :
    Prop :=
  Derivable R (.equality Γ a b A)

/-- `Γ ⊢ A ⊑ B`: a term of `A` is a term of `B`. -/
abbrev Below (R : Rules Head) {n : Nat} (Γ : Ctx Head n) (A B : Tm Head n) : Prop :=
  Derivable R (.sub Γ A B)

/-- A term of a universe is a term of every universe above it: subtyping along
universe cumulativity. -/
theorem Derivable.cumul {R : Rules Head} {n : Nat} {Γ : Ctx Head n} {t : Tm Head n}
    {u v : Head} (typing : Derivable R (.typing Γ t (.head u))) (c : R.cumulative u v) :
    Derivable R (.typing Γ t (.head v)) :=
  .sub typing (.subUniv c)

/-- An equality at a universe holds at every universe above it. -/
theorem Derivable.cumulEq {R : Rules Head} {n : Nat} {Γ : Ctx Head n} {A B : Tm Head n}
    {u v : Head} (equal : Derivable R (.equality Γ A B (.head u))) (c : R.cumulative u v) :
    Derivable R (.equality Γ A B (.head v)) :=
  .subEq equal (.subUniv c)

end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
