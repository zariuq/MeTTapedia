import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Consistency.Data

/-!
# The meaning of codes

Under a reading, a code denotes a meaning. Codes are read by weak-head
reduction:

* `imp p q` means the reading's implication of the meanings of `p` and `q`;
* `eq@A x y` means the reading's equation of the meanings of `x` and `y` at `A`;
* `all@A f` means the reading's quantification of the meanings of `f` at every
  meaning at `A`;
* a neutral code means the reading's neutral meaning.

The quantifier clause is Girard's. A meaning at a generic carrier is not a
term but a value: a meaning of codes, a point, or a function of meanings. The
quantifier ranges over all of them, not only over the meanings that codes
happen to have.

So that `f` can be applied to an arbitrary meaning, terms live in a world:
their free variables are generics, each carrying a generic carrier and a
meaning. To read `f` at `A → B` for a generic carrier `A`, the world is
extended by a generic of carrier `A`, and `f` is applied to that generic. A
generic applied to arguments denotes its meaning at the arguments' meanings.

Data is the exception: it is inspected by computation, so it is represented
by terms. A term related to itself at a data carrier means its value, and a
function on a data carrier is read at every such term, in every world reached
by a morphism.

Under the reading by truth values, a code means a Lean proposition: its truth.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace Consistency

open Normalization

variable {Head : Type} (S : Reading Head)

mutual

/-- The meaning of a code in a world. -/
inductive Truth : {n : Nat} → World S n → Tm Head n → S.P → Prop where
  | imp {n : Nat} {ξ : World S n} {t p q : Tm Head n} {X Y : S.P} :
      WhRed S.rules S.roles t (.app (.app (.const S.imp) p) q) →
      Truth ξ p X → Truth ξ q Y → Truth ξ t (S.impMeaning X Y)
  | all {n : Nat} {ξ : World S n} {t f : Tm Head n} {a : DeclName} {k : Kind}
      {A : Carrier k} {φ : A.V S → S.P} :
      S.allCarrier a = some ⟨k, A⟩ →
      WhRed S.rules S.roles t (.app (.const a) f) →
      Read ξ f (.arr A .prop) φ →
      Truth ξ t (S.allMeaning A φ)
  | eq {n : Nat} {ξ : World S n} {t x y : Tm Head n} {e : DeclName} {k : Kind}
      {A : Carrier k} {v w : A.V S} :
      S.eqCarrier e = some ⟨k, A⟩ →
      WhRed S.rules S.roles t (.app (.app (.const e) x) y) →
      Read ξ x A v → Read ξ y A w →
      Truth ξ t (S.eqMeaning A v w)
  | generic {n : Nat} {ξ : World S n} {t : Tm Head n} {i : Fin n}
      {args : List (Tm Head n)} {X : S.P} :
      WhRed S.rules S.roles t (appSpine (.var i) args) →
      Apply ξ (ξ i).1 (ξ i).2 args X →
      Truth ξ t X
  | neutral {n : Nat} {ξ : World S n} {t s : Tm Head n} :
      WhRed S.rules S.roles t s → S.neutral s →
      Truth ξ t S.neutralMeaning

/-- The meaning of a term at a carrier, in a world. -/
inductive Read : {n : Nat} → World S n → Tm Head n → {k : Kind} → (A : Carrier k) →
    A.V S → Prop where
  | prop {n : Nat} {ξ : World S n} {t : Tm Head n} {X : S.P} :
      Truth ξ t X → Read ξ t .prop X
  | rigid {n : Nat} {ξ : World S n} {t : Tm Head n} {T : DeclName}
      {u : (Carrier.rigid T).V S} :
      Read ξ t (.rigid T) u
  | data {n : Nat} {ξ : World S n} {t : Tm Head n} {D : Carrier .data}
      (related : DataEq S.toDataSetting D t t) :
      Read ξ t D (dataValue S.toDataSetting D t related)
  | dataArg {n : Nat} {ξ : World S n} {t : Tm Head n} {A : Carrier .data}
      {B : Carrier .gen} {φ : (Carrier.arr A B).V S} :
      (∀ {m : Nat} {ξ' : World S m} {ρ : Ren n m}, Morph ξ ξ' ρ →
        ∀ {s : Tm Head m} (related : DataEq S.toDataSetting A s s),
          Read ξ' (.app (Presentation.rename ρ t) s) B
            (φ (dataValue S.toDataSetting A s related))) →
      Read ξ t (.arr A B) φ
  | genericArg {n : Nat} {ξ : World S n} {t : Tm Head n} {A B : Carrier .gen}
      {φ : (Carrier.arr A B).V S} :
      (∀ v : A.V S, Read (ξ.snoc ⟨A, v⟩)
        (.app (Presentation.rename wk t) (.var 0)) B (φ v)) →
      Read ξ t (.arr A B) φ

/-- A generic of a carrier applied to arguments denotes its meaning at theirs. -/
inductive Apply : {n : Nat} → World S n → (A : Carrier .gen) → A.V S →
    List (Tm Head n) → S.P → Prop where
  | done {n : Nat} {ξ : World S n} {X : S.P} : Apply ξ .prop X [] X
  | arg {n : Nat} {ξ : World S n} {k : Kind} {A : Carrier k} {B : Carrier .gen}
      {φ : (Carrier.arr A B).V S} {a : Tm Head n} {args : List (Tm Head n)} {v : A.V S}
      {X : S.P} :
      Read ξ a A v → Apply ξ B (φ v) args X → Apply ξ (.arr A B) φ (a :: args) X

end

end Consistency
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
