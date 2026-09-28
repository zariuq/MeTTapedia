import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.ValueSide.Model

/-!
# Packs

A type denotes a *pack* in a world: a value relation on the terms of the world,
and the realizers of each value, a candidate of the model's realizer algebra.
There is no skeleton relation: what the skeleton relation guarded, that types
of one pack may be told apart by the transport, is the business of the
universe relation, which carries the shapes of types.

The packs of dependent function and pair types are read from a family of
packs of the domain and codomain at every world reached by a morphism:

* related functions send related valid arguments to related results, at every
  world reached by a morphism; their realizers are Girard's clause over the
  valid arguments;
* related pairs have related first projections, valid, and related second
  projections; their realizers are the pairs of realizers of the projections,
  met over the validity of the first projection.

The other packs of the interpretation: a type whose values are all related
(`Pack.total`), the codes, a decoding, and an identity type.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace ValueSide

open Normalization
open UniverseLevel (LevelOrder)
open Consistency (Rel World Morph Truth)

variable {Head L : Type} [LevelOrder L]

/-- The denotation of a type: a value relation and the realizers of each
value. -/
structure Pack (V : Model Head L) (n : Nat) where
  rel : Rel Head n
  real : Tm Head n → V.alg.Cand

variable {V : Model Head L}

/-- A valid value: related to itself. -/
abbrev Pack.Val {n : Nat} (P : Pack V n) (a : Tm Head n) : Prop := P.rel a a

variable (V) in
/-- The pack of a type whose values are all related, realized by `top`. -/
def Pack.total (n : Nat) : Pack V n where
  rel := fun _ _ => True
  real := fun _ => V.alg.top

variable (V) in
/-- A relation between types in worlds and their packs. The scope is a strict
implicit argument: it is inferred from the world when the relation is applied,
and an interpretation passed as an argument stays the same term. -/
abbrev IPack := ∀ ⦃n : Nat⦄, World V.reading n → Tm Head n → Pack V n → Prop

/-- No type is interpreted. -/
def IPack.empty : IPack V := fun _ _ _ _ => False

/-! ## Dependent function and pair types -/

variable (V) in
/-- The packs of a dependent function or pair type's domain and codomain, at
every world reached by a morphism. -/
structure PiPack {n : Nat} (ξ : World V.reading n) where
  dom : ∀ {m : Nat} {ξ' : World V.reading m} {ρ : Ren n m}, Morph ξ ξ' ρ → Pack V m
  cod : ∀ {m : Nat} {ξ' : World V.reading m} {ρ : Ren n m} (w : Morph ξ ξ' ρ) {a : Tm Head m},
    (dom w).Val a → Pack V m

namespace PiPack

variable {n : Nat} {ξ : World V.reading n} (P : PiPack V ξ)

/-- Functions that send related valid arguments to related results, at every
world reached by a morphism. -/
def rel : Rel Head n := fun f g =>
  ∀ {m : Nat} {ξ' : World V.reading m} {ρ : Ren n m} (w : Morph ξ ξ' ρ) {a b : Tm Head m}
    (ha : (P.dom w).Val a), (P.dom w).rel a b →
      (P.cod w ha).rel (.app (Presentation.rename ρ f) a) (.app (Presentation.rename ρ g) b)

/-- A valid argument at a world reached by a morphism. -/
structure Arg where
  m : Nat
  world : World V.reading m
  ren : Ren n m
  morph : Morph ξ world ren
  arg : Tm Head m
  valid : (P.dom morph).Val arg

/-- The realizers of a function: Girard's clause over the valid arguments, from
the realizers of the argument to those of the result. -/
def real (f : Tm Head n) : V.alg.Cand :=
  V.alg.piOver (fun a : P.Arg => (P.dom a.morph).real a.arg)
    (fun a => (P.cod a.morph a.valid).real (.app (Presentation.rename a.ren f) a.arg))

/-- The pack of a dependent function type. -/
def piPack : Pack V n where
  rel := P.rel
  real := P.real

/-- Pairs with valid first projections, related first projections, and related
second projections, at the world itself. -/
def pairRel : Rel Head n := fun p q =>
  ∃ hp : (P.dom (Morph.id ξ)).Val (.fst p), (P.dom (Morph.id ξ)).rel (.fst p) (.fst q) ∧
    (P.cod (Morph.id ξ) hp).rel (.snd p) (.snd q)

/-- The realizers of a pair: pairs of realizers of the projections, over the
validity of the first projection. -/
def pairReal (p : Tm Head n) : V.alg.Cand :=
  V.alg.meet fun hp : PLift ((P.dom (Morph.id ξ)).Val (.fst p)) =>
    V.alg.sigmaOver ((P.dom (Morph.id ξ)).real (.fst p))
      ((P.cod (Morph.id ξ) hp.down).real (.snd p))

/-- The pack of a dependent pair type. -/
def sigmaPack : Pack V n where
  rel := P.pairRel
  real := P.pairReal

/-- A family of packs interprets, for `I`, the domain `A` and the codomain `B` of
a dependent function or pair type: at every world reached by a morphism, its
domain pack interprets the renamed domain, its codomain packs interpret the
codomain at valid arguments, and related arguments have one codomain pack. -/
structure Interprets (I : IPack V) (A : Tm Head n) (B : Tm Head (n + 1)) : Prop where
  dom : ∀ {m : Nat} {ξ' : World V.reading m} {ρ : Ren n m} (w : Morph ξ ξ' ρ),
    I ξ' (Presentation.rename ρ A) (P.dom w)
  cod : ∀ {m : Nat} {ξ' : World V.reading m} {ρ : Ren n m} (w : Morph ξ ξ' ρ)
    {a : Tm Head m} (ha : (P.dom w).Val a),
    I ξ' (inst0 a (Presentation.rename (liftRen ρ) B)) (P.cod w ha)
  codRespect : ∀ {m : Nat} {ξ' : World V.reading m} {ρ : Ren n m} (w : Morph ξ ξ' ρ)
    {a b : Tm Head m} (ha : (P.dom w).Val a) (hb : (P.dom w).Val b),
    (P.dom w).rel a b → P.cod w ha = P.cod w hb

end PiPack

/-! ## The packs of codes, decodings and identity types -/

variable (V) in
/-- The pack of the codes: codes with one meaning, realized by `codes`. -/
def propPack {n : Nat} (ξ : World V.reading n) : Pack V n where
  rel := fun c c' => ∃ X, Truth V.reading ξ c X ∧ Truth V.reading ξ c' X
  real := fun _ => V.alg.codes

variable (V) in
/-- The pack of a decoding of a code meaning `X`: every pair of values, realized
by `X`. -/
def holdsPack (n : Nat) (X : V.alg.Cand) : Pack V n where
  rel := fun _ _ => True
  real := fun _ => X

/-- The pack of an identity type at a type of pack `R`: every pair of values,
realized by the identity candidate of the endpoints' relation. -/
def identPack {n : Nat} (R : Pack V n) (lhs rhs : Tm Head n) : Pack V n where
  rel := fun _ _ => True
  real := fun _ => V.alg.ident (R.rel lhs rhs)

end ValueSide
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
