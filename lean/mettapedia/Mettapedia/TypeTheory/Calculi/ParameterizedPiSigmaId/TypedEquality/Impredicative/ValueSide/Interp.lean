import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.ValueSide.Shape

/-!
# The interpretation of types over a level order

A type denotes a pack in a world. The interpretation reads a type from its
weak-head normal form, at a level `l` of the level order, given the
interpretations at the levels below:

* a universe below `l`: its universe pack over the interpretation at its level,
  types with one pack and one shape at every world reached by a morphism;
* a head that is not a universe, another rigid spine, or a daimonic type: every
  pair of values, realized by `top`;
* a dependent function or pair type: the pack of a family of packs of its
  domain and codomain, related arguments giving one codomain pack;
* an identity type at an interpreted type with valid endpoints: every pair of
  values, realized by the identity candidate of the endpoints' relation;
* a simple inductive type, with the packs of its closed field types: its
  inductive pack; the numbers are one such type;
* the codes: codes with one meaning; the decoding of a code with a meaning:
  every pair of values, realized by the meaning.

The table of the interpretations below a level is the level order's table
(`UniverseLevel.below`), and it unfolds by its equation (`levelsBelow_iff`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace ValueSide

open Normalization
open UniverseLevel (LevelOrder)
open Consistency (World Morph Truth)
open Realizability (Daimonic)

variable {Head L : Type} [LevelOrder L] (V : Model Head L)

/-- The interpretation of types at level `l`, given the interpretations below. -/
inductive SInterp (l : L) (below : L → IPack V) : IPack V where
  | sort {n : Nat} {ξ : World V.reading n} {A : Tm Head n} {u : Head}
      (isUniverse : V.rules.isUniverse u) (level : V.levels.level u < l)
      (red : WhRed V.rules V.roles A (.head u)) :
      SInterp l below ξ A (universePack V (below (V.levels.level u)) ξ)
  | ground {n : Nat} {ξ : World V.reading n} {A : Tm Head n} {h : Head}
      (notUniverse : ¬ V.rules.isUniverse h) (red : WhRed V.rules V.roles A (.head h)) :
      SInterp l below ξ A (Pack.total V n)
  | pi {n : Nat} {ξ : World V.reading n} {A dom : Tm Head n} {cod : Tm Head (n + 1)}
      (red : WhRed V.rules V.roles A (.pi dom cod)) (P : PiPack V ξ)
      (domInterp : ∀ {m : Nat} {ξ' : World V.reading m} {ρ : Ren n m} (w : Morph ξ ξ' ρ),
        SInterp l below ξ' (Presentation.rename ρ dom) (P.dom w))
      (codInterp : ∀ {m : Nat} {ξ' : World V.reading m} {ρ : Ren n m} (w : Morph ξ ξ' ρ)
        {a : Tm Head m} (ha : (P.dom w).Val a),
        SInterp l below ξ' (inst0 a (Presentation.rename (liftRen ρ) cod)) (P.cod w ha))
      (codRespect : ∀ {m : Nat} {ξ' : World V.reading m} {ρ : Ren n m} (w : Morph ξ ξ' ρ)
        {a b : Tm Head m} (ha : (P.dom w).Val a) (hb : (P.dom w).Val b),
        (P.dom w).rel a b → P.cod w ha = P.cod w hb) :
      SInterp l below ξ A P.piPack
  | sigma {n : Nat} {ξ : World V.reading n} {A dom : Tm Head n} {cod : Tm Head (n + 1)}
      (red : WhRed V.rules V.roles A (.sigma dom cod)) (P : PiPack V ξ)
      (domInterp : ∀ {m : Nat} {ξ' : World V.reading m} {ρ : Ren n m} (w : Morph ξ ξ' ρ),
        SInterp l below ξ' (Presentation.rename ρ dom) (P.dom w))
      (codInterp : ∀ {m : Nat} {ξ' : World V.reading m} {ρ : Ren n m} (w : Morph ξ ξ' ρ)
        {a : Tm Head m} (ha : (P.dom w).Val a),
        SInterp l below ξ' (inst0 a (Presentation.rename (liftRen ρ) cod)) (P.cod w ha))
      (codRespect : ∀ {m : Nat} {ξ' : World V.reading m} {ρ : Ren n m} (w : Morph ξ ξ' ρ)
        {a b : Tm Head m} (ha : (P.dom w).Val a) (hb : (P.dom w).Val b),
        (P.dom w).rel a b → P.cod w ha = P.cod w hb) :
      SInterp l below ξ A P.sigmaPack
  | ident {n : Nat} {ξ : World V.reading n} {A ty lhs rhs : Tm Head n}
      (red : WhRed V.rules V.roles A (.id ty lhs rhs)) (R : Pack V n)
      (tyInterp : SInterp l below ξ ty R) (lhsVal : R.Val lhs) (rhsVal : R.Val rhs) :
      SInterp l below ξ A (identPack R lhs rhs)
  | ind {n : Nat} {ξ : World V.reading n} {A : Tm Head n} {T : DeclName}
      {cs : List (DeclName × List (Field Head))}
      (red : WhRed V.rules V.roles A (.const T)) (role : V.roles T = .inductive cs)
      (field : Tm Head 0 → Pack V n)
      (fieldInterp : ∀ {F : Tm Head 0}, F ∈ closedFields cs →
        SInterp l below ξ (liftClosed F) (field F)) :
      SInterp l below ξ A (indPack V T cs field)
  | prop {n : Nat} {ξ : World V.reading n} {A : Tm Head n}
      (red : WhRed V.rules V.roles A (.const V.prop)) :
      SInterp l below ξ A (propPack V ξ)
  | holds {n : Nat} {ξ : World V.reading n} {A c : Tm Head n} {X : V.alg.Cand}
      (red : WhRed V.rules V.roles A (.app (.const V.holds) c))
      (truth : Truth V.reading ξ c X) :
      SInterp l below ξ A (holdsPack V n X)
  | rigid {n : Nat} {ξ : World V.reading n} {A : Tm Head n} {T : DeclName}
      {args : List (Tm Head n)}
      (red : WhRed V.rules V.roles A (appSpine (.const T) args)) (role : V.roles T = .rigid)
      (notProp : T ≠ V.prop) (notHolds : T ≠ V.holds) :
      SInterp l below ξ A (Pack.total V n)
  | daimon {n : Nat} {ξ : World V.reading n} {A u : Tm Head n}
      (red : WhRed V.rules V.roles A u) (daimonic : Daimonic V.roles V.star u) :
      SInterp l below ξ A (Pack.total V n)

/-- The interpretations below each level: the level order's table of `SInterp`. -/
noncomputable def levelsBelow : L → L → IPack V :=
  UniverseLevel.below (fun k below => SInterp V k below) IPack.empty

/-- The interpretation of types at level `l`. -/
noncomputable def InterpAt (l : L) : IPack V :=
  SInterp V l (levelsBelow V l)

variable {V}

/-- A level below `l` is read by the interpretation at that level. -/
theorem levelsBelow_iff {l k : L} (h : k < l) {n : Nat} (ξ : World V.reading n)
    (A : Tm Head n) (P : Pack V n) : levelsBelow V l k ξ A P ↔ InterpAt V k ξ A P := by
  unfold levelsBelow InterpAt
  rw [UniverseLevel.below_of_lt _ _ h]
  exact Iff.rfl

/-- No type is interpreted at a level that is not below `l`. -/
theorem levelsBelow_of_not_lt {l k : L} (h : ¬ k < l) {n : Nat} (ξ : World V.reading n)
    (A : Tm Head n) (P : Pack V n) : ¬ levelsBelow V l k ξ A P := by
  unfold levelsBelow
  rw [UniverseLevel.below_of_not_lt _ _ h]
  exact id

/-- The numbers are interpreted at every level by their inductive pack. -/
theorem InterpAt.num (laws : V.Laws) (l : L) {n : Nat} {ξ : World V.reading n} {A : Tm Head n}
    (red : WhRed V.rules V.roles A (.const V.num)) : InterpAt V l ξ A (numIndPack V n) :=
  SInterp.ind red laws.num_role _ fun mem => by
    rw [closedFields_numConstructors] at mem
    cases mem

end ValueSide
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
