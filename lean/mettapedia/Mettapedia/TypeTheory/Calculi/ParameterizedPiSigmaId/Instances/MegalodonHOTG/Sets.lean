import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerAnnotated
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerEmbedding
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerLevelSubstitution
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.HeadMorphism
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.PackageSum
import Mettapedia.TypeTheory.UniverseLevel.Above

/-!
# The tower of universes inside the sets

In the tower of universes over a level order `L`, a universe is a member of the next one and
nothing lies above them all. This file puts that tower inside one further type, the type of
all sets, so that the sets are the ambient universe and the types live in them.

No rule is added. The tower is taken over the levels of `L` followed by the natural numbers
(`UniverseLevel.Above`), and three of its universes are named:

* `universeAt d`, the universe at a level `d` of `L`;
* `allSets`, the universe at the first level above all of `L`: **the type of all sets**;
* `allClasses`, the universe at the next level: the sort of `allSets` and of the types of
  predicates and functions on the sets.

The universe at the least level of `L` is `U0`.

The rules of the tower then say:

* every universe at a level of `L` is a member of `allSets` (`universe_isSet`), and so is
  every type of such a universe (`small_isSet`): **a type is a set**;
* a member of `allSets` is a type, and a dependent function type over a set, of a family of
  sets, is a set (`family_isSet`); a function type between types of the least universe is a
  type of the least universe (`smallFunctions_typed`);
* `allSets` is a member of `allClasses` (`sets_typed`), and the function types with `allSets`
  on either side are members of `allClasses` (`setToClass_typed`, `classToSet_typed`,
  `classToClass_typed`).

Because the rules are those of the tower, everything proved of the tower over an arbitrary
level order holds here. A rule package contains the rules of the tower (`Contains`) when it
has its typings of heads, universes, joins and cumulativity; every package over them does
(`package_contains`), and the typings below hold in every such package. The tower over `L` is its lower part: every derivation of the tower
over `L` is a derivation here, along the inclusion of the levels (`tower_morphism`).

A level parameter of the tower ranges over all its levels. A parameter that stands for a
level an author writes is bounded by the level of the sets, with the bounds the tower already
has (`writtenBounds`; the valuations into the levels of `L` respect them,
`writtenBounds_valid`). Under these bounds every universe at a level expression over `L`,
level parameters included, is a set (`universeExpr_isSet`, `universe_param_isSet`); without
them the comparison fails (`universe_param_not_below_sets`).

What makes `allSets` the type of all sets, and not only one more universe, is its reading:
in the set model (`MegalodonHOTG.SetsModel`) it is a universe closed under the universe operation,
which the universe at a limit level of a tower is not.

Positive examples: the universe at a level is a set (`universe_isSet`); the functions from
sets to sets form a type of `allClasses` (`setFunctions_typed`); the identity on the sets has
the type of functions from sets to sets (`setIdentity_typed`).

Negative examples: the sets are contained in no universe at a level of `L`
(`sets_not_below`); the classes are not contained in the sets (`classes_not_below_sets`).

Scope: the named universes and their typings in every package over these rules. The set model
is in `MegalodonHOTG.SetsModel`.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
namespace MegalodonHOTG

open Presentation Presentation.TypedEquality Presentation.TypedEquality.Annotated
open Presentation.TypedEquality.Annotated.TowerControls (P₀)
open Mettapedia.TypeTheory.UniverseLevel

/-- **The heads of the tower inside the sets**: those of the tower over the levels of `L`
followed by the natural numbers. -/
abbrev Head (L : Type) := LevelTower.Head (Above L)

variable {L : Type}

section Terms

variable {n : Nat}

/-- The universe at a level of `L`. -/
abbrev universeAt (d : L) : CTm (Head L) n := .head (.sort (.const (.below d)))

/-- **The type of all sets**: the universe at the first level above the levels of `L`. -/
abbrev allSets : CTm (Head L) n := .head (.sort (.const (.above 0)))

/-- The sort of the type of all sets: the universe at the next level. -/
abbrev allClasses : CTm (Head L) n := .head (.sort (.const (.above 1)))

end Terms

variable [LevelOrder L]

/-- **The least universe**: the universe at the least level of `L`. -/
abbrev U0 {n : Nat} : CTm (Head L) n := universeAt LevelOrder.bot

variable (L) in
/-- The rules: those of the tower over the levels of `L` followed by the natural numbers. -/
abbrev rules : Rules (Head L) := LevelTower.rules (Above L)

variable (L) in
/-- The annotated package of the tower inside the sets, with no declaration. -/
abbrev bare : ChurchRules (rules L) := P₀

/-! ## The tower over `L` inside -/

/-- **The annotated tower over `L` is contained in the tower inside the sets**, along the
inclusion of the levels: every derivation of the tower over `L` is a derivation here. -/
theorem tower_morphism :
    (P₀ (L := L)).Morphism (bare L) (LevelTower.Head.map (Above.belowEmbedding L)) where
  headTyping := (LevelTower.morphism (Above.belowEmbedding L)).headTyping
  isUniverse := (LevelTower.morphism (Above.belowEmbedding L)).isUniverse
  join := (LevelTower.morphism (Above.belowEmbedding L)).join
  cumulative := (LevelTower.morphism (Above.belowEmbedding L)).cumulative
  headEq := (LevelTower.morphism (Above.belowEmbedding L)).headEq
  constantType := fun {_ T} (declared : (none : Option (CTm (LevelTower.Head L) 0)) = some T) =>
    nomatch declared
  computation := fun step => step.elim
  requires := fun step _ => step.elim

/-! ## Types are sets -/

section Typings

variable {R : Rules (Head L)} {P : ChurchRules R} {n : Nat} {Γ : CCtx (Head L) n}

/-- A rule package over these heads that contains the rules of the tower. -/
structure Contains (R : Rules (Head L)) : Prop where
  headTyping : ∀ {h u : Head L}, LevelTower.HeadTyping h u → R.headTyping h u
  isUniverse : ∀ {u : Head L}, LevelTower.IsUniverse u → R.isUniverse u
  join : ∀ {u v w : Head L}, LevelTower.Join u v w → R.join u v w
  cumulative : ∀ {u v : Head L}, LevelTower.Cumulative u v → R.cumulative u v

/-- The rules of the tower contain themselves. -/
theorem contains_rules : Contains (rules L) where
  headTyping := id
  isUniverse := id
  join := id
  cumulative := id

/-- **A package over the rules of the tower contains them.** -/
theorem package_contains {R₂ : Rules (Head L)} : Contains (Rules.sum (rules L) R₂) where
  headTyping := id
  isUniverse := id
  join := id
  cumulative := id

variable (contains : Contains R)

include contains

/-- **The universe at a level of `L` is a set.** -/
theorem universe_isSet (d : L) : CTyped P Γ (universeAt d) allSets :=
  CDerivable.cumul (.headType (contains.headTyping (LevelTower.HeadTyping.sort _)))
    (contains.cumulative (u := .sort (.succ (.const (.below d)))) (v := .sort (.const (.above 0)))
      fun _ => Above.below_le_above _ 0)

/-- The universe at a level of `L` is a member of the universe at the next level. -/
theorem universe_typed (d : L) : CTyped P Γ (universeAt d) (universeAt (LevelOrder.succ d)) :=
  CDerivable.cumul (.headType (contains.headTyping (LevelTower.HeadTyping.sort _)))
    (contains.cumulative (u := .sort (.succ (.const (.below d))))
      (v := .sort (.const (.below (LevelOrder.succ d)))) fun _ => le_refl _)

/-- **A type of a universe at a level of `L` is a set.** -/
theorem small_isSet {A : CTm (Head L) n} {d : L} (typed : CTyped P Γ A (universeAt d)) :
    CTyped P Γ A allSets :=
  CDerivable.cumul typed
    (contains.cumulative (u := .sort (.const (.below d))) (v := .sort (.const (.above 0)))
      fun _ => Above.below_le_above d 0)

/-- The type of all sets is a member of `allClasses`. -/
theorem sets_typed : CTyped P Γ allSets allClasses :=
  CDerivable.cumul (.headType (contains.headTyping (LevelTower.HeadTyping.sort _)))
    (contains.cumulative (u := .sort (.succ (.const (.above 0)))) (v := .sort (.const (.above 1)))
      fun _ => le_refl _)

/-- A set is a member of `allClasses`. -/
theorem set_isClass {X : CTm (Head L) n} (typed : CTyped P Γ X allSets) :
    CTyped P Γ X allClasses :=
  CDerivable.cumul typed
    (contains.cumulative (u := .sort (.const (.above 0))) (v := .sort (.const (.above 1)))
      fun _ => Above.above_le_above.mpr (Nat.zero_le 1))

/-- **A dependent function type over a set, of a family of sets, is a set.** -/
theorem family_isSet {A : CTm (Head L) n} {B : CTm (Head L) (n + 1)}
    (domain : CTyped P Γ A allSets) (family : CTyped P (.snoc Γ A) B allSets) :
    CTyped P Γ (.pi A B) allSets :=
  CDerivable.cumul
    (.piForm domain (contains.isUniverse (.sort _)) family (contains.isUniverse (.sort _))
      (contains.join (.sorts _ _)))
    (contains.cumulative
      (u := .sort (.max (.const (.above 0)) (.const (.above 0)))) (v := .sort (.const (.above 0)))
      fun _ => max_le (le_refl _) (le_refl _))

/-- A function type between types of the least universe is a type of the least universe. -/
theorem smallFunctions_typed {A : CTm (Head L) n} {B : CTm (Head L) (n + 1)}
    (domain : CTyped P Γ A U0) (codomain : CTyped P (.snoc Γ A) B U0) :
    CTyped P Γ (.pi A B) U0 :=
  CDerivable.cumul
    (.piForm domain (contains.isUniverse (.sort _)) codomain
      (contains.isUniverse (.sort _)) (contains.join (.sorts _ _)))
    (contains.cumulative
      (u := .sort (.max (.const (.below LevelOrder.bot)) (.const (.below LevelOrder.bot))))
      (v := .sort (.const (.below LevelOrder.bot))) fun _ => max_le (le_refl _) (le_refl _))

/-- A function type from a set into a type of `allClasses` is a type of `allClasses`. -/
theorem setToClass_typed {A : CTm (Head L) n} {B : CTm (Head L) (n + 1)}
    (domain : CTyped P Γ A allSets) (codomain : CTyped P (.snoc Γ A) B allClasses) :
    CTyped P Γ (.pi A B) allClasses :=
  CDerivable.cumul
    (.piForm domain (contains.isUniverse (.sort _)) codomain (contains.isUniverse (.sort _))
      (contains.join (.sorts _ _)))
    (contains.cumulative
      (u := .sort (.max (.const (.above 0)) (.const (.above 1)))) (v := .sort (.const (.above 1)))
      fun _ => max_le (Above.above_le_above.mpr (Nat.zero_le 1)) (le_refl _))

/-- A function type from a type of `allClasses` into a set is a type of `allClasses`. -/
theorem classToSet_typed {A : CTm (Head L) n} {B : CTm (Head L) (n + 1)}
    (domain : CTyped P Γ A allClasses) (codomain : CTyped P (.snoc Γ A) B allSets) :
    CTyped P Γ (.pi A B) allClasses :=
  CDerivable.cumul
    (.piForm domain (contains.isUniverse (.sort _)) codomain (contains.isUniverse (.sort _))
      (contains.join (.sorts _ _)))
    (contains.cumulative
      (u := .sort (.max (.const (.above 1)) (.const (.above 0)))) (v := .sort (.const (.above 1)))
      fun _ => max_le (le_refl _) (Above.above_le_above.mpr (Nat.zero_le 1)))

/-- A function type between types of `allClasses` is a type of `allClasses`. -/
theorem classToClass_typed {A : CTm (Head L) n} {B : CTm (Head L) (n + 1)}
    (domain : CTyped P Γ A allClasses) (codomain : CTyped P (.snoc Γ A) B allClasses) :
    CTyped P Γ (.pi A B) allClasses :=
  CDerivable.cumul
    (.piForm domain (contains.isUniverse (.sort _)) codomain (contains.isUniverse (.sort _))
      (contains.join (.sorts _ _)))
    (contains.cumulative
      (u := .sort (.max (.const (.above 1)) (.const (.above 1)))) (v := .sort (.const (.above 1)))
      fun _ => max_le (le_refl _) (le_refl _))

/-- The functions from the sets to the sets form a type of `allClasses`. -/
theorem setFunctions_typed : CTyped P Γ (.pi allSets allSets) allClasses :=
  classToClass_typed contains (sets_typed contains) (sets_typed contains)

/-- Positive example: the identity on the sets is a function from the sets to the sets. -/
theorem setIdentity_typed : CTyped P Γ (.lam allSets (.var 0)) (.pi allSets allSets) :=
  .lamIntro (sets_typed contains) (contains.isUniverse (.sort _)) (setFunctions_typed contains)
    (contains.isUniverse (.sort _)) (.var 0)

end Typings

/-! ## Level parameters -/

variable (L) in
/-- **The bounds under which every level parameter stands for a level of `L`**: each
parameter is below the level of the sets. -/
def writtenBounds : LevelBounds (Above L) := fun _ => some (Above.above 0)

/-- A valuation into the levels of `L` respects these bounds. -/
theorem writtenBounds_valid (ν : Nat → L) :
    (writtenBounds L).Valid fun i => Above.below (ν i) := fun i c known => by
  cases known
  exact Above.below_lt_above (ν i) 0

/-- Under these bounds a level expression whose constants are levels of `L` has its value
below the level of the sets. -/
theorem eval_written_lt {ν : Nat → Above L} (valid : (writtenBounds L).Valid ν) :
    ∀ e : LevelExpr L, (e.map Above.below).eval ν < Above.above 0
  | .const c => Above.below_lt_above c 0
  | .param i => valid i (Above.above 0) rfl
  | .succ e => Above.above_zero_isLimit.succ_lt (eval_written_lt valid e)
  | .max e₁ e₂ => max_lt (eval_written_lt valid e₁) (eval_written_lt valid e₂)

/-- **Every universe at a level expression over `L` is a set**, level parameters included,
when the parameters stand for levels of `L`. -/
theorem universeExpr_isSet {n : Nat} {Γ : CCtx (Head L) n} (e : LevelExpr L) :
    CDerivable (LevelTower.boundedChurch (bare L) (writtenBounds L))
      (.typing Γ (.head (.sort (e.map Above.below))) allSets) :=
  .sub (.headType (LevelTower.HeadTyping.sort _))
    (.subUniv fun _ valid => LevelOrder.succ_le_of_lt (eval_written_lt valid e))

/-- Positive example: the universe at a level parameter is a set. -/
theorem universe_param_isSet {n : Nat} {Γ : CCtx (Head L) n} :
    CDerivable (LevelTower.boundedChurch (bare L) (writtenBounds L))
      (.typing Γ (.head (.sort (.param 0))) allSets) :=
  universeExpr_isSet (.param 0)

/-- Negative example: without the bounds, the universe at a level parameter is not a member of
a universe contained in the sets: the parameter may stand for a level above them. -/
theorem universe_param_not_below_sets :
    ¬ LevelTower.Cumulative (L := Above L) (.sort (.succ (.param 0)))
      (.sort (.const (.above 0))) := fun below =>
  absurd (Above.above_le_above.mp (below fun _ => Above.above 0)) (by decide)

/-! ## What is not a set -/

/-- Negative example: **the sets are contained in no universe at a level of `L`.** -/
theorem sets_not_below (d : L) :
    ¬ LevelTower.Cumulative (L := Above L) (.sort (.const (.above 0)))
      (.sort (.const (.below d))) := fun below =>
  Above.not_above_le_below 0 d (below fun _ => LevelOrder.bot)

/-- Negative example: the classes are not contained in the sets. -/
theorem classes_not_below_sets :
    ¬ LevelTower.Cumulative (L := Above L) (.sort (.const (.above 1)))
      (.sort (.const (.above 0))) := fun below =>
  absurd (Above.above_le_above.mp (below fun _ => (LevelOrder.bot : Above L))) (by decide)

end MegalodonHOTG
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
