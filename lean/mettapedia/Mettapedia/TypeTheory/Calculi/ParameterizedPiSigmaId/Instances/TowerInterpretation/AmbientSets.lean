import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerAnnotated
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerEmbedding
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.HeadMorphism
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

The rules of the tower then say:

* every universe at a level of `L` is a member of `allSets` (`universe_isSet`), and so is
  every type of such a universe (`small_isSet`): **a type is a set**;
* a member of `allSets` is a type, and a dependent function type over a set, of a family of
  sets, is a set (`family_isSet`);
* `allSets` is a member of `allClasses` (`sets_typed`), and the function types with `allSets`
  on either side are members of `allClasses` (`setToClass_typed`, `classToSet_typed`,
  `classToClass_typed`).

Because the rules are those of the tower, everything proved of the tower over an arbitrary
level order holds here. The tower over `L` is its lower part: every derivation of the tower
over `L` is a derivation here, along the inclusion of the levels (`tower_morphism`).

What makes `allSets` the type of all sets, and not only one more universe, is its reading:
in the set model (`AmbientSetsModel`) it is a universe closed under the universe operation,
which the universe at a limit level of a tower is not.

Positive examples: the universe at a level is a set (`universe_isSet`); the functions from
sets to sets form a type of `allClasses` (`setFunctions_typed`); the identity on the sets has
the type of functions from sets to sets (`setIdentity_typed`).

Negative examples: the sets are contained in no universe at a level of `L`
(`sets_not_below`); the classes are not contained in the sets (`classes_not_below_sets`).

Scope: the named universes and their typings in every package over these rules. The set model
is in `AmbientSetsModel`.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
namespace AmbientSets

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

variable (contains : Contains R)

include contains

/-- **The universe at a level of `L` is a set.** -/
theorem universe_isSet (d : L) : CTyped P Γ (universeAt d) allSets :=
  CDerivable.cumul (.headType (contains.headTyping (LevelTower.HeadTyping.sort _)))
    (contains.cumulative (u := .sort (.succ (.const (.below d)))) (v := .sort (.const (.above 0)))
      fun _ => Above.below_le_above _ 0)

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

end AmbientSets
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
