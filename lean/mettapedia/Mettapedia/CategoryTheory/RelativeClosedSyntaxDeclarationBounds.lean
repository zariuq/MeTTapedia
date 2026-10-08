import Mettapedia.CategoryTheory.RelativeClosedSyntax
import Mathlib.Order.Lattice

/-!
# Computed declaration requirements of complete raw expressions

Every finite object or arrow expression has a computed bound on the ranks of
the names it uses. The existing strict rank-admission predicate is equivalent
to that requirement being at most the supplied declaration rank. The
calculation includes function annotations and equalizer conditions.

Renaming preserves admission when the independently assigned ranks agree at
each mapped primitive name. No semantic interpretation is used.
-/

set_option autoImplicit false

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax.DeclarationBounds

open _root_.CategoryTheory

universe u v a w z b

variable {C : Type u} [Category.{v} C] {symbols : Symbols.{a}}
variable (objects : symbols.ObjectName → Nat) (arrows : symbols.ArrowName → Nat)

mutual

def objectRequirement : ObjectCode C symbols → Nat
  | .base _ => 0
  | .name origin => objects origin + 1
  | .terminal => 0
  | .product first second => max (objectRequirement first) (objectRequirement second)
  | .exponential argument result => max (objectRequirement argument) (objectRequirement result)
  | .equalizer source target first second =>
      max (objectRequirement source) (max (objectRequirement target)
        (max (arrowRequirement first) (arrowRequirement second)))

def arrowRequirement : ArrowCode C symbols → Nat
  | .base _ => 0
  | .name origin => arrows origin + 1
  | .identity object => objectRequirement object
  | .compose first second => max (arrowRequirement first) (arrowRequirement second)
  | .terminal source => objectRequirement source
  | .first first second => max (objectRequirement first) (objectRequirement second)
  | .second first second => max (objectRequirement first) (objectRequirement second)
  | .pair first second => max (arrowRequirement first) (arrowRequirement second)
  | .evaluation argument result => max (objectRequirement argument) (objectRequirement result)
  | .curry context argument result body =>
      max (objectRequirement context) (max (objectRequirement argument)
        (max (objectRequirement result) (arrowRequirement body)))
  | .equalizerArrow source target first second =>
      max (objectRequirement source) (max (objectRequirement target)
        (max (arrowRequirement first) (arrowRequirement second)))
  | .equalizerLift source target first second context candidate =>
      max (objectRequirement source) (max (objectRequirement target)
        (max (arrowRequirement first) (max (arrowRequirement second)
          (max (objectRequirement context) (arrowRequirement candidate)))))

end

mutual

theorem object_before_iff (bound : Nat) : (code : ObjectCode C symbols) →
    code.before objects arrows bound ↔ objectRequirement objects arrows code ≤ bound
  | .base _ => by simp [ObjectCode.before, objectRequirement]
  | .name _ => by simp [ObjectCode.before, objectRequirement, Nat.succ_le_iff]
  | .terminal => by simp [ObjectCode.before, objectRequirement]
  | .product _ _ => by simp only [ObjectCode.before, objectRequirement, Nat.max_le, object_before_iff]
  | .exponential _ _ => by simp only [ObjectCode.before, objectRequirement, Nat.max_le, object_before_iff]
  | .equalizer _ _ _ _ => by
      simp only [ObjectCode.before, objectRequirement, Nat.max_le, object_before_iff, arrow_before_iff]

theorem arrow_before_iff (bound : Nat) : (code : ArrowCode C symbols) →
    code.before objects arrows bound ↔ arrowRequirement objects arrows code ≤ bound
  | .base _ => by simp [ArrowCode.before, arrowRequirement]
  | .name _ => by simp [ArrowCode.before, arrowRequirement, Nat.succ_le_iff]
  | .identity _ => by simp only [ArrowCode.before, arrowRequirement, object_before_iff]
  | .compose _ _ => by simp only [ArrowCode.before, arrowRequirement, Nat.max_le, arrow_before_iff]
  | .terminal _ => by simp only [ArrowCode.before, arrowRequirement, object_before_iff]
  | .first _ _ => by simp only [ArrowCode.before, arrowRequirement, Nat.max_le, object_before_iff]
  | .second _ _ => by simp only [ArrowCode.before, arrowRequirement, Nat.max_le, object_before_iff]
  | .pair _ _ => by simp only [ArrowCode.before, arrowRequirement, Nat.max_le, arrow_before_iff]
  | .evaluation _ _ => by simp only [ArrowCode.before, arrowRequirement, Nat.max_le, object_before_iff]
  | .curry _ _ _ _ => by
      simp only [ArrowCode.before, arrowRequirement, Nat.max_le, object_before_iff, arrow_before_iff]
  | .equalizerArrow _ _ _ _ => by
      simp only [ArrowCode.before, arrowRequirement, Nat.max_le, object_before_iff, arrow_before_iff]
  | .equalizerLift _ _ _ _ _ _ => by
      simp only [ArrowCode.before, arrowRequirement, Nat.max_le, object_before_iff, arrow_before_iff]

end

variable {D : Type w} [Category.{z} D] {nextSymbols : Symbols.{b}}
variable (base : C ⥤ D)
variable (objectNames : symbols.ObjectName → nextSymbols.ObjectName)
variable (arrowNames : symbols.ArrowName → nextSymbols.ArrowName)
variable (nextObjects : nextSymbols.ObjectName → Nat) (nextArrows : nextSymbols.ArrowName → Nat)
mutual

theorem object_before_map
    (objectRanks : ∀ origin, nextObjects (objectNames origin) = objects origin)
    (arrowRanks : ∀ origin, nextArrows (arrowNames origin) = arrows origin) (bound : Nat) : (code : ObjectCode C symbols) →
    (code.map base objectNames arrowNames).before nextObjects nextArrows bound ↔
      code.before objects arrows bound
  | .base _ => Iff.rfl
  | .name origin => by simp only [ObjectCode.map, ObjectCode.before, objectRanks origin]
  | .terminal => Iff.rfl
  | .product _ _ => by simp only [ObjectCode.map, ObjectCode.before, object_before_map objectRanks arrowRanks]
  | .exponential _ _ => by simp only [ObjectCode.map, ObjectCode.before, object_before_map objectRanks arrowRanks]
  | .equalizer _ _ _ _ => by
      simp only [ObjectCode.map, ObjectCode.before, object_before_map objectRanks arrowRanks, arrow_before_map objectRanks arrowRanks]

theorem arrow_before_map
    (objectRanks : ∀ origin, nextObjects (objectNames origin) = objects origin)
    (arrowRanks : ∀ origin, nextArrows (arrowNames origin) = arrows origin) (bound : Nat) : (code : ArrowCode C symbols) →
    (code.map base objectNames arrowNames).before nextObjects nextArrows bound ↔
      code.before objects arrows bound
  | .base _ => Iff.rfl
  | .name origin => by simp only [ArrowCode.map, ArrowCode.before, arrowRanks origin]
  | .identity _ => by simp only [ArrowCode.map, ArrowCode.before, object_before_map objectRanks arrowRanks]
  | .compose _ _ => by simp only [ArrowCode.map, ArrowCode.before, arrow_before_map objectRanks arrowRanks]
  | .terminal _ => by simp only [ArrowCode.map, ArrowCode.before, object_before_map objectRanks arrowRanks]
  | .first _ _ => by simp only [ArrowCode.map, ArrowCode.before, object_before_map objectRanks arrowRanks]
  | .second _ _ => by simp only [ArrowCode.map, ArrowCode.before, object_before_map objectRanks arrowRanks]
  | .pair _ _ => by simp only [ArrowCode.map, ArrowCode.before, arrow_before_map objectRanks arrowRanks]
  | .evaluation _ _ => by simp only [ArrowCode.map, ArrowCode.before, object_before_map objectRanks arrowRanks]
  | .curry _ _ _ _ => by
      simp only [ArrowCode.map, ArrowCode.before, object_before_map objectRanks arrowRanks, arrow_before_map objectRanks arrowRanks]
  | .equalizerArrow _ _ _ _ => by
      simp only [ArrowCode.map, ArrowCode.before, object_before_map objectRanks arrowRanks, arrow_before_map objectRanks arrowRanks]
  | .equalizerLift _ _ _ _ _ _ => by
      simp only [ArrowCode.map, ArrowCode.before, object_before_map objectRanks arrowRanks, arrow_before_map objectRanks arrowRanks]

end

end Mettapedia.CategoryTheory.RelativeClosedSyntax.DeclarationBounds
