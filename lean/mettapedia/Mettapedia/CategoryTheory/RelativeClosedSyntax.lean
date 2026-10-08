import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic

/-!
# Relative finite-limit and closed categorical syntax

The raw language retains an independently supplied base category's entire
object and arrow diagram. Fresh object, arrow and equation names are declared
separately. Products, function objects and equalizers are actual syntax
constructors; their formation and universal equations belong to the generated
judgments, rather than to raw expressions or an assumed interpretation.

Categorical abstraction is expressed by curry. Its binder has explicit
context, argument and result annotations. Equalizer lifts retain the candidate
arrow; a generated commutativity derivation is required for its admission.
-/

set_option autoImplicit false

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax

open _root_.CategoryTheory

universe u v w z a b

structure Symbols where
  ObjectName : Type a
  ArrowName : Type a
  EquationName : Type a

variable (C : Type u) [Category.{v} C] (symbols : Symbols.{a})

mutual

inductive ObjectCode : Type (max u v a) where
  | base (object : C)
  | name (origin : symbols.ObjectName)
  | terminal
  | product (first second : ObjectCode)
  | exponential (argument result : ObjectCode)
  | equalizer (source target : ObjectCode) (first second : ArrowCode)

inductive ArrowCode : Type (max u v a) where
  | base {source target : C} (arrow : source ⟶ target)
  | name (origin : symbols.ArrowName)
  | identity (object : ObjectCode)
  | compose (first second : ArrowCode)
  | terminal (source : ObjectCode)
  | first (first second : ObjectCode)
  | second (first second : ObjectCode)
  | pair (first second : ArrowCode)
  | evaluation (argument result : ObjectCode)
  | curry (context argument result : ObjectCode) (body : ArrowCode)
  | equalizerArrow (source target : ObjectCode) (first second : ArrowCode)
  | equalizerLift (source target : ObjectCode) (first second : ArrowCode)
      (context : ObjectCode) (candidate : ArrowCode)

end

variable {C symbols}
variable {D : Type w} [Category.{z} D] {targetSymbols : Symbols.{b}}

mutual

def ObjectCode.map (base : C ⥤ D)
    (objects : symbols.ObjectName → targetSymbols.ObjectName)
    (arrows : symbols.ArrowName → targetSymbols.ArrowName) :
    ObjectCode C symbols → ObjectCode D targetSymbols
  | .base object => .base (base.obj object)
  | .name origin => .name (objects origin)
  | .terminal => .terminal
  | .product first second => .product (first.map base objects arrows) (second.map base objects arrows)
  | .exponential argument result =>
      .exponential (argument.map base objects arrows) (result.map base objects arrows)
  | .equalizer source target first second => .equalizer
      (source.map base objects arrows) (target.map base objects arrows)
      (first.map base objects arrows) (second.map base objects arrows)

def ArrowCode.map (base : C ⥤ D)
    (objects : symbols.ObjectName → targetSymbols.ObjectName)
    (arrows : symbols.ArrowName → targetSymbols.ArrowName) :
    ArrowCode C symbols → ArrowCode D targetSymbols
  | .base arrow => .base (base.map arrow)
  | .name origin => .name (arrows origin)
  | .identity object => .identity (object.map base objects arrows)
  | .compose first second => .compose (first.map base objects arrows) (second.map base objects arrows)
  | .terminal source => .terminal (source.map base objects arrows)
  | .first first second => .first (first.map base objects arrows) (second.map base objects arrows)
  | .second first second => .second (first.map base objects arrows) (second.map base objects arrows)
  | .pair first second => .pair (first.map base objects arrows) (second.map base objects arrows)
  | .evaluation argument result =>
      .evaluation (argument.map base objects arrows) (result.map base objects arrows)
  | .curry context argument result body => .curry
      (context.map base objects arrows) (argument.map base objects arrows)
      (result.map base objects arrows) (body.map base objects arrows)
  | .equalizerArrow source target first second => .equalizerArrow
      (source.map base objects arrows) (target.map base objects arrows)
      (first.map base objects arrows) (second.map base objects arrows)
  | .equalizerLift source target first second context candidate => .equalizerLift
      (source.map base objects arrows) (target.map base objects arrows)
      (first.map base objects arrows) (second.map base objects arrows)
      (context.map base objects arrows) (candidate.map base objects arrows)

end

mutual

theorem ObjectCode.map_identity : (object : ObjectCode C symbols) →
    object.map (Functor.id C) id id = object
  | .base _ => rfl
  | .name _ => rfl
  | .terminal => rfl
  | .product _ _ => by simp only [ObjectCode.map, ObjectCode.map_identity]
  | .exponential _ _ => by simp only [ObjectCode.map, ObjectCode.map_identity]
  | .equalizer _ _ _ _ => by
      simp only [ObjectCode.map, ObjectCode.map_identity, ArrowCode.map_identity]

theorem ArrowCode.map_identity : (arrow : ArrowCode C symbols) →
    arrow.map (Functor.id C) id id = arrow
  | .base _ => rfl
  | .name _ => rfl
  | .identity _ => by simp only [ArrowCode.map, ObjectCode.map_identity]
  | .compose _ _ => by simp only [ArrowCode.map, ArrowCode.map_identity]
  | .terminal _ => by simp only [ArrowCode.map, ObjectCode.map_identity]
  | .first _ _ => by simp only [ArrowCode.map, ObjectCode.map_identity]
  | .second _ _ => by simp only [ArrowCode.map, ObjectCode.map_identity]
  | .pair _ _ => by simp only [ArrowCode.map, ArrowCode.map_identity]
  | .evaluation _ _ => by simp only [ArrowCode.map, ObjectCode.map_identity]
  | .curry _ _ _ _ => by
      simp only [ArrowCode.map, ObjectCode.map_identity, ArrowCode.map_identity]
  | .equalizerArrow _ _ _ _ => by
      simp only [ArrowCode.map, ObjectCode.map_identity, ArrowCode.map_identity]
  | .equalizerLift _ _ _ _ _ _ => by
      simp only [ArrowCode.map, ObjectCode.map_identity, ArrowCode.map_identity]

end

section Composition

variable {E : Type*} [Category E] {lastSymbols : Symbols}
variable (before : C ⥤ D) (after : D ⥤ E)
  (firstObjects : symbols.ObjectName → targetSymbols.ObjectName)
  (secondObjects : targetSymbols.ObjectName → lastSymbols.ObjectName)
  (firstArrows : symbols.ArrowName → targetSymbols.ArrowName)
  (secondArrows : targetSymbols.ArrowName → lastSymbols.ArrowName)

mutual

theorem ObjectCode.map_compose : (object : ObjectCode C symbols) →
    (object.map before firstObjects firstArrows).map after secondObjects secondArrows =
      object.map (before ⋙ after) (secondObjects ∘ firstObjects) (secondArrows ∘ firstArrows)
  | .base _ => rfl
  | .name _ => rfl
  | .terminal => rfl
  | .product _ _ => by simp only [ObjectCode.map, ObjectCode.map_compose]
  | .exponential _ _ => by simp only [ObjectCode.map, ObjectCode.map_compose]
  | .equalizer _ _ _ _ => by
      simp only [ObjectCode.map, ObjectCode.map_compose, ArrowCode.map_compose]

theorem ArrowCode.map_compose : (arrow : ArrowCode C symbols) →
    (arrow.map before firstObjects firstArrows).map after secondObjects secondArrows =
      arrow.map (before ⋙ after) (secondObjects ∘ firstObjects) (secondArrows ∘ firstArrows)
  | .base _ => rfl
  | .name _ => rfl
  | .identity _ => by simp only [ArrowCode.map, ObjectCode.map_compose]
  | .compose _ _ => by simp only [ArrowCode.map, ArrowCode.map_compose]
  | .terminal _ => by simp only [ArrowCode.map, ObjectCode.map_compose]
  | .first _ _ => by simp only [ArrowCode.map, ObjectCode.map_compose]
  | .second _ _ => by simp only [ArrowCode.map, ObjectCode.map_compose]
  | .pair _ _ => by simp only [ArrowCode.map, ArrowCode.map_compose]
  | .evaluation _ _ => by simp only [ArrowCode.map, ObjectCode.map_compose]
  | .curry _ _ _ _ => by
      simp only [ArrowCode.map, ObjectCode.map_compose, ArrowCode.map_compose]
  | .equalizerArrow _ _ _ _ => by
      simp only [ArrowCode.map, ObjectCode.map_compose, ArrowCode.map_compose]
  | .equalizerLift _ _ _ _ _ _ => by
      simp only [ArrowCode.map, ObjectCode.map_compose, ArrowCode.map_compose]

end

end Composition

mutual

def ObjectCode.before (objectRank : symbols.ObjectName → Nat)
    (arrowRank : symbols.ArrowName → Nat) (bound : Nat) : ObjectCode C symbols → Prop
  | .base _ => True
  | .name origin => objectRank origin < bound
  | .terminal => True
  | .product first second => first.before objectRank arrowRank bound ∧
      second.before objectRank arrowRank bound
  | .exponential argument result => argument.before objectRank arrowRank bound ∧
      result.before objectRank arrowRank bound
  | .equalizer source target first second => source.before objectRank arrowRank bound ∧
      target.before objectRank arrowRank bound ∧ first.before objectRank arrowRank bound ∧
      second.before objectRank arrowRank bound

def ArrowCode.before (objectRank : symbols.ObjectName → Nat)
    (arrowRank : symbols.ArrowName → Nat) (bound : Nat) : ArrowCode C symbols → Prop
  | .base _ => True
  | .name origin => arrowRank origin < bound
  | .identity object => object.before objectRank arrowRank bound
  | .compose first second => first.before objectRank arrowRank bound ∧
      second.before objectRank arrowRank bound
  | .terminal source => source.before objectRank arrowRank bound
  | .first first second => first.before objectRank arrowRank bound ∧
      second.before objectRank arrowRank bound
  | .second first second => first.before objectRank arrowRank bound ∧
      second.before objectRank arrowRank bound
  | .pair first second => first.before objectRank arrowRank bound ∧
      second.before objectRank arrowRank bound
  | .evaluation argument result => argument.before objectRank arrowRank bound ∧
      result.before objectRank arrowRank bound
  | .curry context argument result body => context.before objectRank arrowRank bound ∧
      argument.before objectRank arrowRank bound ∧ result.before objectRank arrowRank bound ∧
      body.before objectRank arrowRank bound
  | .equalizerArrow source target first second => source.before objectRank arrowRank bound ∧
      target.before objectRank arrowRank bound ∧ first.before objectRank arrowRank bound ∧
      second.before objectRank arrowRank bound
  | .equalizerLift source target first second context candidate =>
      source.before objectRank arrowRank bound ∧ target.before objectRank arrowRank bound ∧
      first.before objectRank arrowRank bound ∧ second.before objectRank arrowRank bound ∧
      context.before objectRank arrowRank bound ∧ candidate.before objectRank arrowRank bound

end

/-- Local declarations use only earlier object and arrow names. Formation
certificates, which are not implied by rank closure, are supplied separately. -/
structure Signature where
  objectRank : symbols.ObjectName → Nat
  arrowRank : symbols.ArrowName → Nat
  source : symbols.ArrowName → ObjectCode C symbols
  target : symbols.ArrowName → ObjectCode C symbols
  source_before : ∀ origin, (source origin).before objectRank arrowRank (arrowRank origin)
  target_before : ∀ origin, (target origin).before objectRank arrowRank (arrowRank origin)
  equationRank : symbols.EquationName → Nat
  equationSource : symbols.EquationName → ObjectCode C symbols
  equationTarget : symbols.EquationName → ObjectCode C symbols
  left : symbols.EquationName → ArrowCode C symbols
  right : symbols.EquationName → ArrowCode C symbols
  equation_before : ∀ origin,
    (equationSource origin).before objectRank arrowRank (equationRank origin) ∧
    (equationTarget origin).before objectRank arrowRank (equationRank origin) ∧
    (left origin).before objectRank arrowRank (equationRank origin) ∧
    (right origin).before objectRank arrowRank (equationRank origin)

end Mettapedia.CategoryTheory.RelativeClosedSyntax
