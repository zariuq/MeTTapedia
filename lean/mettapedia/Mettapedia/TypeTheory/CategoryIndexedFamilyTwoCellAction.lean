import Mathlib.CategoryTheory.Yoneda
import Mettapedia.TypeTheory.CategoryIndexedFamilyCwf

/-!
# Two-cell action on category-indexed dependent families

For category-indexed families, a natural transformation between two context
substitutions acts on every reindexed family by right whiskering.  This action
extends to natural sections and to the corresponding categories of elements.

The action is jointly faithful: covariant representable families distinguish
distinct natural transformations.  Consequently this dependent semantics
neither creates nor erases context-level two-cell distinctions.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.CategoryIndexedFamilyTwoCellAction

open CategoryTheory
open Opposite
open Mettapedia.TypeTheory.CategoryIndexedFamilyCwf

universe u v uSource vSource uTarget vTarget

/-! ## Universe-polymorphic family action -/

/-- Right whiskering gives the action of a natural transformation on a
covariant family, without requiring the object and morphism universes of the
two categories to coincide. -/
def whiskeredFamilyAction
    {Source : Type uSource} [Category.{vSource} Source]
    {Target : Type uTarget} [Category.{vTarget} Target]
    {left right : Functor Source Target}
    (cell : left ⟶ right) (family : Functor Target (Type v)) :
    left ⋙ family ⟶ right ⋙ family :=
  Functor.whiskerRight cell family

@[simp] theorem whiskeredFamilyAction_identity
    {Source : Type uSource} [Category.{vSource} Source]
    {Target : Type uTarget} [Category.{vTarget} Target]
    (substitution : Functor Source Target)
    (family : Functor Target (Type v)) :
    whiskeredFamilyAction (𝟙 substitution) family =
      𝟙 (substitution ⋙ family) :=
  Functor.whiskerRight_id' family

@[simp] theorem whiskeredFamilyAction_vertical
    {Source : Type uSource} [Category.{vSource} Source]
    {Target : Type uTarget} [Category.{vTarget} Target]
    {first middle last : Functor Source Target}
    (earlier : first ⟶ middle) (later : middle ⟶ last)
    (family : Functor Target (Type v)) :
    whiskeredFamilyAction (earlier ≫ later) family =
      whiskeredFamilyAction earlier family ≫
        whiskeredFamilyAction later family :=
  Functor.whiskerRight_comp earlier later family

/-- The simultaneous action of one context cell on all covariant families
whose fibres live in the hom universe of the target category. -/
abbrev WhiskeredDependentAction
    {Source : Type uSource} [Category.{vSource} Source]
    {Target : Type uTarget} [Category.{vTarget} Target]
    (left right : Functor Source Target) :=
  (family : Functor Target (Type vTarget)) →
    left ⋙ family ⟶ right ⋙ family

/-- Bundle the universe-polymorphic actions of one context cell. -/
def whiskeredDependentAction
    {Source : Type uSource} [Category.{vSource} Source]
    {Target : Type uTarget} [Category.{vTarget} Target]
    {left right : Functor Source Target} :
    (left ⟶ right) → WhiskeredDependentAction left right :=
  fun cell family => whiskeredFamilyAction cell family

/-- Covariant representables jointly distinguish natural transformations,
also when object and morphism universes differ. -/
theorem whiskeredDependentAction_injective
    {Source : Type uSource} [Category.{vSource} Source]
    {Target : Type uTarget} [Category.{vTarget} Target]
    {left right : Functor Source Target} :
    Function.Injective
      (whiskeredDependentAction (left := left) (right := right)) := by
  intro first second equalActions
  apply NatTrans.ext
  funext point
  let representable : Functor Target (Type vTarget) :=
    coyoneda.obj (op (left.obj point))
  have actionEquality := congrFun equalActions representable
  have componentEquality := congrArg
    (fun action => action.app point) actionEquality
  have valueEquality := ConcreteCategory.congr_hom componentEquality
    (𝟙 (left.obj point))
  change
    (𝟙 (left.obj point)) ≫ first.app point =
      (𝟙 (left.obj point)) ≫ second.app point at valueEquality
  simpa using valueEquality

/-! ## Action on families and sections -/

/-- A natural transformation between substitutions acts on a dependent family
by right whiskering. -/
def familyAction
    {source target : Context.{u}}
    {left right : ContextHom source target}
    (cell : left ⟶ right) (family : IndexedFamily target) :
    reindexFamily family left ⟶ reindexFamily family right :=
  Functor.whiskerRight cell family

@[simp] theorem familyAction_app
    {source target : Context.{u}}
    {left right : ContextHom source target}
    (cell : left ⟶ right) (family : IndexedFamily target)
    (point : source) :
    (familyAction cell family).app point =
      family.map (cell.app point) :=
  rfl

@[simp] theorem familyAction_identity
    {source target : Context.{u}}
    (substitution : ContextHom source target)
    (family : IndexedFamily target) :
    familyAction (𝟙 substitution) family =
      𝟙 (reindexFamily family substitution) :=
  Functor.whiskerRight_id' family

@[simp] theorem familyAction_vertical
    {source target : Context.{u}}
    {first middle last : ContextHom source target}
    (earlier : first ⟶ middle) (later : middle ⟶ last)
    (family : IndexedFamily target) :
    familyAction (earlier ≫ later) family =
      familyAction earlier family ≫ familyAction later family :=
  Functor.whiskerRight_comp earlier later family

/-- Map a natural section along a morphism of category-indexed families. -/
def mapSection
    {context : Context.{u}} {left right : IndexedFamily context}
    (cell : left ⟶ right) (term : IndexedSection left) :
    IndexedSection right :=
  ((Functor.sectionsFunctor (context : Type u)).map cell) term

@[simp] theorem mapSection_value
    {context : Context.{u}} {left right : IndexedFamily context}
    (cell : left ⟶ right) (term : IndexedSection left)
    (point : context) :
    (mapSection cell term).1 point = cell.app point (term.1 point) :=
  rfl

@[simp] theorem mapSection_identity
    {context : Context.{u}} {family : IndexedFamily context}
    (term : IndexedSection family) :
    mapSection (𝟙 family) term = term := by
  apply Subtype.ext
  rfl

@[simp] theorem mapSection_vertical
    {context : Context.{u}}
    {first middle last : IndexedFamily context}
    (earlier : first ⟶ middle) (later : middle ⟶ last)
    (term : IndexedSection first) :
    mapSection (earlier ≫ later) term =
      mapSection later (mapSection earlier term) := by
  apply (Functor.sections_ext_iff).2
  intro point
  rfl

/-- Reindexing a global section along either side of a context cell agrees
after applying the induced action on the family. -/
theorem reindexSection_action
    {source target : Context.{u}}
    {left right : ContextHom source target}
    (cell : left ⟶ right) {family : IndexedFamily target}
    (term : IndexedSection family) :
    mapSection (familyAction cell family)
        (reindexSection term left) =
      reindexSection term right := by
  apply (Functor.sections_ext_iff).2
  intro point
  change family.map (cell.app point) (term.1 (left.obj point)) =
    term.1 (right.obj point)
  exact term.2 (cell.app point)

/-! ## Action on comprehension -/

/-- The induced functor between categories of elements. -/
def comprehensionAction
    {source target : Context.{u}}
    {left right : ContextHom source target}
    (cell : left ⟶ right) (family : IndexedFamily target) :
    ContextHom (extend source (reindexFamily family left))
      (extend source (reindexFamily family right)) :=
  ((Functor.elementsFunctor).map
    (familyAction cell family)).toFunctor

@[simp] theorem comprehensionAction_projection
    {source target : Context.{u}}
    {left right : ContextHom source target}
    (cell : left ⟶ right) (family : IndexedFamily target) :
    contextCompose (comprehensionAction cell family)
        (weaken (reindexFamily family right)) =
      weaken (reindexFamily family left) :=
  rfl

@[simp] theorem comprehensionAction_identity
    {source target : Context.{u}}
    (substitution : ContextHom source target)
    (family : IndexedFamily target) :
    comprehensionAction (𝟙 substitution) family =
      contextIdentity (extend source (reindexFamily family substitution)) := by
  change
    ((Functor.elementsFunctor).map
      (familyAction (𝟙 substitution) family)).toFunctor =
      (contextIdentity
        (extend source (reindexFamily family substitution)))
  rw [familyAction_identity]
  have mappedIdentity :=
    (Functor.elementsFunctor).map_id
      (reindexFamily family substitution)
  exact congrArg Cat.Hom.toFunctor mappedIdentity

@[simp] theorem comprehensionAction_vertical
    {source target : Context.{u}}
    {first middle last : ContextHom source target}
    (earlier : first ⟶ middle) (later : middle ⟶ last)
    (family : IndexedFamily target) :
    comprehensionAction (earlier ≫ later) family =
      contextCompose (comprehensionAction earlier family)
        (comprehensionAction later family) := by
  change
    ((Functor.elementsFunctor).map
      (familyAction (earlier ≫ later) family)).toFunctor =
      contextCompose
        (((Functor.elementsFunctor).map
          (familyAction earlier family)).toFunctor)
        (((Functor.elementsFunctor).map
          (familyAction later family)).toFunctor)
  rw [familyAction_vertical]
  have mappedComposition :=
    (Functor.elementsFunctor).map_comp
      (familyAction earlier family) (familyAction later family)
  exact congrArg Cat.Hom.toFunctor mappedComposition

/-- The family action pulled back to the source comprehension. -/
def variableFamilyAction
    {source target : Context.{u}}
    {left right : ContextHom source target}
    (cell : left ⟶ right) (family : IndexedFamily target) :
    reindexFamily (reindexFamily family left)
        (weaken (reindexFamily family left)) ⟶
      reindexFamily (reindexFamily family right)
        (weaken (reindexFamily family left)) :=
  Functor.whiskerLeft (weaken (reindexFamily family left))
    (familyAction cell family)

/-- The induced comprehension functor transports the selected last variable
exactly by the family action. -/
theorem comprehensionAction_lastVariable
    {source target : Context.{u}}
    {left right : ContextHom source target}
    (cell : left ⟶ right) (family : IndexedFamily target) :
    mapSection (variableFamilyAction cell family)
        (lastVariable (reindexFamily family left)) =
      reindexSection (lastVariable (reindexFamily family right))
        (comprehensionAction cell family) := by
  apply (Functor.sections_ext_iff).2
  rintro ⟨point, value⟩
  change family.map (cell.app point) value =
    family.map (cell.app point) value
  rfl

/-! ## Joint faithfulness -/

/-- The full dependent action of a context cell on all target families. -/
abbrev DependentAction
    {source target : Context.{u}}
    (left right : ContextHom source target) :=
  (family : IndexedFamily target) →
    reindexFamily family left ⟶ reindexFamily family right

/-- Bundle all family actions of one context cell. -/
def dependentAction
    {source target : Context.{u}}
    {left right : ContextHom source target} :
    (left ⟶ right) → DependentAction left right :=
  fun cell family => familyAction cell family

/-- Covariant representable families jointly distinguish context cells. -/
theorem dependentAction_injective
    {source target : Context.{u}}
    {left right : ContextHom source target} :
    Function.Injective
      (dependentAction (left := left) (right := right)) := by
  intro first second equalActions
  apply NatTrans.ext
  funext point
  let representable : IndexedFamily target :=
    coyoneda.obj (op (left.obj point))
  have actionEquality := congrFun equalActions representable
  have componentEquality := congrArg
    (fun action => action.app point) actionEquality
  have valueEquality := ConcreteCategory.congr_hom componentEquality
    (𝟙 (left.obj point))
  change
    (𝟙 (left.obj point)) ≫ first.app point =
      (𝟙 (left.obj point)) ≫ second.app point at valueEquality
  simpa using valueEquality

/-- Exact equality criterion: two context cells have the same action on every
dependent family precisely when they are equal. -/
theorem dependentAction_eq_iff
    {source target : Context.{u}}
    {left right : ContextHom source target}
    (first second : left ⟶ right) :
    dependentAction first = dependentAction second ↔ first = second := by
  constructor
  · intro equality
    exact dependentAction_injective equality
  · intro equality
    cases equality
    rfl

/-! ## Point substitutions turn routes into genuine context cells -/

/-- Select one object of a context as a substitution from the terminal
one-object context. -/
def pointSubstitution (context : Context.{u}) (point : context) :
    ContextHom emptyContext context :=
  (Functor.const (emptyContext : Type u)).obj point

/-- A route in a context is equivalently visible as a natural transformation
between the corresponding point substitutions. -/
def pointCell {context : Context.{u}} {source target : context}
    (route : source ⟶ target) :
    pointSubstitution context source ⟶
      pointSubstitution context target where
  app _ := route
  naturality := by
    intro _ _ _
    change (𝟙 source) ≫ route = route ≫ 𝟙 target
    simp

@[simp] theorem pointCell_app
    {context : Context.{u}} {source target : context}
    (route : source ⟶ target) (point : Discrete PUnit) :
    (pointCell route).app point = route :=
  rfl

/-- Point cells retain the identity of their underlying route. -/
theorem pointCell_injective
    {context : Context.{u}} {source target : context} :
    Function.Injective
      (pointCell : (source ⟶ target) →
        (pointSubstitution context source ⟶
          pointSubstitution context target)) := by
  intro first second equality
  have componentEquality := congrArg
    (fun cell => cell.app (Discrete.mk PUnit.unit)) equality
  exact componentEquality

/-- Any family which distinguishes two parallel routes also distinguishes the
induced actions of the corresponding point cells. -/
theorem pointCell_familyActions_ne_of_map_ne
    {context : Context.{u}} {source target : context}
    (family : IndexedFamily context)
    (first second : source ⟶ target) (value : family.obj source)
    (distinguishes : family.map first value ≠ family.map second value) :
    familyAction (pointCell first) family ≠
      familyAction (pointCell second) family := by
  intro actionsEqual
  have componentEquality := congrArg
    (fun action => action.app (Discrete.mk PUnit.unit)) actionsEqual
  have valueEquality := ConcreteCategory.congr_hom componentEquality value
  exact distinguishes valueEquality

/-! ## Axiom audit -/

#print axioms reindexSection_action
#print axioms comprehensionAction_lastVariable
#print axioms whiskeredDependentAction_injective
#print axioms dependentAction_injective
#print axioms pointCell_familyActions_ne_of_map_ne

end Mettapedia.TypeTheory.CategoryIndexedFamilyTwoCellAction
