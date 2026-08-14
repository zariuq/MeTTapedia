import Mathlib.CategoryTheory.Category.Basic

/-!
# Multisorted clones

A multisorted clone is the algebraic core of a cartesian multicategory.  An
operation has an ordered context of input sorts and one output sort.  Variables
select input occurrences, and simultaneous substitution composes operations
over one shared context.  Because inputs may be omitted or cited repeatedly,
weakening and contraction are present without being postulated as equations
between unrelated proof artifacts.
-/

namespace Mettapedia.GSLT.LanguageDef

universe u v

/-- A proof-relevant multisorted clone with positional variables and
simultaneous substitution. -/
structure MultiSortedClone (Sorts : Type u) where
  Hom : List Sorts → Sorts → Type v
  project :
    {context : List Sorts} →
      (index : Fin context.length) → Hom context (context.get index)
  substitute :
    {sourceContext targetContext : List Sorts} → {output : Sorts} →
      Hom sourceContext output →
      ((index : Fin sourceContext.length) →
        Hom targetContext (sourceContext.get index)) →
      Hom targetContext output
  substitute_project :
    ∀ {sourceContext targetContext : List Sorts}
      (environment : (index : Fin sourceContext.length) →
        Hom targetContext (sourceContext.get index))
      (index : Fin sourceContext.length),
      substitute (project index) environment = environment index
  substitute_projects :
    ∀ {context : List Sorts} {output : Sorts}
      (operation : Hom context output),
      substitute operation (fun index => project index) = operation
  substitute_assoc :
    ∀ {firstContext secondContext thirdContext : List Sorts}
      {output : Sorts} (operation : Hom firstContext output)
      (first : (index : Fin firstContext.length) →
        Hom secondContext (firstContext.get index))
      (second : (index : Fin secondContext.length) →
        Hom thirdContext (secondContext.get index)),
      substitute (substitute operation first) second =
        substitute operation
          (fun index => substitute (first index) second)

namespace MultiSortedClone

variable {Sorts : Type u} (clone : MultiSortedClone.{u, v} Sorts)

/-- A simultaneous proof environment from `source` to `target` proves every
target occurrence from the shared source context. -/
def Environment (source target : List Sorts) : Type v :=
  (index : Fin target.length) → clone.Hom source (target.get index)

/-- Contexts for one selected clone.  The clone parameter prevents category
instances for different proof calculi from being conflated. -/
structure ContextObject where
  context : List Sorts
  private cloneMarker : clone = clone

/-- Bundle an ordered list as a context of the selected clone. -/
def ContextObject.ofList (context : List Sorts) : ContextObject clone :=
  ⟨context, rfl⟩

instance : Quiver (ContextObject clone) where
  Hom source target := clone.Environment source.context target.context

/-- Ordered contexts and simultaneous proof environments form a category.
Identity is the vector of positional projections; composition substitutes the
earlier environment into every proof in the later environment. -/
instance : CategoryTheory.Category (ContextObject clone) where
  id := fun context index => clone.project index
  comp earlier later := fun index => clone.substitute (later index) earlier
  id_comp environment := by
    funext index
    exact clone.substitute_projects (environment index)
  comp_id environment := by
    funext index
    exact clone.substitute_project environment index
  assoc first second third := by
    funext index
    exact (clone.substitute_assoc (third index) second first).symm

/-- A clone operation is equivalently a morphism from its context to the
singleton context containing its output. -/
def operationAsSingletonMorphism
    {context : List Sorts} {output : Sorts}
    (operation : clone.Hom context output) :
    ContextObject.ofList clone context ⟶
      ContextObject.ofList clone [output] :=
  fun index => Fin.cases operation (fun impossible => Fin.elim0 impossible) index

@[simp]
theorem operationAsSingletonMorphism_zero
    {context : List Sorts} {output : Sorts}
    (operation : clone.Hom context output) :
    clone.operationAsSingletonMorphism operation (0 : Fin 1) = operation :=
  rfl

end MultiSortedClone

end Mettapedia.GSLT.LanguageDef
