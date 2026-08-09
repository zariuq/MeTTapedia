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

end Mettapedia.GSLT.LanguageDef
