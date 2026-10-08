import Mettapedia.TypeTheory.Calculi.NativeDependent.RepresentableIndexedTerms
import Mettapedia.TypeTheory.Calculi.NativeDependent.RepresentableDeclarationArrows

/-!
# Actual generated substitution acts on complete indexed native families

An independently formed original-arrow substitution is evaluated at the
actual object scopes. Its type, term and predicate actions commute with
native reindexing. In particular, the generated original-arrow fibre type
is pulled back along the complete supplied original map.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.RepresentableIndexedDeclarations

open _root_.CategoryTheory
open ContextualModelTelescopes NativeLocalTypeFormers

universe u
variable {C : Type u} [Category.{u} C]

noncomputable section

def arrowTerm {source target : C} (arrow : source ⟶ target) {n : Nat}
    (argument : TermExpr (symbols C) n) : TermExpr (symbols C) n :=
  .primitive (.ordinary ⟨source, target, arrow⟩) (singletonArgument argument)

def arrowFormed {source target : C} (arrow : source ⟶ target) {n : Nat}
    {context : ContextExpr (symbols C) n} {argument : TermExpr (symbols C) n}
    (formed : Derivation (signature C) (.context context))
    (typed : Derivation (signature C) (.term context argument (objectType source n))) :
    Derivation (signature C) (.term context (arrowTerm arrow argument) (objectType target n)) := by
  have tree := deriveList (.primitive context (.ordinary ⟨source, target, arrow⟩) (singletonArgument argument))
    (.cons formed (.cons (objectContextFormed source)
      (.cons ((headers C).termResult (.ordinary ⟨source, target, arrow⟩))
        (.cons (objectArguments source formed typed) .nil))))
  change Derivation (signature C) (.term context (arrowTerm arrow argument)
    ((objectType target 1).substitute (singletonArgument argument))) at tree
  rw [objectType_substitute] at tree
  exact tree

def originalSubstitution {source target : C} (arrow : source ⟶ target) :
    Substitution (symbols C) 1 1 := singletonArgument (arrowTerm arrow (.var 0))

def originalSubstitutionFormed {source target : C} (arrow : source ⟶ target) :
    Derivation (signature C) (.substitution (objectContext source) (objectContext target)
      (originalSubstitution arrow)) :=
  objectArguments target (objectContextFormed source)
    (arrowFormed arrow (objectContextFormed source) (variableFormed source))

abbrev originalMap {source target : C} (arrow : source ⟶ target) :=
  RepresentableDeclarations.originalPresheafArrow arrow

theorem arrow_read {source target : C} (arrow : source ⟶ target) :
    (model C).evaluateTerm (objectScope source) (arrowTerm arrow (.var 0)) =
      some ⟨RepresentableDeclarations.arrowMeaning ⟨source, target, arrow⟩,
        RepresentableDeclarations.arrowValue ⟨source, target, arrow⟩⟩ := by
  have read := (model C).evaluate_primitive (objectScope source) (.ordinary ⟨source, target, arrow⟩)
    (singletonArgument (.var 0)) (𝟙 (objectScope source).1) (by
      intro position
      cases position using Fin.cases with
      | zero => exact variable_identity source
      | succ impossible => exact Fin.elim0 impossible)
  change (model C).evaluateTerm (objectScope source) (arrowTerm arrow (.var 0)) =
    some (Value.substitute (K := (NativeModel C).toCwf)
      (⟨RepresentableDeclarations.arrowMeaning ⟨source, target, arrow⟩,
        RepresentableDeclarations.arrowValue ⟨source, target, arrow⟩⟩ : NativeValue (objectScope source).1)
      (𝟙 (objectScope source).1)) at read
  exact read.trans (congrArg some
    (Value.substitute_identity (K := (NativeModel C).toCwf)
      ⟨RepresentableDeclarations.arrowMeaning ⟨source, target, arrow⟩,
        RepresentableDeclarations.arrowValue ⟨source, target, arrow⟩⟩))

theorem original_substitution_read {source target : C} (arrow : source ⟶ target) :
    (model C).evaluateSubstitution (objectScope source) (objectScope target)
      (originalSubstitution arrow) = some (originalMap arrow) := by
  apply ((model C).evaluateSubstitution_eq_some_iff _ _ _ _).2
  intro position
  cases position using Fin.cases with
  | zero =>
    change (model C).evaluateTerm (objectScope source) (arrowTerm arrow (.var 0)) = _
    rw [RepresentableDeclarations.original_component]
    exact arrow_read arrow
  | succ impossible => exact Fin.elim0 impossible

def originalModelSubstitution {source target : C} (arrow : source ⟶ target) :
    ModelSubstitution (model C) (objectScope source) (objectScope target) (originalSubstitution arrow) :=
  ModelSubstitution.ofEvaluated (model C) _ _ _ _ (original_substitution_read arrow)

theorem complete_type_substitution {source target : C} (arrow : source ⟶ target)
    (expression : TypeExpr (symbols C) 1) (family : NativeType (objectScope target).1)
    (read : (model C).evaluateType (objectScope target) expression = some family) :
    (model C).evaluateType (objectScope source) (expression.substitute (originalSubstitution arrow)) =
      some (family.reindex (originalMap arrow)) :=
  (model C).evaluateType_substitute (NativeLocalTypeOperations.products_substitution C)
    expression _ _ _ (originalModelSubstitution arrow) family read

theorem complete_value_substitution {source target : C} (arrow : source ⟶ target)
    (expression : TermExpr (symbols C) 1) (value : NativeValue (objectScope target).1)
    (read : (model C).evaluateTerm (objectScope target) expression = some value) :
    (model C).evaluateTerm (objectScope source) (expression.substitute (originalSubstitution arrow)) =
      some (Value.substitute (K := (NativeModel C).toCwf) value (originalMap arrow)) :=
  (model C).evaluateTerm_substitute (NativeLocalTypeOperations.products_substitution C)
    expression _ _ _ (originalModelSubstitution arrow) value read

theorem complete_predicate_substitution {source target : C} (arrow : source ⟶ target)
    (expression : PropExpr (symbols C) 1) (predicate : Subfunctor (objectScope target).1)
    (read : (model C).evaluatePredicate (objectScope target) expression = some predicate) :
    (model C).evaluatePredicate (objectScope source) (expression.substitute (originalSubstitution arrow)) =
      some (predicate.preimage (originalMap arrow)) :=
  (model C).evaluatePredicate_substitute (NativeLocalTypeOperations.products_substitution C)
    expression _ _ _ (originalModelSubstitution arrow) predicate read

theorem complete_indexed_family_substitution (index : ArrowSymbol C) {source : C}
    (before : source ⟶ index.target) :
    (model C).evaluateType (objectScope source)
      ((fibreType index (.var 0)).substitute (originalSubstitution before)) =
        some ((fibreMeaning index).reindex (originalMap before)) :=
  complete_type_substitution before (fibreType index (.var 0)) (fibreMeaning index)
    (generic_fibre_read index)

end

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.RepresentableIndexedDeclarations
