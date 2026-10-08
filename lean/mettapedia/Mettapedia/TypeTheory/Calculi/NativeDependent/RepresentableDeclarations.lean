import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementHeaderFormation
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Subfunctor.Basic

/-!
# Native declarations of objects, arrows and representable predicates

Every object of a supplied category gives a primitive type. Every actual
arrow gives a unary term declaration with its source parameter and target
result. Every subfunctor of a representable gives a unary predicate with
that same object parameter. The syntax, ordered headers and their generated
formation trees are constructed before a semantic interpretation is chosen.

This is a declaration presentation. Its primitive arrow names have not yet
been quotiented by the composition equations of the supplied category.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.RepresentableDeclarations

open _root_.CategoryTheory

universe u
variable (C : Type u) [Category.{u} C]

structure ArrowSymbol where
  source : C
  target : C
  arrow : source ⟶ target

structure PredicateSymbol where
  domain : C
  predicate : Subfunctor (yoneda.obj domain)

def symbols : Symbols where
  TypeSymbol := C
  TermSymbol := ArrowSymbol C
  PredicateSymbol := PredicateSymbol C
  typeArity := fun _ => 0
  termArity := fun _ => 1
  predicateArity := fun _ => 1

variable {C}

def objectType (object : C) (n : Nat) : TypeExpr (symbols C) n :=
  .family object Fin.elim0

def objectContext (object : C) : ContextExpr (symbols C) 1 :=
  .snoc .nil (objectType object 0)

def singletonArgument {n : Nat} (value : TermExpr (symbols C) n) :
    Substitution (symbols C) 1 n := extendSubstitution Fin.elim0 value

def arrowTerm {source target : C} (arrow : source ⟶ target)
    {n : Nat} (argument : TermExpr (symbols C) n) : TermExpr (symbols C) n :=
  .primitive ⟨source, target, arrow⟩ (singletonArgument argument)

def predicateTerm {object : C} (predicate : Subfunctor (yoneda.obj object))
    {n : Nat} (argument : TermExpr (symbols C) n) : PropExpr (symbols C) n :=
  .atom ⟨object, predicate⟩ (singletonArgument argument)

def signature (C : Type u) [Category.{u} C] : Signature (symbols C) where
  typeRank := fun _ => 0
  termRank := fun _ => 1
  predicateRank := fun _ => 1
  typeParameters := fun _ => .nil
  termParameters := fun symbol => objectContext symbol.source
  predicateParameters := fun symbol => objectContext symbol.domain
  termResult := fun symbol => objectType symbol.target 1
  typeParameters_before := fun _ => True.intro
  termParameters_before := by
    intro symbol
    exact ⟨True.intro, Nat.zero_lt_succ 0, fun position => Fin.elim0 position⟩
  predicateParameters_before := by
    intro symbol
    exact ⟨True.intro, Nat.zero_lt_succ 0, fun position => Fin.elim0 position⟩
  termResult_before := by
    intro symbol
    exact ⟨Nat.zero_lt_succ 0, fun position => Fin.elim0 position⟩

@[simp] theorem objectType_rename (object : C) {n m : Nat} (mapping : Renaming n m) :
    (objectType object n).rename mapping = objectType object m := by
  apply congrArg (TypeExpr.family (S := symbols C) object)
  funext position
  exact Fin.elim0 position

@[simp] theorem objectType_substitute (object : C) {n m : Nat}
    (substitution : Substitution (symbols C) n m) :
    (objectType object n).substitute substitution = objectType object m := by
  apply congrArg (TypeExpr.family (S := symbols C) object)
  funext position
  exact Fin.elim0 position

def emptyFormed : Derivation (signature C) (.context .nil) :=
  deriveList .contextNil .nil

def objectFormed (object : C) {n : Nat} {context : ContextExpr (symbols C) n}
    (formed : Derivation (signature C) (.context context)) :
    Derivation (signature C) (.type context (objectType object n)) :=
  deriveList (.typeFamily context object Fin.elim0)
    (.cons formed (.cons emptyFormed
      (.cons (deriveList (.substitutionNil context) (.cons formed .nil)) .nil)))

def objectContextFormed (object : C) :
    Derivation (signature C) (.context (objectContext object)) :=
  deriveList (.contextExtend .nil (objectType object 0))
    (.cons emptyFormed (.cons (objectFormed object emptyFormed) .nil))

theorem emptyFormed_before (bound : Nat) :
    (emptyFormed (C := C)).before bound :=
  deriveList_before .contextNil .nil bound True.intro True.intro

theorem objectFormed_before (object : C) {n : Nat} {context : ContextExpr (symbols C) n}
    (formed : Derivation (signature C) (.context context)) (bound : Nat)
    (ordered : formed.before bound) (positive : 0 < bound) :
    (objectFormed object formed).before bound := by
  have contextOrder := formed.before_judgment ordered
  have emptySubstitutionOrder :
      (deriveList (.substitutionNil context) (.cons formed .nil)).before bound :=
    deriveList_before (.substitutionNil context) (.cons formed .nil) bound
      ⟨contextOrder, True.intro, fun position => Fin.elim0 position⟩ ⟨ordered, True.intro⟩
  exact deriveList_before (.typeFamily context object Fin.elim0) _ bound
    ⟨contextOrder, positive, fun position => Fin.elim0 position⟩
    ⟨ordered, emptyFormed_before bound, emptySubstitutionOrder, True.intro⟩

theorem objectContextFormed_before (object : C) (bound : Nat) (positive : 0 < bound) :
    (objectContextFormed object).before bound :=
  deriveList_before (.contextExtend .nil (objectType object 0)) _ bound
    ⟨True.intro, positive, fun position => Fin.elim0 position⟩
    ⟨emptyFormed_before bound,
      objectFormed_before object emptyFormed bound (emptyFormed_before bound) positive, True.intro⟩

/-- All declaration headers have actual earlier-ranked formation trees. -/
def headers (C : Type u) [Category.{u} C] : HeaderFormation (signature C) where
  typeHeader := fun _ => emptyFormed
  typeHeader_before := fun _ => emptyFormed_before 0
  termHeader := fun symbol => objectContextFormed symbol.source
  termHeader_before := fun symbol => objectContextFormed_before symbol.source 1 (by decide)
  termResult := fun symbol => objectFormed symbol.target (objectContextFormed symbol.source)
  termResult_before := fun symbol => objectFormed_before symbol.target _ 1
    (objectContextFormed_before symbol.source 1 (by decide)) (by decide)
  predicateHeader := fun symbol => objectContextFormed symbol.domain
  predicateHeader_before := fun symbol => objectContextFormed_before symbol.domain 1 (by decide)

def variableFormed (object : C) :
    Derivation (signature C) (.term (objectContext object) (.var 0) (objectType object 1)) := by
  simpa only [RuleCode.conclusion, objectContext, ContextExpr.lookup_zero, objectType_rename] using
    deriveList (.variable (objectContext object) 0) (.cons (objectContextFormed object) .nil)

def objectArguments (object : C) {n : Nat} {context : ContextExpr (symbols C) n}
    {value : TermExpr (symbols C) n} (formed : Derivation (signature C) (.context context))
    (typed : Derivation (signature C) (.term context value (objectType object n))) :
    Derivation (signature C) (.substitution context (objectContext object) (singletonArgument value)) := by
  have valueTree : Derivation (signature C)
      (.term context value ((objectType object 0).substitute Fin.elim0)) := by
    simpa only [objectType_substitute] using typed
  exact deriveList (.substitutionExtend context .nil (objectType object 0) Fin.elim0 value)
    (.cons (deriveList (.substitutionNil context) (.cons formed .nil))
      (.cons (objectFormed object emptyFormed) (.cons valueTree .nil)))

def arrowFormed {source target : C} (arrow : source ⟶ target)
    {n : Nat} {context : ContextExpr (symbols C) n} {argument : TermExpr (symbols C) n}
    (formed : Derivation (signature C) (.context context))
    (typed : Derivation (signature C) (.term context argument (objectType source n))) :
    Derivation (signature C) (.term context (arrowTerm arrow argument) (objectType target n)) := by
  have tree :=
    deriveList (.primitive context ⟨source, target, arrow⟩ (singletonArgument argument))
      (.cons formed (.cons (objectContextFormed source)
        (.cons ((headers C).termResult ⟨source, target, arrow⟩)
          (.cons (objectArguments source formed typed) .nil))))
  change Derivation (signature C) (.term context (arrowTerm arrow argument)
    ((objectType target 1).substitute (singletonArgument argument))) at tree
  rw [objectType_substitute] at tree
  exact tree

def predicateFormed {object : C} (predicate : Subfunctor (yoneda.obj object))
    {n : Nat} {context : ContextExpr (symbols C) n} {argument : TermExpr (symbols C) n}
    (formed : Derivation (signature C) (.context context))
    (typed : Derivation (signature C) (.term context argument (objectType object n))) :
    Derivation (signature C) (.predicate context (predicateTerm predicate argument)) :=
  deriveList (.predicatePrimitive context ⟨object, predicate⟩ (singletonArgument argument))
    (.cons formed (.cons (objectContextFormed object)
      (.cons (objectArguments object formed typed) .nil)))

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.RepresentableDeclarations
