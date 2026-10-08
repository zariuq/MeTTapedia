import Mettapedia.TypeTheory.Calculi.NativeDependent.RepresentableDeclarations

/-!
# Generated dependent declarations indexed by original arrows

An original arrow gives a type over its target object. A value of that
type has a declared forgetful term into the original source object.
Object types precede indexed types, which precede term declarations.
All parameter and result headers have actual generated formation trees.
No semantic family is used to define this judgment presentation.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.RepresentableIndexedDeclarations

open _root_.CategoryTheory

universe u
variable (C : Type u) [Category.{u} C]

abbrev ArrowSymbol := RepresentableDeclarations.ArrowSymbol C
abbrev PredicateSymbol := RepresentableDeclarations.PredicateSymbol C

inductive TypeSymbol where
  | object : C → TypeSymbol
  | fibre : ArrowSymbol C → TypeSymbol

inductive TermSymbol where
  | ordinary : ArrowSymbol C → TermSymbol
  | forget : ArrowSymbol C → TermSymbol

def symbols : Symbols where
  TypeSymbol := TypeSymbol C
  TermSymbol := TermSymbol C
  PredicateSymbol := PredicateSymbol C
  typeArity := fun symbol => match symbol with
    | .object _ => 0
    | .fibre _ => 1
  termArity := fun symbol => match symbol with
    | .ordinary _ => 1
    | .forget _ => 2
  predicateArity := fun _ => 1

variable {C}

def objectType (object : C) (n : Nat) : TypeExpr (symbols C) n :=
  .family (.object object) Fin.elim0

def objectContext (object : C) : ContextExpr (symbols C) 1 :=
  .snoc .nil (objectType object 0)

def singletonArgument {n : Nat} (value : TermExpr (symbols C) n) :
    Substitution (symbols C) 1 n := extendSubstitution Fin.elim0 value

def fibreType (arrow : ArrowSymbol C) {n : Nat}
    (argument : TermExpr (symbols C) n) : TypeExpr (symbols C) n :=
  .family (.fibre arrow) (singletonArgument argument)

def fibreContext (arrow : ArrowSymbol C) : ContextExpr (symbols C) 2 :=
  .snoc (objectContext arrow.target) (fibreType arrow (.var 0))

def signature (C : Type u) [Category.{u} C] : Signature (symbols C) where
  typeRank := fun symbol => match symbol with
    | .object _ => 0
    | .fibre _ => 1
  termRank := fun _ => 2
  predicateRank := fun _ => 2
  typeParameters := fun symbol => match symbol with
    | .object _ => .nil
    | .fibre arrow => objectContext arrow.target
  termParameters := fun symbol => match symbol with
    | .ordinary arrow => objectContext arrow.source
    | .forget arrow => fibreContext arrow
  predicateParameters := fun symbol => objectContext symbol.domain
  termResult := fun symbol => match symbol with
    | .ordinary arrow => objectType arrow.target 1
    | .forget arrow => objectType arrow.source 2
  typeParameters_before := by
    intro symbol
    cases symbol with
    | object => exact True.intro
    | fibre => exact ⟨True.intro, Nat.zero_lt_succ 0, fun position => Fin.elim0 position⟩
  termParameters_before := by
    intro symbol
    cases symbol with
    | ordinary => exact ⟨True.intro, Nat.zero_lt_succ 1, fun position => Fin.elim0 position⟩
    | forget => exact ⟨⟨True.intro, Nat.zero_lt_succ 1, fun position => Fin.elim0 position⟩,
        Nat.lt_succ_self 1, fun position => by
          cases position using Fin.cases with
          | zero => exact True.intro
          | succ impossible => exact Fin.elim0 impossible⟩
  predicateParameters_before := by
    intro symbol
    exact ⟨True.intro, Nat.zero_lt_succ 1, fun position => Fin.elim0 position⟩
  termResult_before := by
    intro symbol
    cases symbol <;> exact ⟨Nat.zero_lt_succ 1, fun position => Fin.elim0 position⟩

@[simp] theorem objectType_rename (object : C) {n m : Nat} (mapping : Renaming n m) :
    (objectType object n).rename mapping = objectType object m := by
  apply congrArg (TypeExpr.family (S := symbols C) (.object object))
  funext position
  exact Fin.elim0 position

@[simp] theorem objectType_substitute (object : C) {n m : Nat}
    (substitution : Substitution (symbols C) n m) :
    (objectType object n).substitute substitution = objectType object m := by
  apply congrArg (TypeExpr.family (S := symbols C) (.object object))
  funext position
  exact Fin.elim0 position

def emptyFormed : Derivation (signature C) (.context .nil) :=
  deriveList .contextNil .nil

def objectFormed (object : C) {n : Nat} {context : ContextExpr (symbols C) n}
    (formed : Derivation (signature C) (.context context)) :
    Derivation (signature C) (.type context (objectType object n)) :=
  deriveList (.typeFamily context (.object object) Fin.elim0)
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
  exact deriveList_before (.typeFamily context (.object object) Fin.elim0) _ bound
    ⟨contextOrder, positive, fun position => Fin.elim0 position⟩
    ⟨ordered, emptyFormed_before bound, emptySubstitutionOrder, True.intro⟩

theorem objectContextFormed_before (object : C) (bound : Nat) (positive : 0 < bound) :
    (objectContextFormed object).before bound :=
  deriveList_before (.contextExtend .nil (objectType object 0)) _ bound
    ⟨True.intro, positive, fun position => Fin.elim0 position⟩
    ⟨emptyFormed_before bound,
      objectFormed_before object emptyFormed bound (emptyFormed_before bound) positive, True.intro⟩

def objectArguments (object : C) {n : Nat} {context : ContextExpr (symbols C) n}
    {value : TermExpr (symbols C) n} (formed : Derivation (signature C) (.context context))
    (typed : Derivation (signature C) (.term context value (objectType object n))) :
    Derivation (signature C) (.substitution context (objectContext object) (singletonArgument value)) := by
  have valueTree : Derivation (signature C)
      (.term context value ((objectType object 0).substitute Fin.elim0)) := by
    exact (congrArg (Judgment.term context value)
      (objectType_substitute object (Fin.elim0 : Substitution (symbols C) 0 n))).symm ▸ typed
  exact deriveList (.substitutionExtend context .nil (objectType object 0) Fin.elim0 value)
    (.cons (deriveList (.substitutionNil context) (.cons formed .nil))
      (.cons (objectFormed object emptyFormed) (.cons valueTree .nil)))

def variableFormed (object : C) :
    Derivation (signature C) (.term (objectContext object) (.var 0) (objectType object 1)) := by
  have equal :
      (.term (objectContext object) (.var 0) ((objectContext object).lookup 0) :
        Judgment (symbols C)) = .term (objectContext object) (.var 0) (objectType object 1) := by
    simp only [objectContext, ContextExpr.lookup_zero, objectType_rename]
  exact equal ▸
    deriveList (.variable (objectContext object) 0) (.cons (objectContextFormed object) .nil)

@[simp] theorem before_cast {first second : Judgment (symbols C)}
    (equal : first = second) (tree : Derivation (signature C) first) (bound : Nat) :
    (equal ▸ tree).before bound ↔ tree.before bound := by
  cases equal
  rfl

def genericFibreFormed (arrow : ArrowSymbol C) :
    Derivation (signature C) (.type (objectContext arrow.target) (fibreType arrow (.var 0))) :=
  deriveList (.typeFamily (objectContext arrow.target) (.fibre arrow) (singletonArgument (.var 0)))
    (.cons (objectContextFormed arrow.target) (.cons (objectContextFormed arrow.target)
      (.cons (objectArguments arrow.target (objectContextFormed arrow.target)
        (variableFormed arrow.target)) .nil)))

def fibreContextFormed (arrow : ArrowSymbol C) :
    Derivation (signature C) (.context (fibreContext arrow)) :=
  deriveList (.contextExtend (objectContext arrow.target) (fibreType arrow (.var 0)))
    (.cons (objectContextFormed arrow.target) (.cons (genericFibreFormed arrow) .nil))

theorem variableFormed_before (object : C) (bound : Nat) (positive : 0 < bound) :
    (variableFormed object).before bound := by
  have treeOrder := deriveList_before (.variable (objectContext object) 0)
    (.cons (objectContextFormed object) .nil) bound
    (show (RuleCode.variable (D := signature C) (objectContext object) 0).conclusion.before
      (signature C) bound from
      ⟨⟨True.intro, positive, fun position => Fin.elim0 position⟩,
        True.intro, positive, fun position => Fin.elim0 position⟩)
    ⟨objectContextFormed_before object bound positive, True.intro⟩
  have equal :
      (.term (objectContext object) (.var 0) ((objectContext object).lookup 0) :
        Judgment (symbols C)) = .term (objectContext object) (.var 0) (objectType object 1) := by
    simp only [objectContext, ContextExpr.lookup_zero, objectType_rename]
  exact (before_cast equal
    (deriveList (.variable (objectContext object) 0) (.cons (objectContextFormed object) .nil)) bound).mpr
    treeOrder

theorem genericFibreFormed_before (arrow : ArrowSymbol C) (bound : Nat) (positive : 1 < bound) :
    (genericFibreFormed arrow).before bound := by
  have zeroPositive : 0 < bound := Nat.lt_trans (Nat.zero_lt_succ 0) positive
  have objectOrder := objectContextFormed_before arrow.target bound zeroPositive
  have emptyOrder := emptyFormed_before (C := C) bound
  have argumentOrder :
      (objectArguments arrow.target (objectContextFormed arrow.target)
        (variableFormed arrow.target)).before bound := by
    unfold objectArguments
    exact deriveList_before
      (.substitutionExtend (objectContext arrow.target) .nil (objectType arrow.target 0)
        Fin.elim0 (.var 0)) _ bound
      ⟨⟨True.intro, zeroPositive, fun p => Fin.elim0 p⟩,
        ⟨True.intro, zeroPositive, fun p => Fin.elim0 p⟩,
        fun p => by
          cases p using Fin.cases with
          | zero => exact True.intro
          | succ impossible => exact Fin.elim0 impossible⟩
      ⟨deriveList_before (.substitutionNil (objectContext arrow.target)) _ bound
          ⟨⟨True.intro, zeroPositive, fun p => Fin.elim0 p⟩,
            True.intro, fun p => Fin.elim0 p⟩ ⟨objectOrder, True.intro⟩,
        objectFormed_before arrow.target emptyFormed bound emptyOrder zeroPositive,
        by simpa only [before_cast] using variableFormed_before arrow.target bound zeroPositive,
        True.intro⟩
  exact deriveList_before
    (.typeFamily (objectContext arrow.target) (.fibre arrow) (singletonArgument (.var 0))) _ bound
    ⟨⟨True.intro, zeroPositive, fun p => Fin.elim0 p⟩,
      positive, fun p => by
        cases p using Fin.cases with
        | zero => exact True.intro
        | succ impossible => exact Fin.elim0 impossible⟩
    ⟨objectOrder, objectOrder, argumentOrder, True.intro⟩

theorem fibreContextFormed_before (arrow : ArrowSymbol C) (bound : Nat) (positive : 1 < bound) :
    (fibreContextFormed arrow).before bound :=
  deriveList_before (.contextExtend (objectContext arrow.target) (fibreType arrow (.var 0))) _ bound
    ⟨⟨True.intro, Nat.lt_trans (Nat.zero_lt_succ 0) positive, fun p => Fin.elim0 p⟩,
      positive, fun p => by
        cases p using Fin.cases with
        | zero => exact True.intro
        | succ impossible => exact Fin.elim0 impossible⟩
    ⟨objectContextFormed_before arrow.target bound (Nat.lt_trans (Nat.zero_lt_succ 0) positive),
      genericFibreFormed_before arrow bound positive, True.intro⟩

def headers (C : Type u) [Category.{u} C] : HeaderFormation (signature C) where
  typeHeader := fun symbol => match symbol with
    | .object _ => emptyFormed
    | .fibre arrow => objectContextFormed arrow.target
  typeHeader_before := by
    intro symbol
    cases symbol with
    | object => exact emptyFormed_before 0
    | fibre arrow => exact objectContextFormed_before arrow.target 1 (by decide)
  termHeader := fun symbol => match symbol with
    | .ordinary arrow => objectContextFormed arrow.source
    | .forget arrow => fibreContextFormed arrow
  termHeader_before := by
    intro symbol
    cases symbol with
    | ordinary arrow => exact objectContextFormed_before arrow.source 2 (by decide)
    | forget arrow => exact fibreContextFormed_before arrow 2 (by decide)
  termResult := fun symbol => match symbol with
    | .ordinary arrow => objectFormed arrow.target (objectContextFormed arrow.source)
    | .forget arrow => objectFormed arrow.source (fibreContextFormed arrow)
  termResult_before := by
    intro symbol
    cases symbol with
    | ordinary arrow =>
      exact objectFormed_before arrow.target _ 2
        (objectContextFormed_before arrow.source 2 (by decide)) (by decide)
    | forget arrow =>
      exact objectFormed_before arrow.source _ 2
        (fibreContextFormed_before arrow 2 (by decide)) (by decide)
  predicateHeader := fun symbol => objectContextFormed symbol.domain
  predicateHeader_before := fun symbol => objectContextFormed_before symbol.domain 2 (by decide)

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.RepresentableIndexedDeclarations
