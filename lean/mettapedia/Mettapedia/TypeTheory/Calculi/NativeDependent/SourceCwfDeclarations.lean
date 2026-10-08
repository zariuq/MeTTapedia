import Mettapedia.TypeTheory.Calculi.NativeDependent.RepresentableDeclarations
import Mettapedia.TypeTheory.CwfYonedaCoherence

/-!
# Generated declarations of an arbitrary source CwF

Source contexts, dependent types, substitutions and terms have independently
formed declarations. A source term's result is the dependent type over its
actual source context, rather than merely the object of its comprehension.
The source substitution universe is the context universe; type and term
universes remain independent. Interpretation and its universal properties
are separate from this raw judgment presentation.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.SourceCwfDeclarations

open _root_.CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder

universe u w w'
variable (K : Cwf.{u, u, w, w'})

abbrev Base := K.base.Context
abbrev ArrowSymbol := RepresentableDeclarations.ArrowSymbol (Base K)
abbrev PredicateSymbol := ULift.{max u w w'} (RepresentableDeclarations.PredicateSymbol (Base K))

inductive TypeSymbol : Type (max u w w') where
  | object : Base K → TypeSymbol
  | source {context : K.Ctx} : K.Ty context → TypeSymbol

inductive TermSymbol : Type (max u w w') where
  | ordinary : ArrowSymbol K → TermSymbol
  | source {context : K.Ctx} {type : K.Ty context} : K.Tm context type → TermSymbol
  | forget {context : K.Ctx} : K.Ty context → TermSymbol

def symbols : Symbols where
  TypeSymbol := TypeSymbol K
  TermSymbol := TermSymbol K
  PredicateSymbol := PredicateSymbol K
  typeArity := fun symbol => match symbol with
    | .object _ => 0
    | .source _ => 1
  termArity := fun symbol => match symbol with
    | .ordinary _ => 1
    | .source _ => 1
    | .forget _ => 2
  predicateArity := fun _ => 1

variable {K}

def objectType (object : Base K) (n : Nat) : TypeExpr (symbols K) n :=
  .family (.object object) Fin.elim0

def objectContext (object : Base K) : ContextExpr (symbols K) 1 :=
  .snoc .nil (objectType object 0)

def singletonArgument {n : Nat} (value : TermExpr (symbols K) n) :
    Substitution (symbols K) 1 n := extendSubstitution Fin.elim0 value

def sourceType {context : K.Ctx} (type : K.Ty context) {n : Nat}
    (argument : TermExpr (symbols K) n) : TypeExpr (symbols K) n :=
  .family (.source type) (singletonArgument argument)

def sourceContext {context : K.Ctx} (type : K.Ty context) : ContextExpr (symbols K) 2 :=
  .snoc (objectContext (⟨context⟩ : Base K)) (sourceType type (.var 0))

def signature (K : Cwf.{u, u, w, w'}) : Signature (symbols K) where
  typeRank := fun symbol => match symbol with
    | .object _ => 0
    | .source _ => 1
  termRank := fun _ => 2
  predicateRank := fun _ => 2
  typeParameters := fun symbol => match symbol with
    | .object _ => .nil
    | .source (context := context) _ => objectContext (⟨context⟩ : Base K)
  termParameters := fun symbol => match symbol with
    | .ordinary arrow => objectContext arrow.source
    | .source (context := context) _ => objectContext (⟨context⟩ : Base K)
    | .forget type => sourceContext type
  predicateParameters := fun symbol => objectContext symbol.down.domain
  termResult := fun symbol => match symbol with
    | .ordinary arrow => objectType arrow.target 1
    | .source (type := type) _ => sourceType type (.var (0 : Fin 1))
    | .forget (context := context) type => objectType (⟨K.ext context type⟩ : Base K) 2
  typeParameters_before := by
    intro symbol
    cases symbol with
    | object => exact True.intro
    | source => exact ⟨True.intro, Nat.zero_lt_succ 0, fun position => Fin.elim0 position⟩
  termParameters_before := by
    intro symbol
    cases symbol with
    | ordinary => exact ⟨True.intro, Nat.zero_lt_succ 1, fun position => Fin.elim0 position⟩
    | source => exact ⟨True.intro, Nat.zero_lt_succ 1, fun position => Fin.elim0 position⟩
    | forget => exact ⟨⟨True.intro, Nat.zero_lt_succ 1, fun position => Fin.elim0 position⟩,
        Nat.lt_succ_self 1, fun position => by
          cases position using Fin.cases with
          | zero => exact True.intro
          | succ impossible => exact Fin.elim0 impossible⟩
  predicateParameters_before := fun _ =>
    ⟨True.intro, Nat.zero_lt_succ 1, fun position => Fin.elim0 position⟩
  termResult_before := by
    intro symbol
    cases symbol with
    | ordinary => exact ⟨Nat.zero_lt_succ 1, fun position => Fin.elim0 position⟩
    | source => exact ⟨Nat.lt_succ_self 1, fun position => by
        cases position using Fin.cases with
        | zero => exact True.intro
        | succ impossible => exact Fin.elim0 impossible⟩
    | forget => exact ⟨Nat.zero_lt_succ 1, fun position => Fin.elim0 position⟩

@[simp] theorem objectType_rename (object : Base K) {n m : Nat} (mapping : Renaming n m) :
    (objectType object n).rename mapping = objectType object m := by
  apply congrArg (TypeExpr.family (S := symbols K) (.object object))
  funext position
  exact Fin.elim0 position

@[simp] theorem objectType_substitute (object : Base K) {n m : Nat}
    (substitution : Substitution (symbols K) n m) :
    (objectType object n).substitute substitution = objectType object m := by
  apply congrArg (TypeExpr.family (S := symbols K) (.object object))
  funext position
  exact Fin.elim0 position

def emptyFormed : Derivation (signature K) (.context .nil) :=
  deriveList .contextNil .nil

def objectFormed (object : Base K) {n : Nat} {context : ContextExpr (symbols K) n}
    (formed : Derivation (signature K) (.context context)) :
    Derivation (signature K) (.type context (objectType object n)) :=
  deriveList (.typeFamily context (.object object) Fin.elim0)
    (.cons formed (.cons emptyFormed
      (.cons (deriveList (.substitutionNil context) (.cons formed .nil)) .nil)))

def objectContextFormed (object : Base K) :
    Derivation (signature K) (.context (objectContext object)) :=
  deriveList (.contextExtend .nil (objectType object 0))
    (.cons emptyFormed (.cons (objectFormed object emptyFormed) .nil))

theorem emptyFormed_before (bound : Nat) :
    (emptyFormed (K := K)).before bound :=
  deriveList_before .contextNil .nil bound True.intro True.intro

theorem objectFormed_before (object : Base K) {n : Nat} {context : ContextExpr (symbols K) n}
    (formed : Derivation (signature K) (.context context)) (bound : Nat)
    (ordered : formed.before bound) (positive : 0 < bound) :
    (objectFormed object formed).before bound := by
  have contextOrder := formed.before_judgment ordered
  have substitutionOrder := deriveList_before (.substitutionNil context) (.cons formed .nil) bound
    ⟨contextOrder, True.intro, fun position => Fin.elim0 position⟩ ⟨ordered, True.intro⟩
  exact deriveList_before (.typeFamily context (.object object) Fin.elim0) _ bound
    ⟨contextOrder, positive, fun position => Fin.elim0 position⟩
    ⟨ordered, emptyFormed_before bound, substitutionOrder, True.intro⟩

theorem objectContextFormed_before (object : Base K) (bound : Nat) (positive : 0 < bound) :
    (objectContextFormed object).before bound :=
  deriveList_before (.contextExtend .nil (objectType object 0)) _ bound
    ⟨True.intro, positive, fun position => Fin.elim0 position⟩
    ⟨emptyFormed_before bound,
      objectFormed_before object emptyFormed bound (emptyFormed_before bound) positive, True.intro⟩

def objectArguments (object : Base K) {n : Nat} {context : ContextExpr (symbols K) n}
    {value : TermExpr (symbols K) n} (formed : Derivation (signature K) (.context context))
    (typed : Derivation (signature K) (.term context value (objectType object n))) :
    Derivation (signature K) (.substitution context (objectContext object) (singletonArgument value)) := by
  have valueTree : Derivation (signature K)
      (.term context value ((objectType object 0).substitute Fin.elim0)) := by
    exact (congrArg (Judgment.term context value)
      (objectType_substitute object (Fin.elim0 : Substitution (symbols K) 0 n))).symm ▸ typed
  exact deriveList (.substitutionExtend context .nil (objectType object 0) Fin.elim0 value)
    (.cons (deriveList (.substitutionNil context) (.cons formed .nil))
      (.cons (objectFormed object emptyFormed) (.cons valueTree .nil)))

def variableFormed (object : Base K) :
    Derivation (signature K) (.term (objectContext object) (.var 0) (objectType object 1)) := by
  have equal :
      (.term (objectContext object) (.var 0) ((objectContext object).lookup 0) :
        Judgment (symbols K)) = .term (objectContext object) (.var 0) (objectType object 1) := by
    simp only [objectContext, ContextExpr.lookup_zero, objectType_rename]
  exact equal ▸ deriveList (.variable (objectContext object) 0)
    (.cons (objectContextFormed object) .nil)

def sourceTypeFormed {context : K.Ctx} (type : K.Ty context) :
    Derivation (signature K) (.type (objectContext (⟨context⟩ : Base K)) (sourceType type (.var 0))) :=
  deriveList (.typeFamily (objectContext (⟨context⟩ : Base K)) (.source type)
    (singletonArgument (.var 0)))
    (.cons (objectContextFormed _) (.cons (objectContextFormed _)
      (.cons (objectArguments _ (objectContextFormed _) (variableFormed _)) .nil)))

def sourceContextFormed {context : K.Ctx} (type : K.Ty context) :
    Derivation (signature K) (.context (sourceContext type)) :=
  deriveList (.contextExtend (objectContext (⟨context⟩ : Base K)) (sourceType type (.var 0)))
    (.cons (objectContextFormed _) (.cons (sourceTypeFormed type) .nil))

@[simp] theorem before_cast {first second : Judgment (symbols K)}
    (equal : first = second) (tree : Derivation (signature K) first) (bound : Nat) :
    (equal ▸ tree).before bound ↔ tree.before bound := by cases equal; rfl

theorem variableFormed_before (object : Base K) (bound : Nat) (positive : 0 < bound) :
    (variableFormed object).before bound := by
  have order := deriveList_before (.variable (objectContext object) 0)
    (.cons (objectContextFormed object) .nil) bound
    (show (RuleCode.variable (D := signature K) (objectContext object) 0).conclusion.before
      (signature K) bound from
      ⟨⟨True.intro, positive, fun p => Fin.elim0 p⟩, True.intro, positive, fun p => Fin.elim0 p⟩)
    ⟨objectContextFormed_before object bound positive, True.intro⟩
  unfold variableFormed
  exact (before_cast _ _ bound).mpr order

theorem sourceTypeFormed_before {context : K.Ctx} (type : K.Ty context)
    (bound : Nat) (positive : 1 < bound) : (sourceTypeFormed type).before bound := by
  have zeroPositive : 0 < bound := Nat.lt_trans (Nat.zero_lt_succ 0) positive
  have objectOrder := objectContextFormed_before (⟨context⟩ : Base K) bound zeroPositive
  have argumentOrder :
      (objectArguments (⟨context⟩ : Base K) (objectContextFormed _) (variableFormed _)).before bound := by
    unfold objectArguments
    exact deriveList_before
      (.substitutionExtend (objectContext (⟨context⟩ : Base K)) .nil
        (objectType (⟨context⟩ : Base K) 0) Fin.elim0 (.var 0)) _ bound
      ⟨⟨True.intro, zeroPositive, fun p => Fin.elim0 p⟩,
        ⟨True.intro, zeroPositive, fun p => Fin.elim0 p⟩,
        fun p => by cases p using Fin.cases with
          | zero => exact True.intro
          | succ impossible => exact Fin.elim0 impossible⟩
      ⟨deriveList_before (.substitutionNil (objectContext (⟨context⟩ : Base K))) _ bound
          ⟨⟨True.intro, zeroPositive, fun p => Fin.elim0 p⟩, True.intro, fun p => Fin.elim0 p⟩
          ⟨objectOrder, True.intro⟩,
        objectFormed_before _ emptyFormed bound (emptyFormed_before bound) zeroPositive,
        by simpa only [before_cast] using variableFormed_before (⟨context⟩ : Base K) bound zeroPositive,
        True.intro⟩
  exact deriveList_before (.typeFamily (objectContext (⟨context⟩ : Base K))
    (.source type) (singletonArgument (.var 0))) _ bound
    ⟨⟨True.intro, zeroPositive, fun p => Fin.elim0 p⟩,
      positive, fun p => by cases p using Fin.cases with
        | zero => exact True.intro
        | succ impossible => exact Fin.elim0 impossible⟩
    ⟨objectOrder, objectOrder, argumentOrder, True.intro⟩

theorem sourceContextFormed_before {context : K.Ctx} (type : K.Ty context)
    (bound : Nat) (positive : 1 < bound) : (sourceContextFormed type).before bound :=
  deriveList_before (.contextExtend (objectContext (⟨context⟩ : Base K)) (sourceType type (.var 0))) _ bound
    ⟨⟨True.intro, Nat.lt_trans (Nat.zero_lt_succ 0) positive, fun p => Fin.elim0 p⟩,
      positive, fun p => by cases p using Fin.cases with
        | zero => exact True.intro
        | succ impossible => exact Fin.elim0 impossible⟩
    ⟨objectContextFormed_before _ bound (Nat.lt_trans (Nat.zero_lt_succ 0) positive),
      sourceTypeFormed_before type bound positive, True.intro⟩

def headers (K : Cwf.{u, u, w, w'}) : HeaderFormation (signature K) where
  typeHeader := fun symbol => match symbol with
    | .object _ => emptyFormed
    | .source (context := context) _ => objectContextFormed (⟨context⟩ : Base K)
  typeHeader_before := by
    intro symbol
    cases symbol with
    | object => exact emptyFormed_before 0
    | source => exact objectContextFormed_before _ 1 (by decide)
  termHeader := fun symbol => match symbol with
    | .ordinary arrow => objectContextFormed arrow.source
    | .source (context := context) _ => objectContextFormed (⟨context⟩ : Base K)
    | .forget type => sourceContextFormed type
  termHeader_before := by
    intro symbol
    cases symbol with
    | ordinary => exact objectContextFormed_before _ 2 (by decide)
    | source => exact objectContextFormed_before _ 2 (by decide)
    | forget type => exact sourceContextFormed_before type 2 (by decide)
  termResult := fun symbol => match symbol with
    | .ordinary arrow => objectFormed arrow.target (objectContextFormed arrow.source)
    | .source (type := type) _ => sourceTypeFormed type
    | .forget (context := context) type => objectFormed (⟨K.ext context type⟩ : Base K)
        (sourceContextFormed type)
  termResult_before := by
    intro symbol
    cases symbol with
    | ordinary arrow => exact objectFormed_before _ _ 2 (objectContextFormed_before _ 2 (by decide)) (by decide)
    | source => exact sourceTypeFormed_before _ 2 (by decide)
    | forget type => exact objectFormed_before _ _ 2 (sourceContextFormed_before type 2 (by decide)) (by decide)
  predicateHeader := fun symbol => objectContextFormed symbol.down.domain
  predicateHeader_before := fun symbol => objectContextFormed_before symbol.down.domain 2 (by decide)

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.SourceCwfDeclarations
