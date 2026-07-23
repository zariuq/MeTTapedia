import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Pairing
import Mathlib.Order.Basic
import Mettapedia.OSLF.MeTTaIL.Syntax

/-!
# Collision-free structural ordering for MeTTaIL patterns

This module supplies a computable, injective structural code for the shared
`Pattern` carrier.  It is independent of any object language: derived
equational compilers can use the same deterministic ordering without placing
language-specific callbacks in the generic engine.
-/

namespace Mettapedia.OSLF.MeTTaIL.PatternCode

open Mettapedia.OSLF.MeTTaIL.Syntax

def charListCode : List Char → Nat
  | [] => 0
  | c :: cs => Nat.succ (Nat.pair c.toNat (charListCode cs))

def stringCode (value : String) : Nat :=
  charListCode value.toList

def stringListCode : List String → Nat
  | [] => 0
  | value :: values => Nat.succ (Nat.pair (stringCode value) (stringListCode values))

def optionStringCode : Option String → Nat
  | none => Nat.pair 0 0
  | some value => Nat.pair 1 (stringCode value)

def collectionCode : CollType → Nat
  | .vec => 0
  | .hashBag => 1
  | .hashSet => 2

/-- Collision-free structural code for an authored type expression. -/
def typeExprCode : TypeExpr → Nat
  | .base name => Nat.pair 0 (stringCode name)
  | .arrow domain codomain =>
      Nat.pair 1 (Nat.pair (typeExprCode domain) (typeExprCode codomain))
  | .multiBinder body => Nat.pair 2 (typeExprCode body)
  | .collection collectionType element =>
      Nat.pair 3
        (Nat.pair (collectionCode collectionType) (typeExprCode element))

/-- Collision-free code for an ordered binder context. -/
def typeExprListCode : List TypeExpr → Nat
  | [] => 0
  | type :: types =>
      Nat.succ (Nat.pair (typeExprCode type) (typeExprListCode types))

mutual
  /-- Structural Gödel numbering for the shared `Pattern` carrier. -/
  def patternCode : Pattern → Nat
    | .bvar index => Nat.pair 0 index
    | .fvar name => Nat.pair 1 (stringCode name)
    | .apply constructor arguments =>
        Nat.pair 2 (Nat.pair (stringCode constructor) (patternListCode arguments))
    | .lambda binderName body =>
        Nat.pair 3 (Nat.pair (optionStringCode binderName) (patternCode body))
    | .multiLambda arity binderNames body =>
        Nat.pair 4
          (Nat.pair arity (Nat.pair (stringListCode binderNames) (patternCode body)))
    | .subst body replacement =>
        Nat.pair 5 (Nat.pair (patternCode body) (patternCode replacement))
    | .collection collectionType elements rest =>
        Nat.pair 6
          (Nat.pair (collectionCode collectionType)
            (Nat.pair (patternListCode elements) (optionStringCode rest)))

  def patternListCode : List Pattern → Nat
    | [] => 0
    | pattern :: patterns =>
        Nat.succ (Nat.pair (patternCode pattern) (patternListCode patterns))
end

theorem charListCode_injective : Function.Injective charListCode := by
  intro left
  induction left with
  | nil =>
      intro right equality
      cases right with
      | nil => rfl
      | cons head tail => simp [charListCode] at equality
  | cons head tail inductionHypothesis =>
      intro right equality
      cases right with
      | nil => simp [charListCode] at equality
      | cons otherHead otherTail =>
          simp only [charListCode, Nat.succ.injEq, Nat.pair_eq_pair] at equality
          have headEquality : head = otherHead := Char.toNat_inj.mp equality.1
          have tailEquality : tail = otherTail := inductionHypothesis equality.2
          exact congrArg₂ List.cons headEquality tailEquality

theorem stringCode_injective : Function.Injective stringCode := by
  intro left right equality
  have listEquality : left.toList = right.toList :=
    charListCode_injective equality
  exact String.toList_inj.mp listEquality

theorem stringListCode_injective : Function.Injective stringListCode := by
  intro left
  induction left with
  | nil =>
      intro right equality
      cases right with
      | nil => rfl
      | cons head tail => simp [stringListCode] at equality
  | cons head tail inductionHypothesis =>
      intro right equality
      cases right with
      | nil => simp [stringListCode] at equality
      | cons otherHead otherTail =>
          simp only [stringListCode, Nat.succ.injEq, Nat.pair_eq_pair] at equality
          have headEquality : head = otherHead := stringCode_injective equality.1
          have tailEquality : tail = otherTail := inductionHypothesis equality.2
          exact congrArg₂ List.cons headEquality tailEquality

theorem optionStringCode_injective : Function.Injective optionStringCode := by
  intro left right equality
  cases left <;> cases right <;>
    simp_all [optionStringCode, Nat.pair_eq_pair, stringCode_injective.eq_iff]

theorem collectionCode_injective : Function.Injective collectionCode := by
  intro left right equality
  cases left <;> cases right <;> simp_all [collectionCode]

/-- `typeExprCode` distinguishes every authored type expression. -/
theorem typeExprCode_injective : Function.Injective typeExprCode := by
  intro left
  induction left with
  | base name =>
      intro right equality
      cases right with
      | base otherName =>
          simp only [typeExprCode, Nat.pair_eq_pair] at equality
          exact congrArg TypeExpr.base (stringCode_injective equality.2)
      | arrow _ _ => simp [typeExprCode, Nat.pair_eq_pair] at equality
      | multiBinder _ => simp [typeExprCode, Nat.pair_eq_pair] at equality
      | collection _ _ => simp [typeExprCode, Nat.pair_eq_pair] at equality
  | arrow domain codomain domainInduction codomainInduction =>
      intro right equality
      cases right with
      | base _ => simp [typeExprCode, Nat.pair_eq_pair] at equality
      | arrow otherDomain otherCodomain =>
          simp only [typeExprCode, Nat.pair_eq_pair] at equality
          exact congrArg₂ TypeExpr.arrow
            (domainInduction equality.2.1)
            (codomainInduction equality.2.2)
      | multiBinder _ => simp [typeExprCode, Nat.pair_eq_pair] at equality
      | collection _ _ => simp [typeExprCode, Nat.pair_eq_pair] at equality
  | multiBinder body inductionHypothesis =>
      intro right equality
      cases right with
      | base _ => simp [typeExprCode, Nat.pair_eq_pair] at equality
      | arrow _ _ => simp [typeExprCode, Nat.pair_eq_pair] at equality
      | multiBinder otherBody =>
          simp only [typeExprCode, Nat.pair_eq_pair] at equality
          exact congrArg TypeExpr.multiBinder
            (inductionHypothesis equality.2)
      | collection _ _ => simp [typeExprCode, Nat.pair_eq_pair] at equality
  | collection collectionType element inductionHypothesis =>
      intro right equality
      cases right with
      | base _ => simp [typeExprCode, Nat.pair_eq_pair] at equality
      | arrow _ _ => simp [typeExprCode, Nat.pair_eq_pair] at equality
      | multiBinder _ => simp [typeExprCode, Nat.pair_eq_pair] at equality
      | collection otherCollectionType otherElement =>
          simp only [typeExprCode, Nat.pair_eq_pair] at equality
          exact congrArg₂ TypeExpr.collection
            (collectionCode_injective equality.2.1)
            (inductionHypothesis equality.2.2)

/-- `typeExprListCode` distinguishes ordered binder contexts. -/
theorem typeExprListCode_injective : Function.Injective typeExprListCode := by
  intro left
  induction left with
  | nil =>
      intro right equality
      cases right with
      | nil => rfl
      | cons head tail => simp [typeExprListCode] at equality
  | cons head tail inductionHypothesis =>
      intro right equality
      cases right with
      | nil => simp [typeExprListCode] at equality
      | cons otherHead otherTail =>
          simp only [typeExprListCode, Nat.succ.injEq, Nat.pair_eq_pair]
            at equality
          exact congrArg₂ List.cons
            (typeExprCode_injective equality.1)
            (inductionHypothesis equality.2)

private theorem patternListCode_eq_imp
    {left right : List Pattern}
    (elementInjective :
      ∀ pattern ∈ left, ∀ other, patternCode pattern = patternCode other → pattern = other)
    (equality : patternListCode left = patternListCode right) :
    left = right := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => rfl
      | cons head tail => simp [patternListCode] at equality
  | cons head tail inductionHypothesis =>
      cases right with
      | nil => simp [patternListCode] at equality
      | cons otherHead otherTail =>
          simp only [patternListCode, Nat.succ.injEq, Nat.pair_eq_pair] at equality
          have headEquality : head = otherHead :=
            elementInjective head (by simp) otherHead equality.1
          have tailEquality : tail = otherTail := by
            apply inductionHypothesis
            · intro pattern membership other codeEquality
              exact elementInjective pattern (by simp [membership]) other codeEquality
            · exact equality.2
          exact congrArg₂ List.cons headEquality tailEquality

/-- `patternCode` is collision-free. -/
theorem patternCode_injective : Function.Injective patternCode := by
  intro pattern
  induction pattern using Pattern.inductionOn with
  | hbvar index =>
      intro other equality
      cases other <;> simp_all [patternCode, Nat.pair_eq_pair]
  | hfvar name =>
      intro other equality
      cases other with
      | fvar otherName =>
          simp only [patternCode, Nat.pair_eq_pair] at equality
          exact congrArg Pattern.fvar (stringCode_injective equality.2)
      | bvar _ => simp [patternCode, Nat.pair_eq_pair] at equality
      | apply _ _ => simp [patternCode, Nat.pair_eq_pair] at equality
      | lambda _ _ => simp [patternCode, Nat.pair_eq_pair] at equality
      | multiLambda _ _ _ => simp [patternCode, Nat.pair_eq_pair] at equality
      | subst _ _ => simp [patternCode, Nat.pair_eq_pair] at equality
      | collection _ _ _ => simp [patternCode, Nat.pair_eq_pair] at equality
  | happly constructor arguments inductionHypothesis =>
      intro other equality
      cases other with
      | apply otherConstructor otherArguments =>
          simp only [patternCode, Nat.pair_eq_pair] at equality
          have constructorEquality : constructor = otherConstructor :=
            stringCode_injective equality.2.1
          have argumentsEquality : arguments = otherArguments :=
            patternListCode_eq_imp inductionHypothesis equality.2.2
          exact congrArg₂ Pattern.apply constructorEquality argumentsEquality
      | bvar _ => simp [patternCode, Nat.pair_eq_pair] at equality
      | fvar _ => simp [patternCode, Nat.pair_eq_pair] at equality
      | lambda _ _ => simp [patternCode, Nat.pair_eq_pair] at equality
      | multiLambda _ _ _ => simp [patternCode, Nat.pair_eq_pair] at equality
      | subst _ _ => simp [patternCode, Nat.pair_eq_pair] at equality
      | collection _ _ _ => simp [patternCode, Nat.pair_eq_pair] at equality
  | hlambda binderName body inductionHypothesis =>
      intro other equality
      cases other with
      | lambda otherBinderName otherBody =>
          simp only [patternCode, Nat.pair_eq_pair] at equality
          have binderEquality : binderName = otherBinderName :=
            optionStringCode_injective equality.2.1
          have bodyEquality : body = otherBody := inductionHypothesis equality.2.2
          exact congrArg₂ Pattern.lambda binderEquality bodyEquality
      | bvar _ => simp [patternCode, Nat.pair_eq_pair] at equality
      | fvar _ => simp [patternCode, Nat.pair_eq_pair] at equality
      | apply _ _ => simp [patternCode, Nat.pair_eq_pair] at equality
      | multiLambda _ _ _ => simp [patternCode, Nat.pair_eq_pair] at equality
      | subst _ _ => simp [patternCode, Nat.pair_eq_pair] at equality
      | collection _ _ _ => simp [patternCode, Nat.pair_eq_pair] at equality
  | hmultiLambda arity binderNames body inductionHypothesis =>
      intro other equality
      cases other with
      | multiLambda otherArity otherBinderNames otherBody =>
          simp only [patternCode, Nat.pair_eq_pair] at equality
          have arityEquality : arity = otherArity := equality.2.1
          have binderNamesEquality : binderNames = otherBinderNames :=
            stringListCode_injective equality.2.2.1
          have bodyEquality : body = otherBody := inductionHypothesis equality.2.2.2
          cases arityEquality
          cases binderNamesEquality
          cases bodyEquality
          rfl
      | bvar _ => simp [patternCode, Nat.pair_eq_pair] at equality
      | fvar _ => simp [patternCode, Nat.pair_eq_pair] at equality
      | apply _ _ => simp [patternCode, Nat.pair_eq_pair] at equality
      | lambda _ _ => simp [patternCode, Nat.pair_eq_pair] at equality
      | subst _ _ => simp [patternCode, Nat.pair_eq_pair] at equality
      | collection _ _ _ => simp [patternCode, Nat.pair_eq_pair] at equality
  | hsubst body replacement bodyInduction replacementInduction =>
      intro other equality
      cases other with
      | subst otherBody otherReplacement =>
          simp only [patternCode, Nat.pair_eq_pair] at equality
          have bodyEquality : body = otherBody := bodyInduction equality.2.1
          have replacementEquality : replacement = otherReplacement :=
            replacementInduction equality.2.2
          exact congrArg₂ Pattern.subst bodyEquality replacementEquality
      | bvar _ => simp [patternCode, Nat.pair_eq_pair] at equality
      | fvar _ => simp [patternCode, Nat.pair_eq_pair] at equality
      | apply _ _ => simp [patternCode, Nat.pair_eq_pair] at equality
      | lambda _ _ => simp [patternCode, Nat.pair_eq_pair] at equality
      | multiLambda _ _ _ => simp [patternCode, Nat.pair_eq_pair] at equality
      | collection _ _ _ => simp [patternCode, Nat.pair_eq_pair] at equality
  | hcollection collectionType elements rest inductionHypothesis =>
      intro other equality
      cases other with
      | collection otherCollectionType otherElements otherRest =>
          simp only [patternCode, Nat.pair_eq_pair] at equality
          have collectionTypeEquality : collectionType = otherCollectionType :=
            collectionCode_injective equality.2.1
          have elementsEquality : elements = otherElements :=
            patternListCode_eq_imp inductionHypothesis equality.2.2.1
          have restEquality : rest = otherRest :=
            optionStringCode_injective equality.2.2.2
          cases collectionTypeEquality
          cases elementsEquality
          cases restEquality
          rfl
      | bvar _ => simp [patternCode, Nat.pair_eq_pair] at equality
      | fvar _ => simp [patternCode, Nat.pair_eq_pair] at equality
      | apply _ _ => simp [patternCode, Nat.pair_eq_pair] at equality
      | lambda _ _ => simp [patternCode, Nat.pair_eq_pair] at equality
      | multiLambda _ _ _ => simp [patternCode, Nat.pair_eq_pair] at equality
      | subst _ _ => simp [patternCode, Nat.pair_eq_pair] at equality

@[reducible] def patternLinearOrder : LinearOrder Pattern :=
  LinearOrder.lift' patternCode patternCode_injective

/-- Deterministic sorting by the injective structural code. -/
def sortPatterns (patterns : List Pattern) : List Pattern :=
  patterns.mergeSort
    (fun left right => decide (patternCode left ≤ patternCode right))

/-- Sorting depends only on the presented multiset. -/
theorem sortPatterns_eq_of_perm {left right : List Pattern}
    (permutation : List.Perm left right) :
    sortPatterns left = sortPatterns right := by
  let relation : Pattern → Pattern → Prop :=
    fun first second => patternCode first ≤ patternCode second
  letI : Std.Total relation :=
    ⟨fun first second => Nat.le_total (patternCode first) (patternCode second)⟩
  letI : IsTrans Pattern relation :=
    ⟨fun _ _ _ firstLe secondLe => Nat.le_trans firstLe secondLe⟩
  letI : Std.Antisymm relation :=
    ⟨fun first second firstLe secondLe =>
      patternCode_injective (Nat.le_antisymm firstLe secondLe)⟩
  apply List.Perm.eq_of_pairwise' (r := relation)
  · simpa [sortPatterns, patternLinearOrder] using
      (List.pairwise_mergeSort' relation left)
  · simpa [sortPatterns, patternLinearOrder] using
      (List.pairwise_mergeSort' relation right)
  · exact (List.mergeSort_perm left _).trans
      (permutation.trans (List.mergeSort_perm right _).symm)

end Mettapedia.OSLF.MeTTaIL.PatternCode
