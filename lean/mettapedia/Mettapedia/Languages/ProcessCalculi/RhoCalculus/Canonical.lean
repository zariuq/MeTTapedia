import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Pairing
import Mathlib.Order.Basic
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence

/-!
# Computable canonical representatives for pure rho terms

The pure rho presentation treats parallel composition as a commutative monoid
and orients the paper's name equation `@(*x) ≡N x` toward `x`.  This module
builds the computational part of a canonical section directly on the shared
locally nameless `Pattern` carrier.

The order used for parallel components is not a hash.  `patternCode` is an
injective structural Gödel numbering, so ordering by that code cannot identify
distinct patterns.  Hashing may be layered over canonical terms later, but it
is not used to justify equality here.

Hash-set behavior is intentionally absent: set accumulation belongs to the
Lean-only extended-rho layer, not the pure calculus.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus

/-! ## An injective, computable structural code -/

/-- Injective prefix code for character lists. -/
def charListCode : List Char → Nat
  | [] => 0
  | c :: cs => Nat.succ (Nat.pair c.toNat (charListCode cs))

/-- Injective structural code for strings. -/
def stringCode (value : String) : Nat :=
  charListCode value.toList

/-- Injective prefix code for lists of strings. -/
def stringListCode : List String → Nat
  | [] => 0
  | value :: values => Nat.succ (Nat.pair (stringCode value) (stringListCode values))

/-- Injective code for optional strings. -/
def optionStringCode : Option String → Nat
  | none => Nat.pair 0 0
  | some value => Nat.pair 1 (stringCode value)

/-- Constructor tag for collection shapes. -/
def collectionCode : CollType → Nat
  | .vec => 0
  | .hashBag => 1
  | .hashSet => 2

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

  /-- Prefix code for pattern lists, using `patternCode` at each element. -/
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

/-- `patternCode` is collision-free.  Consequently it is a canonical ordering
key, not a probabilistic digest. -/
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

/-- A constructive linear order obtained by transporting the natural-number
order along the injective structural code. -/
@[reducible] def patternLinearOrder : LinearOrder Pattern :=
  LinearOrder.lift' patternCode patternCode_injective

/-! ## Pure-rho normalization -/

/-- Splice a normalized parallel bag into its parent bag. -/
def bagSplice : Pattern → List Pattern
  | .collection .hashBag elements none => elements
  | pattern => [pattern]

/-- Sort by the collision-free structural code. -/
def sortPatterns (patterns : List Pattern) : List Pattern :=
  patterns.mergeSort
    (fun left right => decide (patternCode left ≤ patternCode right))

/-- Sorting depends only on the parallel multiset, not on its presentation as a
list. -/
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

/-- Normalize an already-recursively-normalized parallel element list. -/
def normalizeBagElements (patterns : List Pattern) : List Pattern :=
  sortPatterns
    ((patterns.flatMap bagSplice).filter (fun pattern => pattern ≠ .apply "PZero" []))

/-- The unsorted multiset presentation underlying parallel normalization. -/
def bagContents (patterns : List Pattern) : List Pattern :=
  (patterns.flatMap bagSplice).filter (fun pattern => pattern ≠ .apply "PZero" [])

theorem normalizeBagElements_eq_sort_bagContents (patterns : List Pattern) :
    normalizeBagElements patterns = sortPatterns (bagContents patterns) := rfl

/-- Rebuild a parallel composition without representation-only empty and
singleton wrappers. -/
def collapseBag : List Pattern → Pattern
  | [] => .apply "PZero" []
  | [pattern] => pattern
  | patterns => .collection .hashBag patterns none

/-- Orient `NQuote (PDrop name) ≡N name` after recursively normalizing the
argument.  This does not orient the converse process shape
`PDrop (NQuote process)`: free drop stays inert. -/
def normalizeQuote : Pattern → Pattern
  | .apply "PDrop" [name] => name
  | pattern => .apply "NQuote" [pattern]

mutual
  /-- Computable canonical representative for the pure-rho equational theory.

  On the well-sorted pure-rho fragment, binders already use locally nameless
  bodies and carry no operational binder-name data.  Non-rho constructors are
  traversed conservatively so this function is safe to use as a boundary
  normalizer, but the soundness/completeness theorem is intentionally scoped to
  well-sorted pure-rho terms. -/
  def canonicalize : Pattern → Pattern
    | .bvar index => .bvar index
    | .fvar name => .fvar name
    | .apply "NQuote" [argument] => normalizeQuote (canonicalize argument)
    | .apply constructor arguments => .apply constructor (canonicalizeList arguments)
    | .lambda binderName body => .lambda binderName (canonicalize body)
    | .multiLambda arity binderNames body =>
        .multiLambda arity binderNames (canonicalize body)
    | .subst body replacement => .subst (canonicalize body) (canonicalize replacement)
    | .collection .hashBag elements none =>
        collapseBag (normalizeBagElements (canonicalizeList elements))
    | .collection collectionType elements rest =>
        .collection collectionType (canonicalizeList elements) rest

  /-- List recursion for `canonicalize`. -/
  def canonicalizeList : List Pattern → List Pattern
    | [] => []
    | pattern :: patterns => canonicalize pattern :: canonicalizeList patterns
end

/-! ## Structural soundness -/

/-- Pointwise structural congruence lifts through an application node. -/
theorem applyCongruence_of_forall₂ (constructor : String) {left right : List Pattern}
    (argumentsCongruent : List.Forall₂ StructuralCongruence left right) :
    StructuralCongruence (.apply constructor left) (.apply constructor right) :=
  StructuralCongruence.apply_cong constructor left right argumentsCongruent.length_eq
    (fun _ leftBound rightBound => argumentsCongruent.get leftBound rightBound)

/-- Pointwise structural congruence lifts through any collection node. -/
theorem collectionCongruence_of_forall₂ (collectionType : CollType)
    (rest : Option String) {left right : List Pattern}
    (elementsCongruent : List.Forall₂ StructuralCongruence left right) :
    StructuralCongruence
      (.collection collectionType left rest) (.collection collectionType right rest) :=
  StructuralCongruence.collection_general_cong collectionType left right rest
    elementsCongruent.length_eq
    (fun _ leftBound rightBound => elementsCongruent.get leftBound rightBound)

/-- Congruence under a fixed leading parallel component. -/
theorem hashBagConsCongruence (head : Pattern) {left right : List Pattern}
    (tailCongruent :
      StructuralCongruence
        (.collection .hashBag left none) (.collection .hashBag right none)) :
    StructuralCongruence
      (.collection .hashBag (head :: left) none)
      (.collection .hashBag (head :: right) none) := by
  have nestedCongruence :
      StructuralCongruence
        (.collection .hashBag [head, .collection .hashBag left none] none)
        (.collection .hashBag [head, .collection .hashBag right none] none) := by
    refine StructuralCongruence.par_cong
      [head, .collection .hashBag left none]
      [head, .collection .hashBag right none] rfl ?_
    intro index leftBound rightBound
    match index, leftBound with
    | 0, _ => exact StructuralCongruence.refl _
    | 1, _ => exact tailCongruent
  have flattenLeft :
      StructuralCongruence
        (.collection .hashBag [head, .collection .hashBag left none] none)
        (.collection .hashBag (head :: left) none) := by
    simpa using StructuralCongruence.par_flatten [head] left
  have flattenRight :
      StructuralCongruence
        (.collection .hashBag [head, .collection .hashBag right none] none)
        (.collection .hashBag (head :: right) none) := by
    simpa using StructuralCongruence.par_flatten [head] right
  exact StructuralCongruence.trans _ _ _
    (StructuralCongruence.trans _ _ _
      (StructuralCongruence.symm _ _ flattenLeft) nestedCongruence)
    flattenRight

/-- A nested parallel component can be spliced at the head of its parent. -/
theorem hashBagSpliceHead (nested rest : List Pattern) :
    StructuralCongruence
      (.collection .hashBag (.collection .hashBag nested none :: rest) none)
      (.collection .hashBag (nested ++ rest) none) := by
  have moveNestedRight :
      StructuralCongruence
        (.collection .hashBag (.collection .hashBag nested none :: rest) none)
        (.collection .hashBag (rest ++ [.collection .hashBag nested none]) none) := by
    apply StructuralCongruence.par_perm
    simpa using
      (List.perm_append_comm
        (l₁ := [.collection .hashBag nested none]) (l₂ := rest))
  have flatten :
      StructuralCongruence
        (.collection .hashBag (rest ++ [.collection .hashBag nested none]) none)
        (.collection .hashBag (rest ++ nested) none) :=
    StructuralCongruence.par_flatten rest nested
  have restoreOrder :
      StructuralCongruence
        (.collection .hashBag (rest ++ nested) none)
        (.collection .hashBag (nested ++ rest) none) := by
    apply StructuralCongruence.par_perm
    exact List.perm_append_comm (l₁ := rest) (l₂ := nested)
  exact StructuralCongruence.trans _ _ _ moveNestedRight
    (StructuralCongruence.trans _ _ _ flatten restoreOrder)

theorem bagSplice_eq_singleton_of_not_bag {pattern : Pattern}
    (notBag : ∀ elements, pattern ≠ .collection .hashBag elements none) :
    bagSplice pattern = [pattern] := by
  cases pattern with
  | collection collectionType elements rest =>
      cases collectionType <;> cases rest <;> simp_all [bagSplice]
  | _ => rfl

/-- Flattening every already-normalized child is structurally sound. -/
theorem hashBagFlattenSplices : ∀ patterns : List Pattern,
    StructuralCongruence
      (.collection .hashBag patterns none)
      (.collection .hashBag (patterns.flatMap bagSplice) none)
  | [] => StructuralCongruence.refl _
  | pattern :: patterns => by
      have tailCongruence := hashBagConsCongruence pattern (hashBagFlattenSplices patterns)
      by_cases isBag : ∃ elements, pattern = .collection .hashBag elements none
      · obtain ⟨elements, rfl⟩ := isBag
        exact StructuralCongruence.trans _ _ _ tailCongruence
          (hashBagSpliceHead elements (patterns.flatMap bagSplice))
      · have singleton : bagSplice pattern = [pattern] :=
          bagSplice_eq_singleton_of_not_bag (by
            intro elements equality
            exact isBag ⟨elements, equality⟩)
        simpa [List.flatMap_cons, singleton] using tailCongruence

/-- Remove a leading parallel unit from a bag of arbitrary arity. -/
theorem hashBagRemoveLeadingZero (rest : List Pattern) :
    StructuralCongruence
      (.collection .hashBag (.apply "PZero" [] :: rest) none)
      (.collection .hashBag rest none) := by
  have flatten :
      StructuralCongruence
        (.collection .hashBag
          (.apply "PZero" [] :: [.collection .hashBag rest none]) none)
        (.collection .hashBag (.apply "PZero" [] :: rest) none) := by
    simpa using StructuralCongruence.par_flatten [.apply "PZero" []] rest
  exact StructuralCongruence.trans _ _ _
    (StructuralCongruence.symm _ _ flatten)
    (StructuralCongruence.par_nil_left (.collection .hashBag rest none))

/-- Removing every parallel unit from a flat bag is structurally sound. -/
theorem hashBagFilterZero : ∀ patterns : List Pattern,
    StructuralCongruence
      (.collection .hashBag patterns none)
      (.collection .hashBag
        (patterns.filter (fun pattern => pattern ≠ .apply "PZero" [])) none)
  | [] => StructuralCongruence.refl _
  | pattern :: patterns => by
      by_cases isZero : pattern = .apply "PZero" []
      · subst isZero
        simpa using StructuralCongruence.trans _ _ _
          (hashBagRemoveLeadingZero patterns) (hashBagFilterZero patterns)
      · simpa [isZero] using hashBagConsCongruence pattern (hashBagFilterZero patterns)

/-- The sorted result is a permutation of its input. -/
theorem sortPatterns_perm (patterns : List Pattern) :
    List.Perm patterns (sortPatterns patterns) := by
  exact (List.mergeSort_perm patterns _).symm

/-- Sorting the components of a parallel bag is structurally sound. -/
theorem hashBagSort (patterns : List Pattern) :
    StructuralCongruence
      (.collection .hashBag patterns none)
      (.collection .hashBag (sortPatterns patterns) none) :=
  StructuralCongruence.par_perm patterns (sortPatterns patterns)
    (sortPatterns_perm patterns)

/-- Collapsing an empty or singleton parallel wrapper is structurally sound. -/
theorem hashBagCollapse (patterns : List Pattern) :
    StructuralCongruence
      (.collection .hashBag patterns none) (collapseBag patterns) := by
  match patterns with
  | [] => exact StructuralCongruence.par_empty
  | [pattern] => exact StructuralCongruence.par_singleton pattern
  | _ :: _ :: _ => exact StructuralCongruence.refl _

/-- The oriented name equation remains an equational step; it never introduces
an executable free-Drop reduction. -/
theorem normalizeQuote_sound {argument normalizedArgument : Pattern}
    (argumentCongruent : StructuralCongruence argument normalizedArgument) :
    StructuralCongruence
      (.apply "NQuote" [argument]) (normalizeQuote normalizedArgument) := by
  have quoteCongruent :
      StructuralCongruence
        (.apply "NQuote" [argument]) (.apply "NQuote" [normalizedArgument]) :=
    applyCongruence_of_forall₂ "NQuote"
      (List.Forall₂.cons argumentCongruent List.Forall₂.nil)
  unfold normalizeQuote
  split
  · next _ _ =>
      exact StructuralCongruence.trans _ _ _ quoteCongruent
        (StructuralCongruence.quote_drop _)
  · exact quoteCongruent

/-- Reduction equation for the non-quote application branch. -/
theorem canonicalize_apply_general (constructor : String) (arguments : List Pattern)
    (notQuote : ¬ (constructor = "NQuote" ∧ ∃ argument, arguments = [argument])) :
    canonicalize (.apply constructor arguments) =
      .apply constructor (canonicalizeList arguments) := by
  unfold canonicalize
  split <;> simp_all

/-- Reduction equation for collections other than an unguarded parallel bag. -/
theorem canonicalize_collection_general (collectionType : CollType)
    (elements : List Pattern) (rest : Option String)
    (notParallel : ¬ (collectionType = .hashBag ∧ rest = none)) :
    canonicalize (.collection collectionType elements rest) =
      .collection collectionType (canonicalizeList elements) rest := by
  unfold canonicalize
  split <;> simp_all

mutual
  /-- Every pattern is structurally congruent to its computed representative.
  This theorem is deliberately stronger than the pure-fragment theorem needed
  downstream: non-pure constructors are only traversed, never rewritten. -/
  theorem canonicalize_sound : ∀ pattern : Pattern,
      StructuralCongruence pattern (canonicalize pattern)
    | .bvar _ => StructuralCongruence.refl _
    | .fvar _ => StructuralCongruence.refl _
    | .apply constructor arguments => by
        by_cases isQuote : constructor = "NQuote" ∧ ∃ argument, arguments = [argument]
        · obtain ⟨rfl, argument, rfl⟩ := isQuote
          exact normalizeQuote_sound (canonicalize_sound argument)
        · rw [canonicalize_apply_general constructor arguments isQuote]
          exact applyCongruence_of_forall₂ constructor
            (canonicalizeList_sound arguments)
    | .lambda binderName body =>
        StructuralCongruence.lambda_cong binderName body (canonicalize body)
          (canonicalize_sound body)
    | .multiLambda arity binderNames body =>
        StructuralCongruence.multiLambda_cong arity binderNames body (canonicalize body)
          (canonicalize_sound body)
    | .subst body replacement =>
        StructuralCongruence.subst_cong body (canonicalize body)
          replacement (canonicalize replacement)
          (canonicalize_sound body) (canonicalize_sound replacement)
    | .collection collectionType elements rest => by
        by_cases isParallel : collectionType = .hashBag ∧ rest = none
        · obtain ⟨rfl, rfl⟩ := isParallel
          have recurse :
              StructuralCongruence
                (.collection .hashBag elements none)
                (.collection .hashBag (canonicalizeList elements) none) :=
            collectionCongruence_of_forall₂ .hashBag none
              (canonicalizeList_sound elements)
          have flatten := hashBagFlattenSplices (canonicalizeList elements)
          have filter := hashBagFilterZero
            ((canonicalizeList elements).flatMap bagSplice)
          have sort := hashBagSort
            (((canonicalizeList elements).flatMap bagSplice).filter
              (fun pattern => pattern ≠ .apply "PZero" []))
          have collapse := hashBagCollapse
            (normalizeBagElements (canonicalizeList elements))
          exact StructuralCongruence.trans _ _ _ recurse
            (StructuralCongruence.trans _ _ _ flatten
              (StructuralCongruence.trans _ _ _ filter
                (StructuralCongruence.trans _ _ _ sort collapse)))
        · rw [canonicalize_collection_general collectionType elements rest isParallel]
          exact collectionCongruence_of_forall₂ collectionType rest
            (canonicalizeList_sound elements)

  /-- Listwise structural soundness for `canonicalize`. -/
  theorem canonicalizeList_sound : ∀ patterns : List Pattern,
      List.Forall₂ StructuralCongruence patterns (canonicalizeList patterns)
    | [] => List.Forall₂.nil
    | pattern :: patterns =>
        List.Forall₂.cons (canonicalize_sound pattern) (canonicalizeList_sound patterns)
end

/-! ## Normality and idempotence -/

theorem canonicalizeList_length (patterns : List Pattern) :
    (canonicalizeList patterns).length = patterns.length := by
  induction patterns with
  | nil => rfl
  | cons pattern patterns inductionHypothesis =>
      simp [canonicalizeList, inductionHypothesis]

theorem sortPatterns_mem_iff {pattern : Pattern} {patterns : List Pattern} :
    pattern ∈ sortPatterns patterns ↔ pattern ∈ patterns :=
  (sortPatterns_perm patterns).mem_iff.symm

theorem sortPatterns_idempotent (patterns : List Pattern) :
    sortPatterns (sortPatterns patterns) = sortPatterns patterns :=
  (sortPatterns_eq_of_perm (sortPatterns_perm patterns)).symm

theorem normalizeBagElements_sorted (patterns : List Pattern) :
    sortPatterns (normalizeBagElements patterns) = normalizeBagElements patterns := by
  exact sortPatterns_idempotent _

/-- Classification of membership in a splice. -/
theorem mem_bagSplice {source member : Pattern} (membership : member ∈ bagSplice source) :
    (∃ elements, source = .collection .hashBag elements none ∧ member ∈ elements) ∨
      (member = source ∧ ∀ elements, source ≠ .collection .hashBag elements none) := by
  unfold bagSplice at membership
  split at membership
  · next elements => exact Or.inl ⟨elements, rfl, membership⟩
  · rw [List.mem_singleton] at membership
    exact Or.inr ⟨membership, by
      intro elements equality
      subst equality
      simp_all⟩

mutual
  /-- Intrinsic predicate for the image of `canonicalize`.  A canonical
  parallel bag is sorted, flat, unit-free, and has at least two components. -/
  def IsCanonical : Pattern → Prop
    | .collection .hashBag elements none =>
        2 ≤ elements.length ∧
        sortPatterns elements = elements ∧
        (∀ element ∈ elements,
          element ≠ .apply "PZero" [] ∧
          ∀ nested, element ≠ .collection .hashBag nested none) ∧
        IsCanonicalList elements
    | .apply "NQuote" [argument] =>
        IsCanonical argument ∧
        ∀ name, argument ≠ .apply "PDrop" [name]
    | .apply _ arguments => IsCanonicalList arguments
    | .lambda _ body => IsCanonical body
    | .multiLambda _ _ body => IsCanonical body
    | .subst body replacement => IsCanonical body ∧ IsCanonical replacement
    | .collection _ elements _ => IsCanonicalList elements
    | .bvar _ => True
    | .fvar _ => True

  /-- Listwise normality. -/
  def IsCanonicalList : List Pattern → Prop
    | [] => True
    | pattern :: patterns => IsCanonical pattern ∧ IsCanonicalList patterns
end

theorem isCanonicalList_mem : ∀ {patterns : List Pattern},
    IsCanonicalList patterns → ∀ {pattern}, pattern ∈ patterns → IsCanonical pattern
  | [], _, _, membership => by simp at membership
  | head :: tail, normal, pattern, membership => by
      rcases List.mem_cons.mp membership with rfl | tailMembership
      · exact normal.1
      · exact isCanonicalList_mem normal.2 tailMembership

theorem isCanonicalList_of_forall : ∀ {patterns : List Pattern},
    (∀ pattern ∈ patterns, IsCanonical pattern) → IsCanonicalList patterns
  | [], _ => trivial
  | head :: tail, allCanonical =>
      ⟨allCanonical head (by simp),
        isCanonicalList_of_forall (fun pattern membership =>
          allCanonical pattern (by simp [membership]))⟩

theorem normalizeQuote_isCanonical {argument : Pattern}
    (argumentCanonical : IsCanonical argument) :
    IsCanonical (normalizeQuote argument) := by
  by_cases isDrop : ∃ name, argument = .apply "PDrop" [name]
  · obtain ⟨name, rfl⟩ := isDrop
    simpa [normalizeQuote, IsCanonical, IsCanonicalList] using argumentCanonical
  · have notDrop : ∀ name, argument ≠ .apply "PDrop" [name] := by
      intro name equality
      exact isDrop ⟨name, equality⟩
    have quoteForm : normalizeQuote argument = .apply "NQuote" [argument] := by
      cases argument with
      | apply constructor arguments =>
          cases arguments with
          | nil => simp [normalizeQuote]
          | cons first rest =>
              cases rest with
              | nil =>
                  by_cases isConstructor : constructor = "PDrop"
                  · subst isConstructor
                    exact False.elim (isDrop ⟨first, rfl⟩)
                  · simp [normalizeQuote]
              | cons second rest => simp [normalizeQuote]
      | _ => rfl
    rw [quoteForm]
    exact ⟨argumentCanonical, notDrop⟩

theorem normalizeBagElements_mem_source {patterns : List Pattern} {member : Pattern}
    (membership : member ∈ normalizeBagElements patterns) :
    ∃ source ∈ patterns, member ∈ bagSplice source := by
  have filteredMembership :
      member ∈
        ((patterns.flatMap bagSplice).filter
          (fun pattern => pattern ≠ .apply "PZero" [])) :=
    sortPatterns_mem_iff.mp membership
  have flatMembership : member ∈ patterns.flatMap bagSplice :=
    (List.mem_filter.mp filteredMembership).1
  simpa [List.mem_flatMap] using flatMembership

theorem normalizeBagElements_no_zero {patterns : List Pattern} {member : Pattern}
    (membership : member ∈ normalizeBagElements patterns) :
    member ≠ .apply "PZero" [] := by
  have filteredMembership :
      member ∈
        ((patterns.flatMap bagSplice).filter
          (fun pattern => pattern ≠ .apply "PZero" [])) :=
    sortPatterns_mem_iff.mp membership
  exact of_decide_eq_true (List.mem_filter.mp filteredMembership).2

theorem normalizeBagElements_member_isCanonical {patterns : List Pattern}
    (patternsCanonical : IsCanonicalList patterns) {member : Pattern}
    (membership : member ∈ normalizeBagElements patterns) : IsCanonical member := by
  obtain ⟨source, sourceMembership, memberMembership⟩ :=
    normalizeBagElements_mem_source membership
  have sourceCanonical := isCanonicalList_mem patternsCanonical sourceMembership
  rcases mem_bagSplice memberMembership with
    ⟨elements, sourceEquality, memberInElements⟩ | ⟨rfl, _⟩
  · subst sourceEquality
    exact isCanonicalList_mem sourceCanonical.2.2.2 memberInElements
  · exact sourceCanonical

theorem normalizeBagElements_no_nested_bag {patterns : List Pattern}
    (patternsCanonical : IsCanonicalList patterns) {member : Pattern}
    (membership : member ∈ normalizeBagElements patterns) :
    ∀ nested, member ≠ .collection .hashBag nested none := by
  obtain ⟨source, sourceMembership, memberMembership⟩ :=
    normalizeBagElements_mem_source membership
  have sourceCanonical := isCanonicalList_mem patternsCanonical sourceMembership
  rcases mem_bagSplice memberMembership with
    ⟨elements, sourceEquality, memberInElements⟩ | ⟨rfl, sourceNotBag⟩
  · subst sourceEquality
    exact (sourceCanonical.2.2.1 member memberInElements).2
  · exact sourceNotBag

theorem normalizeBagElements_isCanonicalList {patterns : List Pattern}
    (patternsCanonical : IsCanonicalList patterns) :
    IsCanonicalList (normalizeBagElements patterns) :=
  isCanonicalList_of_forall (fun _ membership =>
    normalizeBagElements_member_isCanonical patternsCanonical membership)

/-- Reduction equation for `IsCanonical` away from the quote-special case. -/
theorem isCanonical_apply_general (constructor : String) (arguments : List Pattern)
    (notQuote : ¬ (constructor = "NQuote" ∧ ∃ argument, arguments = [argument])) :
    IsCanonical (.apply constructor arguments) = IsCanonicalList arguments := by
  unfold IsCanonical
  split <;> simp_all

/-- Reduction equation for `IsCanonical` away from an unguarded parallel bag. -/
theorem isCanonical_collection_general (collectionType : CollType)
    (elements : List Pattern) (rest : Option String)
    (notParallel : ¬ (collectionType = .hashBag ∧ rest = none)) :
    IsCanonical (.collection collectionType elements rest) = IsCanonicalList elements := by
  unfold IsCanonical
  split <;> simp_all

mutual
  /-- The result of `canonicalize` satisfies the intrinsic normal-form
  predicate. -/
  theorem canonicalize_isCanonical : ∀ pattern : Pattern,
      IsCanonical (canonicalize pattern)
    | .bvar _ => trivial
    | .fvar _ => trivial
    | .apply constructor arguments => by
        by_cases isQuote : constructor = "NQuote" ∧ ∃ argument, arguments = [argument]
        · obtain ⟨rfl, argument, rfl⟩ := isQuote
          exact normalizeQuote_isCanonical (canonicalize_isCanonical argument)
        · rw [canonicalize_apply_general constructor arguments isQuote,
            isCanonical_apply_general]
          · exact canonicalizeList_isCanonical arguments
          · intro quoteShape
            apply isQuote
            obtain ⟨constructorEquality, _, listEquality⟩ := quoteShape
            have lengthEquality := congrArg List.length listEquality
            have originalLength : arguments.length = 1 := by
              simpa [canonicalizeList_length] using lengthEquality
            match arguments, originalLength with
            | [originalArgument], _ => exact ⟨constructorEquality, originalArgument, rfl⟩
            | [], impossible => simp at impossible
            | _ :: _ :: _, impossible => simp at impossible
    | .lambda binderName body => canonicalize_isCanonical body
    | .multiLambda arity binderNames body => canonicalize_isCanonical body
    | .subst body replacement =>
        ⟨canonicalize_isCanonical body, canonicalize_isCanonical replacement⟩
    | .collection collectionType elements rest => by
        by_cases isParallel : collectionType = .hashBag ∧ rest = none
        · obtain ⟨rfl, rfl⟩ := isParallel
          let normalized := normalizeBagElements (canonicalizeList elements)
          have elementsCanonical := canonicalizeList_isCanonical elements
          have normalizedCanonical : IsCanonicalList normalized :=
            normalizeBagElements_isCanonicalList elementsCanonical
          have normalizedSorted : sortPatterns normalized = normalized :=
            normalizeBagElements_sorted _
          have normalizedProperties : ∀ element ∈ normalized,
              element ≠ .apply "PZero" [] ∧
              ∀ nested, element ≠ .collection .hashBag nested none := by
            intro element membership
            exact ⟨normalizeBagElements_no_zero membership,
              normalizeBagElements_no_nested_bag elementsCanonical membership⟩
          change IsCanonical (collapseBag normalized)
          match normalized with
          | [] => trivial
          | [element] =>
              simpa only [collapseBag] using
                isCanonicalList_mem normalizedCanonical (by simp)
          | first :: second :: tail =>
              exact ⟨by simp, normalizedSorted, normalizedProperties, normalizedCanonical⟩
        · rw [canonicalize_collection_general collectionType elements rest isParallel,
            isCanonical_collection_general collectionType (canonicalizeList elements) rest]
          · exact canonicalizeList_isCanonical elements
          · intro resultingParallel
            exact isParallel ⟨resultingParallel.1, resultingParallel.2⟩

  /-- Listwise normality of canonicalization. -/
  theorem canonicalizeList_isCanonical : ∀ patterns : List Pattern,
      IsCanonicalList (canonicalizeList patterns)
    | [] => trivial
    | pattern :: patterns =>
        ⟨canonicalize_isCanonical pattern, canonicalizeList_isCanonical patterns⟩
end

theorem normalizeQuote_eq_quote_of_not_drop {argument : Pattern}
    (notDrop : ∀ name, argument ≠ .apply "PDrop" [name]) :
    normalizeQuote argument = .apply "NQuote" [argument] := by
  cases argument with
  | apply constructor arguments =>
      cases arguments with
      | nil => simp [normalizeQuote]
      | cons first rest =>
          cases rest with
          | nil =>
              by_cases isConstructor : constructor = "PDrop"
              · subst isConstructor
                exact False.elim (notDrop first rfl)
              · simp [normalizeQuote]
          | cons second rest => simp [normalizeQuote]
  | _ => rfl

theorem flatMap_bagSplice_eq_self {patterns : List Pattern}
    (noNested : ∀ pattern ∈ patterns,
      ∀ nested, pattern ≠ .collection .hashBag nested none) :
    patterns.flatMap bagSplice = patterns := by
  induction patterns with
  | nil => rfl
  | cons pattern patterns inductionHypothesis =>
      have headSplice : bagSplice pattern = [pattern] :=
        bagSplice_eq_singleton_of_not_bag (noNested pattern (by simp))
      have tailNoNested : ∀ child ∈ patterns,
          ∀ nested, child ≠ .collection .hashBag nested none := by
        intro child membership
        exact noNested child (by simp [membership])
      simp [List.flatMap_cons, headSplice, inductionHypothesis tailNoNested]

theorem collapseBag_eq_bag_of_length_ge_two {patterns : List Pattern}
    (lengthAtLeastTwo : 2 ≤ patterns.length) :
    collapseBag patterns = .collection .hashBag patterns none := by
  match patterns with
  | [] => simp at lengthAtLeastTwo
  | [_] => simp at lengthAtLeastTwo
  | _ :: _ :: _ => rfl

mutual
  /-- Intrinsic normal forms are fixed points of `canonicalize`. -/
  theorem canonicalize_eq_of_isCanonical : ∀ {pattern : Pattern},
      IsCanonical pattern → canonicalize pattern = pattern
    | .bvar _, _ => rfl
    | .fvar _, _ => rfl
    | .apply constructor arguments, canonical => by
        by_cases isQuote : constructor = "NQuote" ∧ ∃ argument, arguments = [argument]
        · obtain ⟨rfl, argument, rfl⟩ := isQuote
          change IsCanonical argument ∧
            (∀ name, argument ≠ .apply "PDrop" [name]) at canonical
          change normalizeQuote (canonicalize argument) = .apply "NQuote" [argument]
          rw [canonicalize_eq_of_isCanonical canonical.1,
            normalizeQuote_eq_quote_of_not_drop canonical.2]
        · rw [canonicalize_apply_general constructor arguments isQuote,
            canonicalizeList_eq_of_isCanonical]
          rw [isCanonical_apply_general constructor arguments isQuote] at canonical
          exact canonical
    | .lambda binderName body, canonical => by
        change IsCanonical body at canonical
        change Pattern.lambda binderName (canonicalize body) = Pattern.lambda binderName body
        rw [canonicalize_eq_of_isCanonical canonical]
    | .multiLambda arity binderNames body, canonical => by
        change IsCanonical body at canonical
        change Pattern.multiLambda arity binderNames (canonicalize body) =
          Pattern.multiLambda arity binderNames body
        rw [canonicalize_eq_of_isCanonical canonical]
    | .subst body replacement, canonical => by
        change Pattern.subst (canonicalize body) (canonicalize replacement) =
          Pattern.subst body replacement
        rw [canonicalize_eq_of_isCanonical canonical.1,
          canonicalize_eq_of_isCanonical canonical.2]
    | .collection collectionType elements rest, canonical => by
        by_cases isParallel : collectionType = .hashBag ∧ rest = none
        · obtain ⟨rfl, rfl⟩ := isParallel
          change 2 ≤ elements.length ∧
            sortPatterns elements = elements ∧
            (∀ element ∈ elements,
              element ≠ .apply "PZero" [] ∧
              ∀ nested, element ≠ .collection .hashBag nested none) ∧
            IsCanonicalList elements at canonical
          have listFixed : canonicalizeList elements = elements :=
            canonicalizeList_eq_of_isCanonical canonical.2.2.2
          have spliceFixed : elements.flatMap bagSplice = elements :=
            flatMap_bagSplice_eq_self (fun element membership =>
              (canonical.2.2.1 element membership).2)
          have filterFixed :
              elements.filter (fun element => element ≠ .apply "PZero" []) = elements :=
            List.filter_eq_self.mpr (fun element membership => by
              simpa using (canonical.2.2.1 element membership).1)
          change collapseBag (normalizeBagElements (canonicalizeList elements)) =
            .collection .hashBag elements none
          rw [listFixed]
          unfold normalizeBagElements
          rw [spliceFixed, filterFixed, canonical.2.1]
          exact collapseBag_eq_bag_of_length_ge_two canonical.1
        · rw [canonicalize_collection_general collectionType elements rest isParallel,
            canonicalizeList_eq_of_isCanonical]
          rw [isCanonical_collection_general collectionType elements rest isParallel]
            at canonical
          exact canonical

  /-- Listwise fixed-point theorem. -/
  theorem canonicalizeList_eq_of_isCanonical : ∀ {patterns : List Pattern},
      IsCanonicalList patterns → canonicalizeList patterns = patterns
    | [], _ => rfl
    | pattern :: patterns, canonical => by
        change canonicalize pattern :: canonicalizeList patterns = pattern :: patterns
        rw [canonicalize_eq_of_isCanonical canonical.1,
          canonicalizeList_eq_of_isCanonical canonical.2]
end

/-- Canonicalization is idempotent, constructively and without quotient choice. -/
theorem canonicalize_idempotent (pattern : Pattern) :
    canonicalize (canonicalize pattern) = canonicalize pattern :=
  canonicalize_eq_of_isCanonical (canonicalize_isCanonical pattern)

/-- Listwise idempotence. -/
theorem canonicalizeList_idempotent (patterns : List Pattern) :
    canonicalizeList (canonicalizeList patterns) = canonicalizeList patterns :=
  canonicalizeList_eq_of_isCanonical (canonicalizeList_isCanonical patterns)

/-! ## Algebra of canonical parallel contents -/

theorem bagContents_append (left right : List Pattern) :
    bagContents (left ++ right) = bagContents left ++ bagContents right := by
  simp [bagContents, List.flatMap_append, List.filter_append]

theorem bagContents_perm {left right : List Pattern} (permutation : List.Perm left right) :
    List.Perm (bagContents left) (bagContents right) := by
  exact (permutation.flatMap_right bagSplice).filter
    (fun pattern => pattern ≠ .apply "PZero" [])

theorem normalizeBagElements_eq_of_perm {left right : List Pattern}
    (permutation : List.Perm left right) :
    normalizeBagElements left = normalizeBagElements right := by
  rw [normalizeBagElements_eq_sort_bagContents,
    normalizeBagElements_eq_sort_bagContents]
  exact sortPatterns_eq_of_perm (bagContents_perm permutation)

theorem canonicalizeList_eq_map (patterns : List Pattern) :
    canonicalizeList patterns = patterns.map canonicalize := by
  induction patterns with
  | nil => rfl
  | cons pattern patterns inductionHypothesis =>
      simp [canonicalizeList, inductionHypothesis]

theorem canonicalizeList_perm {left right : List Pattern}
    (permutation : List.Perm left right) :
    List.Perm (canonicalizeList left) (canonicalizeList right) := by
  rw [canonicalizeList_eq_map, canonicalizeList_eq_map]
  exact permutation.map canonicalize

theorem canonicalizeList_append (left right : List Pattern) :
    canonicalizeList (left ++ right) = canonicalizeList left ++ canonicalizeList right := by
  induction left with
  | nil => rfl
  | cons pattern patterns inductionHypothesis =>
      simp [canonicalizeList, inductionHypothesis]

theorem collapse_normalize_singleton_of_isCanonical {pattern : Pattern}
    (canonical : IsCanonical pattern) :
    collapseBag (normalizeBagElements [pattern]) = pattern := by
  by_cases isBag : ∃ elements, pattern = .collection .hashBag elements none
  · obtain ⟨elements, rfl⟩ := isBag
    change 2 ≤ elements.length ∧
      sortPatterns elements = elements ∧
      (∀ element ∈ elements,
        element ≠ .apply "PZero" [] ∧
        ∀ nested, element ≠ .collection .hashBag nested none) ∧
      IsCanonicalList elements at canonical
    have filterFixed :
        elements.filter (fun element => element ≠ .apply "PZero" []) = elements :=
      List.filter_eq_self.mpr (fun element membership => by
        simpa using (canonical.2.2.1 element membership).1)
    rw [normalizeBagElements_eq_sort_bagContents]
    simp only [bagContents, List.flatMap_cons, List.flatMap_nil, bagSplice,
      List.append_nil, filterFixed, canonical.2.1]
    exact collapseBag_eq_bag_of_length_ge_two canonical.1
  · have splice : bagSplice pattern = [pattern] :=
      bagSplice_eq_singleton_of_not_bag (by
        intro elements equality
        exact isBag ⟨elements, equality⟩)
    by_cases isZero : pattern = .apply "PZero" []
    · subst isZero
      simp [normalizeBagElements, bagSplice, sortPatterns, collapseBag]
    · rw [normalizeBagElements_eq_sort_bagContents]
      simp [bagContents, splice, isZero, sortPatterns, collapseBag]

theorem canonicalize_parallel_singleton (pattern : Pattern) :
    canonicalize (.collection .hashBag [pattern] none) = canonicalize pattern := by
  change collapseBag (normalizeBagElements [canonicalize pattern]) = canonicalize pattern
  exact collapse_normalize_singleton_of_isCanonical (canonicalize_isCanonical pattern)

theorem bagContents_zero_cons (patterns : List Pattern) :
    bagContents (.apply "PZero" [] :: patterns) = bagContents patterns := by
  simp [bagContents, bagSplice]

theorem normalizeBagElements_zero_cons (patterns : List Pattern) :
    normalizeBagElements (.apply "PZero" [] :: patterns) =
      normalizeBagElements patterns := by
  rw [normalizeBagElements_eq_sort_bagContents,
    normalizeBagElements_eq_sort_bagContents, bagContents_zero_cons]

theorem bagContents_collapse_normalized {patterns : List Pattern}
    (patternsCanonical : IsCanonicalList patterns) :
    bagContents [collapseBag (normalizeBagElements patterns)] =
      normalizeBagElements patterns := by
  have normalizedNoZero : ∀ element ∈ normalizeBagElements patterns,
      element ≠ .apply "PZero" [] := by
    intro element membership
    exact normalizeBagElements_no_zero membership
  have normalizedNoBag : ∀ element ∈ normalizeBagElements patterns,
      ∀ nested, element ≠ .collection .hashBag nested none := by
    intro element membership
    exact normalizeBagElements_no_nested_bag patternsCanonical membership
  match normalizedEquality : normalizeBagElements patterns with
  | [] =>
      simp [bagContents, collapseBag, bagSplice]
  | [element] =>
      have notZero : element ≠ .apply "PZero" [] :=
        normalizedNoZero element (by rw [normalizedEquality]; simp)
      have notBag : ∀ nested, element ≠ .collection .hashBag nested none :=
        normalizedNoBag element (by rw [normalizedEquality]; simp)
      have splice : bagSplice element = [element] :=
        bagSplice_eq_singleton_of_not_bag notBag
      simp [bagContents, collapseBag, splice, notZero]
  | first :: second :: tail =>
      have filterFixed :
          (first :: second :: tail).filter
              (fun element => element ≠ .apply "PZero" []) =
            first :: second :: tail :=
        List.filter_eq_self.mpr (fun element membership => by
          simpa using normalizedNoZero element (by
            rw [normalizedEquality]
            exact membership))
      rw [show collapseBag (first :: second :: tail) =
        .collection .hashBag (first :: second :: tail) none from rfl]
      unfold bagContents
      simp only [List.flatMap_cons, List.flatMap_nil, bagSplice, List.append_nil]
      exact filterFixed

theorem normalizeBagElements_collapse_cons (patterns rest : List Pattern)
    (patternsCanonical : IsCanonicalList patterns) :
    normalizeBagElements
        (collapseBag (normalizeBagElements patterns) :: rest) =
      normalizeBagElements (patterns ++ rest) := by
  change
    sortPatterns (bagContents (collapseBag (normalizeBagElements patterns) :: rest)) =
      sortPatterns (bagContents (patterns ++ rest))
  apply sortPatterns_eq_of_perm
  rw [show bagContents (collapseBag (normalizeBagElements patterns) :: rest) =
      bagContents [collapseBag (normalizeBagElements patterns)] ++ bagContents rest by
        simpa using bagContents_append [collapseBag (normalizeBagElements patterns)] rest,
    bagContents_collapse_normalized patternsCanonical,
    bagContents_append]
  exact (sortPatterns_perm (bagContents patterns)).symm.append_right (bagContents rest)

/-! ## Pure-fragment boundary -/

mutual
  /-- The shared carrier fragment that excludes the extended-rho set
  constructor. -/
  def HashSetFree : Pattern → Prop
    | .bvar _ => True
    | .fvar _ => True
    | .apply _ arguments => HashSetFreeList arguments
    | .lambda _ body => HashSetFree body
    | .multiLambda _ _ body => HashSetFree body
    | .subst body replacement => HashSetFree body ∧ HashSetFree replacement
    | .collection .hashSet _ _ => False
    | .collection _ elements _ => HashSetFreeList elements

  def HashSetFreeList : List Pattern → Prop
    | [] => True
    | pattern :: patterns => HashSetFree pattern ∧ HashSetFreeList patterns
end

theorem hashSetFreeList_iff_of_pointwise {left right : List Pattern}
    (lengthEquality : left.length = right.length)
    (pointwise : ∀ index (leftBound : index < left.length)
      (rightBound : index < right.length),
      HashSetFree (left.get ⟨index, leftBound⟩) ↔
        HashSetFree (right.get ⟨index, rightBound⟩)) :
    HashSetFreeList left ↔ HashSetFreeList right := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => rfl
      | cons _ _ => simp at lengthEquality
  | cons leftHead leftTail inductionHypothesis =>
      cases right with
      | nil => simp at lengthEquality
      | cons rightHead rightTail =>
          have headEquality : HashSetFree leftHead ↔ HashSetFree rightHead :=
            pointwise 0 (Nat.zero_lt_succ _) (Nat.zero_lt_succ _)
          have tailEquality : HashSetFreeList leftTail ↔ HashSetFreeList rightTail := by
            apply inductionHypothesis
            · simpa using Nat.succ.inj lengthEquality
            · intro index leftBound rightBound
              simpa using pointwise (index + 1)
                (Nat.succ_lt_succ leftBound) (Nat.succ_lt_succ rightBound)
          simp only [HashSetFreeList]
          exact and_congr headEquality tailEquality

theorem hashSetFreeList_iff_of_perm {left right : List Pattern}
    (permutation : List.Perm left right) :
    HashSetFreeList left ↔ HashSetFreeList right := by
  induction permutation with
  | nil => rfl
  | cons pattern _ inductionHypothesis =>
      simp only [HashSetFreeList]
      exact and_congr Iff.rfl inductionHypothesis
  | swap left right tail =>
      simp [HashSetFreeList, and_left_comm]
  | trans _ _ firstInduction secondInduction =>
      exact firstInduction.trans secondInduction

theorem hashSetFreeList_append_iff {left right : List Pattern} :
    HashSetFreeList (left ++ right) ↔ HashSetFreeList left ∧ HashSetFreeList right := by
  induction left with
  | nil => simp [HashSetFreeList]
  | cons pattern patterns inductionHypothesis =>
      simp [HashSetFreeList, inductionHypothesis, and_assoc]

theorem hashSetFreeList_get : ∀ {patterns : List Pattern},
    HashSetFreeList patterns → ∀ index (bound : index < patterns.length),
      HashSetFree (patterns.get ⟨index, bound⟩)
  | [], _, _, bound => by simp at bound
  | pattern :: patterns, free, index, bound => by
      match index, bound with
      | 0, _ => exact free.1
      | Nat.succ tailIndex, successorBound =>
          have tailBound : tailIndex < patterns.length := by simpa using successorBound
          simpa using hashSetFreeList_get free.2 tailIndex tailBound

/-- Structural congruence cannot cross the pure/extended `hashSet` boundary. -/
theorem hashSetFree_iff_of_structuralCongruence {left right : Pattern}
    (congruence : StructuralCongruence left right) :
    HashSetFree left ↔ HashSetFree right := by
  induction congruence with
  | alpha _ _ equality => subst equality; rfl
  | refl _ => rfl
  | symm _ _ _ inductionHypothesis => exact inductionHypothesis.symm
  | trans _ _ _ _ _ firstInduction secondInduction =>
      exact firstInduction.trans secondInduction
  | par_singleton pattern => simp [HashSetFree, HashSetFreeList]
  | par_nil_left pattern => simp [HashSetFree, HashSetFreeList]
  | par_nil_right pattern => simp [HashSetFree, HashSetFreeList]
  | par_empty => simp [HashSetFree, HashSetFreeList]
  | par_comm left right => simp [HashSetFree, HashSetFreeList, and_comm]
  | par_assoc first second third =>
      simp [HashSetFree, HashSetFreeList, and_assoc, and_comm]
  | par_cong left right lengthEquality _ inductionHypothesis =>
      simpa [HashSetFree] using
        hashSetFreeList_iff_of_pointwise lengthEquality inductionHypothesis
  | par_flatten left right =>
      simp [HashSetFree, HashSetFreeList, hashSetFreeList_append_iff]
  | par_perm left right permutation =>
      simpa [HashSetFree] using hashSetFreeList_iff_of_perm permutation
  | set_perm _ _ _ => simp [HashSetFree]
  | set_cong _ _ _ _ _ => simp [HashSetFree]
  | lambda_cong _ _ _ _ inductionHypothesis =>
      simpa [HashSetFree] using inductionHypothesis
  | apply_cong _ _ _ lengthEquality _ inductionHypothesis =>
      simpa [HashSetFree] using
        hashSetFreeList_iff_of_pointwise lengthEquality inductionHypothesis
  | collection_general_cong collectionType left right rest lengthEquality _
      inductionHypothesis =>
      cases collectionType
      · exact hashSetFreeList_iff_of_pointwise lengthEquality inductionHypothesis
      · exact hashSetFreeList_iff_of_pointwise lengthEquality inductionHypothesis
      · simp [HashSetFree]
  | multiLambda_cong _ _ _ _ _ inductionHypothesis =>
      simpa [HashSetFree] using inductionHypothesis
  | subst_cong _ _ _ _ _ _ firstInduction secondInduction =>
      simp [HashSetFree, firstInduction, secondInduction]
  | quote_drop name => simp [HashSetFree, HashSetFreeList]

theorem canonicalizeList_eq_of_pointwise {left right : List Pattern}
    (lengthEquality : left.length = right.length)
    (pointwise : ∀ index (leftBound : index < left.length)
      (rightBound : index < right.length),
      canonicalize (left.get ⟨index, leftBound⟩) =
        canonicalize (right.get ⟨index, rightBound⟩)) :
    canonicalizeList left = canonicalizeList right := by
  rw [canonicalizeList_eq_map, canonicalizeList_eq_map]
  apply List.ext_getElem
  · simpa using lengthEquality
  · intro index leftBound rightBound
    simp only [List.getElem_map]
    exact pointwise index (by simpa using leftBound) (by simpa using rightBound)

theorem canonicalize_parallel_nil_left (pattern : Pattern) :
    canonicalize
        (.collection .hashBag [.apply "PZero" [], pattern] none) =
      canonicalize pattern := by
  change collapseBag
      (normalizeBagElements [.apply "PZero" [], canonicalize pattern]) =
    canonicalize pattern
  rw [normalizeBagElements_zero_cons]
  exact collapse_normalize_singleton_of_isCanonical (canonicalize_isCanonical pattern)

theorem canonicalize_parallel_nil_right (pattern : Pattern) :
    canonicalize
        (.collection .hashBag [pattern, .apply "PZero" []] none) =
      canonicalize pattern := by
  change collapseBag
      (normalizeBagElements [canonicalize pattern, .apply "PZero" []]) =
    canonicalize pattern
  rw [normalizeBagElements_eq_of_perm
      (List.Perm.swap (.apply "PZero" []) (canonicalize pattern) []),
    normalizeBagElements_zero_cons]
  exact collapse_normalize_singleton_of_isCanonical (canonicalize_isCanonical pattern)

theorem canonicalize_parallel_empty :
    canonicalize (.collection .hashBag [] none) = .apply "PZero" [] := by
  simp [canonicalize, canonicalizeList, normalizeBagElements, sortPatterns, collapseBag]

theorem canonicalize_parallel_comm (left right : Pattern) :
    canonicalize (.collection .hashBag [left, right] none) =
      canonicalize (.collection .hashBag [right, left] none) := by
  change collapseBag (normalizeBagElements [canonicalize left, canonicalize right]) =
    collapseBag (normalizeBagElements [canonicalize right, canonicalize left])
  rw [normalizeBagElements_eq_of_perm
    (List.Perm.swap (canonicalize left) (canonicalize right) [])]

theorem canonicalize_parallel_assoc (first second third : Pattern) :
    canonicalize
        (.collection .hashBag
          [.collection .hashBag [first, second] none, third] none) =
      canonicalize
        (.collection .hashBag
          [first, .collection .hashBag [second, third] none] none) := by
  let first' := canonicalize first
  let second' := canonicalize second
  let third' := canonicalize third
  have firstCanonical : IsCanonical first' := canonicalize_isCanonical first
  have secondCanonical : IsCanonical second' := canonicalize_isCanonical second
  have thirdCanonical : IsCanonical third' := canonicalize_isCanonical third
  change collapseBag
      (normalizeBagElements
        [collapseBag (normalizeBagElements [first', second']), third']) =
    collapseBag
      (normalizeBagElements
        [first', collapseBag (normalizeBagElements [second', third'])])
  congr 1
  calc
    normalizeBagElements
        [collapseBag (normalizeBagElements [first', second']), third'] =
      normalizeBagElements ([first', second'] ++ [third']) :=
        normalizeBagElements_collapse_cons [first', second'] [third']
          ⟨firstCanonical, secondCanonical, trivial⟩
    _ = normalizeBagElements [first', second', third'] := rfl
    _ = normalizeBagElements [second', third', first'] :=
      normalizeBagElements_eq_of_perm
        ((List.Perm.swap second' first' [third']).trans
          (List.Perm.cons second' (List.Perm.swap third' first' [])))
    _ = normalizeBagElements
        [collapseBag (normalizeBagElements [second', third']), first'] :=
      (normalizeBagElements_collapse_cons [second', third'] [first']
        ⟨secondCanonical, thirdCanonical, trivial⟩).symm
    _ = normalizeBagElements
        [first', collapseBag (normalizeBagElements [second', third'])] :=
      normalizeBagElements_eq_of_perm
        (List.Perm.swap
          first' (collapseBag (normalizeBagElements [second', third'])) [])

theorem canonicalize_parallel_flatten (leading nestedPatterns : List Pattern) :
    canonicalize
        (.collection .hashBag
          (leading ++ [.collection .hashBag nestedPatterns none]) none) =
      canonicalize (.collection .hashBag (leading ++ nestedPatterns) none) := by
  let leading' := canonicalizeList leading
  let nested' := canonicalizeList nestedPatterns
  have nestedCanonical : IsCanonicalList nested' := canonicalizeList_isCanonical nestedPatterns
  change collapseBag
      (normalizeBagElements
        (canonicalizeList (leading ++ [.collection .hashBag nestedPatterns none]))) =
    collapseBag (normalizeBagElements (canonicalizeList (leading ++ nestedPatterns)))
  rw [canonicalizeList_append, canonicalizeList_append]
  change collapseBag
      (normalizeBagElements
        (leading' ++ [collapseBag (normalizeBagElements nested')])) =
    collapseBag (normalizeBagElements (leading' ++ nested'))
  congr 1
  calc
    normalizeBagElements (leading' ++ [collapseBag (normalizeBagElements nested')]) =
      normalizeBagElements (collapseBag (normalizeBagElements nested') :: leading') :=
        normalizeBagElements_eq_of_perm
          (List.perm_append_comm
            (l₁ := leading') (l₂ := [collapseBag (normalizeBagElements nested')]))
    _ = normalizeBagElements (nested' ++ leading') :=
      normalizeBagElements_collapse_cons nested' leading' nestedCanonical
    _ = normalizeBagElements (leading' ++ nested') :=
      normalizeBagElements_eq_of_perm
        (List.perm_append_comm (l₁ := nested') (l₂ := leading'))

/-- On the pure (`hashSet`-free) fragment, structural congruence has one
computed canonical key.  The extended set laws are deliberately outside this
theorem and outside CeTTa's rho profile. -/
theorem canonicalize_eq_of_structuralCongruence {left right : Pattern}
    (congruence : StructuralCongruence left right) :
    HashSetFree left → HashSetFree right →
      canonicalize left = canonicalize right := by
  induction congruence with
  | alpha _ _ equality =>
      subst equality
      intro _ _
      rfl
  | refl _ =>
      intro _ _
      rfl
  | symm _ _ congruence inductionHypothesis =>
      intro rightFree leftFree
      exact (inductionHypothesis leftFree rightFree).symm
  | trans left middle right firstCongruence secondCongruence firstInduction
      secondInduction =>
      intro leftFree rightFree
      have middleFree : HashSetFree middle :=
        (hashSetFree_iff_of_structuralCongruence firstCongruence).mp leftFree
      exact (firstInduction leftFree middleFree).trans
        (secondInduction middleFree rightFree)
  | par_singleton pattern =>
      intro _ _
      exact canonicalize_parallel_singleton pattern
  | par_nil_left pattern =>
      intro _ _
      exact canonicalize_parallel_nil_left pattern
  | par_nil_right pattern =>
      intro _ _
      exact canonicalize_parallel_nil_right pattern
  | par_empty =>
      intro _ _
      exact canonicalize_parallel_empty
  | par_comm left right =>
      intro _ _
      exact canonicalize_parallel_comm left right
  | par_assoc first second third =>
      intro _ _
      exact canonicalize_parallel_assoc first second third
  | par_cong left right lengthEquality pointwiseCongruence inductionHypothesis =>
      intro leftFree rightFree
      change HashSetFreeList left at leftFree
      change HashSetFreeList right at rightFree
      change collapseBag (normalizeBagElements (canonicalizeList left)) =
        collapseBag (normalizeBagElements (canonicalizeList right))
      rw [canonicalizeList_eq_of_pointwise lengthEquality (fun index leftBound rightBound =>
        inductionHypothesis index leftBound rightBound
          (hashSetFreeList_get leftFree index leftBound)
          (hashSetFreeList_get rightFree index rightBound))]
  | par_flatten leading nestedPatterns =>
      intro _ _
      exact canonicalize_parallel_flatten leading nestedPatterns
  | par_perm left right permutation =>
      intro _ _
      change collapseBag (normalizeBagElements (canonicalizeList left)) =
        collapseBag (normalizeBagElements (canonicalizeList right))
      rw [normalizeBagElements_eq_of_perm (canonicalizeList_perm permutation)]
  | set_perm left right permutation =>
      intro leftFree _
      change False at leftFree
      exact leftFree.elim
  | set_cong left right lengthEquality pointwiseCongruence inductionHypothesis =>
      intro leftFree _
      change False at leftFree
      exact leftFree.elim
  | lambda_cong binderName left right congruence inductionHypothesis =>
      intro leftFree rightFree
      change HashSetFree left at leftFree
      change HashSetFree right at rightFree
      change Pattern.lambda binderName (canonicalize left) =
        Pattern.lambda binderName (canonicalize right)
      rw [inductionHypothesis leftFree rightFree]
  | apply_cong constructor left right lengthEquality pointwiseCongruence
      inductionHypothesis =>
      intro leftFree rightFree
      change HashSetFreeList left at leftFree
      change HashSetFreeList right at rightFree
      by_cases leftQuote : constructor = "NQuote" ∧ ∃ argument, left = [argument]
      · obtain ⟨rfl, leftArgument, rfl⟩ := leftQuote
        have rightLength : right.length = 1 := by simpa using lengthEquality.symm
        obtain ⟨rightArgument, rightEquality⟩ : ∃ argument, right = [argument] := by
          match right, rightLength with
          | [argument], _ => exact ⟨argument, rfl⟩
          | [], impossible => simp at impossible
          | _ :: _ :: _, impossible => simp at impossible
        subst rightEquality
        change normalizeQuote (canonicalize leftArgument) =
          normalizeQuote (canonicalize rightArgument)
        have argumentEquality : canonicalize leftArgument = canonicalize rightArgument := by
          simpa using inductionHypothesis 0 (by simp) (by simp)
            (hashSetFreeList_get leftFree 0 (by simp))
            (hashSetFreeList_get rightFree 0 (by simp))
        rw [argumentEquality]
      · have rightQuote : ¬ (constructor = "NQuote" ∧ ∃ argument, right = [argument]) := by
          rintro ⟨constructorEquality, rightArgument, rightEquality⟩
          apply leftQuote
          refine ⟨constructorEquality, ?_⟩
          have leftLength : left.length = 1 := by simp [lengthEquality, rightEquality]
          match left, leftLength with
          | [leftArgument], _ => exact ⟨leftArgument, rfl⟩
          | [], impossible => simp at impossible
          | _ :: _ :: _, impossible => simp at impossible
        rw [canonicalize_apply_general constructor left leftQuote,
          canonicalize_apply_general constructor right rightQuote,
          canonicalizeList_eq_of_pointwise lengthEquality (fun index leftBound rightBound =>
            inductionHypothesis index leftBound rightBound
              (hashSetFreeList_get leftFree index leftBound)
              (hashSetFreeList_get rightFree index rightBound))]
  | collection_general_cong collectionType left right rest lengthEquality
      pointwiseCongruence inductionHypothesis =>
      intro leftFree rightFree
      cases collectionType with
      | hashSet =>
          change False at leftFree
          exact leftFree.elim
      | vec =>
          change HashSetFreeList left at leftFree
          change HashSetFreeList right at rightFree
          rw [canonicalize_collection_general .vec left rest (by simp),
            canonicalize_collection_general .vec right rest (by simp),
            canonicalizeList_eq_of_pointwise lengthEquality (fun index leftBound rightBound =>
              inductionHypothesis index leftBound rightBound
                (hashSetFreeList_get leftFree index leftBound)
                (hashSetFreeList_get rightFree index rightBound))]
      | hashBag =>
          change HashSetFreeList left at leftFree
          change HashSetFreeList right at rightFree
          cases rest with
          | none =>
              change collapseBag (normalizeBagElements (canonicalizeList left)) =
                collapseBag (normalizeBagElements (canonicalizeList right))
              rw [canonicalizeList_eq_of_pointwise lengthEquality
                (fun index leftBound rightBound =>
                  inductionHypothesis index leftBound rightBound
                    (hashSetFreeList_get leftFree index leftBound)
                    (hashSetFreeList_get rightFree index rightBound))]
          | some guard =>
              rw [canonicalize_collection_general .hashBag left (some guard) (by simp),
                canonicalize_collection_general .hashBag right (some guard) (by simp),
                canonicalizeList_eq_of_pointwise lengthEquality
                  (fun index leftBound rightBound =>
                    inductionHypothesis index leftBound rightBound
                      (hashSetFreeList_get leftFree index leftBound)
                      (hashSetFreeList_get rightFree index rightBound))]
  | multiLambda_cong arity binderNames left right congruence inductionHypothesis =>
      intro leftFree rightFree
      change HashSetFree left at leftFree
      change HashSetFree right at rightFree
      change Pattern.multiLambda arity binderNames (canonicalize left) =
        Pattern.multiLambda arity binderNames (canonicalize right)
      rw [inductionHypothesis leftFree rightFree]
  | subst_cong leftBody rightBody leftReplacement rightReplacement bodyCongruence
      replacementCongruence bodyInduction replacementInduction =>
      intro leftFree rightFree
      change HashSetFree leftBody ∧ HashSetFree leftReplacement at leftFree
      change HashSetFree rightBody ∧ HashSetFree rightReplacement at rightFree
      change Pattern.subst (canonicalize leftBody) (canonicalize leftReplacement) =
        Pattern.subst (canonicalize rightBody) (canonicalize rightReplacement)
      rw [bodyInduction leftFree.1 rightFree.1,
        replacementInduction leftFree.2 rightFree.2]
  | quote_drop name =>
      intro _ _
      change normalizeQuote (.apply "PDrop" [canonicalize name]) = canonicalize name
      rfl

/-- Equal pure canonical keys characterize structural congruence in the reverse
direction as well. -/
theorem structuralCongruence_of_canonicalize_eq {left right : Pattern}
    (equality : canonicalize left = canonicalize right) :
    StructuralCongruence left right :=
  StructuralCongruence.trans _ _ _ (canonicalize_sound left)
    (StructuralCongruence.trans _ _ _
      (equality ▸ StructuralCongruence.refl (canonicalize left))
      (StructuralCongruence.symm _ _ (canonicalize_sound right)))

/-- Full canonical-section criterion for the pure rho boundary. -/
theorem structuralCongruence_iff_canonicalize_eq {left right : Pattern}
    (leftFree : HashSetFree left) (rightFree : HashSetFree right) :
    StructuralCongruence left right ↔ canonicalize left = canonicalize right :=
  ⟨fun congruence =>
      canonicalize_eq_of_structuralCongruence congruence leftFree rightFree,
    structuralCongruence_of_canonicalize_eq⟩

/-! ## Positive and negative executable boundary examples -/

theorem canonicalize_quote_drop_example (name : String) :
    canonicalize (.apply "NQuote" [.apply "PDrop" [.fvar name]]) = .fvar name := by
  rfl

theorem canonicalize_parallel_unit_and_flatten_example (name : String) :
    canonicalize
        (.collection .hashBag
          [.apply "PZero" [], .collection .hashBag [.fvar name] none] none) =
      .fvar name := by
  simp [canonicalize, canonicalizeList, normalizeBagElements, sortPatterns,
    bagSplice, collapseBag]

theorem canonicalize_parallel_permutation_example :
    canonicalize (.collection .hashBag [.bvar 0, .bvar 1] none) =
      canonicalize (.collection .hashBag [.bvar 1, .bvar 0] none) := by
  have zeroNotPZero : Pattern.bvar 0 ≠ .apply "PZero" [] := by
    intro equality
    cases equality
  have oneNotPZero : Pattern.bvar 1 ≠ .apply "PZero" [] := by
    intro equality
    cases equality
  simp [canonicalize, canonicalizeList, normalizeBagElements, bagSplice,
    zeroNotPZero, oneNotPZero]
  rw [sortPatterns_eq_of_perm (List.Perm.swap (.bvar 0) (.bvar 1) [])]

theorem canonicalize_free_drop_stays_inert :
    canonicalize
        (.apply "PDrop" [.apply "NQuote" [.apply "PZero" []]]) =
      .apply "PDrop" [.apply "NQuote" [.apply "PZero" []]] := by
  rfl

theorem canonicalize_free_drop_not_process :
    canonicalize
        (.apply "PDrop" [.apply "NQuote" [.apply "PZero" []]]) ≠
      canonicalize (.apply "PZero" []) := by
  decide

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical
