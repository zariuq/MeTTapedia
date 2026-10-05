import Mettapedia.GSLT.LanguageDef.Cost.LiteralSignatureCommitment
import Mettapedia.GSLT.LanguageDef.Cost.SignatureSyntax
import Mathlib.Algebra.Free
import Mathlib.Algebra.FreeMonoid.Basic

/-!
# Atomic keys and the free-monoid interpretation of generated signatures

The distinct key sort carries finite binary trees. A signature commitment
denotes one free-monoid generator; signature unit and product retain their
ordinary monoid interpretations. Literal authority remains a separate value.
The exact key serializer reuses the existing checked binary serialization,
retagging its tree rather than introducing another number encoding.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Cost.AtomicSignatureInterpretation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.PatternCode
open WellSorted
open SignatureSyntax

abbrev KeyTree := FreeMagma PUnit.{1}
abbrev Account := FreeMonoid KeyTree

def encodeKey : KeyTree → Pattern
  | .of _ => .apply costKeyLeafConstructorName []
  | .mul left right => .apply costKeyBranchConstructorName [encodeKey left, encodeKey right]

def legacyPattern : KeyTree → Pattern
  | .of _ => .apply costSignatureUnitConstructorName []
  | .mul left right => .apply costSignatureProductConstructorName [legacyPattern left, legacyPattern right]

def readLegacy? : Pattern → Option KeyTree
  | .apply constructor [] =>
      if constructor = costSignatureUnitConstructorName then some (.of PUnit.unit) else none
  | .apply constructor [left, right] =>
      if constructor = costSignatureProductConstructorName then
        match readLegacy? left, readLegacy? right with
        | some first, some second => some (.mul first second)
        | _, _ => none
      else none
  | _ => none
termination_by source => sizeOf source
decreasing_by
  all_goals
    simp only [Pattern.apply.sizeOf_spec, List.cons.sizeOf_spec, List.nil.sizeOf_spec]
    omega

def readKey? : Pattern → Option KeyTree
  | .apply constructor [] =>
      if constructor = costKeyLeafConstructorName then some (.of PUnit.unit) else none
  | .apply constructor [left, right] =>
      if constructor = costKeyBranchConstructorName then
        match readKey? left, readKey? right with
        | some first, some second => some (.mul first second)
        | _, _ => none
      else none
  | _ => none
termination_by source => sizeOf source
decreasing_by
  all_goals
    simp only [Pattern.apply.sizeOf_spec, List.cons.sizeOf_spec, List.nil.sizeOf_spec]
    omega

@[simp] theorem readLegacy_legacyPattern (tree : KeyTree) :
    readLegacy? (legacyPattern tree) = some tree := by
  induction tree with
  | of value => cases value; simp [legacyPattern, readLegacy?]
  | mul left right leftIH rightIH => simp [legacyPattern, readLegacy?, leftIH, rightIH]

@[simp] theorem readKey_encodeKey (tree : KeyTree) : readKey? (encodeKey tree) = some tree := by
  induction tree with
  | of value => cases value; simp [encodeKey, readKey?]
  | mul left right leftIH rightIH => simp [encodeKey, readKey?, leftIH, rightIH]

theorem encodeKey_injective : Function.Injective encodeKey := by
  intro left right same
  exact Option.some.inj (by simpa only [readKey_encodeKey] using congrArg readKey? same)

theorem legacy_readout {source : Pattern} (shape : LegacyLiteralSignatureSyntax source) :
    ∃ tree, readLegacy? source = some tree ∧ legacyPattern tree = source := by
  induction shape with
  | unit => exact ⟨.of PUnit.unit, by simp [readLegacy?], rfl⟩
  | product left right leftIH rightIH =>
      obtain ⟨first, firstFound, firstRendered⟩ := leftIH
      obtain ⟨second, secondFound, secondRendered⟩ := rightIH
      exact ⟨.mul first second, by simp [readLegacy?, firstFound, secondFound],
        by simp [legacyPattern, firstRendered, secondRendered]⟩

theorem legacy_isSome {source : Pattern} (shape : LegacyLiteralSignatureSyntax source) :
    (readLegacy? source).isSome := by
  obtain ⟨tree, found, _⟩ := legacy_readout shape
  rw [found]
  rfl

def keyOfLegacy (source : Pattern) (shape : LegacyLiteralSignatureSyntax source) : KeyTree :=
  (readLegacy? source).get (legacy_isSome shape)

theorem legacyPattern_keyOfLegacy (source : Pattern)
    (shape : LegacyLiteralSignatureSyntax source) : legacyPattern (keyOfLegacy source shape) = source := by
  obtain ⟨tree, found, rendered⟩ := legacy_readout shape
  simpa only [keyOfLegacy, found, Option.get_some] using rendered

theorem positive_legacy (number : PosNum) :
    LegacyLiteralSignatureSyntax (LiteralSignatureCommitment.encodePositive number) := by
  induction number with
  | one => exact .product .unit .unit
  | bit0 number ih => exact .product .unit ih
  | bit1 number ih => exact .product (.product .unit .unit) ih

theorem number_legacy (number : Nat) :
    LegacyLiteralSignatureSyntax (LiteralSignatureCommitment.encodeNat number) := by
  unfold LiteralSignatureCommitment.encodeNat
  cases (number : Num) with
  | zero => exact .unit
  | pos value => exact positive_legacy value

/-- This reads the existing serialized number, rather than serializing it anew. -/
def keyOfNat (number : Nat) : KeyTree :=
  keyOfLegacy (LiteralSignatureCommitment.encodeNat number) (number_legacy number)

theorem legacyPattern_keyOfNat (number : Nat) :
    legacyPattern (keyOfNat number) = LiteralSignatureCommitment.encodeNat number :=
  legacyPattern_keyOfLegacy _ _

theorem keyOfNat_injective : Function.Injective keyOfNat := by
  intro left right same
  apply LiteralSignatureCommitment.encodeNat_injective
  simpa only [legacyPattern_keyOfNat] using congrArg legacyPattern same

def encodeNatKey (number : Nat) : Pattern := encodeKey (keyOfNat number)

def decodeNatKey? (key : Pattern) : Option Nat :=
  (readKey? key).bind (fun tree => LiteralSignatureCommitment.decodeNat? (legacyPattern tree))

@[simp] theorem decodeNatKey_encodeNatKey (number : Nat) :
    decodeNatKey? (encodeNatKey number) = some number := by
  simp [decodeNatKey?, encodeNatKey, legacyPattern_keyOfNat]

def literalKey (source : Pattern) : Pattern := encodeNatKey (patternCode source)

def commitLiteral (source : Pattern) : Pattern :=
  .apply costSignatureCommitConstructorName [literalKey source]

theorem literalKey_injective : Function.Injective literalKey := by
  intro left right same
  apply patternCode_injective
  exact Option.some.inj (by
    simpa only [literalKey, decodeNatKey_encodeNatKey] using congrArg decodeNatKey? same)

theorem commitLiteral_injective : Function.Injective commitLiteral := by
  intro left right same
  apply literalKey_injective
  simpa only [commitLiteral, Pattern.apply.injEq, true_and, List.cons.injEq, and_true] using same

def canonical (theory : CIGSLT) (source : theory.CanonicalCarrier) : Pattern :=
  commitLiteral (theory.canonicalKey source).val.val

theorem canonical_eq_iff (theory : CIGSLT) (left right : theory.CanonicalCarrier) :
    canonical theory left = canonical theory right ↔ theory.canonicalEquationSetoid.r left right := by
  rw [canonical, canonical, commitLiteral_injective.eq_iff]
  rw [← Subtype.ext_iff, ← Subtype.ext_iff]
  exact theory.canonicalKey_eq_iff left right

def readSignature? : Pattern → Option Account
  | .apply constructor [] =>
      if constructor = costSignatureUnitConstructorName then some 1 else none
  | .apply constructor [key] =>
      if constructor = costSignatureCommitConstructorName then (readKey? key).map FreeMonoid.of else none
  | .apply constructor [left, right] =>
      if constructor = costSignatureProductConstructorName then
        match readSignature? left, readSignature? right with
        | some first, some second => some (first * second)
        | _, _ => none
      else none
  | _ => none
termination_by source => sizeOf source
decreasing_by
  all_goals
    simp only [Pattern.apply.sizeOf_spec, List.cons.sizeOf_spec, List.nil.sizeOf_spec]
    omega

theorem readSignature_unit :
    readSignature? (.apply costSignatureUnitConstructorName []) = some 1 := by simp [readSignature?]

theorem readSignature_product (left right : Pattern) :
    readSignature? (.apply costSignatureProductConstructorName [left, right]) =
      match readSignature? left, readSignature? right with
      | some first, some second => some (first * second)
      | _, _ => none := by simp [readSignature?]

theorem readSignature_commit (key : KeyTree) :
    readSignature? (.apply costSignatureCommitConstructorName [encodeKey key]) =
      some (FreeMonoid.of key) := by simp [readSignature?]

theorem committed_account_nonunit (key : KeyTree) : (FreeMonoid.of key : Account) ≠ 1 :=
  FreeMonoid.of_ne_one key

theorem readSignature_commitLiteral (source : Pattern) :
    readSignature? (commitLiteral source) =
      some (FreeMonoid.of (keyOfNat (patternCode source))) := by
  exact readSignature_commit _

theorem committed_accounts_injective : Function.Injective
    (fun source => (FreeMonoid.of (keyOfNat (patternCode source)) : Account)) :=
  FreeMonoid.of_injective.comp (keyOfNat_injective.comp patternCode_injective)

theorem encodeKey_syntax (key : KeyTree) : LiteralKeySyntax (encodeKey key) := by
  induction key with
  | of value => exact .leaf
  | mul left right leftIH rightIH => exact .branch leftIH rightIH

theorem literalKey_syntax (source : Pattern) : LiteralKeySyntax (literalKey source) :=
  encodeKey_syntax _

theorem commitLiteral_syntax (source : Pattern) : LiteralSignatureSyntax (commitLiteral source) :=
  .commit (literalKey_syntax source)

theorem canonical_syntax (theory : CIGSLT) (source : theory.CanonicalCarrier) :
    LiteralSignatureSyntax (canonical theory source) := commitLiteral_syntax _

theorem encodeKey_object (key : KeyTree) : isObjectPattern (encodeKey key) = true := by
  induction key <;> simp [encodeKey, isObjectPattern, isObjectPatternList, *]

theorem literalKey_object (source : Pattern) : isObjectPattern (literalKey source) = true :=
  encodeKey_object _

theorem commitLiteral_object (source : Pattern) : isObjectPattern (commitLiteral source) = true := by
  simpa [commitLiteral, isObjectPattern, isObjectPatternList] using literalKey_object source

theorem canonical_object (theory : CIGSLT) (source : theory.CanonicalCarrier) :
    isObjectPattern (canonical theory source) = true := commitLiteral_object _

variable {language : LanguageDef} {free : FreeTypeContext} {bound : List TypeExpr}

theorem keyLeaf_typed (declared : costKeyLeafConstructor ∈ language.terms) :
    HasSort language free bound (.apply costKeyLeafConstructorName []) costKeySortName := by
  apply HasType.constructor declared
  · simp [UsesBareCollection, costKeyLeafConstructor]
  · exact .nil

theorem keyBranch_typed (declared : costKeyBranchConstructor ∈ language.terms)
    {left right : Pattern} (leftTyped : HasSort language free bound left costKeySortName)
    (rightTyped : HasSort language free bound right costKeySortName) :
    HasSort language free bound (.apply costKeyBranchConstructorName [left, right]) costKeySortName := by
  apply HasType.constructor declared
  · simp [UsesBareCollection, costKeyBranchConstructor]
  · exact .cons trivial rfl leftTyped (.cons trivial rfl rightTyped .nil)

theorem encodeKey_typed
    (leafDeclared : costKeyLeafConstructor ∈ language.terms)
    (branchDeclared : costKeyBranchConstructor ∈ language.terms) (key : KeyTree) :
    HasSort language free bound (encodeKey key) costKeySortName := by
  induction key with
  | of value => exact keyLeaf_typed leafDeclared
  | mul left right leftIH rightIH => exact keyBranch_typed branchDeclared leftIH rightIH

theorem literalKey_typed
    (leafDeclared : costKeyLeafConstructor ∈ language.terms)
    (branchDeclared : costKeyBranchConstructor ∈ language.terms) (source : Pattern) :
    HasSort language free bound (literalKey source) costKeySortName :=
  encodeKey_typed leafDeclared branchDeclared _

theorem commit_typed (declared : costSignatureCommitConstructor ∈ language.terms)
    {key : Pattern} (typed : HasSort language free bound key costKeySortName) :
    HasSort language free bound (.apply costSignatureCommitConstructorName [key]) costSignatureSortName := by
  apply HasType.constructor declared
  · simp [UsesBareCollection, costSignatureCommitConstructor]
  · exact .cons trivial rfl typed .nil

theorem commitLiteral_typed
    (leafDeclared : costKeyLeafConstructor ∈ language.terms)
    (branchDeclared : costKeyBranchConstructor ∈ language.terms)
    (commitDeclared : costSignatureCommitConstructor ∈ language.terms) (source : Pattern) :
    HasSort language free bound (commitLiteral source) costSignatureSortName :=
  commit_typed commitDeclared (literalKey_typed leafDeclared branchDeclared source)

theorem canonical_typed (theory : CIGSLT) (source : theory.CanonicalCarrier)
    (leafDeclared : costKeyLeafConstructor ∈ language.terms)
    (branchDeclared : costKeyBranchConstructor ∈ language.terms)
    (commitDeclared : costSignatureCommitConstructor ∈ language.terms) :
    HasSort language free bound (canonical theory source) costSignatureSortName :=
  commitLiteral_typed leafDeclared branchDeclared commitDeclared _

mutual
theorem key_syntax_readout {key : Pattern} (shape : LiteralKeySyntax key) :
    ∃ tree, readKey? key = some tree ∧ encodeKey tree = key := by
  cases shape with
  | leaf => exact ⟨.of PUnit.unit, by simp [readKey?], rfl⟩
  | branch left right =>
      obtain ⟨first, firstFound, firstRendered⟩ := key_syntax_readout left
      obtain ⟨second, secondFound, secondRendered⟩ := key_syntax_readout right
      exact ⟨.mul first second, by simp [readKey?, firstFound, secondFound],
        by simp [encodeKey, firstRendered, secondRendered]⟩

theorem signature_syntax_readout {signature : Pattern} (shape : LiteralSignatureSyntax signature) :
    ∃ account, readSignature? signature = some account := by
  cases shape with
  | unit => exact ⟨1, readSignature_unit⟩
  | product left right =>
      obtain ⟨first, firstFound⟩ := signature_syntax_readout left
      obtain ⟨second, secondFound⟩ := signature_syntax_readout right
      exact ⟨first * second, by simp [readSignature_product, firstFound, secondFound]⟩
  | commit key =>
      obtain ⟨tree, found, _⟩ := key_syntax_readout key
      exact ⟨FreeMonoid.of tree, by simp [readSignature?, found]⟩
end

theorem readSignature_legacy {signature : Pattern} (shape : LegacyLiteralSignatureSyntax signature) :
    readSignature? signature = some 1 := by
  induction shape with
  | unit => exact readSignature_unit
  | product left right leftIH rightIH => simp [readSignature_product, leftIH, rightIH]

/-- The atom constructor does not turn the old monoid unit into an atom. -/
theorem unit_not_key :
    readKey? (.apply costSignatureUnitConstructorName []) = none := by
  have separate : costSignatureUnitConstructorName ≠ costKeyLeafConstructorName := by
    decide +kernel
  simp only [readKey?, if_neg separate]

/-- Distinct key trees give distinct nonunit accounts. -/
theorem leaf_branch_accounts_distinct :
    (FreeMonoid.of (.of PUnit.unit : KeyTree) : Account) ≠
      FreeMonoid.of (.mul (.of PUnit.unit) (.of PUnit.unit)) := by
  intro same
  have trees := FreeMonoid.of_injective same
  cases trees

end Mettapedia.GSLT.LanguageDef.Cost.AtomicSignatureInterpretation
