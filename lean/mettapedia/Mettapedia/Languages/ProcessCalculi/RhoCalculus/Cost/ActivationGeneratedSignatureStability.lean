import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGeneratedNormalization
import Mettapedia.GSLT.LanguageDef.Cost.SignatureSyntax

/-!
# Exact stability of decoder-admitted literal signature keys

The actual closed checker admits unit/product signatures and atomic
commitments to finite key trees. The wrapped quote/drop normalizer and
receiver substitution preserve every accepted literal key. This is not a
monoid quotient and does not cover arbitrary raw typing derivations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.Cost.SignatureSyntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

private theorem key_constructor_catalogue :
    rhoCIGSLT.costWholeLanguage.terms.filter (fun rule => rule.category == costKeySortName) =
      [costKeyLeafConstructor, costKeyBranchConstructor] := by
  decide +kernel

private theorem key_constructor_membership {rule : GrammarRule}
    (member : rule ∈ rhoCIGSLT.costWholeLanguage.terms)
    (category : rule.category = costKeySortName) :
    rule = costKeyLeafConstructor ∨ rule = costKeyBranchConstructor := by
  have selected : rule ∈ rhoCIGSLT.costWholeLanguage.terms.filter
      (fun rule => rule.category == costKeySortName) :=
    List.mem_filter.mpr ⟨member, beq_iff_eq.mpr category⟩
  rw [key_constructor_catalogue] at selected
  simpa using selected

private theorem signature_constructor_catalogue :
    rhoCIGSLT.costWholeLanguage.terms.filter (fun rule => rule.category == costSignatureSortName) =
      [costSignatureUnitConstructor, costSignatureProductConstructor, costSignatureCommitConstructor] := by
  decide +kernel

private theorem signature_constructor_membership {rule : GrammarRule}
    (member : rule ∈ rhoCIGSLT.costWholeLanguage.terms)
    (category : rule.category = costSignatureSortName) :
    rule = costSignatureUnitConstructor ∨ rule = costSignatureProductConstructor ∨
      rule = costSignatureCommitConstructor := by
  have selected : rule ∈ rhoCIGSLT.costWholeLanguage.terms.filter
      (fun rule => rule.category == costSignatureSortName) :=
    List.mem_filter.mpr ⟨member, beq_iff_eq.mpr category⟩
  rw [signature_constructor_catalogue] at selected
  simpa using selected

private theorem apparatus_checked_syntax (source : Pattern) :
    (checkHasType rhoCIGSLT.costWholeLanguage FreeTypeContext.empty []
      source (.base costKeySortName) = true → LiteralKeySyntax source) ∧
    (checkHasType rhoCIGSLT.costWholeLanguage FreeTypeContext.empty []
      source (.base costSignatureSortName) = true → LiteralSignatureSyntax source) := by
  induction source using Pattern.inductionOn with
  | hbvar index => constructor <;> intro checked <;> simp [checkHasType] at checked
  | hfvar name => constructor <;> intro checked <;> simp [checkHasType, FreeTypeContext.empty] at checked
  | happly constructor arguments each =>
    constructor
    · intro checked
      simp only [checkHasType, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at checked
      obtain ⟨rule, member, ⟨⟨⟨label, category⟩, _notBare⟩, argumentsChecked⟩⟩ := checked
      subst constructor
      have choices := key_constructor_membership member (TypeExpr.base.inj category.symm)
      rcases choices with rfl | rfl
      · cases arguments with
        | nil => simpa only [costKeyLeafConstructor] using LiteralKeySyntax.leaf
        | cons head tail => simp [costKeyLeafConstructor, checkArgumentsHaveTypes] at argumentsChecked
      · cases arguments with
        | nil => simp [costKeyBranchConstructor, checkArgumentsHaveTypes] at argumentsChecked
        | cons left arguments =>
          cases arguments with
          | nil => simp [costKeyBranchConstructor, checkArgumentsHaveTypes, parameterType?] at argumentsChecked
          | cons right arguments =>
            cases arguments with
            | cons extra remaining =>
              simp [costKeyBranchConstructor, checkArgumentsHaveTypes,
                parameterType?, matchesParameterRepresentation?] at argumentsChecked
            | nil =>
              simp only [costKeyBranchConstructor, checkArgumentsHaveTypes,
                parameterType?, matchesParameterRepresentation?, Bool.true_and,
                Bool.and_true, Bool.and_eq_true] at argumentsChecked
              exact .branch ((each left (by simp)).1 argumentsChecked.1)
                ((each right (by simp)).1 argumentsChecked.2)
    · intro checked
      simp only [checkHasType, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at checked
      obtain ⟨rule, member, ⟨⟨⟨label, category⟩, _notBare⟩, argumentsChecked⟩⟩ := checked
      subst constructor
      have choices := signature_constructor_membership member (TypeExpr.base.inj category.symm)
      rcases choices with rfl | rfl | rfl
      · cases arguments with
        | nil => simpa only [costSignatureUnitConstructor] using LiteralSignatureSyntax.unit
        | cons head tail => simp [costSignatureUnitConstructor, checkArgumentsHaveTypes] at argumentsChecked
      · cases arguments with
        | nil => simp [costSignatureProductConstructor, checkArgumentsHaveTypes] at argumentsChecked
        | cons left arguments =>
          cases arguments with
          | nil => simp [costSignatureProductConstructor, checkArgumentsHaveTypes, parameterType?] at argumentsChecked
          | cons right arguments =>
            cases arguments with
            | cons extra remaining =>
              simp [costSignatureProductConstructor, checkArgumentsHaveTypes,
                parameterType?, matchesParameterRepresentation?] at argumentsChecked
            | nil =>
              simp only [costSignatureProductConstructor, checkArgumentsHaveTypes,
                parameterType?, matchesParameterRepresentation?, Bool.true_and,
                Bool.and_true, Bool.and_eq_true] at argumentsChecked
              exact .product ((each left (by simp)).2 argumentsChecked.1)
                ((each right (by simp)).2 argumentsChecked.2)
      · cases arguments with
        | nil => simp [costSignatureCommitConstructor, checkArgumentsHaveTypes] at argumentsChecked
        | cons key arguments =>
          cases arguments with
          | cons extra remaining =>
            simp [costSignatureCommitConstructor, checkArgumentsHaveTypes,
              parameterType?, matchesParameterRepresentation?] at argumentsChecked
          | nil =>
            simp only [costSignatureCommitConstructor, checkArgumentsHaveTypes,
              parameterType?, matchesParameterRepresentation?, Bool.true_and,
              Bool.and_true] at argumentsChecked
            exact .commit ((each key (by simp)).1 argumentsChecked)
  | hlambda binder body each => constructor <;> intro checked <;> simp [checkHasType] at checked
  | hmultiLambda arity binders body each => constructor <;> intro checked <;> simp [checkHasType] at checked
  | hsubst body replacement eachBody eachReplacement => constructor <;> intro checked <;> simp [checkHasType] at checked
  | hcollection kind elements rest each =>
    constructor
    · intro checked
      simp only [checkHasType, Bool.false_or, Bool.and_eq_true, List.any_eq_true] at checked
      obtain ⟨_restClosed, rule, member, elementsChecked⟩ := checked
      cases selected : bareCollectionElementType? rule kind (.base costKeySortName) with
      | none => simp [selected] at elementsChecked
      | some elementType =>
        obtain ⟨category, parameter, parameters⟩ :=
          (bareCollectionElementType?_eq_some_iff _ _ _ _).mp selected
        have choices := key_constructor_membership member (TypeExpr.base.inj category.symm)
        rcases choices with rfl | rfl <;>
          simp [costKeyLeafConstructor, costKeyBranchConstructor] at parameters
    · intro checked
      simp only [checkHasType, Bool.false_or, Bool.and_eq_true, List.any_eq_true] at checked
      obtain ⟨_restClosed, rule, member, elementsChecked⟩ := checked
      cases selected : bareCollectionElementType? rule kind (.base costSignatureSortName) with
      | none => simp [selected] at elementsChecked
      | some elementType =>
        obtain ⟨category, parameter, parameters⟩ :=
          (bareCollectionElementType?_eq_some_iff _ _ _ _).mp selected
        have choices := signature_constructor_membership member (TypeExpr.base.inj category.symm)
        rcases choices with rfl | rfl | rfl <;>
          simp [costSignatureUnitConstructor, costSignatureProductConstructor,
            costSignatureCommitConstructor] at parameters

theorem key_checked_syntax {source : Pattern}
    (checked : checkHasType rhoCIGSLT.costWholeLanguage FreeTypeContext.empty []
      source (.base costKeySortName) = true) : LiteralKeySyntax source :=
  (apparatus_checked_syntax source).1 checked

theorem signature_checked_syntax {source : Pattern}
    (checked : checkHasType rhoCIGSLT.costWholeLanguage FreeTypeContext.empty []
      source (.base costSignatureSortName) = true) : LiteralSignatureSyntax source :=
  (apparatus_checked_syntax source).2 checked

theorem signature?_accepted_syntax {source : Pattern} {signature : TypedSignature source}
    (accepted : signature? source = some signature) : LiteralSignatureSyntax source := by
  unfold signature? at accepted
  split at accepted
  · exact signature_checked_syntax ‹_›
  · simp at accepted

mutual
  theorem _root_.Mettapedia.GSLT.LanguageDef.Cost.SignatureSyntax.LiteralKeySyntax.normalize_identity {source : Pattern} (grammar : LiteralKeySyntax source) :
      normalizeReflective wrappedRhoDeclaration source = source := by
    cases grammar with
    | leaf => rfl
    | branch left right =>
      change finishNormalizeReflectiveApply wrappedRhoDeclaration costKeyBranchConstructorName
        [normalizeReflective wrappedRhoDeclaration _, normalizeReflective wrappedRhoDeclaration _] = _
      rw [left.normalize_identity, right.normalize_identity]
      have apart : (costKeyBranchConstructorName == wrappedRhoDeclaration.quoteConstructor) = false := by
        decide +kernel
      simp only [finishNormalizeReflectiveApply, apart, Bool.false_eq_true, ite_false]

  theorem _root_.Mettapedia.GSLT.LanguageDef.Cost.SignatureSyntax.LiteralSignatureSyntax.normalize_identity {source : Pattern} (grammar : LiteralSignatureSyntax source) :
      normalizeReflective wrappedRhoDeclaration source = source := by
    cases grammar with
    | unit => rfl
    | product left right =>
      change finishNormalizeReflectiveApply wrappedRhoDeclaration costSignatureProductConstructorName
        [normalizeReflective wrappedRhoDeclaration _, normalizeReflective wrappedRhoDeclaration _] = _
      rw [left.normalize_identity, right.normalize_identity]
      have apart : (costSignatureProductConstructorName == wrappedRhoDeclaration.quoteConstructor) = false := by
        decide +kernel
      simp only [finishNormalizeReflectiveApply, apart, Bool.false_eq_true, ite_false]
    | commit key =>
      change finishNormalizeReflectiveApply wrappedRhoDeclaration costSignatureCommitConstructorName
        [normalizeReflective wrappedRhoDeclaration _] = _
      rw [key.normalize_identity]
      rfl
end

mutual
  theorem _root_.Mettapedia.GSLT.LanguageDef.Cost.SignatureSyntax.LiteralKeySyntax.substitute_identity {source : Pattern} (grammar : LiteralKeySyntax source)
      (depth : Nat) (replacement : Pattern) :
      substituteReflective wrappedRhoDeclaration depth replacement source = source := by
    cases grammar with
    | leaf => rfl
    | branch left right =>
      simp [substituteReflective, substituteReflectiveList,
        left.substitute_identity depth replacement, right.substitute_identity depth replacement]

  theorem _root_.Mettapedia.GSLT.LanguageDef.Cost.SignatureSyntax.LiteralSignatureSyntax.substitute_identity {source : Pattern} (grammar : LiteralSignatureSyntax source)
      (depth : Nat) (replacement : Pattern) :
      substituteReflective wrappedRhoDeclaration depth replacement source = source := by
    cases grammar with
    | unit => rfl
    | product left right =>
      simp [substituteReflective, substituteReflectiveList,
        left.substitute_identity depth replacement, right.substitute_identity depth replacement]
    | commit key =>
      have notQuote : costSignatureCommitConstructorName ≠ wrappedRhoDeclaration.quoteConstructor := by
        decide +kernel
      have notDrop : costSignatureCommitConstructorName ≠ wrappedRhoDeclaration.dropConstructor := by
        decide +kernel
      simp [substituteReflective, notQuote, notDrop, key.substitute_identity depth replacement]
end

theorem _root_.Mettapedia.GSLT.LanguageDef.Cost.SignatureSyntax.LegacyLiteralSignatureSyntax.normalize_identity {source : Pattern}
    (grammar : LegacyLiteralSignatureSyntax source) :
    normalizeReflective wrappedRhoDeclaration source = source :=
  grammar.toLiteralSignatureSyntax.normalize_identity

theorem _root_.Mettapedia.GSLT.LanguageDef.Cost.SignatureSyntax.LegacyLiteralSignatureSyntax.substitute_identity {source : Pattern}
    (grammar : LegacyLiteralSignatureSyntax source) (depth : Nat) (replacement : Pattern) :
    substituteReflective wrappedRhoDeclaration depth replacement source = source :=
  grammar.toLiteralSignatureSyntax.substitute_identity depth replacement

theorem signature?_accepted_normalization_identity {source : Pattern}
    {signature : TypedSignature source} (accepted : signature? source = some signature) :
    normalizeReflective wrappedRhoDeclaration source = source :=
  (signature?_accepted_syntax accepted).normalize_identity

theorem signature?_accepted_substitution_identity {source : Pattern}
    {signature : TypedSignature source} (accepted : signature? source = some signature)
    (depth : Nat) (replacement : Pattern) :
    substituteReflective wrappedRhoDeclaration depth replacement source = source :=
  (signature?_accepted_syntax accepted).substitute_identity depth replacement

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated
