import Mathlib.Data.List.Perm.Basic
import Mettapedia.GSLT.LanguageDef.CalculusLanguageExtension

/-!
# Constructor-order permutation of flat calculus languages

Incremental generation may retain chronological constructor order while a
batch specification groups constructor families.  Those artifacts are not
equal, and order-sensitive observations must keep them distinct.  This file
defines the narrower evidence relation that changes only constructor-row
order while preserving every other flat-calculus coordinate.

For languages without equations or rewrites, structural validation is
invariant under this relation.  The restriction is explicit because dynamic
schemas may inspect the constructor namespace through additional proof
obligations; they are not silently transported here.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax

/-- Two flat calculus languages differ only by constructor-row order. -/
structure ConstructorPermutation
    (first second : CalculusLanguageDef) : Prop where
  name : first.name = second.name
  types : first.types = second.types
  terms : first.terms.Perm second.terms
  equations : first.equations = second.equations
  rewrites : first.rewrites = second.rewrites
  judgments : first.judgments = second.judgments
  rules : first.rules = second.rules
  conversion : first.conversion = second.conversion

namespace ConstructorPermutation

/-- Constructor permutation is reflexive. -/
theorem refl (definition : CalculusLanguageDef) :
    ConstructorPermutation definition definition where
  name := rfl
  types := rfl
  terms := .refl _
  equations := rfl
  rewrites := rfl
  judgments := rfl
  rules := rfl
  conversion := rfl

/-- Constructor permutation is symmetric. -/
theorem symm {first second : CalculusLanguageDef}
    (permutation : ConstructorPermutation first second) :
    ConstructorPermutation second first where
  name := permutation.name.symm
  types := permutation.types.symm
  terms := permutation.terms.symm
  equations := permutation.equations.symm
  rewrites := permutation.rewrites.symm
  judgments := permutation.judgments.symm
  rules := permutation.rules.symm
  conversion := permutation.conversion.symm

/-- Constructor permutation is transitive. -/
theorem trans {first second third : CalculusLanguageDef}
    (earlier : ConstructorPermutation first second)
    (later : ConstructorPermutation second third) :
    ConstructorPermutation first third where
  name := earlier.name.trans later.name
  types := earlier.types.trans later.types
  terms := earlier.terms.trans later.terms
  equations := earlier.equations.trans later.equations
  rewrites := earlier.rewrites.trans later.rewrites
  judgments := earlier.judgments.trans later.judgments
  rules := earlier.rules.trans later.rules
  conversion := earlier.conversion.trans later.conversion

/-- Applying the same ordered extension to both sides preserves constructor
permutation.  New constructor rows remain a shared suffix. -/
theorem apply_extension {first second : CalculusLanguageDef}
    (permutation : ConstructorPermutation first second)
    (extension : CalculusLanguageExtension) :
    ConstructorPermutation (extension.apply first) (extension.apply second) where
  name := by simp [CalculusLanguageExtension.apply, permutation.name]
  types := by simp [CalculusLanguageExtension.apply, permutation.types]
  terms := permutation.terms.append_right extension.newTerms
  equations := by
    simp [CalculusLanguageExtension.apply, permutation.equations]
  rewrites := by
    simp [CalculusLanguageExtension.apply, permutation.rewrites]
  judgments := by
    simp [CalculusLanguageExtension.apply, permutation.judgments]
  rules := by simp [CalculusLanguageExtension.apply, permutation.rules]
  conversion := permutation.conversion

/-- Constructor permutation preserves the carrier-name environment exactly. -/
theorem typeNames_eq {first second : CalculusLanguageDef}
    (permutation : ConstructorPermutation first second) :
    first.toLanguageDef.typeNames = second.toLanguageDef.typeNames := by
  simp [LanguageDef.typeNames, permutation.types]

private theorem validateTerm_eq_of_typeNames
    (first second : LanguageDef) (term : GrammarRule)
    (typeNames : first.typeNames = second.typeNames) :
    LanguageDef.validateTerm first term =
      LanguageDef.validateTerm second term := by
  unfold LanguageDef.validateTerm
  rw [typeNames]

/-- Reordering constructor rows preserves structural validity for a
constructor-signature-only flat language. -/
theorem target_validate_of_constructorOnly
    {first second : CalculusLanguageDef}
    (permutation : ConstructorPermutation first second)
    (firstEquations : first.equations = [])
    (firstRewrites : first.rewrites = [])
    (firstValid : first.toLanguageDef.validate = []) :
    second.toLanguageDef.validate = [] := by
  have typeNames :
      first.toLanguageDef.typeNames = second.toLanguageDef.typeNames :=
    permutation.typeNames_eq
  have secondEquations : second.equations = [] := by
    rw [← permutation.equations, firstEquations]
  have secondRewrites : second.rewrites = [] := by
    rw [← permutation.rewrites, firstRewrites]
  apply LanguageDef.validate_eq_nil_of_rows
  · rw [← typeNames]
    exact LanguageDef.typeNames_nodup_of_validate_eq_nil
      first.toLanguageDef firstValid
  · exact ((permutation.terms.map (·.label)).nodup_iff).mp
      (LanguageDef.constructorLabels_nodup_of_validate_eq_nil
        first.toLanguageDef firstValid)
  · simp [secondEquations]
  · simp [secondRewrites]
  · intro term membership
    have firstMembership : term ∈ first.terms :=
      permutation.terms.mem_iff.mpr membership
    rw [validateTerm_eq_of_typeNames second.toLanguageDef
      first.toLanguageDef term typeNames.symm]
    exact LanguageDef.validateTerm_eq_nil_of_validate_eq_nil
      first.toLanguageDef firstValid term firstMembership
  · intro equation membership
    simp [secondEquations] at membership
  · intro rewrite membership
    simp [secondRewrites] at membership

/-! ## Positive and negative controls -/

namespace Canary

private def carrier : TypeDecl :=
  TypeDecl.plain "constructor-permutation:T"

private def firstTerm : GrammarRule where
  label := "constructor-permutation:first"
  category := carrier.name
  params := []
  syntaxPattern := []

private def secondTerm : GrammarRule where
  label := "constructor-permutation:second"
  category := carrier.name
  params := []
  syntaxPattern := []

private def authored : CalculusLanguageDef where
  name := "constructor-permutation"
  types := [carrier]
  terms := [firstTerm, secondTerm]
  equations := []
  rewrites := []

private def reordered : CalculusLanguageDef where
  name := "constructor-permutation"
  types := [carrier]
  terms := [secondTerm, firstTerm]
  equations := []
  rewrites := []

private theorem authored_valid : authored.toLanguageDef.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorOnly <;>
    simp [authored, carrier, firstTerm, secondTerm, TypeDecl.plain,
      LanguageDef.typeNames]

private theorem reorderedRows :
    ConstructorPermutation authored reordered where
  name := rfl
  types := rfl
  terms := List.Perm.swap secondTerm firstTerm []
  equations := rfl
  rewrites := rfl
  judgments := rfl
  rules := rfl
  conversion := rfl

/-- A genuine row permutation retains structural validity. -/
theorem reordered_valid : reordered.toLanguageDef.validate = [] :=
  reorderedRows.target_validate_of_constructorOnly rfl rfl authored_valid

private def dropped : CalculusLanguageDef where
  name := "constructor-permutation"
  types := [carrier]
  terms := [firstTerm]
  equations := []
  rewrites := []

/-- Dropping a constructor is not mislabeled as an order permutation. -/
theorem dropped_constructor_not_permutation :
    ¬ ConstructorPermutation authored dropped := by
  intro permutation
  have lengths := permutation.terms.length_eq
  simp [authored, dropped] at lengths

end Canary

#print axioms refl
#print axioms symm
#print axioms trans
#print axioms apply_extension
#print axioms target_validate_of_constructorOnly
#print axioms Canary.reordered_valid
#print axioms Canary.dropped_constructor_not_permutation

end ConstructorPermutation

end Mettapedia.GSLT.LanguageDef
