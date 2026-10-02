import Mettapedia.GSLT.LanguageDef.Cost.AtomicSignatureInterpretation
import Mettapedia.GSLT.LanguageDef.Cost.BindingValuationAction

/-!
# Atomic signature meanings in open declaration-derived models

Key variables receive binary trees and signature variables receive ordered
key words. The five actual Key/Signature grammar rows are interpreted here;
all other authored constructors retain their independently specified algebra
data. The resulting signature model includes every declaration and structural
binding form. No inverse from arbitrary keys to source origins is used.

Signature meaning is a monoid observation, so literal product boundaries and
exact authority remain in the original syntax and its separate evidence.
Source equation satisfaction and runtime funding are not asserted here.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Cost.AtomicSignatureValuation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Binding
open BindingSyntax BindingSyntax.Valuation
open AtomicSignatureInterpretation

/-- Other sort meanings remain independent. Only the actual apparatus Key
and Signature sorts are assigned their free algebra meanings. -/
def Base (other : String → Type) (name : String) : Type :=
  if name = costKeySortName then KeyTree else
    if name = costSignatureSortName then AtomicSignatureInterpretation.Account else other name

@[simp] theorem base_key (other : String → Type) : Base other costKeySortName = KeyTree := by
  simp [Base]

@[simp] theorem base_signature (other : String → Type) :
    Base other costSignatureSortName = AtomicSignatureInterpretation.Account := by
  have different : costSignatureSortName ≠ costKeySortName := by decide
  simp only [Base, if_neg different]
  rfl

/-- Install meanings for the actual apparatus rows, without replacing the
independent interpretations of any remaining authored constructor. -/
def constructors {language : LanguageDef} {other : String → Type}
    (remaining : Constructors language (Base other)) : Constructors language (Base other) where
  ordinary := by
    intro rule member ordinary arity scopes args
    by_cases leaf : rule = costKeyLeafConstructor
    · subst rule
      cases scopes
      exact FreeMagma.of PUnit.unit
    by_cases branch : rule = costKeyBranchConstructor
    · subst rule
      cases scopes with
      | cons first rest =>
        cases first
        cases rest with
        | cons second rest =>
          cases second
          cases rest
          exact FreeMagma.mul (args.1 PUnit.unit) (args.2.1 PUnit.unit)
    by_cases unit : rule = costSignatureUnitConstructor
    · subst rule
      cases scopes
      exact (1 : AtomicSignatureInterpretation.Account)
    by_cases product : rule = costSignatureProductConstructor
    · subst rule
      cases scopes with
      | cons first rest =>
        cases first
        cases rest with
        | cons second rest =>
          cases second
          cases rest
          exact @Mul.mul AtomicSignatureInterpretation.Account inferInstance
            (args.1 PUnit.unit) (args.2.1 PUnit.unit)
    by_cases commit : rule = costSignatureCommitConstructor
    · subst rule
      cases scopes with
      | cons first rest =>
        cases first
        cases rest
        exact FreeMonoid.of (args.1 PUnit.unit)
    exact remaining.ordinary rule member ordinary scopes args
  collection := remaining.collection

abbrev keySort : TypeExpr := .base costKeySortName
abbrev signatureSort : TypeExpr := .base costSignatureSortName

/-- Actual closed and open key terms share the declaration-derived carrier. -/
def leaf {language : LanguageDef} (member : costKeyLeafConstructor ∈ language.terms)
    {Γ : List TypeExpr} : Term (signatureOf language) Γ keySort :=
  .op (.constructor costKeyLeafConstructor member
    (CostApparatusConstructor.grammarRule_notBare "" .keyLeaf) .nil) .nil

def branch {language : LanguageDef} (member : costKeyBranchConstructor ∈ language.terms)
    {Γ : List TypeExpr} (left right : Term (signatureOf language) Γ keySort) :
    Term (signatureOf language) Γ keySort :=
  .op (.constructor costKeyBranchConstructor member
    (CostApparatusConstructor.grammarRule_notBare "" .keyBranch)
    (.cons (.simple _ _) (.cons (.simple _ _) .nil)))
    (.cons left (.cons right .nil))

def unit {language : LanguageDef} (member : costSignatureUnitConstructor ∈ language.terms)
    {Γ : List TypeExpr} : Term (signatureOf language) Γ signatureSort :=
  .op (.constructor costSignatureUnitConstructor member
    (CostApparatusConstructor.grammarRule_notBare "" .signatureUnit) .nil) .nil

def product {language : LanguageDef} (member : costSignatureProductConstructor ∈ language.terms)
    {Γ : List TypeExpr} (left right : Term (signatureOf language) Γ signatureSort) :
    Term (signatureOf language) Γ signatureSort :=
  .op (.constructor costSignatureProductConstructor member
    (CostApparatusConstructor.grammarRule_notBare "" .signatureProduct)
    (.cons (.simple _ _) (.cons (.simple _ _) .nil)))
    (.cons left (.cons right .nil))

def commit {language : LanguageDef} (member : costSignatureCommitConstructor ∈ language.terms)
    {Γ : List TypeExpr} (key : Term (signatureOf language) Γ keySort) :
    Term (signatureOf language) Γ signatureSort :=
  .op (.constructor costSignatureCommitConstructor member
    (CostApparatusConstructor.grammarRule_notBare "" .signatureCommit)
    (.cons (.simple _ _) .nil)) (.cons key .nil)

theorem erase_leaf {language : LanguageDef} (member : costKeyLeafConstructor ∈ language.terms)
    {Γ : List TypeExpr} : erase (leaf (Γ := Γ) member) = encodeKey (.of PUnit.unit) := rfl

theorem erase_commit {language : LanguageDef}
    (member : costSignatureCommitConstructor ∈ language.terms) {Γ : List TypeExpr}
    (key : Term (signatureOf language) Γ keySort) :
    erase (commit member key) = .apply costSignatureCommitConstructorName [erase key] := rfl

theorem read_leaf {language : LanguageDef} {other : String → Type}
    (remaining : Constructors language (Base other))
    (member : costKeyLeafConstructor ∈ language.terms) {Γ : List TypeExpr}
    (assignment : (type : TypeExpr) → Var Γ type → Value (Base other) type) :
    read (constructors remaining) (interpret (constructors remaining) (leaf member)) assignment =
      (FreeMagma.of PUnit.unit : KeyTree) := rfl

theorem read_unit {language : LanguageDef} {other : String → Type}
    (remaining : Constructors language (Base other))
    (member : costSignatureUnitConstructor ∈ language.terms) {Γ : List TypeExpr}
    (assignment : (type : TypeExpr) → Var Γ type → Value (Base other) type) :
    read (constructors remaining) (interpret (constructors remaining) (unit member)) assignment =
      (1 : AtomicSignatureInterpretation.Account) := rfl

theorem read_commit_variable {language : LanguageDef} {other : String → Type}
    (remaining : Constructors language (Base other))
    (member : costSignatureCommitConstructor ∈ language.terms)
    (key : KeyTree) :
    readContext (constructors remaining)
        (interpret (constructors remaining) (commit member (.var .zero)))
        ((key, PUnit.unit) : Context language (Base other) [keySort]) =
      FreeMonoid.of key := rfl

theorem read_signature_variable {language : LanguageDef} {other : String → Type}
    (remaining : Constructors language (Base other))
    (word : AtomicSignatureInterpretation.Account) :
    readContext (constructors remaining)
        (interpret (constructors remaining)
          (.var .zero : Term (signatureOf language) [signatureSort] signatureSort))
        ((word, PUnit.unit) : Context language (Base other) [signatureSort]) = word := rfl

/-- The bound key remains an input to the complete signature-valued function. -/
def commitFunction {language : LanguageDef}
    (member : costSignatureCommitConstructor ∈ language.terms) :
    Term (signatureOf language) [] (.arrow keySort signatureSort) :=
  .op (.lambda keySort signatureSort) (.cons (commit member (.var .zero)) .nil)

theorem read_commitFunction {language : LanguageDef} {other : String → Type}
    (remaining : Constructors language (Base other))
    (member : costSignatureCommitConstructor ∈ language.terms) (key : KeyTree) :
    readContext (constructors remaining)
        (interpret (constructors remaining) (commitFunction member)) PUnit.unit key =
      FreeMonoid.of key := rfl

theorem commitFunction_not_constant {language : LanguageDef} {other : String → Type}
    (remaining : Constructors language (Base other))
    (member : costSignatureCommitConstructor ∈ language.terms) :
    ¬ ∃ word, ∀ key,
      readContext (constructors remaining)
        (interpret (constructors remaining) (commitFunction member)) PUnit.unit key = word := by
  rintro ⟨word, same⟩
  have first := same (FreeMagma.of PUnit.unit)
  have second := same (FreeMagma.mul (.of PUnit.unit) (.of PUnit.unit))
  rw [read_commitFunction] at first second
  have unequal : (FreeMagma.of PUnit.unit : KeyTree) ≠ .mul (.of PUnit.unit) (.of PUnit.unit) := by
    intro equality
    cases equality
  exact unequal (FreeMonoid.of_injective (first.trans second.symm))

end Mettapedia.GSLT.LanguageDef.Cost.AtomicSignatureValuation
