import Mettapedia.GSLT.LanguageDef.Cost.SemanticAccountValuation
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.GeneratedAtomicSignatureReadout
import Mettapedia.GSLT.LanguageDef.BindingCollectionEquationGenerators
import Mathlib.Data.Multiset.MapFold

/-!
# An occurrence account comparison on the actual generated rho signature

Key and Signature retain their binary-tree and ordered-word meanings. Base
and wrapped processes receive multisets of ordered words. Parallel composition
combines occurrences, while Signed and semantic Mark prependWord each occurrence's
word. Every original binding operator remains in the full valuation model.
The actual base output constructor supplies a nonempty occurrence; the
parallel unit remains empty.

This is an independently specified account comparison, not a faithful program
payload model. In particular Name has a one-point observation. Literal runtime
authority, retained source origins and funding remain separate evidence.
Descent through all raw-erasure-selected collection axioms is a further proof
obligation; the semantic account laws do not establish that descent.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.SemanticAccountOccurrenceModel

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Binding
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.BindingSyntax
open Mettapedia.GSLT.LanguageDef.Cost
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open _root_.CategoryTheory

abbrev language := GeneratedCollectionEquationModel.language
abbrev Account := AtomicSignatureInterpretation.Account
abbrev Occurrences := Multiset Account

/-- The word in each occurrence preserves sequential order. -/
def prependWord (account : Account) (values : Occurrences) : Occurrences :=
  values.map (fun value => account * value)

theorem prefix_one (values : Occurrences) : prependWord 1 values = values := by
  simp [prependWord]

theorem prefix_mul (first second : Account) (values : Occurrences) :
    prependWord (first * second) values = prependWord first (prependWord second values) := by
  simp only [prependWord, Multiset.map_map, Function.comp_def, mul_assoc]

theorem prefix_add (account : Account) (first second : Occurrences) :
    prependWord account (first + second) = prependWord account first + prependWord account second :=
  Multiset.map_add _ _ _

theorem prefix_singleton (account value : Account) :
    prependWord account {value} = {account * value} := by simp [prependWord]

abbrev Other (name : String) : Type :=
  if name = costBaseSortName "Proc" ∨ name = costWrappedSortName then Occurrences else PUnit

abbrev Base := AtomicSignatureValuation.Base Other

def defaultBase (name : String) : Base name := by
  by_cases key : name = costKeySortName
  · subst name
    exact FreeMagma.of PUnit.unit
  by_cases signature : name = costSignatureSortName
  · subst name
    exact (1 : Account)
  simp only [Base, AtomicSignatureValuation.Base, if_neg key, if_neg signature]
  unfold Other
  split
  · exact 0
  · exact PUnit.unit

/-- Constructor meanings are specified before the equation quotient. -/
def remaining : Valuation.Constructors language Base where
  ordinary := by
    intro rule member ordinary arity scopes args
    by_cases signed : rule = costSignedConstructor "Proc"
    · subst rule
      cases scopes with
      | cons first rest =>
        cases first
        cases rest with
        | cons second rest =>
          cases second
          cases rest
          exact prependWord (args.2.1 PUnit.unit) (args.1 PUnit.unit)
    by_cases output : rule = costBaseConstructor rhoCIGSLT.cut rhoCalc.terms[4]
    · subst rule
      exact ({1} : Occurrences)
    exact defaultBase rule.category
  collection := by
    intro rule member parameter kind element shape values
    by_cases base : rule = GeneratedCollectionEquationModel.parallelRule .base
    · subst rule
      have elements : element = .base (costBaseSortName "Proc") := by
        have types := congrArg (fun parameters => parameters.head?.map fun parameter =>
          match parameter with
          | .simple _ type => some type
          | _ => none) shape
        simp only [GeneratedCollectionEquationModel.parallelRule,
          costBaseConstructor_def, List.head?_cons, Option.map_some] at types
        cases types
        rfl
      subst element
      change List Occurrences at values
      change Occurrences
      exact values.sum
    by_cases wrapped : rule = GeneratedCollectionEquationModel.parallelRule .wrapped
    · subst rule
      have elements : element = .base costWrappedSortName := by
        have types := congrArg (fun parameters => parameters.head?.map fun parameter =>
          match parameter with
          | .simple _ type => some type
          | _ => none) shape
        simp only [GeneratedCollectionEquationModel.parallelRule,
          costWrappedConstructor, List.head?_cons, Option.map_some] at types
        cases types
        rfl
      subst element
      change List Occurrences at values
      change Occurrences
      exact values.sum
    exact defaultBase rule.category

def constructors : Valuation.Constructors language Base :=
  AtomicSignatureValuation.constructors remaining

abbrev signatureSort : TypeExpr := .base costSignatureSortName
abbrev baseSort : TypeExpr := .base (costBaseSortName "Proc")
abbrev wrappedSort : TypeExpr := .base costWrappedSortName

def apparatus : SemanticAccountSignature.Apparatus (signatureOf language)
    signatureSort baseSort wrappedSort where
  unit := .constructor costSignatureUnitConstructor (by decide +kernel)
    (CostApparatusConstructor.grammarRule_notBare "" .signatureUnit) .nil
  unitArity := rfl
  product := .constructor costSignatureProductConstructor (by decide +kernel)
    (CostApparatusConstructor.grammarRule_notBare "" .signatureProduct)
    (.cons (.simple _ _) (.cons (.simple _ _) .nil))
  productArity := rfl
  signed := .constructor (costSignedConstructor "Proc") (by decide +kernel)
    (CostApparatusConstructor.grammarRule_notBare "Proc" .signed)
    (.cons (.simple _ _) (.cons (.simple _ _) .nil))
  signedArity := rfl

abbrev signature := SemanticAccountValuation.signature (language := language)
  signatureSort wrappedSort

abbrev markMeaning : Valuation.Value Base signatureSort → Valuation.Value Base wrappedSort →
    Valuation.Value Base wrappedSort := prependWord

abbrev algebra := SemanticAccountValuation.algebra constructors signatureSort wrappedSort markMeaning

abbrev read {Γ : List TypeExpr} {sort : TypeExpr}
    (value : algebra.substitution.Carrier Γ sort)
    (assignment : (type : TypeExpr) → Var Γ type → Valuation.Value Base type) :=
  SemanticAccountValuation.read constructors signatureSort wrappedSort markMeaning value assignment

def processRead (color : CostStaticColor) :
    Valuation.Value Base (.base (GeneratedCollectionEquationModel.parallelRule color).category) →
      Occurrences := by
  cases color <;> exact fun value => value

def parallelOperation (color : CostStaticColor) (count : Nat) :
    signature.Op (.base (GeneratedCollectionEquationModel.parallelRule color).category) :=
  .inl (.collectionConstructor (GeneratedCollectionEquationModel.parallelRule color)
    (GeneratedCollectionEquationModel.parallel_member color) "ps" .hashBag
    (.base (GeneratedCollectionEquationModel.parallelRule color).category)
    (GeneratedCollectionEquationModel.parallel_shape color) count)

/-- Actual generated parallel operators preserve each supplied occurrence,
including accounts carried by arbitrary contextual values. -/
theorem parallel_value (color : CostStaticColor) {Γ : List TypeExpr}
    (values : List (algebra.substitution.Carrier Γ
      (.base (GeneratedCollectionEquationModel.parallelRule color).category)))
    (stage : Type) (above : stage ⟶ PUnit)
    (environment : (SemanticAccountValuation.model constructors signatureSort wrappedSort markMeaning).Env
      stage Γ) (point : stage) :
    processRead color ((algebra.operation (parallelOperation color values.length)
      (SemanticAccountValuation.homogeneousArguments constructors signatureSort wrappedSort markMeaning
        values)).value stage above environment point) =
      (values.map (fun value => processRead color (value.value stage above environment point))).sum := by
  cases color
  all_goals
    have complete := SemanticAccountValuation.listArguments_tuple constructors signatureSort wrappedSort
      markMeaning values stage above environment point
    exact congrArg (fun inputs : List Occurrences => inputs.sum) complete

theorem unit_value {Γ : List TypeExpr} (stage : Type) (above : stage ⟶ PUnit)
    (environment : (SemanticAccountValuation.model constructors signatureSort wrappedSort markMeaning).Env
      stage Γ) (point : stage) :
    (algebra.operation (.inl apparatus.unit) .nil).value stage above environment point =
      (1 : Account) := rfl

theorem product_value {Γ : List TypeExpr}
    (first second : algebra.substitution.Carrier Γ signatureSort)
    (stage : Type) (above : stage ⟶ PUnit)
    (environment : (SemanticAccountValuation.model constructors signatureSort wrappedSort markMeaning).Env
      stage Γ) (point : stage) :
    (algebra.operation (.inl apparatus.product) (.cons first (.cons second .nil))).value
      stage above environment point =
        @Mul.mul Account inferInstance
          (first.value stage above environment point) (second.value stage above environment point) := by
  exact congrArg₂ ((· * ·) : Account → Account → Account)
    (congrArg (fun f => f (PUnit.unit, point))
      (first.natural (TypeCat.ofHom (Prod.snd : PUnit × stage → stage)) above environment))
    (congrArg (fun f => f (PUnit.unit, point))
      (second.natural (TypeCat.ofHom (Prod.snd : PUnit × stage → stage)) above environment))

theorem signed_value {Γ : List TypeExpr}
    (body : algebra.substitution.Carrier Γ baseSort)
    (account : algebra.substitution.Carrier Γ signatureSort)
    (stage : Type) (above : stage ⟶ PUnit)
    (environment : (SemanticAccountValuation.model constructors signatureSort wrappedSort markMeaning).Env
      stage Γ) (point : stage) :
    (algebra.operation (.inl apparatus.signed) (.cons body (.cons account .nil))).value
      stage above environment point =
        prependWord (account.value stage above environment point)
          (body.value stage above environment point) := by
  exact congrArg₂ prependWord
    (congrArg (fun f => f (PUnit.unit, point))
      (account.natural (TypeCat.ofHom (Prod.snd : PUnit × stage → stage)) above environment))
    (congrArg (fun f => f (PUnit.unit, point))
      (body.natural (TypeCat.ofHom (Prod.snd : PUnit × stage → stage)) above environment))

theorem mark_value {Γ : List TypeExpr}
    (account : algebra.substitution.Carrier Γ signatureSort)
    (body : algebra.substitution.Carrier Γ wrappedSort)
    (stage : Type) (above : stage ⟶ PUnit)
    (environment : (SemanticAccountValuation.model constructors signatureSort wrappedSort markMeaning).Env
      stage Γ) (point : stage) :
    (algebra.operation (.inr (.mk ⟨0, by decide⟩)) (.cons account (.cons body .nil))).value
      stage above environment point =
        prependWord (account.value stage above environment point)
          (body.value stage above environment point) := by
  exact congrArg₂ prependWord
    (congrArg (fun f => f (PUnit.unit, point))
      (account.natural (TypeCat.ofHom (Prod.snd : PUnit × stage → stage)) above environment))
    (congrArg (fun f => f (PUnit.unit, point))
      (body.natural (TypeCat.ofHom (Prod.snd : PUnit × stage → stage)) above environment))

def unitElement {Γ : List TypeExpr} : algebra.substitution.Carrier Γ signatureSort :=
  algebra.operation (.inl apparatus.unit) .nil

def productElement {Γ : List TypeExpr}
    (first second : algebra.substitution.Carrier Γ signatureSort) :
    algebra.substitution.Carrier Γ signatureSort :=
  algebra.operation (.inl apparatus.product) (.cons first (.cons second .nil))

def signedElement {Γ : List TypeExpr}
    (account : algebra.substitution.Carrier Γ signatureSort)
    (body : algebra.substitution.Carrier Γ baseSort) :
    algebra.substitution.Carrier Γ wrappedSort :=
  algebra.operation (.inl apparatus.signed) (.cons body (.cons account .nil))

def markElement {Γ : List TypeExpr}
    (account : algebra.substitution.Carrier Γ signatureSort)
    (body : algebra.substitution.Carrier Γ wrappedSort) :
    algebra.substitution.Carrier Γ wrappedSort :=
  algebra.operation (.inr (.mk ⟨0, by decide⟩)) (.cons account (.cons body .nil))

/-- The six account equations hold on arbitrary genuine contextual values,
including function values in both independent environments. This does not
assert descent through the additional source/collection equation family. -/
theorem full_account_laws : BindingEquationFamilyModel.Satisfies algebra
    (fun equation => equation ∈ SemanticAccountSignature.laws apparatus) := by
  intro equation member Θ Γ valuation ambient ordinary
  simp only [SemanticAccountSignature.laws, List.mem_cons, List.mem_nil_iff, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    dsimp only [SemanticAccountSignature.markUnit, SemanticAccountSignature.markProduct,
      SemanticAccountSignature.signedAccount, SemanticAccountSignature.unitLeft,
      SemanticAccountSignature.unitRight, SemanticAccountSignature.productAssociative,
      SemanticAccountSignature.equation] at ordinary ⊢
    apply CategoricalBindingModel.Model.ElemOver.ext
    funext stage above environment
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext point
  · change (markElement unitElement (ordinary wrappedSort .zero)).value
      stage above environment point = (ordinary wrappedSort .zero).value stage above environment point
    unfold markElement unitElement
    rw [mark_value, unit_value]
    exact prefix_one ((ordinary wrappedSort .zero).value stage above environment point)
  · change (markElement (productElement (ordinary signatureSort .zero)
      (ordinary signatureSort (.succ .zero))) (ordinary wrappedSort (.succ (.succ .zero)))).value
      stage above environment point =
      (markElement (ordinary signatureSort .zero)
        (markElement (ordinary signatureSort (.succ .zero))
          (ordinary wrappedSort (.succ (.succ .zero))))).value stage above environment point
    unfold markElement productElement
    rw [mark_value, mark_value, mark_value, product_value]
    exact prefix_mul ((ordinary signatureSort .zero).value stage above environment point)
      ((ordinary signatureSort (.succ .zero)).value stage above environment point)
      ((ordinary wrappedSort (.succ (.succ .zero))).value stage above environment point)
  · change (signedElement (ordinary signatureSort .zero) (ordinary baseSort (.succ .zero))).value
      stage above environment point =
      (markElement (ordinary signatureSort .zero)
        (signedElement unitElement (ordinary baseSort (.succ .zero)))).value stage above environment point
    unfold signedElement markElement unitElement
    rw [signed_value, mark_value, signed_value, unit_value]
    exact (congrArg (prependWord ((ordinary signatureSort .zero).value stage above environment point))
      (prefix_one ((ordinary baseSort (.succ .zero)).value stage above environment point))).symm
  · change (productElement unitElement (ordinary signatureSort .zero)).value
      stage above environment point = (ordinary signatureSort .zero).value stage above environment point
    unfold productElement unitElement
    rw [product_value, unit_value]
    exact @one_mul Account inferInstance ((ordinary signatureSort .zero).value stage above environment point)
  · change (productElement (ordinary signatureSort .zero) unitElement).value
      stage above environment point = (ordinary signatureSort .zero).value stage above environment point
    unfold productElement unitElement
    rw [product_value, unit_value]
    exact @mul_one Account inferInstance ((ordinary signatureSort .zero).value stage above environment point)
  · change (productElement (productElement (ordinary signatureSort .zero)
      (ordinary signatureSort (.succ .zero))) (ordinary signatureSort (.succ (.succ .zero)))).value
      stage above environment point =
      (productElement (ordinary signatureSort .zero)
        (productElement (ordinary signatureSort (.succ .zero))
          (ordinary signatureSort (.succ (.succ .zero))))).value stage above environment point
    unfold productElement
    rw [product_value, product_value, product_value, product_value]
    exact @mul_assoc Account inferInstance
      ((ordinary signatureSort .zero).value stage above environment point)
      ((ordinary signatureSort (.succ .zero)).value stage above environment point)
      ((ordinary signatureSort (.succ (.succ .zero))).value stage above environment point)

/-- A seed stands for a supplied process occurrence, rather than identifying
the source process carrier with its account observation. -/
def seed : Occurrences := {1}

def firstAtom : Account := FreeMonoid.of (FreeMagma.of PUnit.unit)
def secondAtom : Account :=
  FreeMonoid.of (FreeMagma.mul (.of PUnit.unit) (.of PUnit.unit))

theorem prefix_nontrivial : prependWord firstAtom seed ≠ seed := by
  intro same
  have words : firstAtom * 1 = 1 := Multiset.singleton_inj.mp
    ((prefix_singleton firstAtom 1).symm.trans same)
  have lengths := congrArg (fun word : Account => word.toList.length) words
  change 1 = 0 at lengths
  contradiction

theorem prefix_order_matters :
    prependWord firstAtom (prependWord secondAtom seed) ≠ prependWord secondAtom (prependWord firstAtom seed) := by
  intro same
  have words : firstAtom * (secondAtom * 1) = secondAtom * (firstAtom * 1) := by
    apply Multiset.singleton_inj.mp
    simpa only [seed, prefix_singleton] using same
  have lists := congrArg (fun word : Account => word.toList) words
  change [FreeMagma.of PUnit.unit,
    FreeMagma.mul (.of PUnit.unit) (.of PUnit.unit)] =
    [FreeMagma.mul (.of PUnit.unit) (.of PUnit.unit), FreeMagma.of PUnit.unit] at lists
  have impossible := List.cons.inj lists
  cases impossible.1

/-- Spatial collection symmetry does not erase order within an occurrence. -/
theorem parallel_occurrence_symmetry :
    prependWord firstAtom seed + prependWord secondAtom seed =
      prependWord secondAtom seed + prependWord firstAtom seed := add_comm _ _

theorem prefix_preserves_multiplicity (account : Account) (values : Occurrences) :
    (prependWord account values).card = values.card := Multiset.card_map _ _

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.SemanticAccountOccurrenceModel
