import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.GeneratedCollectionEquationModel
import Mettapedia.GSLT.LanguageDef.Cost.AtomicSignatureValuation

/-!
# Atomic signature readout of the generated static binding quotient

The complete generated equation quotient retains the program carrier. This
separate readout sends Key to binary trees and Signature to ordered key words;
its other base sorts have one-point observations. It therefore distinguishes
atomic signatures without claiming to retain program payloads or funding.

The readout respects both authored equation copies and every collection law
at arbitrary semantic environments. Its descended map uses the already
constructed full binding quotient. No signature monoid equations are added
to that quotient, and equality of words need not reflect literal authority.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.GeneratedAtomicSignatureReadout

open _root_.CategoryTheory
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Binding
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.GSLT.LanguageDef.BindingSyntax
open Mettapedia.GSLT.LanguageDef.BindingSyntax.CollectionEquationFamily
open Mettapedia.GSLT.LanguageDef.Cost

abbrev language := GeneratedCollectionEquationModel.language

abbrev Base := AtomicSignatureValuation.Base (fun _ => PUnit)

/-- Only the two apparatus sorts have informative values in this readout. -/
def defaultBase (category : String) : Base category := by
  by_cases key : category = costKeySortName
  · subst category
    exact FreeMagma.of PUnit.unit
  by_cases signature : category = costSignatureSortName
  · subst category
    exact (1 : AtomicSignatureInterpretation.Account)
  simpa only [Base, AtomicSignatureValuation.Base, if_neg key, if_neg signature]
    using PUnit.unit

def remaining : Valuation.Constructors language Base where
  ordinary := fun rule _ _ _ _ _ => defaultBase rule.category
  collection := fun rule _ _ _ _ _ _ => defaultBase rule.category

def constructors : Valuation.Constructors language Base :=
  AtomicSignatureValuation.constructors remaining

abbrev algebra := Valuation.algebra constructors

/-- Natural contextual values with an unobserved base result are uniquely
determined, even when their environment contains arbitrary function values. -/
theorem carrier_subsingleton (category : String)
    (notKey : category ≠ costKeySortName)
    (notSignature : category ≠ costSignatureSortName) (Γ : List TypeExpr) :
    Subsingleton (algebra.substitution.Carrier Γ (.base category)) := by
  have unique : Subsingleton (Base category) := by
    simpa only [Base, AtomicSignatureValuation.Base, if_neg notKey,
      if_neg notSignature] using (inferInstance : Subsingleton PUnit)
  constructor
  intro left right
  apply CategoricalBindingModel.Model.ElemOver.ext
  funext stage above environment
  apply ConcreteCategory.ext_apply
  intro value
  change @Eq (Base category) _ _
  exact unique.elim _ _

def bareCollection (rule : GrammarRule) : Bool :=
  match rule.params with
  | [.simple _ (.collection _ _)] => true
  | _ => false

/-- These are the entire collection-constructor inventory of this language. -/
theorem bare_inventory :
    language.terms.filter bareCollection =
      [GeneratedCollectionEquationModel.parallelRule .base,
        GeneratedCollectionEquationModel.parallelRule .wrapped] := by
  decide +kernel

theorem collection_bare {rule : GrammarRule} {kind : CollType}
    (declaration : CollectionCarrierRule language rule kind) :
    rule ∈ language.terms ∧ bareCollection rule = true := by
  obtain ⟨name, element, shape⟩ := declaration.selfSorted
  exact ⟨declaration.authored, by rw [bareCollection, shape]⟩

theorem algebra_bare {rule : GrammarRule} {kind : CollType}
    {account : CollectionAlgebra} (declaration : AlgebraRule language rule kind account) :
    rule ∈ language.terms ∧ bareCollection rule = true := by
  obtain ⟨name, shape⟩ := declaration.selfSorted
  exact ⟨declaration.authored, by rw [bareCollection, shape]⟩

theorem witness_bare {left right : Pattern}
    (witness : DerivedGeneratorWitness language left right) :
    declaringRule witness ∈ language.terms ∧ bareCollection (declaringRule witness) = true := by
  cases witness with
  | bagPerm rule first second declaration sorted permutation => exact collection_bare declaration
  | setPerm rule first second declaration sorted permutation => exact collection_bare declaration
  | setDedup rule value rest declaration sorted => exact collection_bare declaration
  | flatten rule kind account pre inner post declaration enabled sorted => exact algebra_bare declaration
  | singleton rule kind account value declaration enabled sorted => exact algebra_bare declaration
  | unitElim rule kind account unit pre post declaration selected sorted => exact algebra_bare declaration
  | emptyUnit rule kind account unit declaration selected sorted => exact algebra_bare declaration

theorem bare_category (rule : GrammarRule) (member : rule ∈ language.terms)
    (bare : bareCollection rule = true) :
    rule.category ≠ costKeySortName ∧ rule.category ≠ costSignatureSortName := by
  have filtered : rule ∈ language.terms.filter bareCollection := List.mem_filter.mpr ⟨member, bare⟩
  rw [bare_inventory] at filtered
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at filtered
  rcases filtered with rfl | rfl <;> decide +kernel

/-- The actual source and derived laws are satisfied by this readout at all
contextual inputs, not only by values obtained from decoded closed programs. -/
theorem full_contextual_satisfaction :
    BindingEquationFamilyModel.Satisfies algebra GeneratedCollectionEquationModel.family := by
  intro equation admitted Θ Γ valuation ambient ordinary
  rcases admitted with member | ⟨declaration, rfl⟩
  · simp only [GeneratedEquationPresentation.equations, List.mem_cons,
    List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl
    all_goals
      exact (carrier_subsingleton (costBaseSortName "Name") (by decide) (by decide) Γ).elim _ _
  · obtain ⟨member, bare⟩ := witness_bare declaration.witness
    obtain ⟨notKey, notSignature⟩ := bare_category _ member bare
    rw [declaration.sameCategory] at notKey notSignature
    exact (carrier_subsingleton declaration.category notKey notSignature Γ).elim _ _

/-- The informative Key/Signature readout descends from the actual generated
static quotient as a full clone map, preserving complete substitutions. -/
noncomputable def readout :
    FreeBindingClone.Hom GeneratedCollectionEquationModel.algebra algebra :=
  BindingEquationFamilyModel.interpretHom GeneratedCollectionEquationModel.family algebra
    full_contextual_satisfaction

theorem readout_project {Γ : List TypeExpr} {sort : TypeExpr}
    (term : Term (signatureOf language) Γ sort) :
    readout.raw.map (BindingEquationFamilyModel.project GeneratedCollectionEquationModel.family term) =
      Valuation.interpret constructors term := rfl

/-- The descended comparison transports all mixed-sort substitutions,
including supplied functions and account-bearing binder bodies. -/
theorem readout_substitute {Γ Δ : List TypeExpr} {sort : TypeExpr}
    (environment : BindingSubstitutionAlgebra.Environment (signatureOf language)
      GeneratedCollectionEquationModel.algebra.substitution.Carrier Γ Δ)
    (value : GeneratedCollectionEquationModel.algebra.substitution.Carrier Γ sort) :
    readout.raw.map (GeneratedCollectionEquationModel.algebra.substitution.substitute
        environment value) =
      algebra.substitution.substitute (fun type position => readout.raw.map
        (environment type position)) (readout.raw.map value) :=
  readout.map_substitute environment value

def commitFunction : Term (signatureOf language) []
    (.arrow AtomicSignatureValuation.keySort AtomicSignatureValuation.signatureSort) :=
  AtomicSignatureValuation.commitFunction (by decide +kernel)

noncomputable def functionWord (key : AtomicSignatureInterpretation.KeyTree) :
    AtomicSignatureInterpretation.Account :=
  Valuation.readContext constructors (readout.raw.map
    (BindingEquationFamilyModel.project GeneratedCollectionEquationModel.family commitFunction))
    PUnit.unit key

/-- This actual equation-class function keeps the bound key as an input. -/
theorem functionWord_eq (key : AtomicSignatureInterpretation.KeyTree) :
    functionWord key = FreeMonoid.of key := rfl

/-- A binder-dependent annotation cannot be replaced by one outer word. -/
theorem functionWord_not_constant : ¬ ∃ word, ∀ key, functionWord key = word := by
  rintro ⟨word, same⟩
  have first := same (FreeMagma.of PUnit.unit)
  have second := same (FreeMagma.mul (.of PUnit.unit) (.of PUnit.unit))
  rw [functionWord_eq] at first second
  have impossible := FreeMonoid.of_injective (first.trans second.symm)
  cases impossible

def leaf : Term (signatureOf language) [] AtomicSignatureValuation.keySort :=
  AtomicSignatureValuation.leaf (by decide +kernel)

def branch : Term (signatureOf language) [] AtomicSignatureValuation.keySort :=
  AtomicSignatureValuation.branch (by decide +kernel) leaf leaf

def atom : Term (signatureOf language) [] AtomicSignatureValuation.signatureSort :=
  AtomicSignatureValuation.commit (by decide +kernel) leaf

def otherAtom : Term (signatureOf language) [] AtomicSignatureValuation.signatureSort :=
  AtomicSignatureValuation.commit (by decide +kernel) branch

def unit : Term (signatureOf language) [] AtomicSignatureValuation.signatureSort :=
  AtomicSignatureValuation.unit (by decide +kernel)

def unitProduct : Term (signatureOf language) [] AtomicSignatureValuation.signatureSort :=
  AtomicSignatureValuation.product (by decide +kernel) unit unit

def closedAssignment : (sort : TypeExpr) → Var [] sort → Valuation.Value Base sort :=
  fun _ position => nomatch position

noncomputable def word (value : GeneratedCollectionEquationModel.algebra.substitution.Carrier []
    AtomicSignatureValuation.signatureSort) : AtomicSignatureInterpretation.Account :=
  Valuation.read constructors (readout.raw.map value) closedAssignment

theorem atom_word :
    word (BindingEquationFamilyModel.project GeneratedCollectionEquationModel.family atom) =
      FreeMonoid.of (FreeMagma.of PUnit.unit) := rfl

theorem other_atom_word :
    word (BindingEquationFamilyModel.project GeneratedCollectionEquationModel.family otherAtom) =
      FreeMonoid.of (FreeMagma.mul (FreeMagma.of PUnit.unit) (FreeMagma.of PUnit.unit)) := rfl

theorem unit_word :
    word (BindingEquationFamilyModel.project GeneratedCollectionEquationModel.family unit) = 1 := rfl

/-- The atomic account interpretation is nontrivial on the actual generated
quotient, rather than a one-point or all-unit signature model. -/
theorem atom_not_unit :
    BindingEquationFamilyModel.project GeneratedCollectionEquationModel.family atom ≠
      BindingEquationFamilyModel.project GeneratedCollectionEquationModel.family unit := by
  intro same
  have impossible := congrArg (fun value => (word value).toList.length) same
  change 1 = 0 at impossible
  contradiction

/-- Distinct actual binary keys give different account classes. -/
theorem distinct_atoms :
    BindingEquationFamilyModel.project GeneratedCollectionEquationModel.family atom ≠
      BindingEquationFamilyModel.project GeneratedCollectionEquationModel.family otherAtom := by
  intro same
  have impossible := FreeMonoid.of_injective (congrArg word same)
  cases impossible

/-- Unit/product literal boundaries remain visible in retained raw syntax,
although the monoid word readout forgets them. No quotient equality is claimed. -/
theorem unit_boundaries_not_reflected :
    erase unit ≠ erase unitProduct ∧
      word (BindingEquationFamilyModel.project GeneratedCollectionEquationModel.family unit) =
        word (BindingEquationFamilyModel.project GeneratedCollectionEquationModel.family unitProduct) := by
  constructor
  · decide +kernel
  · rfl

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.GeneratedAtomicSignatureReadout
