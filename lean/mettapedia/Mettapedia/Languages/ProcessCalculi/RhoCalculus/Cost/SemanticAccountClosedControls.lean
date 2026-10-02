import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.SemanticAccountOccurrenceModel

/-!
# Closed generated processes with observable occurrence accounts

An actual closed generated output supplies a process occurrence. Signing it
by the unit leaves its observation unchanged; committing an actual key adds
one ordered account atom. Semantic Mark keeps the chronological order of two
different atoms. These are native account observations, not purse authority
or executable funding claims.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.SemanticAccountClosedControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.FreeBindingTerms
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.BindingSyntax
open Mettapedia.GSLT.LanguageDef.Cost
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open SemanticAccountOccurrenceModel
open _root_.CategoryTheory

def baseZero : Term (signatureOf language) [] baseSort :=
  CollectionEquationFamily.nullary (GeneratedCollectionEquationModel.unitRule .base)
    (GeneratedCollectionEquationModel.unit_member .base) rfl

def wrappedZero : Term (signatureOf language) [] wrappedSort :=
  CollectionEquationFamily.nullary (GeneratedCollectionEquationModel.unitRule .wrapped)
    (GeneratedCollectionEquationModel.unit_member .wrapped) rfl

theorem quote_shape : (costBaseConstructor rhoCIGSLT.cut rhoCalc.terms[2]).params =
    [.simple "p" baseSort] := by
  decide +kernel

theorem output_shape : (costBaseConstructor rhoCIGSLT.cut rhoCalc.terms[4]).params =
    [.simple "n" (.base (costBaseSortName "Name")), .simple "q" wrappedSort] := by
  decide +kernel

def quotedZero : Term (signatureOf language) [] (.base (costBaseSortName "Name")) :=
  .op (.constructor (costBaseConstructor rhoCIGSLT.cut rhoCalc.terms[2]) (by decide +kernel)
    (by rw [WellSorted.UsesBareCollection, quote_shape]
        simp [baseSort])
    (by rw [quote_shape]
        exact .cons (.simple _ _) .nil)) (.cons baseZero .nil)

/-- The real generated output uses a wrapped continuation payload. -/
def outputOperator : (signatureOf language).Op baseSort :=
  .constructor (costBaseConstructor rhoCIGSLT.cut rhoCalc.terms[4]) (by decide +kernel)
    (by rw [WellSorted.UsesBareCollection, output_shape]
        simp)
    (by rw [output_shape]
        exact .cons (.simple _ _) (.cons (.simple _ _) .nil))

def outputArguments : Args (signatureOf language) ((signatureOf language).arity outputOperator) [] :=
  .cons quotedZero (.cons wrappedZero .nil)

def output : Term (signatureOf language) [] baseSort := .op outputOperator outputArguments

def firstSignature : Term (signatureOf language) [] signatureSort :=
  AtomicSignatureValuation.commit (by decide +kernel)
    (AtomicSignatureValuation.leaf (by decide +kernel))

def secondSignature : Term (signatureOf language) [] signatureSort :=
  AtomicSignatureValuation.commit (by decide +kernel)
    (AtomicSignatureValuation.branch (by decide +kernel)
      (AtomicSignatureValuation.leaf (by decide +kernel))
      (AtomicSignatureValuation.leaf (by decide +kernel)))

def returned : Term signature [] wrappedSort :=
  .op (.inl apparatus.signed) (.cons (SemanticAccountSignature.embedOriginal output)
    (.cons (.op (.inl apparatus.unit) .nil) .nil))

def signedFirst : Term signature [] wrappedSort :=
  .op (.inl apparatus.signed) (.cons (SemanticAccountSignature.embedOriginal output)
    (.cons (SemanticAccountSignature.embedOriginal firstSignature) .nil))

def marked (account : Term (signatureOf language) [] signatureSort)
    (body : Term signature [] wrappedSort) : Term signature [] wrappedSort :=
  SemanticAccountSignature.mark (SemanticAccountSignature.embedOriginal account) body

def emptyAssignment (sort : TypeExpr) (position : Var [] sort) : Valuation.Value Base sort :=
  nomatch position

abbrev observe {sort : TypeExpr} (term : Term signature [] sort) : Valuation.Value Base sort :=
  read (BindingCloneFoldSubstitution.interpret algebra term) emptyAssignment

theorem first_observation : observe (SemanticAccountSignature.embedOriginal firstSignature) = firstAtom := rfl

theorem second_observation : observe (SemanticAccountSignature.embedOriginal secondSignature) = secondAtom := rfl

theorem marked_observation (account : Term (signatureOf language) [] signatureSort)
    (body : Term signature [] wrappedSort) :
    observe (marked account body) = prependWord
      (observe (SemanticAccountSignature.embedOriginal account)) (observe body) :=
  SemanticAccountValuation.read_mark constructors signatureSort wrappedSort markMeaning
    (SemanticAccountSignature.embedOriginal account) body emptyAssignment

theorem output_meaning {arity : List (List TypeExpr × TypeExpr)}
    (member : costBaseConstructor rhoCIGSLT.cut rhoCalc.terms[4] ∈ language.terms)
    (ordinary : ¬WellSorted.UsesBareCollection (costBaseConstructor rhoCIGSLT.cut rhoCalc.terms[4]))
    (scopes : ParameterScopes (costBaseConstructor rhoCIGSLT.cut rhoCalc.terms[4]).params arity)
    (values : Valuation.Family language Base arity) :
    constructors.ordinary (costBaseConstructor rhoCIGSLT.cut rhoCalc.terms[4])
      member ordinary scopes values = (show Base (costBaseConstructor rhoCIGSLT.cut rhoCalc.terms[4]).category
        from by change Occurrences; exact seed) := by
  have notLeaf : costBaseConstructor rhoCIGSLT.cut rhoCalc.terms[4] ≠ costKeyLeafConstructor := by
    decide +kernel
  have notBranch : costBaseConstructor rhoCIGSLT.cut rhoCalc.terms[4] ≠ costKeyBranchConstructor := by
    decide +kernel
  have notUnit : costBaseConstructor rhoCIGSLT.cut rhoCalc.terms[4] ≠ costSignatureUnitConstructor := by
    decide +kernel
  have notProduct : costBaseConstructor rhoCIGSLT.cut rhoCalc.terms[4] ≠ costSignatureProductConstructor := by
    decide +kernel
  have notCommit : costBaseConstructor rhoCIGSLT.cut rhoCalc.terms[4] ≠ costSignatureCommitConstructor := by
    decide +kernel
  have notSigned : costBaseConstructor rhoCIGSLT.cut rhoCalc.terms[4] ≠ costSignedConstructor "Proc" := by
    decide +kernel
  simp only [constructors, AtomicSignatureValuation.constructors, dif_neg notLeaf,
    dif_neg notBranch, dif_neg notUnit, dif_neg notProduct, dif_neg notCommit,
    remaining, dif_neg notSigned]
  change @Eq Occurrences _ _
  exact (dif_pos rfl).trans rfl

theorem output_observation : observe (SemanticAccountSignature.embedOriginal output) = seed := by
  let inputs := SemanticAccountValuation.toOriginalFamily signatureSort wrappedSort
    ((signatureOf language).arity outputOperator)
    ((SemanticAccountValuation.model constructors signatureSort wrappedSort markMeaning).tupleArgs
      (SecondOrderContext.toAmbientArgs ⟨[]⟩
        (foldArgs algebra.toRaw (embedArgs outputArguments))) PUnit (𝟙 _)
          (fun type position => TypeCat.ofHom (fun _ => emptyAssignment type position)) PUnit.unit)
  exact output_meaning (by decide +kernel)
    (by rw [WellSorted.UsesBareCollection, output_shape]; simp)
    (by rw [output_shape]; exact .cons (.simple _ _) (.cons (.simple _ _) .nil)) inputs

theorem closed_return : observe returned = seed := by
  have signed := signed_value
    (BindingCloneFoldSubstitution.interpret algebra (SemanticAccountSignature.embedOriginal output))
    unitElement PUnit (𝟙 _) (fun type position => TypeCat.ofHom (fun _ => emptyAssignment type position))
    PUnit.unit
  change observe returned = prependWord 1
    (observe (SemanticAccountSignature.embedOriginal output)) at signed
  exact signed.trans ((congrArg (prependWord 1) output_observation).trans (prefix_one seed))

theorem closed_signed : observe signedFirst = prependWord firstAtom seed := by
  have signed := signed_value
    (BindingCloneFoldSubstitution.interpret algebra (SemanticAccountSignature.embedOriginal output))
    (BindingCloneFoldSubstitution.interpret algebra (SemanticAccountSignature.embedOriginal firstSignature))
    PUnit (𝟙 _) (fun type position => TypeCat.ofHom (fun _ => emptyAssignment type position)) PUnit.unit
  change observe signedFirst = prependWord firstAtom
    (observe (SemanticAccountSignature.embedOriginal output)) at signed
  exact signed.trans (congrArg (prependWord firstAtom) output_observation)

theorem closed_signed_nontrivial : observe signedFirst ≠ observe returned := by
  rw [closed_signed, closed_return]
  exact prefix_nontrivial

theorem closed_two_atoms :
    observe (marked firstSignature (marked secondSignature returned)) =
      prependWord firstAtom (prependWord secondAtom seed) := by
  rw [marked_observation, marked_observation, first_observation, second_observation, closed_return]

theorem closed_order_matters :
    observe (marked firstSignature (marked secondSignature returned)) ≠
      observe (marked secondSignature (marked firstSignature returned)) := by
  rw [marked_observation, marked_observation, marked_observation, marked_observation,
    first_observation, second_observation, closed_return]
  exact prefix_order_matters

theorem closed_unit_identity :
    observe (marked (AtomicSignatureValuation.unit (by decide +kernel)) signedFirst) = observe signedFirst := by
  rw [marked_observation]
  change prependWord 1 (observe signedFirst) = observe signedFirst
  exact prefix_one _

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.SemanticAccountClosedControls
