import Mettapedia.Languages.MeTTa.TypeTheory.StagedReflective.Presentation
import Mettapedia.Languages.MeTTa.Prime.DataTranslationKernel
import Mettapedia.GSLT.LanguageDef.WellSorted

/-!
# Prime-internal transport for language-indexed Data

This module internalizes the arrows of the validated-language category in the
existing semantic Prime CwF.  A route is a first-class dependent input, and
`internalTransport` is a Prime-typed dependent function from held source syntax
to held target syntax.  Its computation rule is definitionally the functorial
action of the Data fibration; the nontrivial evidence is supplied by the
fibration's identity/composition laws and the route-indexed hygiene laws below.

This is the semantic I1 boundary.  It does not claim that the eventual syntax
parser and elaborator already expose a constructor for every such route; that
separate definability direction belongs to I2.
-/

namespace Mettapedia.Languages.MeTTa.Prime.InternalDataTransport

open CategoryTheory
open scoped CategoryTheory
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.Languages.MeTTa.StagedReflective
open Mettapedia.Languages.MeTTa.Prime.DataFibration
open Mettapedia.Languages.MeTTa.Prime.DataFibration.ValidatedLanguageData
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.OSLF.MeTTaIL.Syntax

/-! ## The dependent Prime type of transport -/

/-- The closed stage-zero context in the semantic Prime CwF. -/
abbrev PrimeContext := familiesCwF.empty (stageOfNat 0)

/-- First-class validated language codes. -/
def languageTy : familiesCwF.Ty PrimeContext :=
  fun _ => LangCode

abbrev SourceContext := familiesCwF.ext PrimeContext languageTy

/-- A target language may be selected after the source language. -/
def targetLanguageTy : familiesCwF.Ty SourceContext :=
  fun _ => LangCode

abbrev EndpointContext := familiesCwF.ext SourceContext targetLanguageTy

def endpointSource (endpoints : EndpointContext) : LangCode :=
  endpoints.1.2

def endpointTarget (endpoints : EndpointContext) : LangCode :=
  endpoints.2

/-- Structural GSLT-IL arrows are dependent Prime values: their type records
both endpoints. -/
def routeTy : familiesCwF.Ty EndpointContext :=
  fun endpoints => endpointSource endpoints ⟶ endpointTarget endpoints

abbrev RouteContext := familiesCwF.ext EndpointContext routeTy

/-- Held, typed source syntax is the next argument of transport. -/
def sourceDataTy : familiesCwF.Ty RouteContext :=
  fun route => FibreTranslation.AllData (fibre (endpointSource route.1))

abbrev SourceDataContext := familiesCwF.ext RouteContext sourceDataTy

/-- The result lives over the target endpoint selected by the route. -/
def targetDataTy : familiesCwF.Ty SourceDataContext :=
  fun sourceData =>
    FibreTranslation.AllData (fibre (endpointTarget sourceData.1.1))

/--
The Prime type

`(source : LangCode) → (target : LangCode) →
  (route : source ⟶ target) → Data source → Data target`.
-/
def internalTransportType : familiesCwF.Ty PrimeContext :=
  familiesCwF.pi languageTy
    (familiesCwF.pi targetLanguageTy
      (familiesCwF.pi routeTy
        (familiesCwF.pi sourceDataTy targetDataTy)))

/-- Prime-internal language change.  The route and the held syntax are ordinary
dependent arguments of a term in Prime's selected CwF model. -/
def internalTransport :
    familiesCwF.Tm PrimeContext internalTransportType :=
  fun _sourceContext _source _target route value =>
    (translation route).mapAllData value

/-- The computation equation: applying the internal combinator executes the
selected fibration action.  This is a definitional semantics equation, not an
independent validation theorem. -/
@[simp] theorem internalTransport_apply
    (source target : LangCode) (route : source ⟶ target)
    (value : FibreTranslation.AllData (fibre source)) :
    internalTransport PUnit.unit source target route value =
      (translation route).mapAllData value :=
  rfl

/-- Identity routes act as identity on every held syntax value. -/
@[simp] theorem internalTransport_id (language : LangCode)
    (value : FibreTranslation.AllData (fibre language)) :
    internalTransport PUnit.unit language language
      (CategoryTheory.CategoryStruct.id language) value = value :=
  indexedDiagram.map_id language value

/-- Composition of internal routes is composition of their Data actions. -/
@[simp] theorem internalTransport_comp
    {first middle last : LangCode}
    (earlier : first ⟶ middle) (later : middle ⟶ last)
    (value : FibreTranslation.AllData (fibre first)) :
    internalTransport PUnit.unit first last
        (CategoryTheory.CategoryStruct.comp earlier later) value =
      internalTransport PUnit.unit middle last later
        (internalTransport PUnit.unit first middle earlier value) :=
  indexedDiagram.map_comp earlier later value

/-! ## One syntax action, not two parallel stories -/

/-- The translation-kernel traversal and the structural GSLT traversal are the
same constructor-only action when given the route's constructor map. -/
theorem structural_mapPattern_eq_kernel
    (symbols : LanguageDefSymbolMap) (term : Pattern) :
    Mettapedia.GSLT.LanguageDef.mapPattern symbols term =
      Mettapedia.Languages.MeTTa.Prime.DataTranslationKernel.mapPattern
        symbols.constructor term := by
  induction term using Pattern.inductionOn with
  | hbvar index => rfl
  | hfvar name => rfl
  | happly head arguments inductionHypothesis =>
      simp only [Mettapedia.GSLT.LanguageDef.mapPattern,
        Mettapedia.GSLT.LanguageDef.mapPatternList_eq_map,
        Mettapedia.Languages.MeTTa.Prime.DataTranslationKernel.mapPattern,
        Mettapedia.Languages.MeTTa.Prime.DataTranslationKernel.mapPatternList_eq_map]
      congr 1
      apply List.map_congr_left
      intro argument membership
      exact inductionHypothesis argument membership
  | hlambda binder body inductionHypothesis =>
      simp [Mettapedia.GSLT.LanguageDef.mapPattern,
        Mettapedia.Languages.MeTTa.Prime.DataTranslationKernel.mapPattern,
        inductionHypothesis]
  | hmultiLambda arity binders body inductionHypothesis =>
      simp [Mettapedia.GSLT.LanguageDef.mapPattern,
        Mettapedia.Languages.MeTTa.Prime.DataTranslationKernel.mapPattern,
        inductionHypothesis]
  | hsubst body replacement bodyHypothesis replacementHypothesis =>
      simp [Mettapedia.GSLT.LanguageDef.mapPattern,
        Mettapedia.Languages.MeTTa.Prime.DataTranslationKernel.mapPattern,
        bodyHypothesis, replacementHypothesis]
  | hcollection kind elements rest inductionHypothesis =>
      simp only [Mettapedia.GSLT.LanguageDef.mapPattern,
        Mettapedia.GSLT.LanguageDef.mapPatternList_eq_map,
        Mettapedia.Languages.MeTTa.Prime.DataTranslationKernel.mapPattern,
        Mettapedia.Languages.MeTTa.Prime.DataTranslationKernel.mapPatternList_eq_map]
      congr 1
      apply List.map_congr_left
      intro element membership
      exact inductionHypothesis element membership

/-- Internal transport cannot capture a variable while opening a binder. -/
theorem transport_commutes_with_opening
    {source target : LangCode} (route : source ⟶ target)
    (index : Nat) (replacement body : Pattern) :
    Mettapedia.GSLT.LanguageDef.mapPattern route.symbols
        (openBVar index replacement body) =
      openBVar index
        (Mettapedia.GSLT.LanguageDef.mapPattern route.symbols replacement)
        (Mettapedia.GSLT.LanguageDef.mapPattern route.symbols body) := by
  simpa only [structural_mapPattern_eq_kernel] using
    Mettapedia.Languages.MeTTa.Prime.DataTranslationKernel.mapPattern_openBVar
      route.symbols.constructor index replacement body

/-- Internal transport commutes with abstraction of a free name. -/
theorem transport_commutes_with_closing
    {source target : LangCode} (route : source ⟶ target)
    (index : Nat) (name : String) (body : Pattern) :
    Mettapedia.GSLT.LanguageDef.mapPattern route.symbols
        (closeFVar index name body) =
      closeFVar index name
        (Mettapedia.GSLT.LanguageDef.mapPattern route.symbols body) := by
  simpa only [structural_mapPattern_eq_kernel] using
    Mettapedia.Languages.MeTTa.Prime.DataTranslationKernel.mapPattern_closeFVar
      route.symbols.constructor index name body

/-- Internal transport commutes with de Bruijn lifting. -/
theorem transport_commutes_with_lifting
    {source target : LangCode} (route : source ⟶ target)
    (cutoff shift : Nat) (body : Pattern) :
    Mettapedia.GSLT.LanguageDef.mapPattern route.symbols
        (liftBVars cutoff shift body) =
      liftBVars cutoff shift
        (Mettapedia.GSLT.LanguageDef.mapPattern route.symbols body) := by
  simpa only [structural_mapPattern_eq_kernel] using
    Mettapedia.Languages.MeTTa.Prime.DataTranslationKernel.mapPattern_liftBVars
      route.symbols.constructor cutoff shift body

/-- Internal transport commutes with capture-avoiding instantiation. -/
theorem transport_commutes_with_instantiation
    {source target : LangCode} (route : source ⟶ target)
    (depth : Nat) (replacement body : Pattern) :
    Mettapedia.GSLT.LanguageDef.mapPattern route.symbols
        (instantiateBVarAt depth replacement body) =
      instantiateBVarAt depth
        (Mettapedia.GSLT.LanguageDef.mapPattern route.symbols replacement)
        (Mettapedia.GSLT.LanguageDef.mapPattern route.symbols body) := by
  simpa only [structural_mapPattern_eq_kernel] using
    Mettapedia.Languages.MeTTa.Prime.DataTranslationKernel.mapPattern_instantiateBVarAt
      route.symbols.constructor depth replacement body

/-! ## Executable positive and negative controls -/

/-- The concrete Prime unit bundled with its dependent Data type code. -/
def currentPrimeUnitPackage :
    FibreTranslation.AllData
      (fibre
        Mettapedia.Languages.MeTTa.Prime.LanguageDef.currentPrimePresentation) :=
  ⟨.base currentPrimeAtomSort, currentPrimeUnitData⟩

/-- Positive control: internal identity transport retains the concrete held
Prime program from `DataFibration`. -/
theorem internal_identity_retains_prime_unit :
    internalTransport PUnit.unit
        Mettapedia.Languages.MeTTa.Prime.LanguageDef.currentPrimePresentation
        Mettapedia.Languages.MeTTa.Prime.LanguageDef.currentPrimePresentation
        (CategoryTheory.CategoryStruct.id _) currentPrimeUnitPackage =
      currentPrimeUnitPackage :=
  internalTransport_id _ _

/-- Negative control: the new Prime constructors cannot be erased by posing an
identity-symbol route back into the smaller Zero presentation. -/
theorem no_internal_identity_route_prime_to_zero :
    ¬ ∃ route :
        Mettapedia.Languages.MeTTa.Prime.LanguageDef.currentPrimePresentation ⟶
          Mettapedia.Languages.MeTTa.Prime.LanguageDef.currentZeroPresentation,
      route.symbols = LanguageDefSymbolMap.id :=
  Mettapedia.Languages.MeTTa.Prime.LanguageDef.no_identity_symbol_retraction

end Mettapedia.Languages.MeTTa.Prime.InternalDataTransport
