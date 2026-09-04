import Mettapedia.Languages.MeTTa.TypeTheory.StagedReflective.Presentation
import Mettapedia.Languages.MeTTa.Prime.ContextualDataFibration
import Mettapedia.Languages.MeTTa.Prime.InternalDataTransport

/-!
# Prime-internal transport for contextual Data

This module lifts the closed semantic I1 combinator to context-indexed open
code.  Source and target values are language/context pairs, and a route is a
first-class structural morphism whose context equation is part of its type.
The result therefore cannot acquire an untyped free name or an escaping bound
index during language change.

The construction is a term of Prime's selected semantic CwF.  It does not
claim that the current syntax parser already elaborates every contextual
route; that independent definability direction remains an I2 obligation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.Prime.InternalContextualTransport

open CategoryTheory
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.Languages.MeTTa.StagedReflective
open Mettapedia.Languages.MeTTa.Prime.ContextualDataFibration
open Mettapedia.Languages.MeTTa.Prime.DataFibration
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.OSLF.MeTTaIL.Syntax

/-! ## The dependent Prime type -/

abbrev PrimeContext := familiesCwF.empty (stageOfNat 0)

def contextualLanguageTy : familiesCwF.Ty PrimeContext :=
  fun _ => ContextualLanguage

abbrev SourceContext := familiesCwF.ext PrimeContext contextualLanguageTy

def targetLanguageTy : familiesCwF.Ty SourceContext :=
  fun _ => ContextualLanguage

abbrev EndpointContext := familiesCwF.ext SourceContext targetLanguageTy

def endpointSource (endpoints : EndpointContext) : ContextualLanguage :=
  endpoints.1.2

def endpointTarget (endpoints : EndpointContext) : ContextualLanguage :=
  endpoints.2

/-- The route type itself carries the exact context-transport equation. -/
def routeTy : familiesCwF.Ty EndpointContext :=
  fun endpoints =>
    ContextualMorphism (endpointSource endpoints) (endpointTarget endpoints)

abbrev RouteContext := familiesCwF.ext EndpointContext routeTy

def sourceDataTy : familiesCwF.Ty RouteContext :=
  fun route => FibreTranslation.AllData (fibre (endpointSource route.1))

abbrev SourceDataContext := familiesCwF.ext RouteContext sourceDataTy

def targetDataTy : familiesCwF.Ty SourceDataContext :=
  fun sourceData =>
    FibreTranslation.AllData (fibre (endpointTarget sourceData.1.1))

/--
The semantic Prime type

`(source : ContextualLanguage) -> (target : ContextualLanguage) ->
  (route : source --> target) -> Data source -> Data target`.
-/
def internalContextualTransportType : familiesCwF.Ty PrimeContext :=
  familiesCwF.pi contextualLanguageTy
    (familiesCwF.pi targetLanguageTy
      (familiesCwF.pi routeTy
        (familiesCwF.pi sourceDataTy targetDataTy)))

/-- Contextual language change as an ordinary dependent Prime term. -/
def internalContextualTransport :
    familiesCwF.Tm PrimeContext internalContextualTransportType :=
  fun _sourceContext _source _target route value =>
    (translation route).mapAllData value

@[simp]
theorem internalContextualTransport_apply
    (source target : ContextualLanguage)
    (route : ContextualMorphism source target)
    (value : FibreTranslation.AllData (fibre source)) :
    internalContextualTransport PUnit.unit source target route value =
      (translation route).mapAllData value :=
  rfl

@[simp]
theorem internalContextualTransport_id
    (code : ContextualLanguage)
    (value : FibreTranslation.AllData (fibre code)) :
    internalContextualTransport PUnit.unit code code
        (ContextualMorphism.id code) value = value :=
  indexedDiagram.map_id code value

@[simp]
theorem internalContextualTransport_comp
    {first middle last : ContextualLanguage}
    (earlier : ContextualMorphism first middle)
    (later : ContextualMorphism middle last)
    (value : FibreTranslation.AllData (fibre first)) :
    internalContextualTransport PUnit.unit first last
        (ContextualMorphism.comp earlier later) value =
      internalContextualTransport PUnit.unit middle last later
        (internalContextualTransport PUnit.unit first middle earlier value) :=
  indexedDiagram.map_comp earlier later value

/-! ## Contextual hygiene as laws of the internal route -/

/-- The base action used by the internal term, exposed at one authored sort. -/
def transportOpenTerm
    {source target : ContextualLanguage}
    (route : ContextualMorphism source target)
    {sort : StructuralMorphism.DeclaredSort source.language}
    (term : (fibre source).BaseEl sort) :
    (fibre target).BaseEl (route.route.mapSort sort) :=
  (translation route).mapBaseEl term

@[simp]
theorem transportOpenTerm_pattern
    {source target : ContextualLanguage}
    (route : ContextualMorphism source target)
    {sort : StructuralMorphism.DeclaredSort source.language}
    (term : (fibre source).BaseEl sort) :
    (transportOpenTerm route term).1 =
      mapPattern route.route.symbols term.1 :=
  translation_mapBaseEl_pattern route term

/-- Cross-language transport preserves the exact support of free names. -/
theorem transportOpenTerm_free_names
    {source target : ContextualLanguage}
    (route : ContextualMorphism source target)
    {sort : StructuralMorphism.DeclaredSort source.language}
    (term : (fibre source).BaseEl sort) :
    (transportOpenTerm route term).1.freeFvarNames =
      term.1.freeFvarNames := by
  rw [transportOpenTerm_pattern]
  rw [Mettapedia.Languages.MeTTa.Prime.InternalDataTransport.structural_mapPattern_eq_kernel]
  exact Mettapedia.Languages.MeTTa.Prime.DataTranslationKernel.free_names_preserved
    route.route.symbols.constructor term.1

/-- Every name in a transported quotation is authorized by the exact target
typing context. -/
theorem transported_free_name_has_target_type
    {source target : ContextualLanguage}
    (route : ContextualMorphism source target)
    {sort : StructuralMorphism.DeclaredSort source.language}
    (term : (fibre source).BaseEl sort)
    {name : String}
    (membership :
      name ∈ (transportOpenTerm route term).1.freeFvarNames) :
    ∃ type, target.context.free name = some type :=
  (transportOpenTerm route term).freeType_of_mem_freeFvarNames membership

/-- Negative hygiene law: a name absent from the target context cannot appear
after transport.  Constructor translation cannot grant variable authority. -/
theorem absent_target_name_cannot_appear
    {source target : ContextualLanguage}
    (route : ContextualMorphism source target)
    {sort : StructuralMorphism.DeclaredSort source.language}
    (term : (fibre source).BaseEl sort)
    (name : String) (absent : target.context.free name = none) :
    name ∉ (transportOpenTerm route term).1.freeFvarNames := by
  intro membership
  obtain ⟨type, typed⟩ :=
    transported_free_name_has_target_type route term membership
  rw [absent] at typed
  cases typed

/-- Opening commutes with the raw action selected by every internal contextual
route.  Together with the typed carrier above, this is the capture equation
for contextual quotation. -/
theorem contextual_route_commutes_with_opening
    {source target : ContextualLanguage}
    (route : ContextualMorphism source target)
    (index : Nat) (replacement body : Pattern) :
    mapPattern route.route.symbols (openBVar index replacement body) =
      openBVar index (mapPattern route.route.symbols replacement)
        (mapPattern route.route.symbols body) :=
  Mettapedia.Languages.MeTTa.Prime.InternalDataTransport.transport_commutes_with_opening
    route.route index replacement body

/-- Closing a free name commutes with every internal contextual route. -/
theorem contextual_route_commutes_with_closing
    {source target : ContextualLanguage}
    (route : ContextualMorphism source target)
    (index : Nat) (name : String) (body : Pattern) :
    mapPattern route.route.symbols (closeFVar index name body) =
      closeFVar index name (mapPattern route.route.symbols body) :=
  Mettapedia.Languages.MeTTa.Prime.InternalDataTransport.transport_commutes_with_closing
    route.route index name body

/-- Capture-avoiding binder instantiation commutes with every internal
contextual route. -/
theorem contextual_route_commutes_with_instantiation
    {source target : ContextualLanguage}
    (route : ContextualMorphism source target)
    (depth : Nat) (replacement body : Pattern) :
    mapPattern route.route.symbols
        (instantiateBVarAt depth replacement body) =
      instantiateBVarAt depth
        (mapPattern route.route.symbols replacement)
        (mapPattern route.route.symbols body) :=
  Mettapedia.Languages.MeTTa.Prime.InternalDataTransport.transport_commutes_with_instantiation
    route.route depth replacement body

/-! ## Executable controls -/

def zeroOpenVariablePackage : FibreTranslation.AllData (fibre zeroOpenCode) :=
  ⟨DataType.base currentZeroAtomSort, zeroOpenVariableData⟩

@[simp]
theorem internal_zero_to_prime_retains_variable_name :
    let result := internalContextualTransport PUnit.unit zeroOpenCode
      primeOpenCode zeroToPrimeOpen zeroOpenVariablePackage
    match result with
    | ⟨DataType.base _, value⟩ => value.2.1 = .fvar "x"
    | _ => False := by
  rfl

/-- The target context demonstrably does not authorize an unrelated name. -/
theorem prime_open_context_rejects_unrelated_name :
    primeOpenCode.context.free "y" = none := by
  rfl

end Mettapedia.Languages.MeTTa.Prime.InternalContextualTransport
