import Mettapedia.Languages.MeTTa.Prime.DataFibration

/-!
# Contextual language-indexed Data

Closed `Data` is insufficient for hygienic staging: useful quoted programs may
refer to an explicitly typed ambient context.  This module constructs the
open-code side over pairs of a validated language and a locally nameless typing
context.  Its fibres contain actual `OpenTerm`s, not raw patterns.

A contextual language morphism consists of a structural GSLT morphism together
with the equation saying that it transports the source context to the target
context.  Consequently its Data action preserves free-variable names, bound
indices, their types, object shape, canonical binder metadata, and scope by
construction.  This is the formal contextual-data boundary behind contextual boxes;
evaluation or admission authority is deliberately not manufactured here.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.Prime.ContextualDataFibration

open CategoryTheory
open scoped CategoryTheory
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.Languages.MeTTa.Prime.DataFibration
open Mettapedia.Languages.MeTTa.Prime.DataFibration.ValidatedLanguageData
open Mettapedia.OSLF.MeTTaIL.Syntax

/-! ## Contexts and their structural action -/

/-- The explicit environment of an open quoted term.  Free names carry their
types; bound variables use the ordered de Bruijn type stack. -/
structure CodeContext where
  free : FreeTypeContext
  bound : List TypeExpr

namespace CodeContext

@[ext]
theorem ext {first second : CodeContext}
    (free : first.free = second.free)
    (bound : first.bound = second.bound) : first = second := by
  cases first
  cases second
  cases free
  cases bound
  rfl

/-- A presentation-symbol action transports the types in an open context but
does not rename either free names or de Bruijn positions. -/
def map (symbols : PresentationSymbols) (context : CodeContext) : CodeContext where
  free := context.free.map symbols
  bound := context.bound.map (mapTypeExpr symbols)

@[simp]
theorem map_id (context : CodeContext) :
    context.map PresentationSymbols.id = context := by
  apply ext
  · exact FreeTypeContext.map_id context.free
  · change context.bound.map (mapTypeExpr PresentationSymbols.id) =
      context.bound
    have mapIdentity : mapTypeExpr PresentationSymbols.id = _root_.id := by
      funext type
      exact mapTypeExpr_id type
    rw [mapIdentity, List.map_id]

@[simp]
theorem map_comp (context : CodeContext)
    (earlier later : PresentationSymbols) :
    context.map (earlier.comp later) =
      (context.map earlier).map later := by
  apply ext
  · exact FreeTypeContext.map_comp context.free earlier later
  · simp [map, List.map_map]

end CodeContext

/-! ## The category of validated languages in explicit open contexts -/

/-- A validated language together with the only variables open code may use. -/
structure ContextualLanguage where
  language : LangCode
  context : CodeContext

/-- A language-changing operation whose context action is explicit. -/
structure ContextualMorphism (source target : ContextualLanguage) where
  route : source.language ⟶ target.language
  mapsContext : source.context.map route.symbols = target.context

namespace ContextualMorphism

@[ext]
theorem ext {source target : ContextualLanguage}
    {first second : ContextualMorphism source target}
    (route : first.route = second.route) : first = second := by
  cases first
  cases second
  cases route
  rfl

def id (language : ContextualLanguage) :
    ContextualMorphism language language where
  route := StructuralMorphism.id language.language
  mapsContext := CodeContext.map_id language.context

def comp {first middle last : ContextualLanguage}
    (earlier : ContextualMorphism first middle)
    (later : ContextualMorphism middle last) :
    ContextualMorphism first last where
  route := StructuralMorphism.comp earlier.route later.route
  mapsContext := by
    change first.context.map (earlier.route.symbols.comp later.route.symbols) =
      last.context
    rw [CodeContext.map_comp, earlier.mapsContext, later.mapsContext]

end ContextualMorphism

instance : CategoryTheory.Category ContextualLanguage where
  Hom := ContextualMorphism
  id := ContextualMorphism.id
  comp := ContextualMorphism.comp
  id_comp morphism := by
    apply ContextualMorphism.ext
    apply StructuralMorphism.ext
    rfl
  comp_id morphism := by
    apply ContextualMorphism.ext
    apply StructuralMorphism.ext
    rfl
  assoc first second third := by
    apply ContextualMorphism.ext
    apply StructuralMorphism.ext
    rfl

/-! ## Open Data fibres and typed transport -/

/-- The contextual fibre at a language/context pair.  A base inhabitant is a
well-sorted open object term in exactly that context. -/
def fibre (code : ContextualLanguage) : Fibre where
  BaseType := StructuralMorphism.AuthoredSort code.language
  BaseEl := fun sort =>
    OpenTerm code.language.language code.context.free code.context.bound
      (authoredSortToLangSort code.language sort)
  Stamp := Bool

/-- Transport open held syntax along a contextual language morphism. -/
def translation {source target : ContextualLanguage}
    (morphism : ContextualMorphism source target) :
    FibreTranslation (fibre source) (fibre target) where
  mapBase := morphism.route.mapSort
  mapBaseEl := fun {type} term => by
    let mapped := term.map morphism.route
    exact mapped.reindex
      (congrArg CodeContext.free morphism.mapsContext)
      (congrArg CodeContext.bound morphism.mapsContext)
      (mapLangSort_authoredSortToLangSort morphism.route type)
  mapStamp := _root_.id

@[simp]
theorem translation_mapBaseEl_pattern
    {source target : ContextualLanguage}
    (morphism : ContextualMorphism source target)
    {sort : StructuralMorphism.AuthoredSort source.language}
    (term : (fibre source).BaseEl sort) :
    ((translation morphism).mapBaseEl term).1 =
      mapPattern morphism.route.symbols term.1 := by
  simp only [translation, OpenTerm.reindex_pattern, OpenTerm.map_pattern]

theorem translation_mapType_id (code : ContextualLanguage)
    (type : DataType (fibre code).BaseType) :
    type.map (translation (ContextualMorphism.id code)).mapBase = type := by
  induction type with
  | base sort =>
      simp only [DataType.map_base]
      apply congrArg DataType.base
      exact StructuralMorphism.mapSort_id code.language sort
  | data payload inductionHypothesis => simp [inductionHypothesis]

theorem translation_mapType_comp
    {first middle last : ContextualLanguage}
    (earlier : ContextualMorphism first middle)
    (later : ContextualMorphism middle last)
    (type : DataType (fibre first).BaseType) :
    type.map (translation (ContextualMorphism.comp earlier later)).mapBase =
      (type.map (translation earlier).mapBase).map
        (translation later).mapBase := by
  induction type with
  | base sort =>
      simp only [DataType.map_base]
      apply congrArg DataType.base
      exact StructuralMorphism.mapSort_comp earlier.route later.route sort
  | data payload inductionHypothesis => simp [inductionHypothesis]

theorem translation_mapInterpret_id (code : ContextualLanguage)
    (type : DataType (fibre code).BaseType)
    (value : interpret (fibre code).Stamp (fibre code).BaseEl type) :
    HEq
      ((translation (ContextualMorphism.id code)).mapInterpret type value)
      value := by
  induction type with
  | base sort =>
      have sortEquality :=
        StructuralMorphism.mapSort_id code.language sort
      cases sortEquality
      simp only [FibreTranslation.mapInterpret]
      apply heq_of_eq
      apply Subtype.ext
      rw [translation_mapBaseEl_pattern]
      exact mapPattern_id value.1
  | data payload inductionHypothesis =>
      rcases value with ⟨stamp, inner⟩
      simp only [FibreTranslation.mapInterpret, translation, DataType.map_data]
      exact FibreTranslation.prod_heq HEq.rfl (inductionHypothesis inner)

theorem translation_mapInterpret_comp
    {first middle last : ContextualLanguage}
    (earlier : ContextualMorphism first middle)
    (later : ContextualMorphism middle last)
    (type : DataType (fibre first).BaseType)
    (value : interpret (fibre first).Stamp (fibre first).BaseEl type) :
    HEq
      ((translation (ContextualMorphism.comp earlier later)).mapInterpret
        type value)
      ((translation later).mapInterpret
        (type.map (translation earlier).mapBase)
        ((translation earlier).mapInterpret type value)) := by
  induction type with
  | base sort =>
      have sortEquality :=
        StructuralMorphism.mapSort_comp earlier.route later.route sort
      cases sortEquality
      simp only [DataType.map_base, FibreTranslation.mapInterpret]
      apply heq_of_eq
      apply Subtype.ext
      rw [translation_mapBaseEl_pattern, translation_mapBaseEl_pattern,
        translation_mapBaseEl_pattern]
      exact mapPattern_comp earlier.route.symbols later.route.symbols value.1
  | data payload inductionHypothesis =>
      rcases value with ⟨stamp, inner⟩
      simp only [FibreTranslation.mapInterpret, translation, DataType.map_data]
      exact FibreTranslation.prod_heq HEq.rfl (inductionHypothesis inner)

/-- Open Data is functorial over the category of validated languages in
explicit contexts. -/
def indexedDiagram : IndexedDataDiagram ContextualLanguage where
  fibre := fibre
  map := translation
  map_id := by
    intro code value
    rcases value with ⟨type, value⟩
    apply Sigma.ext
    · exact translation_mapType_id code type
    · exact translation_mapInterpret_id code (.data type) value
  map_comp := by
    intro first middle last earlier later value
    rcases value with ⟨type, value⟩
    apply Sigma.ext
    · exact translation_mapType_comp earlier later type
    · exact translation_mapInterpret_comp earlier later (.data type) value

abbrev TypeOf (code : ContextualLanguage) :=
  IndexedDataDiagram.TypeOf indexedDiagram code

abbrev DataAt (code : ContextualLanguage) (type : TypeOf code) :=
  IndexedDataDiagram.DataAt indexedDiagram code type

/-- Quote one already checked open term.  Raw syntax cannot enter this
constructor without its authored typing, object-shape, and scope evidence. -/
def quoteOpenTerm (code : ContextualLanguage)
    (sort : StructuralMorphism.AuthoredSort code.language)
    (term : (fibre code).BaseEl sort) (stamp : Bool) :
    DataAt code (DataType.base sort) :=
  (stamp, term)

@[simp]
theorem eval_quoteOpenTerm (code : ContextualLanguage)
    (sort : StructuralMorphism.AuthoredSort code.language)
    (term : (fibre code).BaseEl sort) (stamp : Bool) :
    eval (quoteOpenTerm code sort term stamp) = term :=
  rfl

/-! ## Cross-language positive and negative controls -/

open Mettapedia.Languages.MeTTa.MeTTaZero
open Mettapedia.Languages.MeTTa.Prime.LanguageDef

/-- One free object variable, explicitly classified as an Atom. -/
def oneAtomFree : FreeTypeContext :=
  fun name => if name = "x" then some (.base "Atom") else none

def oneAtomContext : CodeContext where
  free := oneAtomFree
  bound := []

def currentZeroAtomSort :
    StructuralMorphism.AuthoredSort currentZeroPresentation :=
  ⟨atomType, by
    change List.Mem atomType [atomType, spaceType, processType, alternativesType]
    exact List.mem_cons_self⟩

def zeroOpenCode : ContextualLanguage where
  language := currentZeroPresentation
  context := oneAtomContext

def primeOpenCode : ContextualLanguage where
  language := currentPrimePresentation
  context := oneAtomContext.map currentZeroToPrimePresentation.symbols

def zeroToPrimeOpen : ContextualMorphism zeroOpenCode primeOpenCode where
  route := currentZeroToPrimePresentation
  mapsContext := rfl

/-- Positive control: an open Zero atom is admitted only with its explicit
free-variable context. -/
def zeroOpenVariable :
    (fibre zeroOpenCode).BaseEl currentZeroAtomSort := by
  refine ⟨.fvar "x", ?_⟩
  refine ⟨HasType.fvar ?_, rfl, rfl, rfl⟩
  simp [zeroOpenCode, oneAtomContext, oneAtomFree, currentZeroAtomSort,
    atomType, TypeDecl.plain, authoredSortToLangSort]

/-- Cross-language transport retains the free name while transporting its
type and carrier sort into Prime. -/
@[simp]
theorem zeroToPrimeOpen_variable_pattern :
    ((translation zeroToPrimeOpen).mapBaseEl zeroOpenVariable).1 =
      .fvar "x" :=
  rfl

/-- A bound index outside the declared context cannot be packaged as open
Data.  Quotation therefore cannot turn an escaping variable into held code. -/
theorem escaping_bvar_not_open_data :
    ¬ OpenTermWellSorted currentZeroPresentation.language
      FreeTypeContext.empty [(.base "Atom")]
      (authoredSortToLangSort currentZeroPresentation currentZeroAtomSort)
      (.bvar 1) := by
  rintro ⟨typed, _canonical, _object, _scope⟩
  cases typed with
  | bvar lookup => simp at lookup

/-- Identity transport retains a concrete open quotation, including its
context-indexed typing evidence. -/
def zeroOpenVariableData :
    DataAt zeroOpenCode (DataType.base currentZeroAtomSort) :=
  quoteOpenTerm zeroOpenCode currentZeroAtomSort zeroOpenVariable false

theorem identity_retains_zero_open_variable :
    FibreTranslation.mapAllData
        (indexedDiagram.map (ContextualMorphism.id zeroOpenCode))
        ⟨DataType.base currentZeroAtomSort, zeroOpenVariableData⟩ =
      ⟨DataType.base currentZeroAtomSort, zeroOpenVariableData⟩ :=
  indexedDiagram.map_id zeroOpenCode _

end Mettapedia.Languages.MeTTa.Prime.ContextualDataFibration
