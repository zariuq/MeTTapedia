import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.FiberedCategory.Cocartesian
import Mathlib.CategoryTheory.Monad.Products
import Mettapedia.GSLT.LanguageDef.NIK
import Mettapedia.GSLT.LanguageDef.NIKIndexedOperational
import Mettapedia.GSLT.LanguageDef.StructuralCategory
import Mettapedia.GSLT.LanguageDef.WellSorted
import Mettapedia.Languages.MeTTa.Prime.IndexedLanguageChange

/-!
# Language-indexed Data for Prime

This module constructs the quotation family over typed language changes.  The
syntax name is `Data`; its covariant Grothendieck construction has a chosen
strongly cocartesian push-forward lift over every language morphism.

The construction keeps three layers distinct:

* `DataType` is the intensional type-code constructor and strictly raises quote
  depth;
* `dataComonad` is the per-language product comonad carrying a selected stamp;
* `IndexedDataDiagram` transports typed Data values along language morphisms.

Raw syntax admission is not the comonad counit.  NIK's checking modes govern
entry into an admitted Data fibre; the counit then exposes an already-admitted
payload without an interior replay.
-/

namespace Mettapedia.Languages.MeTTa.Prime.DataFibration

open CategoryTheory
open CategoryTheory.Limits
open scoped CategoryTheory
open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.GSLT.LanguageDef.KernelAuthority.Checker
open Mettapedia.GSLT.LanguageDef.NIKMetalogic
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.Languages.MeTTa.Prime.IndexedLanguageChange
open Mettapedia.OSLF.MeTTaIL.Syntax

universe uLang vLang uBase uValue

/-! ## Intensional Data codes -/

/-- The free, non-idempotent Data closure of a language's base type codes. -/
inductive DataType (Base : Type uBase) where
  | base (type : Base)
  | data (payload : DataType Base)
  deriving DecidableEq, Repr

namespace DataType

/-- Number of explicit Data constructors surrounding the base type. -/
def level : DataType Base → Nat
  | .base _ => 0
  | .data payload => payload.level + 1

/-- Map a base-type translation through every Data layer. -/
def map (translate : Source → Target) : DataType Source → DataType Target
  | .base type => .base (translate type)
  | .data payload => .data (payload.map translate)

/-- The underlying base type beneath every quotation layer. -/
def root : DataType Base → Base
  | .base type => type
  | .data payload => payload.root

@[simp] theorem level_base (type : Base) : (base type).level = 0 := rfl

@[simp] theorem level_data (payload : DataType Base) :
    (data payload).level = payload.level + 1 := rfl

@[simp] theorem map_base (translate : Source → Target) (type : Source) :
    (base type).map translate = base (translate type) := rfl

@[simp] theorem map_data (translate : Source → Target)
    (payload : DataType Source) :
    (data payload).map translate = data (payload.map translate) := rfl

@[simp] theorem map_id (type : DataType Base) : type.map id = type := by
  induction type with
  | base => rfl
  | data payload inductionHypothesis => simp [map, inductionHypothesis]

@[simp] theorem map_comp (earlier : Source → Middle) (later : Middle → Target)
    (type : DataType Source) :
    type.map (later ∘ earlier) = (type.map earlier).map later := by
  induction type with
  | base => rfl
  | data payload inductionHypothesis => simp [map, inductionHypothesis]

@[simp] theorem level_map (translate : Source → Target)
    (type : DataType Source) :
    (type.map translate).level = type.level := by
  induction type with
  | base => rfl
  | data payload inductionHypothesis => simp [level, inductionHypothesis]

@[simp] theorem root_map (translate : Source → Target)
    (type : DataType Source) :
    (type.map translate).root = translate type.root := by
  induction type with
  | base => rfl
  | data payload inductionHypothesis => simp [root, inductionHypothesis]

/-- Quotation strictly raises the intensional level. -/
theorem data_strictly_raises (type : DataType Base) :
    type.level < (data type).level := by
  simp [level]

/-- No type code is definitionally its own quotation. -/
theorem no_self_data (type : DataType Base) : data type ≠ type := by
  intro equal
  have levelEqual := congrArg level equal
  simp only [level_data] at levelEqual
  omega

/-- Quoting twice cannot collapse to quoting once. -/
theorem data_data_ne_data (type : DataType Base) :
    data (data type) ≠ data type :=
  no_self_data (data type)

end DataType

/-! ## The per-fibre product comonad -/

/-- Interpret Data codes using a stamp carrier and an interpretation of base
types.  A Data layer retains one stamp rather than an execution transcript. -/
def interpret (Stamp : Type uValue) (BaseEl : Base → Type uValue) :
    DataType Base → Type uValue
  | .base type => BaseEl type
  | .data payload => Stamp × interpret Stamp BaseEl payload

/-- One admitted Data value. -/
abbrev Data (Stamp : Type uValue) (BaseEl : Base → Type uValue)
    (payload : DataType Base) : Type uValue :=
  interpret Stamp BaseEl (.data payload)

/-- The categorical Data modality in one language fibre. -/
noncomputable def dataComonad (Stamp : Type uValue) :
    CategoryTheory.Comonad (Type uValue) :=
  CategoryTheory.prodComonad Stamp

/-- Quote at an explicitly selected space/stage/revision stamp. -/
def quoteAt (stamp : Stamp) (value : interpret Stamp BaseEl payload) :
    Data Stamp BaseEl payload :=
  (stamp, value)

/-- The syntax `!`: expose an already-admitted payload. -/
def eval (value : Data Stamp BaseEl payload) :
    interpret Stamp BaseEl payload :=
  value.2

/-- Comultiplication: retain the fact that this is held Data as Data. -/
def requote (value : Data Stamp BaseEl payload) :
    Data Stamp BaseEl (.data payload) :=
  (value.1, value)

@[simp] theorem eval_quoteAt (stamp : Stamp)
    (value : interpret Stamp BaseEl payload) :
    eval (quoteAt stamp value) = value := rfl

@[simp] theorem eval_requote (value : Data Stamp BaseEl payload) :
    eval (requote value) = value := rfl

/-- Mapping the counit inside a requoted value is the other counit law. -/
@[simp] theorem mapEval_requote (value : Data Stamp BaseEl payload) :
    (requote value).1 = value.1 ∧ eval (eval (requote value)) = eval value :=
  ⟨rfl, rfl⟩

/-- Requotation is coassociative. -/
@[simp] theorem requote_coassoc (value : Data Stamp BaseEl payload) :
    requote (requote value) =
      (value.1, requote value) := rfl

/-- A two-valued stamp exposes semantic non-idempotence: comultiplication is
not surjective even at an inhabited payload. -/
theorem bool_requote_not_surjective :
    ¬ Function.Surjective
      (requote (Stamp := Bool) (BaseEl := fun _ : PUnit => PUnit)
        (payload := .base PUnit.unit)) := by
  intro surjective
  let outside : Data Bool (fun _ : PUnit => PUnit)
      (.data (.base PUnit.unit)) :=
    (false, (true, PUnit.unit))
  obtain ⟨source, equal⟩ := surjective outside
  have outer : source.1 = false := congrArg Prod.fst equal
  have inner : source.1 = true := congrArg (fun value => value.2.1) equal
  exact Bool.false_ne_true (outer.symm.trans inner)

/-! ## Typed transport between language fibres -/

/-- The semantic ingredients of one language fibre. -/
structure Fibre where
  BaseType : Type uBase
  BaseEl : BaseType → Type uValue
  Stamp : Type uValue

/-- A typed language translation.  It maps base type codes, their inhabitants,
and the selected stamp. -/
structure FibreTranslation (source target : Fibre.{uBase, uValue}) where
  mapBase : source.BaseType → target.BaseType
  mapBaseEl : {type : source.BaseType} →
    source.BaseEl type → target.BaseEl (mapBase type)
  mapStamp : source.Stamp → target.Stamp

namespace FibreTranslation

/-- Congruence for pairs whose component types may differ propositionally. -/
theorem prod_heq
    {First : Type uValue} {SecondLeft SecondRight : Type uValue}
    {firstLeft firstRight : First}
    {secondLeft : SecondLeft} {secondRight : SecondRight}
    (first : HEq firstLeft firstRight)
    (second : HEq secondLeft secondRight) :
    HEq (firstLeft, secondLeft) (firstRight, secondRight) := by
  cases first
  cases second
  rfl

/-- Map a value through every nested Data layer. -/
def mapInterpret (translation : FibreTranslation source target) :
    (type : DataType source.BaseType) →
      interpret source.Stamp source.BaseEl type →
        interpret target.Stamp target.BaseEl
          (type.map translation.mapBase)
  | .base _, value => translation.mapBaseEl value
  | .data payload, value =>
      (translation.mapStamp value.1,
        mapInterpret translation payload value.2)

/-- Map one admitted Data value. -/
def mapData (translation : FibreTranslation source target)
    (type : DataType source.BaseType) :
    Data source.Stamp source.BaseEl type →
      Data target.Stamp target.BaseEl (type.map translation.mapBase) :=
  mapInterpret translation (.data type)

/-- Total typed Data in one language fibre. -/
abbrev AllData (fibre : Fibre.{uBase, uValue}) :=
  Σ type : DataType fibre.BaseType, Data fibre.Stamp fibre.BaseEl type

/-- Map the entire dependent Data pair. -/
def mapAllData (translation : FibreTranslation source target) :
    AllData source → AllData target
  | ⟨type, value⟩ =>
      ⟨type.map translation.mapBase, translation.mapData type value⟩

/-- The identity translation. -/
def id (fibre : Fibre.{uBase, uValue}) : FibreTranslation fibre fibre where
  mapBase := _root_.id
  mapBaseEl := _root_.id
  mapStamp := _root_.id

/-- Composition in execution order. -/
def comp (earlier : FibreTranslation first middle)
    (later : FibreTranslation middle last) : FibreTranslation first last where
  mapBase := later.mapBase ∘ earlier.mapBase
  mapBaseEl := later.mapBaseEl ∘ earlier.mapBaseEl
  mapStamp := later.mapStamp ∘ earlier.mapStamp

theorem mapInterpret_id (type : DataType fibre.BaseType)
    (value : interpret fibre.Stamp fibre.BaseEl type) :
    HEq (mapInterpret (id fibre) type value) value := by
  induction type with
  | base baseType => rfl
  | data payload inductionHypothesis =>
      rcases value with ⟨stamp, value⟩
      simp only [mapInterpret, id, DataType.map_data]
      exact prod_heq HEq.rfl (inductionHypothesis value)

theorem mapInterpret_comp
    (earlier : FibreTranslation first middle)
    (later : FibreTranslation middle last)
    (type : DataType first.BaseType)
    (value : interpret first.Stamp first.BaseEl type) :
    HEq
      (mapInterpret (comp earlier later) type value)
      (mapInterpret later (type.map earlier.mapBase)
        (mapInterpret earlier type value)) := by
  induction type with
  | base baseType => rfl
  | data payload inductionHypothesis =>
      rcases value with ⟨stamp, value⟩
      simp only [mapInterpret, comp, Function.comp_apply,
        DataType.map_data]
      exact prod_heq HEq.rfl (inductionHypothesis value)

@[simp] theorem mapAllData_id (value : AllData fibre) :
    mapAllData (id fibre) value = value := by
  rcases value with ⟨type, value⟩
  apply Sigma.ext (DataType.map_id type)
  exact mapInterpret_id (.data type) value

@[simp] theorem mapAllData_comp
    (earlier : FibreTranslation first middle)
    (later : FibreTranslation middle last)
    (value : AllData first) :
    mapAllData (comp earlier later) value =
      mapAllData later (mapAllData earlier value) := by
  rcases value with ⟨type, value⟩
  apply Sigma.ext (DataType.map_comp earlier.mapBase later.mapBase type)
  exact mapInterpret_comp earlier later (.data type) value

/-- Typed transport commutes with the Data counit. -/
theorem mapData_eval (translation : FibreTranslation source target)
    (type : DataType source.BaseType)
    (value : Data source.Stamp source.BaseEl type) :
    eval (translation.mapData type value) =
      translation.mapInterpret type (eval value) := rfl

/-- Typed transport commutes with comultiplication. -/
theorem mapData_requote (translation : FibreTranslation source target)
    (type : DataType source.BaseType)
    (value : Data source.Stamp source.BaseEl type) :
    translation.mapData (.data type) (requote value) =
      requote (translation.mapData type value) := rfl

end FibreTranslation

/-! ## The indexed Data diagram and its total category -/

/-- A covariant, typed Data family over an authored category of languages. -/
structure IndexedDataDiagram (Lang : Type uLang)
    [CategoryTheory.Category.{vLang} Lang] where
  fibre : Lang → Fibre.{uBase, uValue}
  map : {source target : Lang} → (source ⟶ target) →
    FibreTranslation (fibre source) (fibre target)
  map_id : ∀ (language : Lang)
      (value : FibreTranslation.AllData (fibre language)),
    FibreTranslation.mapAllData
      (map (CategoryTheory.CategoryStruct.id language)) value = value
  map_comp : ∀ {first middle last : Lang}
      (earlier : first ⟶ middle) (later : middle ⟶ last)
      (value : FibreTranslation.AllData (fibre first)),
    FibreTranslation.mapAllData
        (map (CategoryTheory.CategoryStruct.comp earlier later)) value =
      FibreTranslation.mapAllData (map later)
        (FibreTranslation.mapAllData (map earlier) value)

namespace IndexedDataDiagram

variable {Lang : Type uLang} [CategoryTheory.Category.{vLang} Lang]

/-- Type codes available at one authored language point. -/
abbrev TypeOf
    (diagram : IndexedDataDiagram.{uLang, vLang, uBase, uValue} Lang)
    (language : Lang) := DataType (diagram.fibre language).BaseType

/-- The promised dependent notation: admitted Data at language `language` and
type code `type`. -/
abbrev DataAt
    (diagram : IndexedDataDiagram.{uLang, vLang, uBase, uValue} Lang)
    (language : Lang) (type : TypeOf diagram language) :=
  Data (diagram.fibre language).Stamp (diagram.fibre language).BaseEl type

/-- The covariant total-Data family. -/
def dataFunctor (diagram : IndexedDataDiagram.{uLang, vLang, uBase, uValue} Lang) :
    CategoryTheory.Functor Lang (Type (max uBase uValue)) where
  obj language := FibreTranslation.AllData (diagram.fibre language)
  map route := TypeCat.ofHom (diagram.map route).mapAllData
  map_id language := by
    apply CategoryTheory.ConcreteCategory.hom_ext
    intro value
    exact diagram.map_id language value
  map_comp earlier later := by
    apply CategoryTheory.ConcreteCategory.hom_ext
    intro value
    exact diagram.map_comp earlier later value

/-- Total category of a language and one typed, admitted Data value. -/
abbrev DataTotal
    (diagram : IndexedDataDiagram.{uLang, vLang, uBase, uValue} Lang) :=
  (dataFunctor diagram).Elements

/-- Forget Data and retain its language code. -/
def projection (diagram : IndexedDataDiagram.{uLang, vLang, uBase, uValue} Lang) :
    CategoryTheory.Functor (DataTotal diagram) Lang :=
  CategoryTheory.CategoryOfElements.π (dataFunctor diagram)

/-- Canonical language-changing push-forward object. -/
def pushforwardObject
    (diagram : IndexedDataDiagram.{uLang, vLang, uBase, uValue} Lang)
    (object : DataTotal diagram) {target : Lang}
    (route : object.1 ⟶ target) : DataTotal diagram :=
  ⟨target, (dataFunctor diagram).map route object.2⟩

/-- Canonical lift of a language morphism to typed Data. -/
def pushforwardLift
    (diagram : IndexedDataDiagram.{uLang, vLang, uBase, uValue} Lang)
    (object : DataTotal diagram) {target : Lang}
    (route : object.1 ⟶ target) :
    object ⟶ pushforwardObject diagram object route :=
  CategoryTheory.CategoryOfElements.homMk _ _ route rfl

/-- The Data family earns a strongly cocartesian push-forward lift. -/
instance pushforwardLift_isStronglyCocartesian
    (diagram : IndexedDataDiagram.{uLang, vLang, uBase, uValue} Lang)
    (object : DataTotal diagram) {target : Lang}
    (route : object.1 ⟶ target) :
    (projection diagram).IsStronglyCocartesian route
      (pushforwardLift diagram object route) where
  toIsHomLift := by
    change (projection diagram).IsHomLift
      ((projection diagram).map (pushforwardLift diagram object route))
      (pushforwardLift diagram object route)
    infer_instance
  universal_property' := by
    intro targetObject tailRoute candidate candidateLift
    letI : (projection diagram).IsHomLift
        (CategoryTheory.CategoryStruct.comp route tailRoute) candidate :=
      candidateLift
    have baseEq :
        CategoryTheory.CategoryStruct.comp route tailRoute = candidate.val :=
      @CategoryTheory.IsHomLift.eq_of_isHomLift _ _ _ _
        (projection diagram) object targetObject
        (CategoryTheory.CategoryStruct.comp route tailRoute)
        candidate candidateLift
    let mediator : pushforwardObject diagram object route ⟶ targetObject :=
      CategoryTheory.CategoryOfElements.homMk _ _ tailRoute (by
        change (dataFunctor diagram).map tailRoute
            ((dataFunctor diagram).map route object.2) = targetObject.2
        calc
          _ = (dataFunctor diagram).map
                (CategoryTheory.CategoryStruct.comp route tailRoute) object.2 :=
              (CategoryTheory.Functor.map_comp_apply
                (dataFunctor diagram) route tailRoute object.2).symm
          _ = (dataFunctor diagram).map candidate.val object.2 := by
              exact congrArg
                (fun arrow => (dataFunctor diagram).map arrow object.2) baseEq
          _ = targetObject.2 := candidate.property)
    have mediatorLift : (projection diagram).IsHomLift tailRoute mediator := by
      change (projection diagram).IsHomLift
        ((projection diagram).map mediator) mediator
      infer_instance
    have factor : CategoryTheory.CategoryStruct.comp
        (pushforwardLift diagram object route) mediator = candidate := by
      apply CategoryTheory.CategoryOfElements.ext
      exact baseEq
    refine ⟨mediator, ⟨mediatorLift, factor⟩, ?_⟩
    intro other properties
    have otherBase : tailRoute = (projection diagram).map other :=
      @CategoryTheory.IsHomLift.eq_of_isHomLift _ _ _ _
        (projection diagram) (pushforwardObject diagram object route)
        targetObject tailRoute other properties.1
    change tailRoute = other.val at otherBase
    apply CategoryTheory.CategoryOfElements.ext
    change other.val = tailRoute
    exact otherBase.symm

end IndexedDataDiagram

/-! ## The four local NIK service faces at a Data boundary -/

/-- Turn an independently stated meaning on claims into an object of the
common admission algebra. -/
def claimAdmissionObject {Claim : Type uBase} (Meaning : Claim → Prop) :
    AdmissionObject.{uBase} where
  Carrier := Claim
  Meaning := Meaning

/-- The four ways in which raw material may earn entry into a typed Data
fibre.  This is the Data-local view of the canonical `NIK.Service` doctrine,
not a definition of NIK itself.  These are capabilities, not a global switch:
one language may expose several modes at distinct boundaries. -/
inductive EntryMode (Claim : Type uBase) where
  /-- A total algorithm computes the judgment directly. -/
  | directDecision (Meaning : Claim → Prop)
      (kernel : DecisionKernel Claim Meaning)
  /-- A native proof term is checked by its guest's computing kernel, with
  exact proof-fibre preservation. -/
  | nativeProof (guest : NativeProofSystem.{uBase, uValue} Claim)
      (kernel : NativeProofKernel guest)
  /-- A native meaning-preserving construction, computation, inference, or
  transformation was admitted once and now runs without an interior checker. -/
  | admittedFlow (source : AdmissionObject.{uBase})
      (Meaning : Claim → Prop)
      (operation : source ⟶ claimAdmissionObject Meaning)
  /-- Evidence is required at an explicitly named search or trust boundary. -/
  | certificateBoundary (Certificate : Type uValue)
      (Meaning : Claim → Prop) (checker : Checker Claim Certificate)
      (authority : checker.Authority Meaning)

namespace EntryMode

/-- Independent meaning selected by each mode. -/
def Accepted {Claim : Type uBase} :
    EntryMode.{uBase, uValue} Claim → Claim → Prop
  | .directDecision Meaning _ => Meaning
  | .nativeProof guest _ => fun claim => Nonempty (guest.ProofFibre claim)
  | .admittedFlow _ Meaning _ => Meaning
  | .certificateBoundary _ Meaning _ _ => Meaning

/-- Only the fourth mode has a separate external certificate language.  A
native proof object belongs to its guest calculus and is not such a boundary
certificate. -/
def requiresCertificate {Claim : Type uBase} :
    EntryMode.{uBase, uValue} Claim → Bool
  | .directDecision .. => false
  | .nativeProof .. => false
  | .admittedFlow .. => false
  | .certificateBoundary .. => true

@[simp] theorem directDecision_certificate_free
    {Claim : Type uBase} (Meaning : Claim → Prop)
    (kernel : DecisionKernel Claim Meaning) :
    requiresCertificate (.directDecision Meaning kernel) = false := rfl

@[simp] theorem nativeProof_has_no_separate_certificate_language
    {Claim : Type uBase}
    (guest : NativeProofSystem.{uBase, uValue} Claim)
    (kernel : NativeProofKernel guest) :
    requiresCertificate (.nativeProof guest kernel) = false := rfl

@[simp] theorem admittedFlow_has_no_interior_certificate
    {Claim : Type uBase} (source : AdmissionObject.{uBase})
    (Meaning : Claim → Prop)
    (operation : source ⟶ claimAdmissionObject Meaning) :
    requiresCertificate (.admittedFlow source Meaning operation) = false := rfl

@[simp] theorem boundary_requires_certificate
    {Claim : Type uBase} (Certificate : Type uValue)
    (Meaning : Claim → Prop) (checker : Checker Claim Certificate)
    (authority : checker.Authority Meaning) :
    requiresCertificate
      (.certificateBoundary Certificate Meaning checker authority) = true := rfl

/-- The Data counit is independent of how the value earned admission.  Entry
may check; ordinary use of already-admitted Data never checks itself again. -/
theorem eval_after_admission
    {Claim : Type uBase} (mode : EntryMode.{uBase, uValue} Claim)
    (value : Data Stamp BaseEl payload) :
    eval value = value.2 := by
  cases mode <;> rfl

/-- An admitted-flow operation preserves its target meaning by applying the
proof retained at admission time; no checker or certificate is an argument. -/
theorem admitted_run_preserves
    {Claim : Type uBase} {source : AdmissionObject.{uBase}}
    {Meaning : Claim → Prop}
    (operation : source ⟶ claimAdmissionObject Meaning)
    (value : source.Carrier) (meaningful : source.Meaning value) :
    Meaning (operation.run value) :=
  operation.preserves value meaningful

/-! ### Exact bridge to the canonical NIK service doctrine -/

/-- Every Data-local entry mode is one canonical NIK service over exactly the
meaning selected by that mode.  In particular, admitted computation maps to a
native operation, not to a certificate checker. -/
def toNIKService {Claim : Type uBase}
    (mode : EntryMode.{uBase, uValue} Claim) :
    Mettapedia.GSLT.LanguageDef.NIK.Service
      (claimAdmissionObject (Accepted mode)) :=
  match mode with
  | .directDecision _Meaning kernel => .directDecision kernel
  | .nativeProof guest kernel =>
      .nativeProof guest kernel (fun _claim => Iff.rfl)
  | .admittedFlow source _Meaning operation =>
      .nativeOperation source operation
  | .certificateBoundary Certificate _Meaning checker authority =>
      .certificateBoundary Certificate checker authority

/-- The Data-local discriminator agrees exactly with the canonical service
discriminator. -/
@[simp] theorem toNIKService_external_boundary
    {Claim : Type uBase} (mode : EntryMode.{uBase, uValue} Claim) :
    Mettapedia.GSLT.LanguageDef.NIK.Service.hasExternalCertificateBoundary
        (toNIKService mode) =
      requiresCertificate mode := by
  cases mode <;> rfl

/-! ### Nondegenerate mode witnesses -/

def trueDecisionKernel : DecisionKernel Bool (fun claim => claim = true) where
  decide := _root_.id
  correct := by intro claim; cases claim <;> simp

def directWitness : EntryMode Bool :=
  .directDecision (fun claim => claim = true) trueDecisionKernel

def booleanProofSystem : NativeProofSystem Bool where
  ProofObject := PUnit
  Judges := fun _ claim => claim = true

def booleanProofKernel : NativeProofKernel booleanProofSystem where
  decide := fun claim _ => claim
  correct := by intro claim proof; cases claim <;> simp [booleanProofSystem]

def nativeProofWitness : EntryMode Bool :=
  .nativeProof booleanProofSystem booleanProofKernel

def positiveSuccessor :
    AdmissionCanary.positiveNaturals ⟶
      claimAdmissionObject (fun value : Nat => value ≠ 0) :=
  AdmissionCanary.successor

def admittedFlowWitness : EntryMode Nat :=
  .admittedFlow AdmissionCanary.positiveNaturals
    (fun value => value ≠ 0) positiveSuccessor

def haltingBoundaryWitness : EntryMode Nat.Partrec.Code :=
  .certificateBoundary Nat HaltingMeaning haltingTrustBoundaryChecker
    haltingTrustBoundaryAuthority

theorem direct_positive : Accepted directWitness true := rfl

theorem direct_negative : ¬ Accepted directWitness false := by
  simp [Accepted, directWitness]

theorem nativeProof_positive : Accepted nativeProofWitness true := by
  exact ⟨⟨PUnit.unit, rfl⟩⟩

theorem nativeProof_negative : ¬ Accepted nativeProofWitness false := by
  rintro ⟨⟨proof, judged⟩⟩
  exact Bool.false_ne_true judged

theorem admittedFlow_positive :
    Accepted admittedFlowWitness (positiveSuccessor.run (1 : Nat)) :=
  positiveSuccessor.preserves (1 : Nat) (by
    change (1 : Nat) ≠ 0
    decide)

theorem certificate_mode_is_strictly_separate :
    requiresCertificate haltingBoundaryWitness = true ∧
      requiresCertificate directWitness = false ∧
      requiresCertificate nativeProofWitness = false ∧
      requiresCertificate admittedFlowWitness = false := by
  decide

end EntryMode

/-! ## Data over the actual category of validated language codes

The abstract diagram above is instantiated here on the repository's authored
category of validated GSLT presentations and structural morphisms.  Base type
codes are exact authored sorts, rather than unstructured strings.  This is the
first general language-code family; the later operational instance enriches
its inhabitants with semantic states. -/

namespace ValidatedLanguageData

open Mettapedia.GSLT.LanguageDef

/-- The language codes are the exact validated presentations already used by
the native theory's Tarski language-code universe. -/
abbrev LangCode := ValidatedLanguageDef

/-- One fibre over an arbitrary validated language.  Its inhabitants are
actual closed, well-sorted object terms at the selected authored sort; the
fibre therefore transports held syntax rather than merely transporting a
sort label with a unit witness. -/
def fibre (language : LangCode) : Fibre where
  BaseType := StructuralMorphism.DeclaredSort language
  BaseEl := fun sort =>
    ClosedTerm language.language (declaredSortToLangSort language sort)
  Stamp := Bool

/-- Every structural GSLT morphism transports authored sorts and their held
Data. -/
def translation {source target : LangCode} (route : source ⟶ target) :
    FibreTranslation (fibre source) (fibre target) where
  mapBase := route.mapSort
  mapBaseEl := fun {_type} term =>
    ⟨mapPattern route.symbols term.1,
      ClosedTermWellSorted.map route rfl term.2⟩
  mapStamp := _root_.id

theorem translation_mapType_id (language : LangCode)
    (type : DataType (fibre language).BaseType) :
    type.map (translation (CategoryTheory.CategoryStruct.id language)).mapBase =
      type := by
  induction type with
  | base sort =>
      simp only [DataType.map_base]
      apply congrArg DataType.base
      change (StructuralMorphism.id language).mapSort sort = sort
      exact StructuralMorphism.mapSort_id language sort
  | data payload inductionHypothesis => simp [inductionHypothesis]

theorem translation_mapType_comp {first middle last : LangCode}
    (earlier : first ⟶ middle) (later : middle ⟶ last)
    (type : DataType (fibre first).BaseType) :
    type.map
        (translation
          (CategoryTheory.CategoryStruct.comp earlier later)).mapBase =
      (type.map (translation earlier).mapBase).map
        (translation later).mapBase := by
  induction type with
  | base sort =>
      simp only [DataType.map_base]
      apply congrArg DataType.base
      change (StructuralMorphism.comp earlier later).mapSort sort =
        later.mapSort (earlier.mapSort sort)
      exact StructuralMorphism.mapSort_comp earlier later sort
  | data payload inductionHypothesis => simp [inductionHypothesis]

theorem translation_mapInterpret_id (language : LangCode)
    (type : DataType (fibre language).BaseType)
    (value : interpret (fibre language).Stamp (fibre language).BaseEl type) :
    HEq
      ((translation
        (CategoryTheory.CategoryStruct.id language)).mapInterpret type value)
      value := by
  induction type with
  | base sort =>
      apply heq_of_eq
      exact (by
        apply Subtype.ext
        exact mapPattern_id value.1)
  | data payload inductionHypothesis =>
      rcases value with ⟨stamp, inner⟩
      simp only [FibreTranslation.mapInterpret, translation, DataType.map_data]
      exact FibreTranslation.prod_heq HEq.rfl (inductionHypothesis inner)

theorem translation_mapInterpret_comp {first middle last : LangCode}
    (earlier : first ⟶ middle) (later : middle ⟶ last)
    (type : DataType (fibre first).BaseType)
    (value : interpret (fibre first).Stamp (fibre first).BaseEl type) :
    HEq
      ((translation
        (CategoryTheory.CategoryStruct.comp earlier later)).mapInterpret
          type value)
      ((translation later).mapInterpret
        (type.map (translation earlier).mapBase)
        ((translation earlier).mapInterpret type value)) := by
  induction type with
  | base sort =>
      apply heq_of_eq
      exact (by
        apply Subtype.ext
        exact mapPattern_comp earlier.symbols later.symbols value.1)
  | data payload inductionHypothesis =>
      rcases value with ⟨stamp, inner⟩
      simp only [FibreTranslation.mapInterpret, translation, DataType.map_data]
      exact FibreTranslation.prod_heq HEq.rfl (inductionHypothesis inner)

/-- The actual category of validated language codes acts functorially on
typed Data. -/
def indexedDiagram : IndexedDataDiagram LangCode where
  fibre := fibre
  map := translation
  map_id := by
    intro language value
    rcases value with ⟨type, value⟩
    apply Sigma.ext
    · exact translation_mapType_id language type
    · exact translation_mapInterpret_id language (.data type) value
  map_comp := by
    intro first middle last earlier later value
    rcases value with ⟨type, value⟩
    apply Sigma.ext
    · exact translation_mapType_comp earlier later type
    · exact translation_mapInterpret_comp earlier later (.data type) value

/-- `TypeOf ℓ` in the requested dependent shape. -/
abbrev TypeOf (language : LangCode) :=
  IndexedDataDiagram.TypeOf indexedDiagram language

/-- `Data ℓ A` in the requested dependent shape. -/
abbrev DataAt (language : LangCode) (type : TypeOf language) :=
  IndexedDataDiagram.DataAt indexedDiagram language type

/-- Quote a genuine closed term at an authored sort. -/
def quoteTerm (language : LangCode)
    (sort : StructuralMorphism.DeclaredSort language)
    (term : ClosedTerm language.language
      (declaredSortToLangSort language sort))
    (stamp : Bool) : DataAt language (.base sort) :=
  (stamp, term)

@[simp] theorem eval_quoteTerm (language : LangCode)
    (sort : StructuralMorphism.DeclaredSort language)
    (term : ClosedTerm language.language
      (declaredSortToLangSort language sort)) (stamp : Bool) :
    eval (quoteTerm language sort term stamp) = term := rfl

/-! ### Concrete non-vacuity controls -/

open Mettapedia.Languages.MeTTa.Prime.LanguageDef in
/-- The authored `Atom` sort in today's Prime presentation. -/
def currentPrimeAtomSort :
    StructuralMorphism.DeclaredSort currentPrimePresentation :=
  ⟨Mettapedia.Languages.MeTTa.MeTTaZero.atomType, by
    change List.Mem Mettapedia.Languages.MeTTa.MeTTaZero.atomType
      [Mettapedia.Languages.MeTTa.MeTTaZero.atomType,
       Mettapedia.Languages.MeTTa.MeTTaZero.spaceType,
       Mettapedia.Languages.MeTTa.MeTTaZero.processType,
       Mettapedia.Languages.MeTTa.MeTTaZero.alternativesType,
       nameType, receiptType]
    exact List.mem_cons_self⟩

open Mettapedia.Languages.MeTTa.Prime.LanguageDef in
/-- A concrete, closed Prime term inhabits the strengthened Data fibre. -/
def currentPrimeUnitTerm :
    ClosedTerm currentPrimePresentation.language
      (declaredSortToLangSort currentPrimePresentation currentPrimeAtomSort) := by
  let unitPattern : Pattern := .apply "prime-unit" []
  refine ⟨unitPattern, ?_⟩
  have typed : HasSort currentPrimePresentation.language FreeTypeContext.empty []
      unitPattern "Atom" := by
    apply HasType.constructor (rule := unitConstructor)
    · simp [currentPrimePresentation, language]
    · rintro ⟨parameterName, collectionType, elementType, shape⟩
      have impossible := congrArg List.length shape
      change (0 : Nat) = 1 at impossible
      omega
    · exact ArgumentsHaveTypes.nil
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [currentPrimePresentation, currentPrimeAtomSort,
      declaredSortToLangSort,
      Mettapedia.Languages.MeTTa.MeTTaZero.atomType, TypeDecl.plain] using typed
  · rfl
  · rfl
  · rfl
  · rfl

/-- Positive witness: the actual validated-language fibre holds syntax, not a
unit placeholder. -/
def currentPrimeUnitData :
    DataAt
      Mettapedia.Languages.MeTTa.Prime.LanguageDef.currentPrimePresentation
      (.base currentPrimeAtomSort) :=
  quoteTerm _ currentPrimeAtomSort currentPrimeUnitTerm false

@[simp] theorem currentPrimeUnitData_payload :
    (eval currentPrimeUnitData).1 = .apply "prime-unit" [] :=
  rfl

open Mettapedia.Languages.MeTTa.Prime.LanguageDef in
/-- Negative witness: an unbound free variable cannot be smuggled into closed
Prime Data merely by selecting the `Atom` sort. -/
theorem free_variable_not_currentPrimeAtom :
    ¬ ClosedTermWellSorted currentPrimePresentation.language
      (declaredSortToLangSort currentPrimePresentation currentPrimeAtomSort)
      (.fvar "unbound") := by
  intro purported
  cases purported.1 with
  | fvar lookup => simp [FreeTypeContext.empty] at lookup

/-- Transport changes constructor heads according to the structural route and
retains the exact held object term as the Data payload. -/
@[simp] theorem translation_mapBaseEl_pattern
    {source target : LangCode} (route : source ⟶ target)
    {sort : StructuralMorphism.DeclaredSort source}
    (term : ClosedTerm source.language
      (declaredSortToLangSort source sort)) :
    ((translation route).mapBaseEl term).1 =
      mapPattern route.symbols term.1 :=
  rfl

/-- Language-changing Data retains the exact authored-sort action of the
structural GSLT morphism. -/
theorem root_preserved {source target : LangCode} (route : source ⟶ target)
    (value : FibreTranslation.AllData (fibre source)) :
    ((translation route).mapAllData value).1.root =
      route.mapSort value.1.root := by
  rcases value with ⟨type, value⟩
  exact DataType.root_map (translation route).mapBase type

/-- Every actual language-code route has the canonical strongly cocartesian
Data lift furnished by the general construction. -/
theorem route_lift_is_strongly_cocartesian
    (object : IndexedDataDiagram.DataTotal indexedDiagram)
    {target : LangCode} (route : object.1 ⟶ target) :
    (IndexedDataDiagram.projection indexedDiagram).IsStronglyCocartesian route
      (IndexedDataDiagram.pushforwardLift indexedDiagram object route) := by
  infer_instance

end ValidatedLanguageData

/-! ## Orthogonal program-typing axes and legacy syntax refinements -/

/-- Precision information is not evaluation control.  `dynamic` is gradual
unknown; `atomTop` is the inert top of the value lattice. -/
inductive ValueType where
  | dynamic
  | atomTop
  | number
  | string
  deriving DecidableEq, Repr

/-- Evaluation control is a separate modal axis. -/
inductive EvaluationControl where
  | ambient
  | held
  deriving DecidableEq, Repr

/-- A program classification records both axes without allowing either to
silently determine the other. -/
structure ProgramType where
  valueType : ValueType
  control : EvaluationControl
  deriving DecidableEq, Repr

def pDynamicProgramType : ProgramType := ⟨.dynamic, .ambient⟩
def atomProgramType : ProgramType := ⟨.atomTop, .ambient⟩
def dataProgramType (payload : ValueType) : ProgramType := ⟨payload, .held⟩

/-- Gradual consistency is deliberately not transitive. -/
def Consistent : ValueType → ValueType → Prop
  | .dynamic, _ => True
  | _, .dynamic => True
  | left, right => left = right

/-- Subtyping has an ordinary inert top and remains transitive. -/
def Subtype : ValueType → ValueType → Prop
  | _, .atomTop => True
  | left, right => left = right

theorem subtype_transitive :
    ∀ {first middle last}, Subtype first middle → Subtype middle last →
      Subtype first last := by
  intro first middle last firstToMiddle middleToLast
  cases first <;> cases middle <;> cases last <;>
    simp_all [Subtype]

theorem dynamic_consistency_is_nontransitive :
    Consistent .number .dynamic ∧ Consistent .dynamic .string ∧
      ¬ Consistent .number .string := by
  simp [Consistent]

theorem atom_is_inert_top (type : ValueType) :
    Subtype type .atomTop ∧ atomProgramType.control = .ambient := by
  exact ⟨by cases type <;> trivial, rfl⟩

theorem dynamic_atom_data_are_pairwise_distinct (payload : ValueType) :
    pDynamicProgramType ≠ atomProgramType ∧
      atomProgramType ≠ dataProgramType payload ∧
      pDynamicProgramType ≠ dataProgramType payload := by
  constructor
  · intro equal
    injection equal with precision
    cases precision
  constructor <;> intro equal <;> injection equal with _ control <;>
    cases control

/-- Each space selects only its ambient polarity.  Explicit `!` always asks
for evaluation; explicit Data quotation always asks for holding. -/
inductive SpacePolarity where
  | evaluateByDefault
  | dataByDefault
  deriving DecidableEq, Repr

def ambientControl : SpacePolarity → EvaluationControl
  | .evaluateByDefault => .ambient
  | .dataByDefault => .held

def bangControl (_ : SpacePolarity) : EvaluationControl := .ambient
def quoteControl (_ : SpacePolarity) : EvaluationControl := .held

theorem polarity_changes_only_the_ambient :
    ambientControl .evaluateByDefault ≠ ambientControl .dataByDefault ∧
      bangControl .evaluateByDefault = bangControl .dataByDefault ∧
      quoteControl .evaluateByDefault = quoteControl .dataByDefault := by
  decide

/-- Syntax held as Data.  Grounded hooks are explicit because the locally
nameless `Pattern` syntax does not itself carry their runtime payload. -/
inductive HeldSyntax where
  | pattern (term : Pattern)
  | grounded (hook : String)
  deriving DecidableEq, Repr

/-- The four legacy HE meta-types become disjoint refinements of held syntax,
not evaluation-changing value types. -/
inductive SyntaxShape where
  | symbol
  | variable
  | expression
  | grounded
  deriving DecidableEq, Repr

def classifySyntax : HeldSyntax → SyntaxShape
  | .grounded _ => .grounded
  | .pattern (.bvar _) => .variable
  | .pattern (.fvar _) => .variable
  | .pattern (.apply _ []) => .symbol
  | .pattern _ => .expression

def HasShape (term : HeldSyntax) (shape : SyntaxShape) : Prop :=
  classifySyntax term = shape

/-- Every held syntax object has exactly one legacy refinement. -/
theorem syntax_refinements_partition (term : HeldSyntax) :
    ∃! shape, HasShape term shape := by
  exact ⟨classifySyntax term, rfl, fun shape equal => equal.symm⟩

/-- A genuine Data fibre refined by one syntax shape. -/
def RefinedSyntaxData (shape : SyntaxShape) :=
  Σ term : { held : HeldSyntax // HasShape held shape },
    Data Bool (fun _ : HeldSyntax => PUnit) (.base term.1)

def symbolData : RefinedSyntaxData .symbol :=
  ⟨⟨.pattern (.apply "held-symbol" []), rfl⟩, (false, PUnit.unit)⟩

def variableData : RefinedSyntaxData .variable :=
  ⟨⟨.pattern (.fvar "held-variable"), rfl⟩, (false, PUnit.unit)⟩

def expressionData : RefinedSyntaxData .expression :=
  ⟨⟨.pattern (.apply "held-application" [.apply "argument" []]), rfl⟩,
    (false, PUnit.unit)⟩

def groundedData : RefinedSyntaxData .grounded :=
  ⟨⟨.grounded "native-hook", rfl⟩, (false, PUnit.unit)⟩

theorem grounded_is_not_expression :
    ¬ HasShape groundedData.1.1 .expression := by
  simp [HasShape, classifySyntax, groundedData]

/-! ## The current Zero-to-Prime operational instance -/

namespace CurrentOperationalData

abbrev CurrentModel :=
  Mettapedia.Languages.MeTTa.Prime.Language.QueryFirstModel

abbrev TheoryAt (model : CurrentModel) (stage : Stage) :=
  ((IndexedLanguageChange.diagram model).obj stage).theory

/-- A semantic state is carried by the type index itself.  Its term-level
inhabitant is only the canonical witness; no duplicate state payload and no
replay transcript are retained. -/
abbrev StateWitness {theory : GSLT} (_expected : SemanticTerm theory) := PUnit

/-- The current selected language fibre: operational semantic terms as base
types, exact-state inhabitants, and a nontrivial one-bit quotation stamp. -/
def fibre (model : CurrentModel) (stage : Stage) : Fibre where
  BaseType := SemanticTerm (TheoryAt model stage)
  BaseEl := StateWitness
  Stamp := Bool

/-- The live operational translation lifted through exact-state inhabitants. -/
def translation (model : CurrentModel) {source target : Stage}
    (route : source ⟶ target) :
    FibreTranslation (fibre model source) (fibre model target) where
  mapBase := transportTerm (IndexedLanguageChange.diagram model) route
  mapBaseEl := _root_.id
  mapStamp := _root_.id

/-- The type action is the existing operational state map, including at
identity routes. -/
theorem translation_mapBase (model : CurrentModel)
    {source target : Stage} (route : source ⟶ target)
    (state : SemanticTerm (TheoryAt model source)) :
    (translation model route).mapBase state =
      transportTerm (IndexedLanguageChange.diagram model) route state := by
  rfl

/-- Identity transport preserves every intensional Data code. -/
theorem translation_mapType_id (model : CurrentModel) (stage : Stage)
    (type : DataType (fibre model stage).BaseType) :
    type.map (translation model (CategoryTheory.CategoryStruct.id stage)).mapBase =
      type := by
  induction type with
  | base state => simp [translation]
  | data payload inductionHypothesis => simp [inductionHypothesis]

/-- Composite transport acts compositionally on intensional Data codes. -/
theorem translation_mapType_comp (model : CurrentModel)
    {first middle last : Stage}
    (earlier : first ⟶ middle) (later : middle ⟶ last)
    (type : DataType (fibre model first).BaseType) :
    type.map
        (translation model
          (CategoryTheory.CategoryStruct.comp earlier later)).mapBase =
      (type.map (translation model earlier).mapBase).map
        (translation model later).mapBase := by
  induction type with
  | base state => simp [translation]
  | data payload inductionHypothesis => simp [inductionHypothesis]

/-- Identity language transport acts identically on every nested Data
inhabitant, including the exact-state proof carried at the base. -/
theorem translation_mapInterpret_id (model : CurrentModel) (stage : Stage)
    (type : DataType (fibre model stage).BaseType)
    (value : interpret (fibre model stage).Stamp
      (fibre model stage).BaseEl type) :
    HEq
      ((translation model
        (CategoryTheory.CategoryStruct.id stage)).mapInterpret type value)
      value := by
  induction type with
  | base state => rfl
  | data payload inductionHypothesis =>
      rcases value with ⟨stamp, inner⟩
      simp only [FibreTranslation.mapInterpret, translation, DataType.map_data]
      exact FibreTranslation.prod_heq HEq.rfl (inductionHypothesis inner)

/-- Composite language transport agrees with successive transport on every
nested Data inhabitant. -/
theorem translation_mapInterpret_comp (model : CurrentModel)
    {first middle last : Stage}
    (earlier : first ⟶ middle) (later : middle ⟶ last)
    (type : DataType (fibre model first).BaseType)
    (value : interpret (fibre model first).Stamp
      (fibre model first).BaseEl type) :
    HEq
      ((translation model
        (CategoryTheory.CategoryStruct.comp earlier later)).mapInterpret
          type value)
      ((translation model later).mapInterpret
        (type.map (translation model earlier).mapBase)
        ((translation model earlier).mapInterpret type value)) := by
  induction type with
  | base state => rfl
  | data payload inductionHypothesis =>
      rcases value with ⟨stamp, inner⟩
      simp only [FibreTranslation.mapInterpret, translation, DataType.map_data]
      exact FibreTranslation.prod_heq HEq.rfl (inductionHypothesis inner)

/-- Today's two-point language diagram acts functorially on typed Data. -/
def indexedDiagram (model : CurrentModel) : IndexedDataDiagram Stage where
  fibre := fibre model
  map := translation model
  map_id := by
    intro stage value
    rcases value with ⟨type, value⟩
    apply Sigma.ext
    · exact translation_mapType_id model stage type
    · exact translation_mapInterpret_id model stage (.data type) value
  map_comp := by
    intro first middle last earlier later value
    rcases value with ⟨type, value⟩
    apply Sigma.ext
    · exact translation_mapType_comp model earlier later type
    · exact translation_mapInterpret_comp model earlier later (.data type) value

/-- The operational state indexed by a total Data value. -/
def stateOf (model : CurrentModel) (stage : Stage)
    (value : FibreTranslation.AllData (fibre model stage)) :
    SemanticTerm (TheoryAt model stage) :=
  value.1.root

/-- State preservation is not an extra replay relation: it follows from the
typed action on the exact semantic-state index. -/
theorem state_preserved (model : CurrentModel)
    {source target : Stage} (route : source ⟶ target)
    (value : FibreTranslation.AllData (fibre model source)) :
    stateOf model target ((translation model route).mapAllData value) =
      transportTerm (IndexedLanguageChange.diagram model) route
        (stateOf model source value) := by
  rcases value with ⟨type, value⟩
  exact DataType.root_map (translation model route).mapBase type

/-- A concrete typed Data value at any selected semantic state. -/
def exactData (model : CurrentModel) (stage : Stage)
    (state : SemanticTerm (TheoryAt model stage))
    (stamp : Bool) : FibreTranslation.AllData (fibre model stage) :=
  ⟨.base state, (stamp, PUnit.unit)⟩

@[simp] theorem stateOf_exactData (model : CurrentModel) (stage : Stage)
    (state : SemanticTerm (TheoryAt model stage))
    (stamp : Bool) :
    stateOf model stage (exactData model stage state stamp) = state := by
  rfl

/-- The existing Zero-to-Prime operational route is exactly the state action
of the language-indexed Data push-forward. -/
theorem promote_preserves_exact_state (model : CurrentModel)
    (state : SemanticTerm (ZeroTheory model)) (stamp : Bool) :
    stateOf model primeStage
      ((translation model promote).mapAllData
        (exactData model zeroStage state stamp)) =
      transportTerm (IndexedLanguageChange.diagram model) promote state := by
  exact state_preserved model promote (exactData model zeroStage state stamp)

/-- The selected promotion has the canonical strongly cocartesian Data lift. -/
theorem promotion_lift_is_strongly_cocartesian
    (model : CurrentModel)
    (state : SemanticTerm (ZeroTheory model)) (stamp : Bool) :
    ((indexedDiagram model).projection).IsStronglyCocartesian promote
      ((indexedDiagram model).pushforwardLift
        ⟨zeroStage, exactData model zeroStage state stamp⟩ promote) := by
  infer_instance

/-- Negative direction: the current Data opfibration has no reverse
Prime-to-Zero push-forward because the base language category has no route. -/
theorem no_reverse_pushforward :
    ¬ Nonempty (primeStage ⟶ zeroStage) :=
  no_reverse_language_change

end CurrentOperationalData

end Mettapedia.Languages.MeTTa.Prime.DataFibration
