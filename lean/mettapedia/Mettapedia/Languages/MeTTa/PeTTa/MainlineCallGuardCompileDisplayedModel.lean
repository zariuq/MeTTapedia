import Mettapedia.OSLF.Framework.SelectedNativeTypeAuthoredVariableClaim
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileIntroductionSemantics

/-!
# A shared-world displayed model for the generated call-guard calculus

The generated binder-free calculus mixes direct carrier judgments,
contextual judgments, exact occurrence claims, and source-bound guard claims.
This module gives those formula families one independent proof-relevant
interpretation.

A semantic world is one authentic source match for one exact authored cold
rewrite occurrence.  In particular, guard evidence is indexed by that one
world: evidence from unrelated matches cannot be combined merely because its
propositional truth values happen to agree.  Carrier typing and displayed
modal meaning remain supplied by an external `CarrierModel`; neither checker
acceptance nor generated derivability occurs below.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileDisplayedModel

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.ContextualInference
open Mettapedia.GSLT.LanguageDef.ContextualInferenceSemantics
open Mettapedia.OSLF.Framework
open Mettapedia.OSLF.Framework.ContextualFamilyApplication
open Mettapedia.OSLF.Framework.SelectedNativeTypeAuthoredOccurrenceSyntax
open Mettapedia.OSLF.Framework.SelectedNativeTypeBoundRelationClaim
open Mettapedia.OSLF.Framework.SelectedNativeTypeContextualCalculus
open Mettapedia.OSLF.Framework.SelectedNativeTypeDisplayedSemantics
open Mettapedia.OSLF.Framework.SelectedNativeTypeSourceIndexedCarrierSupport
open Mettapedia.OSLF.Framework.SelectedNativeTypeSourceIndexedFormationSemantics
open Mettapedia.OSLF.Framework.SelectedNativeTypeSourceIndexedIntroduction
open Mettapedia.OSLF.Framework.SelectedNativeTypeSourceIndexedSemanticDecoding
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardOperational
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileNTT
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileSourceIndexedNTT
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileGuardedContextSemantics
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileIntroductionSemantics

/-- One exact selected star/box occurrence of the cold compiler. -/
abbrev Occurrence :=
  SelectedNativeTypeContextualCalculus.Occurrence demand

abbrev CarrierSlot :=
  SelectedNativeTypeSourceIndexedSemanticDecoding.CarrierSlot demand

/-- One proof-relevant semantic world.  The world retains the selected source
occurrence, the concrete state matched by that occurrence, and the one matcher
environment shared by every explicit formula in a contextual judgment. -/
structure ActivationWorld where
  slot : Occurrence
  before : Pattern
  environment : ActivationEnvironment slot before

/-- Request slot of a selected occurrence's rewrite-result carrier. -/
theorem rewriteType_required (slot : Occurrence) :
    (typingAt demand slot).rewriteType ∈
      SelectedNativeTypeFoundation.requiredCarrierRoots
        (typingAt demand slot) := by
  simp [SelectedNativeTypeFoundation.requiredCarrierRoots]

/-- Proof-relevant request slot of the selected rewrite-result carrier. -/
def rewriteCarrier (slot : Occurrence) : CarrierSlot :=
  requiredCarrierSlot demand slot (rewriteType_required slot)

@[simp] theorem rewriteCarrier_expression (slot : Occurrence) :
    (rewriteCarrier slot).expression = (typingAt demand slot).rewriteType := by
  simp [rewriteCarrier, requiredCarrierSlot]

@[simp] theorem rewriteCarrier_name (slot : Occurrence) :
    carrierName (rewriteCarrier slot) =
      sourceCarrierAt demand (typingAt demand slot).rewriteType := by
  exact carrierName_requiredCarrierSlot demand slot
    (rewriteType_required slot)

/-- Only modal and defunctionalized-family heads need a specialized
interpretation.  Universe objects and authored terms remain in the ordinary
carrier interpretation. -/
def ordinaryTypingTerm (term : Pattern) : Bool :=
  match decodeApplication? demand term with
  | some { head := .modal _, arguments := _ } => false
  | some { head := .familyApplication _, arguments := _ } => false
  | _ => true

/-- A selected cold root has no contextual rely values in its authored
family application. -/
@[simp] theorem authoredRelyValues_eq_nil (slot : Occurrence) :
    authoredRelyValues demand slot = [] := by
  simp [authoredRelyValues, selected_bindings_eq_nil]

/-- A selected cold root likewise has no contextual rely-type parameters in
its modal application. -/
@[simp] theorem relyTypes_eq_nil (slot : Occurrence) :
    relyTypes demand slot = [] := by
  simp [relyTypes, selected_bindings_eq_nil]

theorem authoredFamilyApplication_eq (slot : Occurrence)
    (family : Pattern) :
    authoredFamilyApplication demand slot family =
      ({ head := .familyApplication slot
         arguments := [family] } : ApplicationView demand).encode := by
  simp [authoredFamilyApplication,
    ContextualFamilyApplication.applyFamily, ApplicationView.encode,
    encodeHead]

theorem modalType_eq (slot : Occurrence) (family : Pattern) :
    modalType demand slot family =
      ({ head := .modal slot
         arguments := [family] } : ApplicationView demand).encode := by
  simp [modalType, ApplicationView.encode, encodeHead]

@[simp] theorem decodeApplication_authoredFamilyApplication
    (slot : Occurrence) (family : Pattern) :
    decodeApplication? demand
        (authoredFamilyApplication demand slot family) =
      some
        ({ head := .familyApplication slot
           arguments := [family] } : ApplicationView demand) := by
  rw [authoredFamilyApplication_eq]
  apply decodeApplication?_encode
  simp [ApplicationView.ShapeValid, arity, selected_bindings_eq_nil]

@[simp] theorem decodeApplication_modalType
    (slot : Occurrence) (family : Pattern) :
    decodeApplication? demand (modalType demand slot family) =
      some
        ({ head := .modal slot
           arguments := [family] } : ApplicationView demand) := by
  rw [modalType_eq]
  apply decodeApplication?_encode
  simp [ApplicationView.ShapeValid, arity, selected_bindings_eq_nil]

@[simp] theorem ordinaryTypingTerm_authoredFamilyApplication
    (slot : Occurrence) (family : Pattern) :
    ordinaryTypingTerm (authoredFamilyApplication demand slot family) =
      false := by
  unfold ordinaryTypingTerm
  rw [decodeApplication_authoredFamilyApplication]

@[simp] theorem ordinaryTypingTerm_modalType
    (slot : Occurrence) (family : Pattern) :
    ordinaryTypingTerm (modalType demand slot family) = false := by
  unfold ordinaryTypingTerm
  rw [decodeApplication_modalType]

@[simp] theorem ordinaryTypingTerm_rewriteSort
    (slot : Occurrence) (code : CarrierUniverseSignature.Code) :
    ordinaryTypingTerm
        (sortCode
          (sourceCarrierAt demand (typingAt demand slot).rewriteType)
          code) = true := by
  rw [← rewriteCarrier_name]
  unfold sortCode ordinaryTypingTerm
  rw [decodeApplication?_carrierUniverse]

@[simp] theorem ordinaryTypingTerm_focusSort
    (slot : Occurrence) (code : CarrierUniverseSignature.Code) :
    ordinaryTypingTerm
        (sortCode
          (sourceCarrierAt demand (typingAt demand slot).focusType)
          code) = true := by
  rw [← MainlineCallGuardCompileFormationSemantics.focusCarrier_name]
  unfold sortCode ordinaryTypingTerm
  rw [decodeApplication?_carrierUniverse]

private theorem typingClaim_components
    {firstCarrier secondCarrier : String}
    {firstTerm secondTerm firstType secondType : Pattern}
    (equality :
      ContextualCarrierClaims.typingClaim
          firstCarrier firstTerm firstType =
        ContextualCarrierClaims.typingClaim
          secondCarrier secondTerm secondType) :
    firstTerm = secondTerm ∧ firstType = secondType := by
  injection equality with _ argumentsEquality
  injection argumentsEquality with termEquality tailEquality
  injection tailEquality with typeEquality _
  exact ⟨termEquality, typeEquality⟩

@[simp] theorem decodeGeneratedFormula_bodyClaim
    (slot : Occurrence) (target family : Pattern) :
    decodeGeneratedFormula? demand
        (ContextualCarrierClaims.typingClaim
          (sourceCarrierAt demand (typingAt demand slot).rewriteType)
          target (authoredFamilyApplication demand slot family)) =
      some (.typingClaim (rewriteCarrier slot) target
        (authoredFamilyApplication demand slot family)) := by
  simpa [encodeGeneratedFormula] using
    (decodeGeneratedFormula?_encodeGeneratedFormula
      (.typingClaim (rewriteCarrier slot) target
        (authoredFamilyApplication demand slot family)))

@[simp] theorem decodeGeneratedFormula_modalClaim
    (slot : Occurrence) (focus family : Pattern) :
    decodeGeneratedFormula? demand
        (ContextualCarrierClaims.typingClaim
          (sourceCarrierAt demand (typingAt demand slot).focusType)
          focus (modalType demand slot family)) =
      some (.typingClaim
        (MainlineCallGuardCompileFormationSemantics.focusCarrier slot)
        focus (modalType demand slot family)) := by
  simpa [encodeGeneratedFormula] using
    (decodeGeneratedFormula?_encodeGeneratedFormula
      (.typingClaim
        (MainlineCallGuardCompileFormationSemantics.focusCarrier slot)
        focus (modalType demand slot family)))

/-- Provenance tag for one independently interpreted formula family. -/
inductive FormulaKind
  | variableClaim
  | directTyping
  | resultFamilySorted
  | bodyTyped
  | modalWellFormed
  | modalMember
  | reduction
  | occurrenceStep
  | guard

abbrev AuthoredBindingIndex (world : ActivationWorld) :=
  SelectedNativeTypeAuthoredVariableClaim.Binding demand world.slot

def authoredBindingAt (world : ActivationWorld)
    (binding : AuthoredBindingIndex world) : String × TypeExpr :=
  SelectedNativeTypeAuthoredVariableClaim.sourceBinding
    demand world.slot binding

def groundedVariableClaim (world : ActivationWorld)
    (binding : AuthoredBindingIndex world) : Pattern :=
  (SelectedNativeTypeAuthoredVariableClaim.groundedView
    demand world.slot binding world.environment.bindings).encode

structure VariableWitness (model : CarrierModel)
    (world : ActivationWorld) where
  binding : AuthoredBindingIndex world
  typed :
    let authored := authoredBindingAt world binding
    model.Typed authored.2
      (applyBindings world.environment.bindings (.fvar authored.1))
      (model.universeObject authored.2 .star)

/-- Independent meaning of one decoded authored-variable claim.  The decoded
wire must be exactly the grounded claim at one binding position of this same
activation world; carrier typing alone is insufficient. -/
structure VariableMeaning (model : CarrierModel) (world : ActivationWorld)
    (view : SelectedNativeTypeAuthoredVariableClaim.View demand) where
  binding : AuthoredBindingIndex world
  viewExact : view =
    SelectedNativeTypeAuthoredVariableClaim.groundedView
      demand world.slot binding world.environment.bindings
  typed :
    let authored := authoredBindingAt world binding
    model.Typed authored.2
      (applyBindings world.environment.bindings (.fvar authored.1))
      (model.universeObject authored.2 .star)

structure DirectTypingWitness (model : CarrierModel) where
  view : CarrierTypingView demand
  termOrdinary : ordinaryTypingTerm view.term = true
  typeOrdinary : ordinaryTypingTerm view.type = true
  meaning : model.Typed view.carrier.expression
    (interpretUniverseTerm model demand view.term)
    (interpretUniverseTerm model demand view.type)

structure ResultFamilySortedWitness (model : CarrierModel)
    (world : ActivationWorld) where
  family : Pattern
  sorted : model.Typed (typingAt demand world.slot).rewriteType family
    (model.universeObject (typingAt demand world.slot).rewriteType
      (ContextualModalProfile.resultCode
        (occurrenceAt demand world.slot).profile))

structure BodyTypedWitness (model : CarrierModel)
    (world : ActivationWorld) where
  family : Pattern
  typed : model.Typed (typingAt demand world.slot).rewriteType
    (applyBindingsForRule language
      (typingAt demand world.slot).site.rewrite world.environment.bindings)
    family

structure ModalWellFormedWitness (model : CarrierModel)
    (world : ActivationWorld) where
  family : Pattern
  wellFormed : (rootFormer world.slot family).WellFormed model

structure ModalMemberWitness (model : CarrierModel)
    (world : ActivationWorld) where
  family : Pattern
  member : (rootFormer world.slot family).Member model relationEnv world.before

structure ReductionWitness where
  carrier : CarrierSlot
  source : Pattern
  target : Pattern
  reduces : langReducesUsing relationEnv language source target

structure OccurrenceStepWitness (world : ActivationWorld) where
  after : Pattern
  occurs : OccursAt relationEnv (typingAt demand world.slot)
    world.before after

structure GuardWitness (world : ActivationWorld) where
  premise : Fin (viewsAt guardProfile world.slot).length
  meaning : (groundedView guardProfile world.slot premise
    world.environment.bindings).Meaning relationEnv

/-- Each semantic family owns a small payload.  The sum is factored through
this tag so the kernel never needs to normalize all family indices as one
large inductive declaration. -/
abbrev FormulaPayload (model : CarrierModel) (world : ActivationWorld) :
    FormulaKind → Type
  | .variableClaim => VariableWitness model world
  | .directTyping => DirectTypingWitness model
  | .resultFamilySorted => ResultFamilySortedWitness model world
  | .bodyTyped => BodyTypedWitness model world
  | .modalWellFormed => ModalWellFormedWitness model world
  | .modalMember => ModalMemberWitness model world
  | .reduction => ReductionWitness
  | .occurrenceStep => OccurrenceStepWitness world
  | .guard => GuardWitness world

/-- One proof-relevant witness tagged by its semantic provenance. -/
abbrev FormulaWitness (model : CarrierModel) (world : ActivationWorld) :=
  Sigma (FormulaPayload model world)

/-- Exact wire denoted by a proof-relevant formula witness. -/
def FormulaWitness.formula {model : CarrierModel} {world : ActivationWorld} :
    FormulaWitness model world → Pattern
  | ⟨.variableClaim, witness⟩ =>
      groundedVariableClaim world witness.binding
  | ⟨.directTyping, witness⟩ =>
      ContextualCarrierClaims.typingClaim
        (carrierName witness.view.carrier) witness.view.term witness.view.type
  | ⟨.resultFamilySorted, witness⟩ =>
      ContextualCarrierClaims.typingClaim
        (sourceCarrierAt demand (typingAt demand world.slot).rewriteType)
        (authoredFamilyApplication demand world.slot witness.family)
        (sortCode
          (sourceCarrierAt demand
            (typingAt demand world.slot).rewriteType)
          (ContextualModalProfile.resultCode
            (occurrenceAt demand world.slot).profile))
  | ⟨.bodyTyped, witness⟩ =>
      ContextualCarrierClaims.typingClaim
        (sourceCarrierAt demand (typingAt demand world.slot).rewriteType)
        (applyBindingsForRule language
          (typingAt demand world.slot).site.rewrite
          world.environment.bindings)
        (authoredFamilyApplication demand world.slot witness.family)
  | ⟨.modalWellFormed, witness⟩ =>
      ContextualCarrierClaims.typingClaim
        (sourceCarrierAt demand (typingAt demand world.slot).focusType)
        (modalType demand world.slot witness.family)
        (sortCode
          (sourceCarrierAt demand (typingAt demand world.slot).focusType)
          (ContextualModalProfile.resultCode
            (occurrenceAt demand world.slot).profile))
  | ⟨.modalMember, witness⟩ =>
      ContextualCarrierClaims.typingClaim
        (sourceCarrierAt demand (typingAt demand world.slot).focusType)
        world.before (modalType demand world.slot witness.family)
  | ⟨.reduction, witness⟩ =>
      ContextualCarrierClaims.reductionClaim
        (carrierName witness.carrier) witness.source witness.target
  | ⟨.occurrenceStep, witness⟩ =>
      SelectedNativeTypeOccurrenceStepClaim.claim
        world.slot world.before witness.after
  | ⟨.guard, witness⟩ =>
      (groundedView guardProfile world.slot witness.premise
        world.environment.bindings).encode

/-- A formula has meaning exactly when a semantic witness reconstructs its
wire.  The explicit reconstruction equation makes every later inversion use
the public fail-closed decoders. -/
structure FormulaEvidence (model : CarrierModel) (world : ActivationWorld)
    (formula : Pattern) where
  witness : FormulaWitness model world
  formulaExact : witness.formula = formula

def FormulaEvidence.variable (model : CarrierModel) (world : ActivationWorld)
    (binding : AuthoredBindingIndex world)
    (typed :
      let authored := authoredBindingAt world binding
      model.Typed authored.2
        (applyBindings world.environment.bindings (.fvar authored.1))
        (model.universeObject authored.2 .star)) :
    FormulaEvidence model world
      (groundedVariableClaim world binding) :=
  ⟨⟨.variableClaim, ⟨binding, typed⟩⟩, rfl⟩

def FormulaEvidence.directTyping (model : CarrierModel)
    (world : ActivationWorld) (view : CarrierTypingView demand)
    (termOrdinary : ordinaryTypingTerm view.term = true)
    (typeOrdinary : ordinaryTypingTerm view.type = true)
    (meaning : model.Typed view.carrier.expression
      (interpretUniverseTerm model demand view.term)
      (interpretUniverseTerm model demand view.type)) :
    FormulaEvidence model world
      (ContextualCarrierClaims.typingClaim
        (carrierName view.carrier) view.term view.type) :=
  ⟨⟨.directTyping,
    ⟨view, termOrdinary, typeOrdinary, meaning⟩⟩, rfl⟩

def FormulaEvidence.resultFamilySorted (model : CarrierModel)
    (world : ActivationWorld) (family : Pattern)
    (sorted : model.Typed (typingAt demand world.slot).rewriteType family
      (model.universeObject (typingAt demand world.slot).rewriteType
        (ContextualModalProfile.resultCode
          (occurrenceAt demand world.slot).profile))) :
    FormulaEvidence model world
      (ContextualCarrierClaims.typingClaim
        (sourceCarrierAt demand (typingAt demand world.slot).rewriteType)
        (authoredFamilyApplication demand world.slot family)
        (sortCode
          (sourceCarrierAt demand (typingAt demand world.slot).rewriteType)
          (ContextualModalProfile.resultCode
            (occurrenceAt demand world.slot).profile))) :=
  ⟨⟨.resultFamilySorted, ⟨family, sorted⟩⟩, rfl⟩

def FormulaEvidence.bodyTyped (model : CarrierModel)
    (world : ActivationWorld) (family : Pattern)
    (typed : model.Typed (typingAt demand world.slot).rewriteType
      (applyBindingsForRule language
        (typingAt demand world.slot).site.rewrite
        world.environment.bindings)
      family) :
    FormulaEvidence model world
      (ContextualCarrierClaims.typingClaim
        (sourceCarrierAt demand (typingAt demand world.slot).rewriteType)
        (applyBindingsForRule language
          (typingAt demand world.slot).site.rewrite
          world.environment.bindings)
        (authoredFamilyApplication demand world.slot family)) :=
  ⟨⟨.bodyTyped, ⟨family, typed⟩⟩, rfl⟩

def FormulaEvidence.modalWellFormed (model : CarrierModel)
    (world : ActivationWorld) (family : Pattern)
    (wellFormed : (rootFormer world.slot family).WellFormed model) :
    FormulaEvidence model world
      (ContextualCarrierClaims.typingClaim
        (sourceCarrierAt demand (typingAt demand world.slot).focusType)
        (modalType demand world.slot family)
        (sortCode
          (sourceCarrierAt demand (typingAt demand world.slot).focusType)
          (ContextualModalProfile.resultCode
            (occurrenceAt demand world.slot).profile))) :=
  ⟨⟨.modalWellFormed, ⟨family, wellFormed⟩⟩, rfl⟩

def FormulaEvidence.modalMember (model : CarrierModel)
    (world : ActivationWorld) (family : Pattern)
    (member : (rootFormer world.slot family).Member
      model relationEnv world.before) :
    FormulaEvidence model world
      (ContextualCarrierClaims.typingClaim
        (sourceCarrierAt demand (typingAt demand world.slot).focusType)
        world.before (modalType demand world.slot family)) :=
  ⟨⟨.modalMember, ⟨family, member⟩⟩, rfl⟩

def FormulaEvidence.reduction (model : CarrierModel)
    (world : ActivationWorld) (carrier : CarrierSlot)
    (source target : Pattern)
    (reduces : langReducesUsing relationEnv language source target) :
    FormulaEvidence model world
      (ContextualCarrierClaims.reductionClaim
        (carrierName carrier) source target) :=
  ⟨⟨.reduction, ⟨carrier, source, target, reduces⟩⟩, rfl⟩

def FormulaEvidence.occurrenceStep (model : CarrierModel)
    (world : ActivationWorld) (after : Pattern)
    (occurs : OccursAt relationEnv (typingAt demand world.slot)
      world.before after) :
    FormulaEvidence model world
      (SelectedNativeTypeOccurrenceStepClaim.claim
        world.slot world.before after) :=
  ⟨⟨.occurrenceStep, ⟨after, occurs⟩⟩, rfl⟩

/-- Construct evidence for one exact guard premise in one activation world. -/
def FormulaEvidence.guard (model : CarrierModel) (world : ActivationWorld)
    (premise : Fin (viewsAt guardProfile world.slot).length)
    (meaning :
      (groundedView guardProfile world.slot premise
        world.environment.bindings).Meaning relationEnv) :
    FormulaEvidence model world
      (groundedView guardProfile world.slot premise
        world.environment.bindings).encode :=
  ⟨⟨.guard, ⟨premise, meaning⟩⟩, rfl⟩

/-- Any evidence whose wire decodes as an authored-variable claim supplies
the exact binding position and typing fact from this same activation world.
Every other formula family is rejected by its public constructor namespace. -/
def FormulaEvidence.variableMeaning {model : CarrierModel}
    {world : ActivationWorld} {formula : Pattern}
    (evidence : FormulaEvidence model world formula)
    {view : SelectedNativeTypeAuthoredVariableClaim.View demand}
    (decoded : SelectedNativeTypeAuthoredVariableClaim.decode?
      demand formula = some view) : VariableMeaning model world view := by
  rcases evidence with ⟨witness, formulaExact⟩
  rw [← formulaExact] at decoded
  rcases witness with ⟨kind, payload⟩
  cases kind with
  | variableClaim =>
      rcases payload with ⟨binding, typed⟩
      change SelectedNativeTypeAuthoredVariableClaim.decode? demand
          (SelectedNativeTypeAuthoredVariableClaim.groundedView
            demand world.slot binding world.environment.bindings).encode =
        some view at decoded
      rw [SelectedNativeTypeAuthoredVariableClaim.decode?_encode] at decoded
      exact ⟨binding, (Option.some.inj decoded).symm, typed⟩
  | directTyping =>
      simp [FormulaWitness.formula,
        ContextualCarrierClaims.typingClaim] at decoded
  | resultFamilySorted =>
      simp [FormulaWitness.formula,
        ContextualCarrierClaims.typingClaim] at decoded
  | bodyTyped =>
      simp [FormulaWitness.formula,
        ContextualCarrierClaims.typingClaim] at decoded
  | modalWellFormed =>
      simp [FormulaWitness.formula,
        ContextualCarrierClaims.typingClaim] at decoded
  | modalMember =>
      simp [FormulaWitness.formula,
        ContextualCarrierClaims.typingClaim] at decoded
  | reduction =>
      simp [FormulaWitness.formula,
        ContextualCarrierClaims.reductionClaim] at decoded
  | occurrenceStep =>
      simp [FormulaWitness.formula] at decoded
  | guard =>
      rcases payload with ⟨premise, _meaning⟩
      simp [FormulaWitness.formula,
        SelectedNativeTypeBoundRelationClaim.View.encode] at decoded

/-- Any evidence whose wire decodes as a bound-relation claim supplies that
claim's independent relation meaning.  Other witness families are rejected
by namespace-disjoint decoding, not by dependent reduction of labels. -/
def FormulaEvidence.guardMeaning {model : CarrierModel}
    {world : ActivationWorld} {formula : Pattern}
    (evidence : FormulaEvidence model world formula)
    {view : SelectedNativeTypeBoundRelationClaim.View guardProfile}
    (decoded : SelectedNativeTypeBoundRelationClaim.decode?
      guardProfile formula = some view) : view.Meaning relationEnv := by
  rcases evidence with ⟨witness, formulaExact⟩
  rw [← formulaExact] at decoded
  rcases witness with ⟨kind, payload⟩
  cases kind with
  | variableClaim =>
      rcases payload with ⟨binding, _typed⟩
      change SelectedNativeTypeBoundRelationClaim.decode? guardProfile
          (SelectedNativeTypeAuthoredVariableClaim.groundedView
            demand world.slot binding world.environment.bindings).encode =
        some view at decoded
      simp [SelectedNativeTypeAuthoredVariableClaim.groundedView,
        SelectedNativeTypeAuthoredVariableClaim.View.encode,
        SelectedNativeTypeAuthoredVariableClaim.claim,
        SelectedNativeTypeBoundRelationClaim.decode?,
        SelectedNativeTypeBoundRelationClaim.Naming.coordinate?,
        SelectedNativeTypeAuthoredVariableClaim.Naming.label,
        String.toList_append] at decoded
  | directTyping =>
      simp [FormulaWitness.formula,
        ContextualCarrierClaims.typingClaim] at decoded
  | resultFamilySorted =>
      simp [FormulaWitness.formula,
        ContextualCarrierClaims.typingClaim] at decoded
  | bodyTyped =>
      simp [FormulaWitness.formula,
        ContextualCarrierClaims.typingClaim] at decoded
  | modalWellFormed =>
      simp [FormulaWitness.formula,
        ContextualCarrierClaims.typingClaim] at decoded
  | modalMember =>
      simp [FormulaWitness.formula,
        ContextualCarrierClaims.typingClaim] at decoded
  | reduction =>
      simp [FormulaWitness.formula,
        ContextualCarrierClaims.reductionClaim] at decoded
  | occurrenceStep =>
      simp [FormulaWitness.formula] at decoded
  | guard =>
      rcases payload with ⟨premise, meaning⟩
      change
        SelectedNativeTypeBoundRelationClaim.decode? guardProfile
            (groundedView guardProfile world.slot premise
              world.environment.bindings).encode = some view at decoded
      have canonical :=
        SelectedNativeTypeBoundRelationClaim.decode?_encode
          (groundedView guardProfile world.slot premise
            world.environment.bindings)
      rw [canonical] at decoded
      have viewExact :
          view = groundedView guardProfile world.slot premise
            world.environment.bindings :=
        (Option.some.inj decoded).symm
      simpa only [viewExact] using meaning

/-- Detailed inversion of the occurrence-indexed result-family sorting
claim.  The private family-application head recovers both the exact authored
occurrence and its family argument; all other semantic witness families are
rejected by the public syntax decoders. -/
def FormulaEvidence.resultFamilySortedMeaningDetailed {model : CarrierModel}
    {world : ActivationWorld} {slot : Occurrence} {family : Pattern}
    (evidence : FormulaEvidence model world
      (ContextualCarrierClaims.typingClaim
        (sourceCarrierAt demand (typingAt demand slot).rewriteType)
        (authoredFamilyApplication demand slot family)
        (sortCode
          (sourceCarrierAt demand (typingAt demand slot).rewriteType)
          (ContextualModalProfile.resultCode
            (occurrenceAt demand slot).profile)))) :
    world.slot = slot ∧
      model.Typed (typingAt demand slot).rewriteType family
        (model.universeObject (typingAt demand slot).rewriteType
          (ContextualModalProfile.resultCode
            (occurrenceAt demand slot).profile)) := by
  rcases evidence with ⟨witness, formulaExact⟩
  rcases witness with ⟨kind, payload⟩
  cases kind with
  | variableClaim =>
      rcases payload with ⟨binding, _typed⟩
      change groundedVariableClaim world binding =
        ContextualCarrierClaims.typingClaim
          (sourceCarrierAt demand (typingAt demand slot).rewriteType)
          (authoredFamilyApplication demand slot family)
          (sortCode
            (sourceCarrierAt demand (typingAt demand slot).rewriteType)
            (ContextualModalProfile.resultCode
              (occurrenceAt demand slot).profile)) at formulaExact
      have decodedExact := congrArg
        (SelectedNativeTypeAuthoredVariableClaim.decode? demand) formulaExact
      have leftDecode :
          SelectedNativeTypeAuthoredVariableClaim.decode? demand
              (groundedVariableClaim world binding) =
            some (SelectedNativeTypeAuthoredVariableClaim.groundedView
              demand world.slot binding world.environment.bindings) :=
        SelectedNativeTypeAuthoredVariableClaim.decode?_encode _
      have rightDecode :
          SelectedNativeTypeAuthoredVariableClaim.decode? demand
              (ContextualCarrierClaims.typingClaim
                (sourceCarrierAt demand (typingAt demand slot).rewriteType)
                (authoredFamilyApplication demand slot family)
                (sortCode
                  (sourceCarrierAt demand
                    (typingAt demand slot).rewriteType)
                  (ContextualModalProfile.resultCode
                    (occurrenceAt demand slot).profile))) = none :=
        SelectedNativeTypeAuthoredVariableClaim.decode?_contextualCarrierClaim
          ContextualCarrierClaims.ClaimKind.typing
          (sourceCarrierAt demand (typingAt demand slot).rewriteType)
          [authoredFamilyApplication demand slot family,
            sortCode
              (sourceCarrierAt demand (typingAt demand slot).rewriteType)
              (ContextualModalProfile.resultCode
                (occurrenceAt demand slot).profile)]
      rw [leftDecode, rightDecode] at decodedExact
      cases decodedExact
  | directTyping =>
      rcases payload with
        ⟨view, termOrdinary, _typeOrdinary, _meaning⟩
      change ContextualCarrierClaims.typingClaim
          (carrierName view.carrier) view.term view.type =
        ContextualCarrierClaims.typingClaim
          (sourceCarrierAt demand (typingAt demand slot).rewriteType)
          (authoredFamilyApplication demand slot family)
          (sortCode
            (sourceCarrierAt demand (typingAt demand slot).rewriteType)
            (ContextualModalProfile.resultCode
              (occurrenceAt demand slot).profile)) at formulaExact
      have termExact := (typingClaim_components formulaExact).1
      rw [termExact] at termOrdinary
      simp at termOrdinary
  | resultFamilySorted =>
      rcases payload with ⟨otherFamily, sorted⟩
      change ContextualCarrierClaims.typingClaim
          (sourceCarrierAt demand (typingAt demand world.slot).rewriteType)
          (authoredFamilyApplication demand world.slot otherFamily)
          (sortCode
            (sourceCarrierAt demand (typingAt demand world.slot).rewriteType)
            (ContextualModalProfile.resultCode
              (occurrenceAt demand world.slot).profile)) =
        ContextualCarrierClaims.typingClaim
          (sourceCarrierAt demand (typingAt demand slot).rewriteType)
          (authoredFamilyApplication demand slot family)
          (sortCode
            (sourceCarrierAt demand (typingAt demand slot).rewriteType)
            (ContextualModalProfile.resultCode
              (occurrenceAt demand slot).profile)) at formulaExact
      have termExact := (typingClaim_components formulaExact).1
      have decodedExact := congrArg (decodeApplication? demand) termExact
      simp only [decodeApplication_authoredFamilyApplication] at decodedExact
      have viewsExact := Option.some.inj decodedExact
      have headsExact := congrArg ApplicationView.head viewsExact
      have slotsExact : world.slot = slot := by
        injection headsExact
      have argumentsExact := congrArg ApplicationView.arguments viewsExact
      have familiesExact : otherFamily = family := by
        simpa using argumentsExact
      rw [slotsExact, familiesExact] at sorted
      exact ⟨slotsExact, sorted⟩
  | bodyTyped =>
      rcases payload with ⟨otherFamily, _typed⟩
      change ContextualCarrierClaims.typingClaim
          (sourceCarrierAt demand (typingAt demand world.slot).rewriteType)
          (applyBindingsForRule language
            (typingAt demand world.slot).site.rewrite
            world.environment.bindings)
          (authoredFamilyApplication demand world.slot otherFamily) =
        ContextualCarrierClaims.typingClaim
          (sourceCarrierAt demand (typingAt demand slot).rewriteType)
          (authoredFamilyApplication demand slot family)
          (sortCode
            (sourceCarrierAt demand (typingAt demand slot).rewriteType)
            (ContextualModalProfile.resultCode
              (occurrenceAt demand slot).profile)) at formulaExact
      have typeExact := (typingClaim_components formulaExact).2
      have ordinaryExact := congrArg ordinaryTypingTerm typeExact
      rw [ordinaryTypingTerm_authoredFamilyApplication,
        ordinaryTypingTerm_rewriteSort] at ordinaryExact
      cases ordinaryExact
  | modalWellFormed =>
      rcases payload with ⟨otherFamily, _wellFormed⟩
      change ContextualCarrierClaims.typingClaim
          (sourceCarrierAt demand (typingAt demand world.slot).focusType)
          (modalType demand world.slot otherFamily)
          (sortCode
            (sourceCarrierAt demand (typingAt demand world.slot).focusType)
            (ContextualModalProfile.resultCode
              (occurrenceAt demand world.slot).profile)) =
        ContextualCarrierClaims.typingClaim
          (sourceCarrierAt demand (typingAt demand slot).rewriteType)
          (authoredFamilyApplication demand slot family)
          (sortCode
            (sourceCarrierAt demand (typingAt demand slot).rewriteType)
            (ContextualModalProfile.resultCode
              (occurrenceAt demand slot).profile)) at formulaExact
      have termExact := (typingClaim_components formulaExact).1
      have decodedExact := congrArg (decodeApplication? demand) termExact
      simp at decodedExact
  | modalMember =>
      rcases payload with ⟨otherFamily, _member⟩
      change ContextualCarrierClaims.typingClaim
          (sourceCarrierAt demand (typingAt demand world.slot).focusType)
          world.before (modalType demand world.slot otherFamily) =
        ContextualCarrierClaims.typingClaim
          (sourceCarrierAt demand (typingAt demand slot).rewriteType)
          (authoredFamilyApplication demand slot family)
          (sortCode
            (sourceCarrierAt demand (typingAt demand slot).rewriteType)
            (ContextualModalProfile.resultCode
              (occurrenceAt demand slot).profile)) at formulaExact
      have typeExact := (typingClaim_components formulaExact).2
      have ordinaryExact := congrArg ordinaryTypingTerm typeExact
      rw [ordinaryTypingTerm_modalType,
        ordinaryTypingTerm_rewriteSort] at ordinaryExact
      cases ordinaryExact
  | reduction =>
      rcases payload with ⟨carrier, source, target, _reduces⟩
      change ContextualCarrierClaims.reductionClaim
          (carrierName carrier) source target =
        ContextualCarrierClaims.typingClaim
          (sourceCarrierAt demand (typingAt demand slot).rewriteType)
          (authoredFamilyApplication demand slot family)
          (sortCode
            (sourceCarrierAt demand (typingAt demand slot).rewriteType)
            (ContextualModalProfile.resultCode
              (occurrenceAt demand slot).profile)) at formulaExact
      have heads := (Pattern.apply.inj formulaExact).1
      exact False.elim
        (ContextualCarrierClaims.claimLabel_ne_of_kind_ne
          (by decide) _ _ heads)
  | occurrenceStep =>
      rcases payload with ⟨after, _occurs⟩
      change SelectedNativeTypeOccurrenceStepClaim.claim
          world.slot world.before after =
        ContextualCarrierClaims.typingClaim
          (sourceCarrierAt demand (typingAt demand slot).rewriteType)
          (authoredFamilyApplication demand slot family)
          (sortCode
            (sourceCarrierAt demand (typingAt demand slot).rewriteType)
            (ContextualModalProfile.resultCode
              (occurrenceAt demand slot).profile)) at formulaExact
      have decodedExact := congrArg
        (decodeGeneratedFormula? demand) formulaExact
      have leftDecode :
          decodeGeneratedFormula? demand
              (SelectedNativeTypeOccurrenceStepClaim.claim
                world.slot world.before after) =
            some (.occurrenceStep world.slot world.before after) := by
        simpa [encodeGeneratedFormula] using
          (decodeGeneratedFormula?_encodeGeneratedFormula
            (.occurrenceStep world.slot world.before after))
      have rightDecode :
          decodeGeneratedFormula? demand
              (ContextualCarrierClaims.typingClaim
                (sourceCarrierAt demand (typingAt demand slot).rewriteType)
                (authoredFamilyApplication demand slot family)
                (sortCode
                  (sourceCarrierAt demand
                    (typingAt demand slot).rewriteType)
                  (ContextualModalProfile.resultCode
                    (occurrenceAt demand slot).profile))) =
            some (.typingClaim (rewriteCarrier slot)
              (authoredFamilyApplication demand slot family)
              (sortCode
                (sourceCarrierAt demand (typingAt demand slot).rewriteType)
                (ContextualModalProfile.resultCode
                  (occurrenceAt demand slot).profile))) := by
        simpa [encodeGeneratedFormula] using
          (decodeGeneratedFormula?_encodeGeneratedFormula
            (.typingClaim (rewriteCarrier slot)
              (authoredFamilyApplication demand slot family)
              (sortCode
                (sourceCarrierAt demand (typingAt demand slot).rewriteType)
                (ContextualModalProfile.resultCode
                  (occurrenceAt demand slot).profile))))
      rw [leftDecode, rightDecode] at decodedExact
      cases decodedExact
  | guard =>
      rcases payload with ⟨premise, _meaning⟩
      change
        (groundedView guardProfile world.slot premise
          world.environment.bindings).encode =
        ContextualCarrierClaims.typingClaim
          (sourceCarrierAt demand (typingAt demand slot).rewriteType)
          (authoredFamilyApplication demand slot family)
          (sortCode
            (sourceCarrierAt demand (typingAt demand slot).rewriteType)
            (ContextualModalProfile.resultCode
              (occurrenceAt demand slot).profile)) at formulaExact
      have decodedExact := congrArg
        (SelectedNativeTypeBoundRelationClaim.decode? guardProfile)
        formulaExact
      have leftDecode :
          SelectedNativeTypeBoundRelationClaim.decode? guardProfile
              (groundedView guardProfile world.slot premise
                world.environment.bindings).encode =
            some (groundedView guardProfile world.slot premise
              world.environment.bindings) :=
        SelectedNativeTypeBoundRelationClaim.decode?_encode _
      have rightDecode :
          SelectedNativeTypeBoundRelationClaim.decode? guardProfile
              (ContextualCarrierClaims.typingClaim
                (sourceCarrierAt demand (typingAt demand slot).rewriteType)
                (authoredFamilyApplication demand slot family)
                (sortCode
                  (sourceCarrierAt demand
                    (typingAt demand slot).rewriteType)
                  (ContextualModalProfile.resultCode
                    (occurrenceAt demand slot).profile))) = none :=
        SelectedNativeTypeBoundRelationClaim.decode?_contextualCarrierClaim
          guardProfile ContextualCarrierClaims.ClaimKind.typing
          (sourceCarrierAt demand (typingAt demand slot).rewriteType)
          [authoredFamilyApplication demand slot family,
            sortCode
              (sourceCarrierAt demand (typingAt demand slot).rewriteType)
              (ContextualModalProfile.resultCode
                (occurrenceAt demand slot).profile)]
      rw [leftDecode, rightDecode] at decodedExact
      cases decodedExact

/-- Detailed inversion of an exact generated body-typing claim.  Besides the
independent typing fact, the occurrence-specific family constructor recovers
the exact selected source occurrence.  The proof rejects every other witness
family by its public syntax decoder; in particular, a direct typing witness
cannot classify a private family application as an ordinary term. -/
def FormulaEvidence.bodyTypedMeaningDetailed {model : CarrierModel}
    {world : ActivationWorld} {slot : Occurrence}
    {target family : Pattern}
    (evidence : FormulaEvidence model world
      (ContextualCarrierClaims.typingClaim
        (sourceCarrierAt demand (typingAt demand slot).rewriteType)
        target (authoredFamilyApplication demand slot family))) :
    world.slot = slot ∧
      model.Typed (typingAt demand slot).rewriteType target family := by
  rcases evidence with ⟨witness, formulaExact⟩
  rcases witness with ⟨kind, payload⟩
  cases kind with
  | variableClaim =>
      rcases payload with ⟨binding, _typed⟩
      change groundedVariableClaim world binding =
        ContextualCarrierClaims.typingClaim
          (sourceCarrierAt demand (typingAt demand slot).rewriteType)
          target (authoredFamilyApplication demand slot family)
        at formulaExact
      have decodedExact := congrArg
        (SelectedNativeTypeAuthoredVariableClaim.decode? demand) formulaExact
      have leftDecode :
          SelectedNativeTypeAuthoredVariableClaim.decode? demand
              (groundedVariableClaim world binding) =
            some (SelectedNativeTypeAuthoredVariableClaim.groundedView
              demand world.slot binding world.environment.bindings) := by
        exact SelectedNativeTypeAuthoredVariableClaim.decode?_encode _
      have rightDecode :
          SelectedNativeTypeAuthoredVariableClaim.decode? demand
              (ContextualCarrierClaims.typingClaim
                (sourceCarrierAt demand (typingAt demand slot).rewriteType)
                target (authoredFamilyApplication demand slot family)) =
            none := by
        exact
          SelectedNativeTypeAuthoredVariableClaim.decode?_contextualCarrierClaim
            ContextualCarrierClaims.ClaimKind.typing
            (sourceCarrierAt demand (typingAt demand slot).rewriteType)
            [target, authoredFamilyApplication demand slot family]
      rw [leftDecode, rightDecode] at decodedExact
      cases decodedExact
  | directTyping =>
      rcases payload with
        ⟨view, _termOrdinary, typeOrdinary, _meaning⟩
      change ContextualCarrierClaims.typingClaim
          (carrierName view.carrier) view.term view.type =
        ContextualCarrierClaims.typingClaim
          (sourceCarrierAt demand (typingAt demand slot).rewriteType)
          target (authoredFamilyApplication demand slot family)
        at formulaExact
      have components := typingClaim_components formulaExact
      rw [components.2] at typeOrdinary
      simp at typeOrdinary
  | resultFamilySorted =>
      rcases payload with ⟨otherFamily, _sorted⟩
      change ContextualCarrierClaims.typingClaim
          (sourceCarrierAt demand (typingAt demand world.slot).rewriteType)
          (authoredFamilyApplication demand world.slot otherFamily)
          (sortCode
            (sourceCarrierAt demand (typingAt demand world.slot).rewriteType)
            (ContextualModalProfile.resultCode
              (occurrenceAt demand world.slot).profile)) =
        ContextualCarrierClaims.typingClaim
          (sourceCarrierAt demand (typingAt demand slot).rewriteType)
          target (authoredFamilyApplication demand slot family)
        at formulaExact
      have typeExact := (typingClaim_components formulaExact).2
      have ordinaryExact := congrArg ordinaryTypingTerm typeExact
      rw [ordinaryTypingTerm_rewriteSort,
        ordinaryTypingTerm_authoredFamilyApplication] at ordinaryExact
      cases ordinaryExact
  | bodyTyped =>
      rcases payload with ⟨otherFamily, typed⟩
      change ContextualCarrierClaims.typingClaim
          (sourceCarrierAt demand (typingAt demand world.slot).rewriteType)
          (applyBindingsForRule language
            (typingAt demand world.slot).site.rewrite
            world.environment.bindings)
          (authoredFamilyApplication demand world.slot otherFamily) =
        ContextualCarrierClaims.typingClaim
          (sourceCarrierAt demand (typingAt demand slot).rewriteType)
          target (authoredFamilyApplication demand slot family)
        at formulaExact
      have components := typingClaim_components formulaExact
      have decodedExact := congrArg (decodeApplication? demand) components.2
      simp only [decodeApplication_authoredFamilyApplication] at decodedExact
      have viewsExact := Option.some.inj decodedExact
      have headsExact := congrArg ApplicationView.head viewsExact
      have slotsExact : world.slot = slot := by
        injection headsExact
      have argumentsExact := congrArg ApplicationView.arguments viewsExact
      have familiesExact : otherFamily = family := by
        simpa using argumentsExact
      have rewriteTypeExact :
          (typingAt demand world.slot).rewriteType =
            (typingAt demand slot).rewriteType :=
        congrArg (fun occurrence => (typingAt demand occurrence).rewriteType)
          slotsExact
      rw [rewriteTypeExact, components.1, familiesExact] at typed
      exact ⟨slotsExact, typed⟩
  | modalWellFormed =>
      rcases payload with ⟨otherFamily, _wellFormed⟩
      change ContextualCarrierClaims.typingClaim
          (sourceCarrierAt demand (typingAt demand world.slot).focusType)
          (modalType demand world.slot otherFamily)
          (sortCode
            (sourceCarrierAt demand (typingAt demand world.slot).focusType)
            (ContextualModalProfile.resultCode
              (occurrenceAt demand world.slot).profile)) =
        ContextualCarrierClaims.typingClaim
          (sourceCarrierAt demand (typingAt demand slot).rewriteType)
          target (authoredFamilyApplication demand slot family)
        at formulaExact
      have typeExact := (typingClaim_components formulaExact).2
      have ordinaryExact := congrArg ordinaryTypingTerm typeExact
      rw [ordinaryTypingTerm_focusSort,
        ordinaryTypingTerm_authoredFamilyApplication] at ordinaryExact
      cases ordinaryExact
  | modalMember =>
      rcases payload with ⟨otherFamily, _member⟩
      change ContextualCarrierClaims.typingClaim
          (sourceCarrierAt demand (typingAt demand world.slot).focusType)
          world.before (modalType demand world.slot otherFamily) =
        ContextualCarrierClaims.typingClaim
          (sourceCarrierAt demand (typingAt demand slot).rewriteType)
          target (authoredFamilyApplication demand slot family)
        at formulaExact
      have typeExact := (typingClaim_components formulaExact).2
      have decodedExact := congrArg (decodeApplication? demand) typeExact
      simp at decodedExact
  | reduction =>
      rcases payload with ⟨carrier, source, reductionTarget, _reduces⟩
      change ContextualCarrierClaims.reductionClaim
          (carrierName carrier) source reductionTarget =
        ContextualCarrierClaims.typingClaim
          (sourceCarrierAt demand (typingAt demand slot).rewriteType)
          target (authoredFamilyApplication demand slot family)
        at formulaExact
      have heads := (Pattern.apply.inj formulaExact).1
      exact False.elim
        (ContextualCarrierClaims.claimLabel_ne_of_kind_ne
          (by decide) _ _ heads)
  | occurrenceStep =>
      rcases payload with ⟨after, _occurs⟩
      change SelectedNativeTypeOccurrenceStepClaim.claim
          world.slot world.before after =
        ContextualCarrierClaims.typingClaim
          (sourceCarrierAt demand (typingAt demand slot).rewriteType)
          target (authoredFamilyApplication demand slot family)
        at formulaExact
      have decodedExact :=
        congrArg (decodeGeneratedFormula? demand) formulaExact
      have leftDecode :
          decodeGeneratedFormula? demand
              (SelectedNativeTypeOccurrenceStepClaim.claim
                world.slot world.before after) =
            some (.occurrenceStep world.slot world.before after) := by
        simpa [encodeGeneratedFormula] using
          (decodeGeneratedFormula?_encodeGeneratedFormula
            (.occurrenceStep world.slot world.before after))
      rw [leftDecode, decodeGeneratedFormula_bodyClaim] at decodedExact
      cases decodedExact
  | guard =>
      rcases payload with ⟨premise, _meaning⟩
      change
        (groundedView guardProfile world.slot premise
          world.environment.bindings).encode =
        ContextualCarrierClaims.typingClaim
          (sourceCarrierAt demand (typingAt demand slot).rewriteType)
          target (authoredFamilyApplication demand slot family)
        at formulaExact
      have decodedExact :=
        congrArg
          (SelectedNativeTypeBoundRelationClaim.decode? guardProfile)
          formulaExact
      have leftDecode :
          SelectedNativeTypeBoundRelationClaim.decode? guardProfile
              (groundedView guardProfile world.slot premise
                world.environment.bindings).encode =
            some (groundedView guardProfile world.slot premise
              world.environment.bindings) :=
        SelectedNativeTypeBoundRelationClaim.decode?_encode _
      have rightDecode :
          SelectedNativeTypeBoundRelationClaim.decode? guardProfile
              (ContextualCarrierClaims.typingClaim
                (sourceCarrierAt demand (typingAt demand slot).rewriteType)
                target (authoredFamilyApplication demand slot family)) =
            none := by
        exact
          SelectedNativeTypeBoundRelationClaim.decode?_contextualCarrierClaim
            guardProfile ContextualCarrierClaims.ClaimKind.typing
            (sourceCarrierAt demand (typingAt demand slot).rewriteType)
            [target, authoredFamilyApplication demand slot family]
      rw [leftDecode, rightDecode] at decodedExact
      cases decodedExact

/-- The typing projection of detailed body-claim inversion. -/
def FormulaEvidence.bodyTypedMeaning {model : CarrierModel}
    {world : ActivationWorld} {slot : Occurrence}
    {target family : Pattern}
    (evidence : FormulaEvidence model world
      (ContextualCarrierClaims.typingClaim
        (sourceCarrierAt demand (typingAt demand slot).rewriteType)
        target (authoredFamilyApplication demand slot family))) :
    model.Typed (typingAt demand slot).rewriteType target family :=
  evidence.bodyTypedMeaningDetailed.2

/-- Ambient context holes are parameters of an open contextual judgment.
They carry no guard or modal authority; all such authority occurs in explicit
formula evidence above. -/
def displayedModel (model : CarrierModel) :
    ContextualInferenceSemantics.Model where
  World := ActivationWorld
  FormulaEvidence := FormulaEvidence model
  HoleEvidence := fun _world _name => Unit

/-! ## One fail-closed judgment interpretation -/

/-- Independent meaning for the complete binder-free generated judgment
image.  Direct carrier typings, canonical-context certificates, and ordinary
contextual sequents are distinct decoding branches.  The first successful
decoder owns the meaning; generated derivability is never consulted. -/
def JudgmentMeaning (model : CarrierModel) (wire : Pattern) : Prop :=
  match decodeCarrierTyping? demand wire with
  | some view =>
      model.Typed view.carrier.expression
        (interpretUniverseTerm model demand view.term)
        (interpretUniverseTerm model demand view.type)
  | none =>
      match ContextualInference.decodeSequent? wire with
      | none => False
      | some sequent =>
          match ContextualInferenceCanonicalContext.decodeClaim?
              sequent.conclusion with
          | some contextWire =>
              ContextualInferenceCanonicalContext.Canonical contextWire
          | none => SequentValid (displayedModel model) sequent

@[simp] theorem judgmentMeaning_carrierTyping (model : CarrierModel)
    (view : CarrierTypingView demand) :
    JudgmentMeaning model view.encode ↔
      model.Typed view.carrier.expression
        (interpretUniverseTerm model demand view.term)
        (interpretUniverseTerm model demand view.type) := by
  simp [JudgmentMeaning]

@[simp] theorem judgmentMeaning_canonicalContext (model : CarrierModel)
    (wire : Pattern) :
    JudgmentMeaning model
        (ContextualInference.lowerSequent
          (ContextualInferenceCanonicalContext.sequent wire)) ↔
      ContextualInferenceCanonicalContext.Canonical wire := by
  unfold JudgmentMeaning
  have carrierNone :
      decodeCarrierTyping? demand
          (ContextualInference.lowerSequent
            (ContextualInferenceCanonicalContext.sequent wire)) = none := by
    simp [decodeCarrierTyping?, ContextualInference.lowerSequent]
  rw [carrierNone,
    ContextualInference.decodeSequent?_lowerSequent]
  simp [ContextualInferenceCanonicalContext.sequent]

/-- A contextual sequent whose conclusion is not a canonical-context claim
has exactly the shared-world displayed meaning. -/
theorem judgmentMeaning_contextual (model : CarrierModel)
    (sequent : ContextualInference.Sequent)
    (notCanonical :
      ContextualInferenceCanonicalContext.decodeClaim? sequent.conclusion =
        none) :
    JudgmentMeaning model (ContextualInference.lowerSequent sequent) ↔
      SequentValid (displayedModel model) sequent := by
  unfold JudgmentMeaning
  have carrierNone :
      decodeCarrierTyping? demand
          (ContextualInference.lowerSequent sequent) = none := by
    simp [decodeCarrierTyping?, ContextualInference.lowerSequent]
  simp only [carrierNone,
    ContextualInference.decodeSequent?_lowerSequent, notCanonical]

/-! ## Exact retained-context meaning -/

/-- Independent carrier meaning for every exact authored variable position in
one activation world.  The quantifier ranges over positions, not merely over
ground values or carrier names. -/
def VariableMeanings (model : CarrierModel) (world : ActivationWorld) : Prop :=
  ∀ binding : AuthoredBindingIndex world,
    let authored := authoredBindingAt world binding
    model.Typed authored.2
      (applyBindings world.environment.bindings (.fvar authored.1))
      (model.universeObject authored.2 .star)

/-- Complete grounded authored-variable row at one semantic world. -/
def groundedVariableClaims (world : ActivationWorld) : List Pattern :=
  SelectedNativeTypeAuthoredVariableClaim.groundedClaims
    demand world.slot world.environment.bindings

@[simp] theorem length_groundedVariableClaims (world : ActivationWorld) :
    (groundedVariableClaims world).length =
      (authoredBindings demand world.slot).length := by
  simp [groundedVariableClaims]

@[simp] theorem groundedVariableClaims_get (world : ActivationWorld)
    (binding : AuthoredBindingIndex world) :
    (groundedVariableClaims world).get
        ⟨binding.val, by
          rw [length_groundedVariableClaims]
          exact binding.isLt⟩ =
      groundedVariableClaim world binding := by
  simpa only [groundedVariableClaims, groundedVariableClaim] using
    (SelectedNativeTypeAuthoredVariableClaim.groundedClaims_get
      demand world.slot world.environment.bindings binding)

/-- Evidence for a row grounded at an arbitrary reference endpoint recovers
the exact decoded variable meaning at each reference position.  The semantic
world need not yet be identified with that endpoint; the reconstruction
equation records precisely the evidence needed to prove such agreement. -/
def variableMeaningOfGroundedRowEvidence (model : CarrierModel)
    (world : ActivationWorld) (slot : Occurrence) (bindings : Bindings)
    (evidence : FormulaRowEvidence (displayedModel model) world
      (SelectedNativeTypeAuthoredVariableClaim.groundedClaims
        demand slot bindings))
    (binding : SelectedNativeTypeAuthoredVariableClaim.Binding demand slot) :
    VariableMeaning model world
      (SelectedNativeTypeAuthoredVariableClaim.groundedView
        demand slot binding bindings) := by
  let rowIndex : Fin
      (SelectedNativeTypeAuthoredVariableClaim.groundedClaims
        demand slot bindings).length :=
    ⟨binding.val, by simp⟩
  have evidenceAt := evidence.get rowIndex
  have formulaExact :
      (SelectedNativeTypeAuthoredVariableClaim.groundedClaims
        demand slot bindings).get rowIndex =
      (SelectedNativeTypeAuthoredVariableClaim.groundedView
        demand slot binding bindings).encode := by
    simpa only [rowIndex] using
      (SelectedNativeTypeAuthoredVariableClaim.groundedClaims_get
        demand slot bindings binding)
  rw [formulaExact] at evidenceAt
  exact evidenceAt.variableMeaning
    (SelectedNativeTypeAuthoredVariableClaim.decode?_encode _)

/-- Exact authored-variable meaning constructs evidence at every retained
context position in the same activation world. -/
def variableRowEvidenceOfMeanings (model : CarrierModel)
    (world : ActivationWorld)
    (meanings : VariableMeanings model world) :
    FormulaRowEvidence (displayedModel model) world
      (groundedVariableClaims world) := by
  apply FormulaRowEvidence.ofIndexed
  intro rowIndex
  let binding : AuthoredBindingIndex world :=
    ⟨rowIndex.val, by simpa using rowIndex.isLt⟩
  have formulaExact :
      (groundedVariableClaims world).get rowIndex =
        groundedVariableClaim world binding := by
    simpa only [binding] using
      (groundedVariableClaims_get world binding)
  rw [formulaExact]
  exact FormulaEvidence.variable model world binding (meanings binding)

/-- Evidence for the exact authored-variable row reconstructs the independent
typing fact at every exact binding coordinate. -/
def meaningsOfVariableRowEvidence (model : CarrierModel)
    (world : ActivationWorld)
    (evidence : FormulaRowEvidence (displayedModel model) world
      (groundedVariableClaims world)) :
    VariableMeanings model world := by
  intro binding
  let rowIndex : Fin (groundedVariableClaims world).length :=
    ⟨binding.val, by
      rw [length_groundedVariableClaims]
      exact binding.isLt⟩
  have evidenceAt := evidence.get rowIndex
  rw [groundedVariableClaims_get world binding] at evidenceAt
  have meaning := evidenceAt.variableMeaning
    (SelectedNativeTypeAuthoredVariableClaim.decode?_encode _)
  have bindingExact : binding = meaning.binding := by
    have viewExact := meaning.viewExact
    injection viewExact
  simpa only [bindingExact] using meaning.typed

/-- Shared-world satisfaction of the retained variable row is exactly the
position-indexed authored carrier meaning. -/
theorem variableRowSatisfies_iff_meanings (model : CarrierModel)
    (world : ActivationWorld) :
    FormulaRowSatisfies (displayedModel model) world
        (groundedVariableClaims world) ↔
      VariableMeanings model world := by
  constructor
  · rintro ⟨evidence⟩
    exact meaningsOfVariableRowEvidence model world evidence
  · intro meanings
    exact ⟨variableRowEvidenceOfMeanings model world meanings⟩

/-- Exact ordered guard formula row at one semantic world. -/
def groundedGuardClaims (world : ActivationWorld) : List Pattern :=
  SelectedNativeTypeBoundRelationClaim.groundedClaims
    guardProfile world.slot world.environment.bindings

@[simp] theorem length_groundedGuardClaims (world : ActivationWorld) :
    (groundedGuardClaims world).length =
      (viewsAt guardProfile world.slot).length := by
  simp [groundedGuardClaims]

@[simp] theorem groundedGuardClaims_get (world : ActivationWorld)
    (premise : Fin (viewsAt guardProfile world.slot).length) :
    (groundedGuardClaims world).get
        ⟨premise.val, by
          rw [length_groundedGuardClaims]
          exact premise.isLt⟩ =
      (groundedView guardProfile world.slot premise
        world.environment.bindings).encode := by
  simpa only [groundedGuardClaims] using
    (SelectedNativeTypeBoundRelationClaim.groundedClaims_get
      guardProfile world.slot world.environment.bindings premise)

/-- Evidence for an exact guard row grounded at an arbitrary reference
endpoint reconstructs the complete ordered source-relation meaning at that
endpoint.  Evidence remains indexed by one semantic world, so unrelated
formula witnesses cannot be spliced into the row. -/
def groundMeaningsOfGroundedGuardRowEvidence (model : CarrierModel)
    (world : ActivationWorld) (slot : Occurrence) (bindings : Bindings)
    (evidence : FormulaRowEvidence (displayedModel model) world
      (SelectedNativeTypeBoundRelationClaim.groundedClaims
        guardProfile slot bindings)) :
    GroundMeanings guardProfile relationEnv slot bindings := by
  intro premise
  let rowIndex : Fin
      (SelectedNativeTypeBoundRelationClaim.groundedClaims
        guardProfile slot bindings).length :=
    ⟨premise.val, by simp⟩
  have evidenceAt := evidence.get rowIndex
  have formulaExact :
      (SelectedNativeTypeBoundRelationClaim.groundedClaims
        guardProfile slot bindings).get rowIndex =
      (groundedView guardProfile slot premise bindings).encode := by
    simpa only [rowIndex] using
      (SelectedNativeTypeBoundRelationClaim.groundedClaims_get
        guardProfile slot bindings premise)
  rw [formulaExact] at evidenceAt
  exact evidenceAt.guardMeaning
    (SelectedNativeTypeBoundRelationClaim.decode?_encode _)

/-- Complete independent truth of the ordered source guard row constructs
formula evidence at every exact position in the same activation world. -/
def guardRowEvidenceOfMeanings (model : CarrierModel)
    (world : ActivationWorld)
    (meanings : GroundMeanings guardProfile relationEnv world.slot
      world.environment.bindings) :
    FormulaRowEvidence (displayedModel model) world
      (groundedGuardClaims world) := by
  apply FormulaRowEvidence.ofIndexed
  intro rowIndex
  let premise : Fin (viewsAt guardProfile world.slot).length :=
    ⟨rowIndex.val, by simpa using rowIndex.isLt⟩
  have formulaExact :
      (groundedGuardClaims world).get rowIndex =
        (groundedView guardProfile world.slot premise
          world.environment.bindings).encode := by
    simpa only [premise] using
      (groundedGuardClaims_get world premise)
  rw [formulaExact]
  exact FormulaEvidence.guard model world premise (meanings premise)

/-- Evidence for the exact grounded guard row reconstructs all ordered
relation meanings at that same activation world. -/
def meaningsOfGuardRowEvidence (model : CarrierModel)
    (world : ActivationWorld)
    (evidence : FormulaRowEvidence (displayedModel model) world
      (groundedGuardClaims world)) :
    GroundMeanings guardProfile relationEnv world.slot
      world.environment.bindings := by
  intro premise
  let rowIndex : Fin (groundedGuardClaims world).length :=
    ⟨premise.val, by
      rw [length_groundedGuardClaims]
      exact premise.isLt⟩
  have evidenceAt := evidence.get rowIndex
  rw [groundedGuardClaims_get world premise] at evidenceAt
  exact evidenceAt.guardMeaning
    (SelectedNativeTypeBoundRelationClaim.decode?_encode _)

/-- Shared-world contextual satisfaction is exactly truth of the complete
ordered guard row. -/
theorem guardRowSatisfies_iff_groundMeanings (model : CarrierModel)
    (world : ActivationWorld) :
    FormulaRowSatisfies (displayedModel model) world
        (groundedGuardClaims world) ↔
      GroundMeanings guardProfile relationEnv world.slot
        world.environment.bindings := by
  constructor
  · rintro ⟨evidence⟩
    exact meaningsOfGuardRowEvidence model world evidence
  · intro meanings
    exact ⟨guardRowEvidenceOfMeanings model world meanings⟩

/-! ## Discriminating controls -/

private abbrev skipHeadStar : Occurrence :=
  ⟨2, by
    change 2 < selectedOccurrences.length
    rw [selectedOccurrences_count]
    decide⟩

private theorem skipHeadStar_authoredBindings_exact :
    authoredBindings demand skipHeadStar =
      [ ("owner", .base "CGOwner")
      , ("revision", .base "CGNat")
      , ("head", .base "CGName")
      , ("arity", .base "CGNat")
      , ("occurrence", .base "CGNat")
      , ("declarationHead", .base "CGName")
      , ("inputs", .base "CGTerms")
      , ("output", .base "CGTerm")
      , ("remaining", .base "CGDeclarations")
      , ("accepted", .base "CGPlans") ] := by
  unfold authoredBindings endpointVariableNames
  rw [typingAt_eq_rootTyping]
  have rewriteExact :
      (rootTyping (rootIndexAt skipHeadStar)).site.rewrite =
        skipHeadTransition := by
    rfl
  unfold DisplayedRewriteVariableProfile.typedBindings
    DisplayedRewriteVariableProfile.variableType?
  simp only [rewriteExact]
  rw [skipHeadTransition_typeContext]
  simp [
    WellSorted.FreeTypeContext.ofList,
    skipHeadTransition,
    compileRunning, declarationsCons, declarationPattern, v,
    Pattern.freeFvarNames]
  decide

private abbrev skipHeadRequestedName :
    SelectedNativeTypeAuthoredVariableClaim.Binding demand skipHeadStar :=
  ⟨2, by
    rw [skipHeadStar_authoredBindings_exact]
    decide⟩

private abbrev skipHeadDeclarationName :
    SelectedNativeTypeAuthoredVariableClaim.Binding demand skipHeadStar :=
  ⟨5, by
    rw [skipHeadStar_authoredBindings_exact]
    decide⟩

/-- The real `skip-head` occurrence contains two distinct `CGName` binding
positions.  Even arbitrary values at those same-carrier positions cannot
exchange claims, because the generated head retains the authored coordinate. -/
theorem skipHead_sameCarrier_claims_not_exchangeable
    (requestedValue declarationValue : Pattern) :
    (SelectedNativeTypeAuthoredVariableClaim.sourceBinding demand skipHeadStar
        skipHeadRequestedName).2 =
      (SelectedNativeTypeAuthoredVariableClaim.sourceBinding demand skipHeadStar
        skipHeadDeclarationName).2 ∧
    SelectedNativeTypeAuthoredVariableClaim.claim skipHeadStar
        skipHeadRequestedName requestedValue ≠
      SelectedNativeTypeAuthoredVariableClaim.claim skipHeadStar
        skipHeadDeclarationName declarationValue := by
  constructor
  · simp [SelectedNativeTypeAuthoredVariableClaim.sourceBinding,
      skipHeadStar_authoredBindings_exact]
  · apply
      SelectedNativeTypeAuthoredVariableClaim.distinct_bindings_have_distinct_claims
    decide

/-- A missing exact premise meaning prevents satisfaction of the grounded
guard row even though ambient holes remain available. -/
theorem not_guardRowSatisfies_of_missing (model : CarrierModel)
    (world : ActivationWorld)
    (missing : ¬ GroundMeanings guardProfile relationEnv world.slot
      world.environment.bindings) :
    ¬ FormulaRowSatisfies (displayedModel model) world
      (groundedGuardClaims world) := by
  rw [guardRowSatisfies_iff_groundMeanings]
  exact missing

#print axioms rewriteCarrier_expression
#print axioms rewriteCarrier_name
#print axioms FormulaEvidence.variableMeaning
#print axioms FormulaEvidence.resultFamilySortedMeaningDetailed
#print axioms FormulaEvidence.bodyTypedMeaningDetailed
#print axioms FormulaEvidence.bodyTypedMeaning
#print axioms variableMeaningOfGroundedRowEvidence
#print axioms variableRowSatisfies_iff_meanings
#print axioms skipHead_sameCarrier_claims_not_exchangeable
#print axioms guardRowSatisfies_iff_groundMeanings
#print axioms groundMeaningsOfGroundedGuardRowEvidence
#print axioms not_guardRowSatisfies_of_missing

end Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileDisplayedModel
