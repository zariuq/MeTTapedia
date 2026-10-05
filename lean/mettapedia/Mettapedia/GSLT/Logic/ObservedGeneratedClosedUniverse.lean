import Mettapedia.GSLT.Logic.ObservedGeneratedFamilyDescent
import Mettapedia.GSLT.Logic.ObservedGeneratedModelControls
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualClosedUniverseCodes

/-!
# Constructor-closed codes of observed dependent material families

The actual observed family supplies the seed of the constructor-closed
code quotient. Arbitrary domain and dependent-body codes form full future
Pi, Sigma, discrete identity and hereditary-natural W families. Their
interpreted restrictions construct compatible material source transport.

Natural Pi and Sigma sections pass through the proved whole-family
decoder equations. Their beta, eta and material-value laws therefore
apply to quotient codes, including genuinely argument-dependent bodies.
The enclosure retains external family codes and dictionaries; its bare
present carrier is not a universe presheaf.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Mettapedia.GSLT.ObservedGeneratedClosedUniverse

open _root_.CategoryTheory
open Mettapedia.TypeTheory.MaterialSets
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open ContextualGeneratedUniverse
open ContextualObservedFamilyEnclosure
open PowerClassPresheafDescent


universe u
variable {C : Type u} [Category.{u} C]
variable (profile : ContextualSystem C) (worlds : ArgumentCoding Cᵒᵖ)
variable (arrows : (first second : Cᵒᵖ) → ArgumentCoding (first ⟶ second))
variable (graphs : profile.sourceFace.Elements → AccessiblePointedGraph.{u})
variable (transport : MaterialTransport profile.sourceFace profile.classFace profile.observation graphs)

abbrev Code (declared : LabelledContext C) :=
  ContextualClosedUniverseCodes.Code (ObservedGeneratedModel.Seeds profile worlds)
    (ObservedGeneratedModel.seedModel profile worlds graphs transport) arrows declared

def decode {declared : LabelledContext C} : Code profile worlds arrows graphs transport declared → MaterialFamily declared :=
  ContextualClosedUniverseCodes.decodeFamily _ _ _

def inputCode : Code profile worlds arrows graphs transport (ObservedGeneratedModel.context profile worlds) :=
  ContextualClosedUniverseCodes.seed _ _ _ (ObservedGeneratedModel.context profile worlds) (ULift.up (PLift.up rfl))

theorem decode_input : decode profile worlds arrows graphs transport
    (inputCode profile worlds arrows graphs transport) = ObservedGeneratedModel.input profile worlds graphs transport := rfl

def substitute {declared other : LabelledContext C} (change : NatTrans other.base declared.base) :
    Code profile worlds arrows graphs transport declared → Code profile worlds arrows graphs transport other :=
  ContextualClosedUniverseCodes.reindex _ _ _ change

theorem decode_substitute {declared other : LabelledContext C} (change : NatTrans other.base declared.base)
    (code : Code profile worlds arrows graphs transport declared) :
    decode profile worlds arrows graphs transport (substitute profile worlds arrows graphs transport change code) =
      (decode profile worlds arrows graphs transport code).reindex change :=
  ContextualClosedUniverseCodes.decode_reindex _ _ _ change code

variable {declared : LabelledContext C}
variable (domain : Code profile worlds arrows graphs transport declared)
variable (body : Code profile worlds arrows graphs transport (decode profile worlds arrows graphs transport domain).extension)

def piCode : Code profile worlds arrows graphs transport declared := ContextualClosedUniverseCodes.pi _ _ _ domain body
def sigmaCode : Code profile worlds arrows graphs transport declared := ContextualClosedUniverseCodes.sigma _ _ _ domain body
def wCode : Code profile worlds arrows graphs transport declared := ContextualClosedUniverseCodes.w _ _ _ domain body

theorem decode_pi :
    decode profile worlds arrows graphs transport (piCode profile worlds arrows graphs transport domain body) =
      (decode profile worlds arrows graphs transport domain).pi (decode profile worlds arrows graphs transport body) arrows :=
  ContextualClosedUniverseCodes.decode_binary _ _ _ .pi domain body

theorem decode_sigma :
    decode profile worlds arrows graphs transport (sigmaCode profile worlds arrows graphs transport domain body) =
      (decode profile worlds arrows graphs transport domain).sigma (decode profile worlds arrows graphs transport body) :=
  ContextualClosedUniverseCodes.decode_binary _ _ _ .sigma domain body

theorem decode_w :
    decode profile worlds arrows graphs transport (wCode profile worlds arrows graphs transport domain body) =
      (decode profile worlds arrows graphs transport domain).w (decode profile worlds arrows graphs transport body) arrows :=
  ContextualClosedUniverseCodes.decode_binary _ _ _ .w domain body

private def sectionEquality {first second : MaterialFamily declared} (same : first = second) :
    first.family.sections ≃ second.family.sections :=
  Mettapedia.TypeTheory.DependentFamilySectionDescent.equalityEquiv
    (congrArg (fun family : MaterialFamily declared => ↥family.family.sections) same)

private theorem sectionEquality_value {first second : MaterialFamily declared} (same : first = second)
    (term : first.family.sections) (point : declared.base.Elements) :
    (second.model point).value ((sectionEquality same term).val point) =
      (first.model point).value (term.val point) := by
  cases same
  rfl

private theorem sectionEquality_symm {first second : MaterialFamily declared} (same : first = second) :
    (sectionEquality same).symm = sectionEquality same.symm := by
  cases same
  rfl

private def objectEquality {first second : MaterialFamily declared} (same : first = second)
    (point : declared.base.Elements) : first.family.obj point ≃ second.family.obj point :=
  Mettapedia.TypeTheory.DependentFamilySectionDescent.equalityEquiv
    (congrArg (fun family : MaterialFamily declared => family.family.obj point) same)

private theorem objectEquality_value {first second : MaterialFamily declared} (same : first = second)
    (point : declared.base.Elements) (term : first.family.obj point) :
    (second.model point).value (objectEquality same point term) = (first.model point).value term := by
  cases same
  rfl

private theorem objectEquality_reverse {first second : MaterialFamily declared} (same : first = second)
    (point : declared.base.Elements) (term : second.family.obj point) :
    objectEquality same point (objectEquality same.symm point term) = term := by
  cases same
  rfl

private theorem objectEquality_natural {first second : MaterialFamily declared} (same : first = second)
    {point next : declared.base.Elements} (step : point ⟶ next) (term : first.family.obj point) :
    objectEquality same next (first.family.map step term) = second.family.map step (objectEquality same point term) := by
  cases same
  rfl

private theorem materialValue_heq (family : MaterialFamily declared) {first second : declared.base.Elements}
    (same : first = second) (left : family.family.obj first) (right : family.family.obj second)
    (members : HEq left right) : (family.model first).value left = (family.model second).value right := by
  cases same
  cases eq_of_heq members
  rfl

/-- Sections of the actual decoded Pi code are exactly natural sections
of its arbitrary dependent body. -/
def piSections : (decode profile worlds arrows graphs transport body).family.sections ≃
    (decode profile worlds arrows graphs transport (piCode profile worlds arrows graphs transport domain body)).family.sections :=
  (PowerClassPresheafProducts.piSectionEquiv (decode profile worlds arrows graphs transport domain).family
    (decode profile worlds arrows graphs transport body).family).trans
      (sectionEquality (decode_pi profile worlds arrows graphs transport domain body).symm)

def piLambda (term : (decode profile worlds arrows graphs transport body).family.sections) :
    (decode profile worlds arrows graphs transport (piCode profile worlds arrows graphs transport domain body)).family.sections :=
  piSections profile worlds arrows graphs transport domain body term

def piBody (function :
    (decode profile worlds arrows graphs transport (piCode profile worlds arrows graphs transport domain body)).family.sections) :
    (decode profile worlds arrows graphs transport body).family.sections :=
  (piSections profile worlds arrows graphs transport domain body).symm function

theorem pi_beta (term : (decode profile worlds arrows graphs transport body).family.sections) :
    piBody profile worlds arrows graphs transport domain body
      (piLambda profile worlds arrows graphs transport domain body term) = term :=
  (piSections profile worlds arrows graphs transport domain body).symm_apply_apply term

theorem pi_eta (function :
    (decode profile worlds arrows graphs transport (piCode profile worlds arrows graphs transport domain body)).family.sections) :
    piLambda profile worlds arrows graphs transport domain body
      (piBody profile worlds arrows graphs transport domain body function) = function :=
  (piSections profile worlds arrows graphs transport domain body).apply_symm_apply function

theorem piLambda_value (term : (decode profile worlds arrows graphs transport body).family.sections)
    (point : declared.base.Elements) :
    ((decode profile worlds arrows graphs transport (piCode profile worlds arrows graphs transport domain body)).model point).value
      ((piLambda profile worlds arrows graphs transport domain body term).val point) =
    (((decode profile worlds arrows graphs transport domain).pi
      (decode profile worlds arrows graphs transport body) arrows).model point).value
        ((PowerClassPresheafProducts.piLambda term).val point) :=
  sectionEquality_value (decode_pi profile worlds arrows graphs transport domain body).symm _ point

/-- Whole future graph evaluation retains the actual target context,
context arrow and dependent argument of the body code. -/
theorem piLambda_row (term : (decode profile worlds arrows graphs transport body).family.sections)
    (point : declared.base.Elements)
    (argument : PowerClassContextualMaterialization.FutureArguments
      (decode profile worlds arrows graphs transport domain).family point) :
    LabelledDependentProducts.evalValue
      ((decode profile worlds arrows graphs transport domain).futureCoding arrows point)
      ((decode profile worlds arrows graphs transport domain).futureOutputs
        (decode profile worlds arrows graphs transport body) point)
      (((decode profile worlds arrows graphs transport (piCode profile worlds arrows graphs transport domain body)).model point).value
        ((piLambda profile worlds arrows graphs transport domain body term).val point)) argument =
    ((decode profile worlds arrows graphs transport body).model
      ⟨argument.1.1.1, ⟨argument.1.1.2, argument.2⟩⟩).value
        (term.val ⟨argument.1.1.1, ⟨argument.1.1.2, argument.2⟩⟩) := by
  rw [piLambda_value]
  exact ((decode profile worlds arrows graphs transport domain).pi_evaluation
    (decode profile worlds arrows graphs transport body) arrows point _ argument).trans
      (congrArg ((decode profile worlds arrows graphs transport body).model
        ⟨argument.1.1.1, ⟨argument.1.1.2, argument.2⟩⟩).value
          (PowerClassPresheafProducts.piLambda_value term point argument.1.1 argument.1.2 argument.2))

def appliedBodyCode (argument : (decode profile worlds arrows graphs transport domain).family.sections) :
    Code profile worlds arrows graphs transport declared :=
  substitute profile worlds arrows graphs transport
    (PowerClassPresheafProducts.sectionMap (decode profile worlds arrows graphs transport domain).family argument) body

def piApply
    (function : (decode profile worlds arrows graphs transport (piCode profile worlds arrows graphs transport domain body)).family.sections)
    (argument : (decode profile worlds arrows graphs transport domain).family.sections) :
    (decode profile worlds arrows graphs transport (appliedBodyCode profile worlds arrows graphs transport domain body argument)).family.sections :=
  sectionEquality (decode_substitute profile worlds arrows graphs transport
    (PowerClassPresheafProducts.sectionMap (decode profile worlds arrows graphs transport domain).family argument) body).symm
      (PowerClassPresheafProducts.reindexSection
        (PowerClassPresheafProducts.sectionMap (decode profile worlds arrows graphs transport domain).family argument)
        (decode profile worlds arrows graphs transport body).family
        (piBody profile worlds arrows graphs transport domain body function))

/-- Application's result is a section of the actually substituted body
code, with the original dependent result value. -/
theorem piApply_beta_value
    (term : (decode profile worlds arrows graphs transport body).family.sections)
    (argument : (decode profile worlds arrows graphs transport domain).family.sections)
    (point : declared.base.Elements) :
    ((decode profile worlds arrows graphs transport (appliedBodyCode profile worlds arrows graphs transport domain body argument)).model point).value
      ((piApply profile worlds arrows graphs transport domain body
        (piLambda profile worlds arrows graphs transport domain body term) argument).val point) =
    ((decode profile worlds arrows graphs transport body).model ⟨point.1, ⟨point.2, argument.val point⟩⟩).value
      (term.val ⟨point.1, ⟨point.2, argument.val point⟩⟩) := by
  have preserved := sectionEquality_value
    (decode_substitute profile worlds arrows graphs transport
      (PowerClassPresheafProducts.sectionMap (decode profile worlds arrows graphs transport domain).family argument) body).symm
    (PowerClassPresheafProducts.reindexSection
      (PowerClassPresheafProducts.sectionMap (decode profile worlds arrows graphs transport domain).family argument)
      (decode profile worlds arrows graphs transport body).family
      (piBody profile worlds arrows graphs transport domain body
        (piLambda profile worlds arrows graphs transport domain body term))) point
  exact preserved.trans (congrArg (fun chosen : (decode profile worlds arrows graphs transport body).family.sections =>
    ((decode profile worlds arrows graphs transport body).model ⟨point.1, ⟨point.2, argument.val point⟩⟩).value
      (chosen.val ⟨point.1, ⟨point.2, argument.val point⟩⟩))
        (pi_beta profile worlds arrows graphs transport domain body term))

/-- The sum code retains both natural coordinates and their actual
dependent substitution. -/
def sigmaSections :
    (decode profile worlds arrows graphs transport (sigmaCode profile worlds arrows graphs transport domain body)).family.sections ≃
      (Σ first : (decode profile worlds arrows graphs transport domain).family.sections,
        (PowerClassPresheafProducts.reindex (PowerClassPresheafProducts.sectionMap (decode profile worlds arrows graphs transport domain).family first)
          (decode profile worlds arrows graphs transport body).family).sections) :=
  (sectionEquality (decode_sigma profile worlds arrows graphs transport domain body)).trans
    (PowerClassPresheafProducts.sigmaSectionEquiv (decode profile worlds arrows graphs transport domain).family
      (decode profile worlds arrows graphs transport body).family)

def sigmaPair (first : (decode profile worlds arrows graphs transport domain).family.sections)
    (second : (PowerClassPresheafProducts.reindex (PowerClassPresheafProducts.sectionMap (decode profile worlds arrows graphs transport domain).family first)
      (decode profile worlds arrows graphs transport body).family).sections) :
    (decode profile worlds arrows graphs transport (sigmaCode profile worlds arrows graphs transport domain body)).family.sections :=
  (sigmaSections profile worlds arrows graphs transport domain body).symm ⟨first, second⟩

theorem sigma_beta (first : (decode profile worlds arrows graphs transport domain).family.sections)
    (second : (PowerClassPresheafProducts.reindex (PowerClassPresheafProducts.sectionMap (decode profile worlds arrows graphs transport domain).family first)
      (decode profile worlds arrows graphs transport body).family).sections) :
    sigmaSections profile worlds arrows graphs transport domain body
      (sigmaPair profile worlds arrows graphs transport domain body first second) = ⟨first, second⟩ :=
  (sigmaSections profile worlds arrows graphs transport domain body).apply_symm_apply ⟨first, second⟩

theorem sigma_eta (term :
    (decode profile worlds arrows graphs transport (sigmaCode profile worlds arrows graphs transport domain body)).family.sections) :
    (sigmaSections profile worlds arrows graphs transport domain body).symm
      (sigmaSections profile worlds arrows graphs transport domain body term) = term :=
  (sigmaSections profile worlds arrows graphs transport domain body).symm_apply_apply term

theorem sigmaPair_value (first : (decode profile worlds arrows graphs transport domain).family.sections)
    (second : (PowerClassPresheafProducts.reindex (PowerClassPresheafProducts.sectionMap (decode profile worlds arrows graphs transport domain).family first)
      (decode profile worlds arrows graphs transport body).family).sections)
    (point : declared.base.Elements) :
    ((decode profile worlds arrows graphs transport (sigmaCode profile worlds arrows graphs transport domain body)).model point).value
      ((sigmaPair profile worlds arrows graphs transport domain body first second).val point) =
    (((decode profile worlds arrows graphs transport domain).sigma
      (decode profile worlds arrows graphs transport body)).model point).value
        ((PowerClassPresheafProducts.sigmaPair first second).val point) := by
  change ((decode profile worlds arrows graphs transport (sigmaCode profile worlds arrows graphs transport domain body)).model point).value
    (((sectionEquality (decode_sigma profile worlds arrows graphs transport domain body)).symm
      (PowerClassPresheafProducts.sigmaPair first second)).val point) = _
  rw [sectionEquality_symm]
  exact sectionEquality_value (decode_sigma profile worlds arrows graphs transport domain body).symm _ point

theorem sigmaPair_coordinates (first : (decode profile worlds arrows graphs transport domain).family.sections)
    (second : (PowerClassPresheafProducts.reindex (PowerClassPresheafProducts.sectionMap (decode profile worlds arrows graphs transport domain).family first)
      (decode profile worlds arrows graphs transport body).family).sections)
    (point : declared.base.Elements) :
    HSet.fst (((decode profile worlds arrows graphs transport (sigmaCode profile worlds arrows graphs transport domain body)).model point).value
      ((sigmaPair profile worlds arrows graphs transport domain body first second).val point)) =
        ((decode profile worlds arrows graphs transport domain).model point).value (first.val point) ∧
    HSet.snd (((decode profile worlds arrows graphs transport (sigmaCode profile worlds arrows graphs transport domain body)).model point).value
      ((sigmaPair profile worlds arrows graphs transport domain body first second).val point)) =
        ((decode profile worlds arrows graphs transport body).model ⟨point.1, ⟨point.2, first.val point⟩⟩).value
          (second.val point) := by
  rw [sigmaPair_value]
  constructor
  · exact ((decode profile worlds arrows graphs transport domain).sigma_first
      (decode profile worlds arrows graphs transport body) point _).trans
        (congrArg ((decode profile worlds arrows graphs transport domain).model point).value
          (PowerClassPresheafProducts.sigmaPair_value_fst first second point))
  · exact ((decode profile worlds arrows graphs transport domain).sigma_second
      (decode profile worlds arrows graphs transport body) point _).trans
        (materialValue_heq (decode profile worlds arrows graphs transport body)
          (congrArg (fun argument => (⟨point.1, ⟨point.2, argument⟩⟩ :
            (decode profile worlds arrows graphs transport domain).extension.base.Elements))
              (PowerClassPresheafProducts.sigmaPair_value_fst first second point)) _ _
          (PowerClassPresheafProducts.sigmaPair_value_snd first second point))

def wConstructor (point : declared.base.Elements)
    (label : (decode profile worlds arrows graphs transport domain).family.obj point)
    (branches : ContextualWTypes.Branches (decode profile worlds arrows graphs transport domain).family
      (PowerClassPresheafProducts.indexedBody (decode profile worlds arrows graphs transport domain).family
        (decode profile worlds arrows graphs transport body).family)
      ((decode profile worlds arrows graphs transport domain).w (decode profile worlds arrows graphs transport body) arrows).family label) :
    (decode profile worlds arrows graphs transport (wCode profile worlds arrows graphs transport domain body)).family.obj point :=
  objectEquality (decode_w profile worlds arrows graphs transport domain body).symm point
    ((ContextualWTypes.treeAlgebra (decode profile worlds arrows graphs transport domain).family
      (PowerClassPresheafProducts.indexedBody (decode profile worlds arrows graphs transport domain).family
        (decode profile worlds arrows graphs transport body).family)).make point label branches)

theorem wConstructor_value (point : declared.base.Elements)
    (label : (decode profile worlds arrows graphs transport domain).family.obj point)
    (branches : ContextualWTypes.Branches (decode profile worlds arrows graphs transport domain).family
      (PowerClassPresheafProducts.indexedBody (decode profile worlds arrows graphs transport domain).family
        (decode profile worlds arrows graphs transport body).family)
      ((decode profile worlds arrows graphs transport domain).w (decode profile worlds arrows graphs transport body) arrows).family label) :
    ((decode profile worlds arrows graphs transport (wCode profile worlds arrows graphs transport domain body)).model point).value
      (wConstructor profile worlds arrows graphs transport domain body point label branches) =
        (((decode profile worlds arrows graphs transport domain).w (decode profile worlds arrows graphs transport body) arrows).model point).value
          ((ContextualWTypes.treeAlgebra (decode profile worlds arrows graphs transport domain).family
            (PowerClassPresheafProducts.indexedBody (decode profile worlds arrows graphs transport domain).family
              (decode profile worlds arrows graphs transport body).family)).make point label branches) :=
  objectEquality_value (decode_w profile worlds arrows graphs transport domain body).symm point _

noncomputable def wFold (target : MaterialFamily declared)
    (algebra : ContextualWTypes.Algebra (decode profile worlds arrows graphs transport domain).family
      (PowerClassPresheafProducts.indexedBody (decode profile worlds arrows graphs transport domain).family
        (decode profile worlds arrows graphs transport body).family) target.family)
    (point : declared.base.Elements)
    (tree : (decode profile worlds arrows graphs transport (wCode profile worlds arrows graphs transport domain body)).family.obj point) :
    target.family.obj point :=
  ContextualWTypes.fold (decode profile worlds arrows graphs transport domain).family
    (PowerClassPresheafProducts.indexedBody (decode profile worlds arrows graphs transport domain).family
      (decode profile worlds arrows graphs transport body).family) algebra
    (objectEquality (decode_w profile worlds arrows graphs transport domain body) point tree)

theorem wFold_natural (target : MaterialFamily declared)
    (algebra : ContextualWTypes.Algebra (decode profile worlds arrows graphs transport domain).family
      (PowerClassPresheafProducts.indexedBody (decode profile worlds arrows graphs transport domain).family
        (decode profile worlds arrows graphs transport body).family) target.family)
    {point next : declared.base.Elements} (step : point ⟶ next)
    (tree : (decode profile worlds arrows graphs transport (wCode profile worlds arrows graphs transport domain body)).family.obj point) :
    target.family.map step (wFold profile worlds arrows graphs transport domain body target algebra point tree) =
      wFold profile worlds arrows graphs transport domain body target algebra next
        ((decode profile worlds arrows graphs transport (wCode profile worlds arrows graphs transport domain body)).family.map step tree) :=
  (ContextualWTypes.fold_natural (decode profile worlds arrows graphs transport domain).family
    (PowerClassPresheafProducts.indexedBody (decode profile worlds arrows graphs transport domain).family
      (decode profile worlds arrows graphs transport body).family) algebra step _).trans
        (congrArg (ContextualWTypes.fold (decode profile worlds arrows graphs transport domain).family
          (PowerClassPresheafProducts.indexedBody (decode profile worlds arrows graphs transport domain).family
            (decode profile worlds arrows graphs transport body).family) algebra)
          (objectEquality_natural (decode_w profile worlds arrows graphs transport domain body) step tree).symm)

theorem wFold_beta (target : MaterialFamily declared)
    (algebra : ContextualWTypes.Algebra (decode profile worlds arrows graphs transport domain).family
      (PowerClassPresheafProducts.indexedBody (decode profile worlds arrows graphs transport domain).family
        (decode profile worlds arrows graphs transport body).family) target.family)
    (point : declared.base.Elements)
    (label : (decode profile worlds arrows graphs transport domain).family.obj point)
    (branches : ContextualWTypes.Branches (decode profile worlds arrows graphs transport domain).family
      (PowerClassPresheafProducts.indexedBody (decode profile worlds arrows graphs transport domain).family
        (decode profile worlds arrows graphs transport body).family)
      ((decode profile worlds arrows graphs transport domain).w (decode profile worlds arrows graphs transport body) arrows).family label) :
    wFold profile worlds arrows graphs transport domain body target algebra point
      (wConstructor profile worlds arrows graphs transport domain body point label branches) =
        algebra.make point label (branches.map (ContextualWTypes.foldMap
          (decode profile worlds arrows graphs transport domain).family
          (PowerClassPresheafProducts.indexedBody (decode profile worlds arrows graphs transport domain).family
            (decode profile worlds arrows graphs transport body).family) algebra)) :=
  (congrArg (ContextualWTypes.fold (decode profile worlds arrows graphs transport domain).family
    (PowerClassPresheafProducts.indexedBody (decode profile worlds arrows graphs transport domain).family
      (decode profile worlds arrows graphs transport body).family) algebra)
    (objectEquality_reverse (decode_w profile worlds arrows graphs transport domain body) point _)).trans
      (ContextualWTypes.fold_beta _ _ algebra label branches)

def identityCode (left right : (decode profile worlds arrows graphs transport domain).family.sections) :
    Code profile worlds arrows graphs transport declared := ContextualClosedUniverseCodes.identity _ _ _ domain left right

theorem identity_fibre_inhabited_iff
    (left right : (decode profile worlds arrows graphs transport domain).family.sections)
    (point : declared.base.Elements) :
    Nonempty ((decode profile worlds arrows graphs transport (identityCode profile worlds arrows graphs transport domain left right)).family.obj point) ↔
      left.val point = right.val point := by
  have interpretation : decode profile worlds arrows graphs transport
      (identityCode profile worlds arrows graphs transport domain left right) =
        (decode profile worlds arrows graphs transport domain).identity left right :=
    ContextualClosedUniverseCodes.decode_identity _ _ _ domain left right
  have inhabited : Nonempty ((decode profile worlds arrows graphs transport
      (identityCode profile worlds arrows graphs transport domain left right)).family.obj point) =
        Nonempty (PresheafIdentityWitness.Witness (left.val point) (right.val point)) :=
    congrArg (fun family : MaterialFamily declared => Nonempty (family.family.obj point)) interpretation
  constructor
  · intro supported
    obtain ⟨witness⟩ := Eq.mp inhabited supported
    exact PresheafIdentityWitness.decode witness
  · intro same
    exact Eq.mpr inhabited ⟨PresheafIdentityWitness.encode same⟩

theorem code_enclosed (code : Code profile worlds arrows graphs transport declared) (point : declared.base.Elements) :
    HSet.lift ((decode profile worlds arrows graphs transport code).model point).carrier ∈
      enclosure (ObservedGeneratedModel.Seeds profile worlds)
        (ObservedGeneratedModel.seedModel profile worlds graphs transport) arrows declared point :=
  ContextualClosedUniverseCodes.interpreted_code_enclosed _ _ _ code point

/-- The pointwise carrier range is constructed directly over the closed
codes. The full family data remain in its external indexing carrier. -/
def codeImage (declared : LabelledContext C) (point : declared.base.Elements) : HSet.{u + 1} :=
  HSet.imageUp (fun code : Code profile worlds arrows graphs transport declared =>
    (decode profile worlds arrows graphs transport code).model point |>.carrier)

theorem codeImage_eq (point : declared.base.Elements) :
    codeImage profile worlds arrows graphs transport declared point =
      enclosure (ObservedGeneratedModel.Seeds profile worlds)
        (ObservedGeneratedModel.seedModel profile worlds graphs transport) arrows declared point := by
  apply HSet.ext
  intro value
  constructor
  · intro belongs
    obtain ⟨code, same⟩ := HSet.mem_imageUp_iff.mp belongs
    revert same
    refine Quotient.inductionOn code ?_
    intro raw same
    exact (mem_enclosure_iff _ _ _).mpr ⟨raw, same⟩
  · intro belongs
    obtain ⟨raw, same⟩ := (mem_enclosure_iff _ _ _).mp belongs
    exact HSet.mem_imageUp_iff.mpr ⟨ContextualClosedUniverseCodes.ofRaw _ _ _ raw, same⟩

section Source

variable (code : Code profile worlds arrows graphs transport (ObservedGeneratedModel.context profile worlds))

/-- The source family of every closed code has constructed material
transport with its exact observation-fibre compatibility. -/
def sourceTransport : MaterialTransport profile.sourceFace profile.classFace profile.observation
    (ObservedGeneratedFamilyDescent.rawGraphs profile worlds (decode profile worlds arrows graphs transport code)) :=
  ObservedGeneratedFamilyDescent.rawTransport profile worlds (decode profile worlds arrows graphs transport code)

def sourceSections : (decode profile worlds arrows graphs transport code).family.sections ≃
    {term : RawSection profile.sourceFace (ObservedGeneratedFamilyDescent.rawGraphs profile worlds (decode profile worlds arrows graphs transport code)) //
      ContextualCompatible profile.sourceFace profile.classFace profile.observation
        (ObservedGeneratedFamilyDescent.rawGraphs profile worlds (decode profile worlds arrows graphs transport code))
        (sourceTransport profile worlds arrows graphs transport code) term} :=
  ObservedGeneratedFamilyDescent.compatibleSectionEquiv profile worlds (decode profile worlds arrows graphs transport code)

theorem sourceSections_value (term : (decode profile worlds arrows graphs transport code).family.sections)
    (source : profile.sourceFace.Elements) :
    ((sourceSections profile worlds arrows graphs transport code term).val source).1 =
      ((decode profile worlds arrows graphs transport code).model
        (ObservedGeneratedModel.observedPoint profile worlds source)).value
          (term.val (ObservedGeneratedModel.observedPoint profile worlds source)) :=
  ObservedGeneratedFamilyDescent.compatibleSectionEquiv_value profile worlds _ term source

theorem classifier_factors :
    ∃ classifier : NatTrans profile.classFace (Mettapedia.GSLT.Topos.omegaFunctor (C := C)),
      ∀ X source, classifier.app X (profile.observation.app X source) =
        (Mettapedia.OSLF.Bridges.TypeTheory.ContextualObservedNativeTypes.Classifier.characteristic
          (Mettapedia.GSLT.Topos.support (ObservedGeneratedModel.sourceFamily profile worlds
            (decode profile worlds arrows graphs transport code)))).app X source :=
  ObservedGeneratedModel.source_classifier_factors profile worlds _

end Source

namespace Modal

open Mettapedia.GSLT.Topos.ConstructivePresheaf
open Mettapedia.GSLT.Topos.PresheafEventModalities
open Mettapedia.OSLF.Bridges.TypeTheory.ContextualObservedNativeTypes

variable (occurrences : ∀ X, ObservedMaterialization.ActionOccurrences (profile.system X))
variable (action : Events.EventAction profile occurrences)
variable (code : Code profile worlds arrows graphs transport (ObservedGeneratedModel.context profile worlds))

theorem source_diamond :
    preimage profile.observation
      (diamond (Modal.observedGraph profile occurrences action)
        (observedImage profile (Mettapedia.GSLT.Topos.support (ObservedGeneratedModel.sourceFamily profile worlds
          (decode profile worlds arrows graphs transport code))))) =
      diamond (Modal.sourceGraph profile occurrences action)
        (Mettapedia.GSLT.Topos.support (ObservedGeneratedModel.sourceFamily profile worlds
          (decode profile worlds arrows graphs transport code))) :=
  Modal.diamond_image_exact profile occurrences action _
    (ObservedGeneratedModel.source_support_kernel profile worlds _)

theorem source_box (incoming : ∀ X, ((occurrences X).observation (profile.readings X)).TargetLifts) :
    preimage profile.observation
      (box (Modal.observedGraph profile occurrences action)
        (observedImage profile (Mettapedia.GSLT.Topos.support (ObservedGeneratedModel.sourceFamily profile worlds
          (decode profile worlds arrows graphs transport code))))) =
      box (Modal.sourceGraph profile occurrences action)
        (Mettapedia.GSLT.Topos.support (ObservedGeneratedModel.sourceFamily profile worlds
          (decode profile worlds arrows graphs transport code))) :=
  Modal.box_image_exact profile occurrences action incoming _
    (ObservedGeneratedModel.source_support_kernel profile worlds _)

end Modal

namespace Paths

open ObservedGeneratedModelControls.Paths

def seed : Code model worldCoding arrowCoding familyGraphs familyTransport (ObservedGeneratedModel.context model worldCoding) :=
  inputCode model worldCoding arrowCoding familyGraphs familyTransport

def dependentBody : Code model worldCoding arrowCoding familyGraphs familyTransport
    (decode model worldCoding arrowCoding familyGraphs familyTransport seed).extension :=
  ContextualClosedUniverseCodes.ofRaw _ _ _ ⟨argumentBody, argumentBodyGenerated⟩

def dependentPi : Code model worldCoding arrowCoding familyGraphs familyTransport (ObservedGeneratedModel.context model worldCoding) :=
  piCode model worldCoding arrowCoding familyGraphs familyTransport seed dependentBody

def dependentSigma : Code model worldCoding arrowCoding familyGraphs familyTransport (ObservedGeneratedModel.context model worldCoding) :=
  sigmaCode model worldCoding arrowCoding familyGraphs familyTransport seed dependentBody

def dependentW : Code model worldCoding arrowCoding familyGraphs familyTransport (ObservedGeneratedModel.context model worldCoding) :=
  wCode model worldCoding arrowCoding familyGraphs familyTransport seed dependentBody

theorem dependentBody_empty_argument :
    ((decode model worldCoding arrowCoding familyGraphs familyTransport dependentBody).model emptyPoint).carrier = {∅} :=
  empty_positions

theorem dependentBody_cyclic_argument :
    ((decode model worldCoding arrowCoding familyGraphs familyTransport dependentBody).model cyclicPoint).carrier = ∅ :=
  cyclic_positions

theorem dependentPi_empty_initial :
    ((decode model worldCoding arrowCoding familyGraphs familyTransport dependentPi).model
      (ObservedGeneratedModel.observedPoint model worldCoding oldRaw)).carrier = ∅ := by
  exact (congrArg (fun family : MaterialFamily (ObservedGeneratedModel.context model worldCoding) =>
    (family.model (ObservedGeneratedModel.observedPoint model worldCoding oldRaw)).carrier)
      (decode_pi model worldCoding arrowCoding familyGraphs familyTransport seed dependentBody)).trans
        dependent_pi_empty_initial

theorem dependentPi_not_unit :
    dependentPi ≠ ContextualClosedUniverseCodes.unit (ObservedGeneratedModel.Seeds model worldCoding)
      (ObservedGeneratedModel.seedModel model worldCoding familyGraphs familyTransport) arrowCoding
      (ObservedGeneratedModel.context model worldCoding) := by
  intro same
  have carriers := congrArg (fun code => ((decode model worldCoding arrowCoding familyGraphs familyTransport code).model
    (ObservedGeneratedModel.observedPoint model worldCoding oldRaw)).carrier) same
  have unitCarrier : ((decode model worldCoding arrowCoding familyGraphs familyTransport
      (ContextualClosedUniverseCodes.unit (ObservedGeneratedModel.Seeds model worldCoding)
        (ObservedGeneratedModel.seedModel model worldCoding familyGraphs familyTransport) arrowCoding
        (ObservedGeneratedModel.context model worldCoding))).model
      (ObservedGeneratedModel.observedPoint model worldCoding oldRaw)).carrier = {∅} :=
    AccessiblePointedGraph.mk_singletonGraph AccessiblePointedGraph.empty |>.trans
      (congrArg (fun value : HSet.{0} => ({value} : HSet.{0})) HSet.mk_empty)
  exact HSet.empty_ne_singleton_empty (dependentPi_empty_initial.symm.trans (carriers.trans unitCarrier))

theorem dependent_operations_enclosed (point : (ObservedGeneratedModel.context model worldCoding).base.Elements) :
    HSet.lift ((decode model worldCoding arrowCoding familyGraphs familyTransport dependentPi).model point).carrier ∈
        enclosure (ObservedGeneratedModel.Seeds model worldCoding)
          (ObservedGeneratedModel.seedModel model worldCoding familyGraphs familyTransport) arrowCoding
          (ObservedGeneratedModel.context model worldCoding) point ∧
    HSet.lift ((decode model worldCoding arrowCoding familyGraphs familyTransport dependentSigma).model point).carrier ∈
        enclosure (ObservedGeneratedModel.Seeds model worldCoding)
          (ObservedGeneratedModel.seedModel model worldCoding familyGraphs familyTransport) arrowCoding
          (ObservedGeneratedModel.context model worldCoding) point ∧
    HSet.lift ((decode model worldCoding arrowCoding familyGraphs familyTransport dependentW).model point).carrier ∈
        enclosure (ObservedGeneratedModel.Seeds model worldCoding)
          (ObservedGeneratedModel.seedModel model worldCoding familyGraphs familyTransport) arrowCoding
          (ObservedGeneratedModel.context model worldCoding) point :=
  ⟨code_enclosed model worldCoding arrowCoding familyGraphs familyTransport dependentPi point,
    code_enclosed model worldCoding arrowCoding familyGraphs familyTransport dependentSigma point,
    code_enclosed model worldCoding arrowCoding familyGraphs familyTransport dependentW point⟩

end Paths

end Mettapedia.GSLT.ObservedGeneratedClosedUniverse
