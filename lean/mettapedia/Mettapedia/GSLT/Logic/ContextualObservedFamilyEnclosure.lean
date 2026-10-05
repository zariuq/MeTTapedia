import Mettapedia.GSLT.Logic.ObservedFamilyEnclosure
import Mettapedia.GSLT.Logic.HennessyMilnerTransport
import Mettapedia.GSLT.Logic.ObserverPresheaf
import Mettapedia.TypeTheory.MaterialSets.Hypersets.PowerClassPresheafDescent
import Mettapedia.TypeTheory.MaterialSets.Hypersets.PowerClassPresheafProducts
import Mettapedia.TypeTheory.DisplayedPresheafPiSubstitution
import Mettapedia.TypeTheory.DisplayedPresheafSlicePi
import Mettapedia.TypeTheory.DisplayedPresheafSliceSigma
import Mettapedia.TypeTheory.PresheafDependentBaseChange

/-!
# Contextual observed values and dependent families

Authored restrictions act on operational states and preserve the declared
observed bisimulation. Their images determine maps of whole observation
fibres, and these maps give a presheaf of actual material values. No source
representative is selected. Original action occurrences remain alongside
that readout.

The small observation face supports the existing displayed-presheaf CwF.
Its dependent product is the full contextual right-Kan product; the
pointwise material product is a separate construction. Ordinary model
identity and categorical substitution comparisons do not assert native
judgmental conversion or higher identity rules.

The value, occurrence and direct all-future function constructions use no
classical choice. The categorical comparison declarations reuse the
existing presheaf adjoints and retain their classical-choice dependency.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.ContextualObservedFamilyEnclosure

open CategoryTheory
open Mettapedia.TypeTheory.MaterialSets
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open ObservedMaterialization HennessyMilner

universe u

variable {C : Type u} [Category.{u} C]

/-- A contextual operational system with its authored restrictions.
Kernel preservation is the semantic condition on those restrictions;
the observation quotient and its maps are constructed below. -/
structure ContextualSystem (C : Type u) [Category.{u} C] where
  theory : Cᵒᵖ → GSLT.{u}
  system : ∀ X, System.{u, u} (theory X)
  readings : ∀ X, LabelReadings (system X)
  faithful : ∀ X, (readings X).Faithful
  restrict : ∀ {X Y : Cᵒᵖ}, (X ⟶ Y) → (theory X).Term → (theory Y).Term
  restrict_id : ∀ X term, restrict (𝟙 X) term = term
  restrict_comp : ∀ {X Y Z : Cᵒᵖ} (first : X ⟶ Y) (second : Y ⟶ Z) term,
    restrict (first ≫ second) term = restrict second (restrict first term)
  bisim_restrict : ∀ {X Y : Cᵒᵖ} (step : X ⟶ Y) {left right},
    (system X).Bisimilar left right →
      (system Y).Bisimilar (restrict step left) (restrict step right)

namespace ContextualSystem

variable (P : ContextualSystem C)

def sourceFace : Cᵒᵖ ⥤ Type u where
  obj X := (P.theory X).Term
  map step := TypeCat.ofHom (P.restrict step)
  map_id X := by
    apply ConcreteCategory.hom_ext
    exact P.restrict_id X
  map_comp first second := by
    apply ConcreteCategory.hom_ext
    exact P.restrict_comp first second

theorem restrict_value_eq {X Y : Cᵒᵖ} (step : X ⟶ Y) {left right}
    (same : (P.readings X).value left = (P.readings X).value right) :
    (P.readings Y).value (P.restrict step left) =
      (P.readings Y).value (P.restrict step right) :=
  (P.readings Y).value_eq_of_bisimilar
    (P.bisim_restrict step (((P.readings X).value_eq_iff_bisimilar (P.faithful X) _ _).mp same))

/-- The entire target fibre containing the image of an input fibre. -/
def restrictClass {X Y : Cᵒᵖ} (step : X ⟶ Y)
    (observed : ObservedFamilyEnclosure.Classes (P.readings X)) :
    ObservedFamilyEnclosure.Classes (P.readings Y) :=
  ⟨{target | ∃ source, source ∈ observed.1 ∧
      (P.readings Y).value target = (P.readings Y).value (P.restrict step source)}, by
    obtain ⟨source, same⟩ := observed.2
    refine ⟨P.restrict step source, ?_⟩
    ext target
    constructor
    · rintro ⟨other, member, targetEqual⟩
      have equal : (P.readings X).value other = (P.readings X).value source := by
        rw [same] at member
        exact member
      exact targetEqual.trans (P.restrict_value_eq step equal)
    · intro targetEqual
      exact ⟨source, by rw [same]; rfl, targetEqual⟩⟩

theorem restrictClass_classOf {X Y : Cᵒᵖ} (step : X ⟶ Y) (source : (P.theory X).Term) :
    P.restrictClass step (PowerClassFamilyDescent.classOf (P.readings X).value source) =
      PowerClassFamilyDescent.classOf (P.readings Y).value (P.restrict step source) := by
  apply Subtype.ext
  ext target
  constructor
  · rintro ⟨other, member, targetEqual⟩
    exact targetEqual.trans (P.restrict_value_eq step member)
  · intro targetEqual
    exact ⟨source, rfl, targetEqual⟩

def classFace : Cᵒᵖ ⥤ Type u where
  obj X := ObservedFamilyEnclosure.Classes (P.readings X)
  map step := TypeCat.ofHom (P.restrictClass step)
  map_id X := by
    apply ConcreteCategory.hom_ext
    intro observed
    obtain ⟨source, rfl⟩ := PowerClassFamilyDescent.classOf_surjective (P.readings X).value observed
    exact (P.restrictClass_classOf (𝟙 X) source).trans
      (congrArg (PowerClassFamilyDescent.classOf (P.readings X).value) (P.restrict_id X source))
  map_comp first second := by
    apply ConcreteCategory.hom_ext
    intro observed
    obtain ⟨source, rfl⟩ := PowerClassFamilyDescent.classOf_surjective (P.readings _).value observed
    change P.restrictClass (first ≫ second) _ = P.restrictClass second (P.restrictClass first _)
    rw [P.restrictClass_classOf, P.restrictClass_classOf, P.restrictClass_classOf, P.restrict_comp]

def observation : NatTrans P.sourceFace P.classFace where
  app X := TypeCat.ofHom (PowerClassFamilyDescent.classOf (P.readings X).value)
  naturality X Y step := by
    apply ConcreteCategory.hom_ext
    intro source
    exact (P.restrictClass_classOf step source).symm

theorem observation_eq_iff (X : Cᵒᵖ) (left right : (P.theory X).Term) :
    P.observation.app X left = P.observation.app X right ↔ (P.system X).Bisimilar left right :=
  (PowerClassFamilyDescent.classOf_eq_iff (P.readings X).value left right).trans
    ((P.readings X).value_eq_iff_bisimilar (P.faithful X) left right)

/-- Material restriction is induced by the actual small-class/member
equivalence. Its action on source readings is proved below. -/
def materialFace : Cᵒᵖ ⥤ Type (u + 1) where
  obj X := LiftedFamilyModel.Elements (ObservedFamilyEnclosure.valueRange (P.readings X))
  map {X Y} step := TypeCat.ofHom (fun member =>
    ObservedFamilyEnclosure.classMemberEquiv (P.readings Y)
      (P.classFace.map step ((ObservedFamilyEnclosure.classMemberEquiv (P.readings X)).symm member)))
  map_id X := by
    apply ConcreteCategory.hom_ext
    intro member
    change ObservedFamilyEnclosure.classMemberEquiv (P.readings X)
      (P.classFace.map (𝟙 X) ((ObservedFamilyEnclosure.classMemberEquiv (P.readings X)).symm member)) = member
    exact (congrArg (ObservedFamilyEnclosure.classMemberEquiv (P.readings X))
      (P.classFace.map_id_apply X _)).trans
        ((ObservedFamilyEnclosure.classMemberEquiv (P.readings X)).apply_symm_apply member)
  map_comp {X Y Z} first second := by
    apply ConcreteCategory.hom_ext
    intro member
    change ObservedFamilyEnclosure.classMemberEquiv (P.readings Z)
        (P.classFace.map (first ≫ second)
          ((ObservedFamilyEnclosure.classMemberEquiv (P.readings X)).symm member)) =
      ObservedFamilyEnclosure.classMemberEquiv (P.readings Z)
        (P.classFace.map second ((ObservedFamilyEnclosure.classMemberEquiv (P.readings Y)).symm
          (ObservedFamilyEnclosure.classMemberEquiv (P.readings Y)
            (P.classFace.map first ((ObservedFamilyEnclosure.classMemberEquiv (P.readings X)).symm member)))))
    exact (congrArg (ObservedFamilyEnclosure.classMemberEquiv (P.readings Z))
      (P.classFace.map_comp_apply first second _)).trans
        (congrArg (fun value => ObservedFamilyEnclosure.classMemberEquiv (P.readings Z)
          (P.classFace.map second value))
          ((ObservedFamilyEnclosure.classMemberEquiv (P.readings Y)).symm_apply_apply _).symm)

/-- Every authored source restriction commutes with the material readout. -/
theorem materialFace_valueMember {X Y : Cᵒᵖ} (step : X ⟶ Y) (source : (P.theory X).Term) :
    P.materialFace.map step (ObservedFamilyEnclosure.valueMember (P.readings X) source) =
      ObservedFamilyEnclosure.valueMember (P.readings Y) (P.restrict step source) := by
  change ObservedFamilyEnclosure.classMemberEquiv (P.readings Y)
      (P.restrictClass step ((ObservedFamilyEnclosure.classMemberEquiv (P.readings X)).symm
        (ObservedFamilyEnclosure.valueMember (P.readings X) source))) = _
  rw [ObservedFamilyEnclosure.classMemberEquiv_symm_valueMember, P.restrictClass_classOf,
    ObservedFamilyEnclosure.classMemberEquiv_classOf]

theorem materialFace_source_kernel (X : Cᵒᵖ) (left right : (P.theory X).Term) :
    ObservedFamilyEnclosure.valueMember (P.readings X) left =
      ObservedFamilyEnclosure.valueMember (P.readings X) right ↔
        (P.system X).Bisimilar left right :=
  ObservedFamilyEnclosure.valueMember_eq_iff (P.readings X) (P.faithful X) left right

/-- The universe lift changes the carrier level only. Its natural map is
the actual material readout proved against authored restrictions. -/
def liftedSourceFace : Cᵒᵖ ⥤ Type (u + 1) where
  obj X := ULift.{u + 1} ((P.theory X).Term)
  map step := TypeCat.ofHom (fun source => ULift.up (P.restrict step source.down))
  map_id X := by
    apply ConcreteCategory.hom_ext
    rintro ⟨source⟩
    exact congrArg ULift.up (P.restrict_id X source)
  map_comp first second := by
    apply ConcreteCategory.hom_ext
    rintro ⟨source⟩
    exact congrArg ULift.up (P.restrict_comp first second source)

def materialReadout : NatTrans P.liftedSourceFace P.materialFace where
  app X := TypeCat.ofHom (fun source => ObservedFamilyEnclosure.valueMember (P.readings X) source.down)
  naturality X Y step := by
    apply ConcreteCategory.hom_ext
    intro source
    exact (P.materialFace_valueMember step source.down).symm

/-- Covers reaching every target atom and action label discharge the
restriction kernel condition from operational matching. -/
theorem bisim_restrict_of_cover {X Y : Cᵒᵖ} (step : X ⟶ Y)
    (cover : SystemCover (P.system X) (P.system Y))
    (termMap : cover.mapTerm = P.restrict step)
    (atoms : Function.Surjective cover.mapAtom)
    (labels : Function.Surjective cover.mapLabel) {left right}
    (related : (P.system X).Bisimilar left right) :
    (P.system Y).Bisimilar (P.restrict step left) (P.restrict step right) := by
  rw [← termMap]
  exact cover.bisimilar_map atoms labels related

end ContextualSystem

namespace Events

open Mettapedia.OSLF.Framework.DerivedModalities ObservationSpans

variable (P : ContextualSystem C) (occurrences : ∀ X, ActionOccurrences (P.system X))

/-- The restriction of occurrence data is authored independently of its
propositional erasure. Its endpoint and composition laws retain that data. -/
structure EventAction where
  restrict : ∀ {X Y : Cᵒᵖ}, (X ⟶ Y) →
    ActionOccurrences.Event (occurrences X) → ActionOccurrences.Event (occurrences Y)
  source_comm : ∀ {X Y : Cᵒᵖ} (step : X ⟶ Y) event,
    (restrict step event).source = P.restrict step event.source
  target_comm : ∀ {X Y : Cᵒᵖ} (step : X ⟶ Y) event,
    (restrict step event).target = P.restrict step event.target
  restrict_id : ∀ X event, restrict (𝟙 X) event = event
  restrict_comp : ∀ {X Y Z : Cᵒᵖ} (first : X ⟶ Y) (second : Y ⟶ Z) event,
    restrict (first ≫ second) event = restrict second (restrict first event)

variable (action : EventAction P occurrences)

def occurrenceFace : Cᵒᵖ ⥤ Type u where
  obj X := ActionOccurrences.Event (occurrences X)
  map step := TypeCat.ofHom (action.restrict step)
  map_id X := by apply ConcreteCategory.hom_ext; exact action.restrict_id X
  map_comp first second := by
    apply ConcreteCategory.hom_ext
    exact action.restrict_comp first second

def source : NatTrans (occurrenceFace P occurrences action) P.sourceFace where
  app _ := TypeCat.ofHom ActionOccurrences.Event.source
  naturality _ _ step := by
    apply ConcreteCategory.hom_ext
    intro event
    exact action.source_comm step event

def target : NatTrans (occurrenceFace P occurrences action) P.sourceFace where
  app _ := TypeCat.ofHom ActionOccurrences.Event.target
  naturality _ _ step := by
    apply ConcreteCategory.hom_ext
    intro event
    exact action.target_comm step event

def sourceSpanMap {X Y : Cᵒᵖ} (step : X ⟶ Y) :
    SpanMap (occurrences X).sourceSpan (occurrences Y).sourceSpan where
  states := P.restrict step
  events := action.restrict step
  source_comm := action.source_comm step
  target_comm := action.target_comm step

/-- Material restriction keeps the authored event map and changes its
endpoints through the proved natural value map. -/
def materialSpanMap {X Y : Cᵒᵖ} (step : X ⟶ Y) :
    SpanMap (ObservedFamilyEnclosure.Events.memberSpan (P.readings X) (occurrences X))
      (ObservedFamilyEnclosure.Events.memberSpan (P.readings Y) (occurrences Y)) where
  states := P.materialFace.map step
  events := action.restrict step
  source_comm event :=
    (congrArg (ObservedFamilyEnclosure.valueMember (P.readings Y))
      (action.source_comm step event)).trans (P.materialFace_valueMember step event.source).symm
  target_comm event :=
    (congrArg (ObservedFamilyEnclosure.valueMember (P.readings Y))
      (action.target_comm step event)).trans (P.materialFace_valueMember step event.target).symm

private theorem spanMap_ext {X : Type*} {Y : Type*} {A : ReductionSpan X} {B : ReductionSpan Y}
    {first second : SpanMap A B} (states : first.states = second.states)
    (events : first.events = second.events) : first = second := by
  cases first
  cases second
  cases states
  cases events
  rfl

theorem materialSpanMap_natural {X Y : Cᵒᵖ} (step : X ⟶ Y) :
    SpanMap.comp (materialSpanMap P occurrences action step)
        (ObservedFamilyEnclosure.Events.observation (P.readings X) (occurrences X)) =
      SpanMap.comp (ObservedFamilyEnclosure.Events.observation (P.readings Y) (occurrences Y))
        (sourceSpanMap P occurrences action step) := by
  apply spanMap_ext
  · funext state
    exact P.materialFace_valueMember step state
  · rfl

theorem materialSpanMap_events_injective {X Y : Cᵒᵖ} (step : X ⟶ Y)
    (injective : Function.Injective (action.restrict step)) :
    Function.Injective (materialSpanMap P occurrences action step).events := injective

end Events

namespace SaturatedObservers

open Mettapedia.GSLT.AdmissibleContextCongruence
open Mettapedia.GSLT.MinimalEnablingContext

variable {S : GSLT.{u}} {rules : ContextualRules.{u, u} S}
variable (observations : ContextualRules.Observations.{u} S)
variable (readings : ∀ A : AdmissibleClass rules, LabelReadings (A.saturated observations))
variable (faithful : ∀ A, (readings A).Faithful)

/-- The actual admissible-observer presheaf supplies a contextual system.
Its raw restriction keeps authored terms; weakening observation derives
kernel preservation from the existing saturated congruence theorem. -/
def profile : ContextualSystem (AdmissibleClass rules) where
  theory _ := S
  system X := X.unop.saturated observations
  readings X := readings X.unop
  faithful X := faithful X.unop
  restrict _ := id
  restrict_id _ _ := rfl
  restrict_comp _ _ _ := rfl
  bisim_restrict := by
    intro X Y step left right related
    exact AdmissibleClass.relEquiv_antitone observations (leOfHom step.unop) related

def classOfStage (A : AdmissibleClass rules) :
    AdmissibleClass.Stage observations A →
      ((profile observations readings faithful).classFace).obj (Opposite.op A) :=
  Quotient.lift (PowerClassFamilyDescent.classOf (readings A).value)
    (fun left right related => (PowerClassFamilyDescent.classOf_eq_iff _ left right).mpr
      ((readings A).value_eq_of_bisimilar related))

theorem classOfStage_stageClass (A : AdmissibleClass rules) (term : S.Term) :
    classOfStage observations readings faithful A (A.stageClass observations term) =
      PowerClassFamilyDescent.classOf (readings A).value term := rfl

theorem classOfStage_injective (A : AdmissibleClass rules) :
    Function.Injective (classOfStage observations readings faithful A) := by
  intro first second same
  induction first using Quotient.inductionOn with
  | _ left =>
    induction second using Quotient.inductionOn with
    | _ right =>
      exact Quotient.sound (((readings A).value_eq_iff_bisimilar (faithful A) left right).mp
        ((PowerClassFamilyDescent.classOf_eq_iff _ left right).mp same))

theorem classOfStage_surjective (A : AdmissibleClass rules) :
    Function.Surjective (classOfStage observations readings faithful A) := by
  intro observed
  obtain ⟨source, same⟩ := PowerClassFamilyDescent.classOf_surjective (readings A).value observed
  exact ⟨A.stageClass observations source, same⟩

/-- Existing observer restriction and material-class restriction commute
on the actual quotient. The proof eliminates the quotient, without
selecting its representative as data. -/
def stageComparison : NatTrans (AdmissibleClass.observerPresheaf observations)
    (profile observations readings faithful).classFace where
  app X := TypeCat.ofHom (classOfStage observations readings faithful X.unop)
  naturality X Y step := by
    apply ConcreteCategory.hom_ext
    intro observed
    induction observed using Quotient.inductionOn with
    | _ term =>
      exact ((profile observations readings faithful).restrictClass_classOf step term).symm

theorem admissible_plug_preserves_kernel (A : AdmissibleClass rules) (faithfulA : (readings A).Faithful)
    (context : rules.Context) (admissible : A.Admissible context) {left right : S.Term}
    (same : (readings A).value left = (readings A).value right) :
    (readings A).value (rules.plug context left) = (readings A).value (rules.plug context right) :=
  ObservedMaterialization.Relative.context_preserves_value_eq A observations
    (readings A) faithfulA context admissible same

end SaturatedObservers

namespace Families

open Mettapedia.TypeTheory.DisplayedPresheafTransport
open Mettapedia.TypeTheory.DisplayedPresheafComprehension
open Mettapedia.TypeTheory.DisplayedPresheafPi
open Mettapedia.TypeTheory.DisplayedPresheafPiSubstitution
open Mettapedia.TypeTheory.DisplayedPresheafSigma
open Mettapedia.TypeTheory.DisplayedPresheafSlice
open Mettapedia.TypeTheory.PresheafDependentAdjunction

variable (P : ContextualSystem C)
variable (graphs : P.sourceFace.Elements → AccessiblePointedGraph.{u})
variable (transport : PowerClassPresheafDescent.MaterialTransport
  P.sourceFace P.classFace P.observation graphs)

abbrev observedBase : Cᵒᵖ ⥤ Type u :=
  PowerClassPresheafDescent.classFace P.sourceFace P.classFace P.observation
abbrev readout : P.sourceFace ⟶ observedBase P :=
  PowerClassPresheafDescent.classObservation P.sourceFace P.classFace P.observation
abbrev displayed := PowerClassPresheafDescent.observedDisplayed
  P.sourceFace P.classFace P.observation graphs transport

/-- The family criterion concerns the declared behavioral observation,
including its atoms, rather than only successor bisimulation. -/
theorem family_invariant_iff :
    (∀ X, PowerClassFamilyDescent.FamilyInvariant (P.observation.app X)
      (fun value => graphs ⟨X, value⟩)) ↔
    ∀ X left right, (P.system X).Bisimilar left right →
      HSet.mk (graphs ⟨X, left⟩) = HSet.mk (graphs ⟨X, right⟩) := by
  constructor
  · intro invariant X left right related
    exact invariant X ((P.observation_eq_iff X left right).mpr related)
  · intro invariant X left right same
    exact invariant X left right ((P.observation_eq_iff X left right).mp same)

/-- Comprehension identifies exactly the behavioral base and the complete
material member; it retains the latter independently of source tags. -/
theorem comprehension_kernel (X : Cᵒᵖ)
    (left right : TotalAt (PowerClassPresheafDescent.nativeSourceDisplayed
      P.sourceFace P.classFace P.observation graphs transport) X) :
    (PowerClassPresheafDescent.comprehensionReadout
      P.sourceFace P.classFace P.observation graphs transport).app X left =
    (PowerClassPresheafDescent.comprehensionReadout
      P.sourceFace P.classFace P.observation graphs transport).app X right ↔
      (P.system X).Bisimilar left.1 right.1 ∧
        (PowerClassPresheafDescent.sourceMaterialMemberEquiv P.sourceFace graphs ⟨X, left.1⟩ left.2).1 =
          (PowerClassPresheafDescent.sourceMaterialMemberEquiv P.sourceFace graphs ⟨X, right.1⟩ right.2).1 := by
  exact (PowerClassPresheafDescent.comprehensionReadout_eq_iff
    P.sourceFace P.classFace P.observation graphs transport X left right).trans
      (and_congr (P.observation_eq_iff X left.1 right.1) Iff.rfl)

variable (term : PowerClassPresheafDescent.RawSection P.sourceFace graphs)
variable (compatible : PowerClassPresheafDescent.ContextualCompatible
  P.sourceFace P.classFace P.observation graphs transport term)

abbrev descendedArgument := PowerClassPresheafDescent.descendContextualSection
  P.sourceFace P.classFace P.observation graphs transport term compatible

/-- The argument passed to a contextual dependent function decodes to
the authored section's full material value. -/
theorem descendedArgument_value (point : P.sourceFace.Elements) :
    (PowerClassPresheafDescent.contextualMemberEquiv P.sourceFace P.classFace P.observation graphs
      ⟨point.1, PowerClassFamilyDescent.classOf (P.observation.app point.1) point.2⟩
      ((descendedArgument P graphs transport term compatible).val
        ⟨point.1, PowerClassFamilyDescent.classOf (P.observation.app point.1) point.2⟩)).1 =
      (term point).1 := by
  exact (PowerClassPresheafDescent.pullContextualSection_value
    P.sourceFace P.classFace P.observation graphs transport
    (descendedArgument P graphs transport term compatible) point).symm.trans
      (congrArg (fun sectionValue => (sectionValue point).1)
        (PowerClassPresheafDescent.pull_descendContextualSection
          P.sourceFace P.classFace P.observation graphs transport term compatible))

/-- Full contextual application evaluates an arbitrary natural dependent
body at the descended argument, retaining the entire codomain value. -/
theorem application_raw_beta
    (codomain : DisplayedFamily.{u, u, u, u} (totalSpace (displayed P graphs transport)))
    (body : codomain.sections) (point : (observedBase P).Elements) :
    (appDisplayed (lamDisplayed body) (descendedArgument P graphs transport term compatible)).val point =
      body.val ⟨point.1, ⟨point.2, (descendedArgument P graphs transport term compatible).val point⟩⟩ := by
  rw [pi_beta]
  rfl

/-- Both dependent adjunctions apply to the constructed source readout,
on the actual presheaf slices. This uses the existing categorical model. -/
noncomputable def readoutAdjointTriple :
    (Over.map (readout P) ⊣ Over.pullback (readout P)) ×
      (Over.pullback (readout P) ⊣ dependentProduct (readout P)) :=
  adjointTriple (readout P)

/-- The existing full contextual Pi compares to its slice product for
this constructed material family. -/
noncomputable def piSliceComparison
    (codomain : DisplayedFamily.{u, u, u, u} (totalSpace (displayed P graphs transport))) :
    (dependentProduct (totalProjection (displayed P graphs transport))).obj
      ((totalFunctor (totalSpace (displayed P graphs transport))).obj codomain) ≅
    (totalFunctor (observedBase P)).obj (piDisplayed (displayed P graphs transport) codomain) :=
  Mettapedia.TypeTheory.DisplayedPresheafSlicePi.piSliceIso (displayed P graphs transport) codomain

def sigmaSliceComparison
    (codomain : DisplayedFamily.{u, u, u, u} (totalSpace (displayed P graphs transport))) :
    (totalFunctor (observedBase P)).obj (sigmaDisplayed (displayed P graphs transport) codomain) ≅
      (Over.map (totalProjection (displayed P graphs transport))).obj
        ((totalFunctor (totalSpace (displayed P graphs transport))).obj codomain) :=
  Mettapedia.TypeTheory.DisplayedPresheafSliceSigma.sigmaSliceIso (displayed P graphs transport) codomain

/-- Readout and comprehension give a proved pullback square. Pi base
change therefore follows without an extra observation-amalgamation premise. -/
noncomputable def readoutPiBaseChange :
    dependentProduct (totalProjection (displayed P graphs transport)) ⋙ Over.pullback (readout P) ≅
      Over.pullback (totalReindexMap (readout P) (displayed P graphs transport)) ⋙
        dependentProduct (totalProjection (reindexDisplayed (readout P) (displayed P graphs transport))) :=
  Mettapedia.TypeTheory.PresheafDependentBaseChange.piBaseChange
    (totalReindexMap_isPullback (readout P) (displayed P graphs transport)).flip

noncomputable def readoutPiFormation
    (codomain : DisplayedFamily.{u, u, u, u} (totalSpace (displayed P graphs transport))) :
    piDisplayed (reindexDisplayed (readout P) (displayed P graphs transport))
      (reindexDisplayed (totalReindexMap (readout P) (displayed P graphs transport)) codomain) ≅
    reindexDisplayed (readout P) (piDisplayed (displayed P graphs transport) codomain) :=
  piSubstitutionIso (readout P) (displayed P graphs transport) codomain

theorem readoutSigmaFormation
    (codomain : DisplayedFamily.{u, u, u, u} (totalSpace (displayed P graphs transport))) :
    reindexDisplayed (readout P) (sigmaDisplayed (displayed P graphs transport) codomain) =
      sigmaDisplayed (reindexDisplayed (readout P) (displayed P graphs transport))
        (reindexDisplayed (totalReindexMap (readout P) (displayed P graphs transport)) codomain) :=
  sigmaDisplayed_reindex (readout P) (displayed P graphs transport) codomain

/-- The function formation comparison also preserves abstraction. -/
theorem readoutLambdaSubstitution
    (codomain : DisplayedFamily.{u, u, u, u} (totalSpace (displayed P graphs transport)))
    (body : codomain.sections) :
    (Functor.sectionsFunctor P.sourceFace.Elements).map
      (readoutPiFormation P graphs transport codomain).hom
      (lamDisplayed (reindexDisplayedSection
        (totalReindexMap (readout P) (displayed P graphs transport)) codomain body)) =
    reindexDisplayedSection (readout P)
      (piDisplayed (displayed P graphs transport) codomain) (lamDisplayed body) :=
  lam_substitution_section (readout P) (displayed P graphs transport) codomain body

/-- Substitution preserves full dependent application, including the
codomain transport induced by the constructed comprehension square. -/
theorem readoutApplicationSubstitution
    (codomain : DisplayedFamily.{u, u, u, u} (totalSpace (displayed P graphs transport)))
    (function : (piDisplayed (displayed P graphs transport) codomain).sections)
    (argument : (displayed P graphs transport).sections) :
    appDisplayed (reindexFunction (readout P) (displayed P graphs transport) codomain function)
        (reindexDisplayedSection (readout P) (displayed P graphs transport) argument) =
      Mettapedia.TypeTheory.DisplayedPresheafCwf.reindexDependentSection
        (readout P) (displayed P graphs transport) codomain argument (appDisplayed function argument) :=
  app_substitution (readout P) (displayed P graphs transport) codomain function argument

/-- The comprehension pullback comparison preserves the counit, hence
actual dependent evaluation rather than only product formation. -/
theorem readoutPiBaseChange_evaluation
    (codomain : Over (totalSpace (displayed P graphs transport))) :
    (Over.pullback (totalProjection (reindexDisplayed (readout P) (displayed P graphs transport))) ⋙
      Over.map (totalReindexMap (readout P) (displayed P graphs transport))).map
        ((readoutPiBaseChange P graphs transport).hom.app codomain) ≫
      ((dependentAdjunction (totalProjection (reindexDisplayed (readout P) (displayed P graphs transport)))).comp
        (Over.mapPullbackAdj (totalReindexMap (readout P) (displayed P graphs transport)))).counit.app codomain =
    (Mettapedia.TypeTheory.SliceBeckChevalley.sigmaBaseChange
      (totalReindexMap_isPullback (readout P) (displayed P graphs transport))).hom.app
        ((dependentProduct (totalProjection (displayed P graphs transport)) ⋙
          Over.pullback (readout P)).obj codomain) ≫
      ((Over.mapPullbackAdj (readout P)).comp
        (dependentAdjunction (totalProjection (displayed P graphs transport)))).counit.app codomain :=
  Mettapedia.TypeTheory.PresheafDependentBaseChange.piBaseChange_evaluation
    (totalReindexMap_isPullback (readout P) (displayed P graphs transport)).flip codomain

end Families

namespace ConstructiveFamilies

open Mettapedia.TypeTheory.DisplayedPresheafComprehension
open PowerClassPresheafProducts

variable (P : ContextualSystem C)
variable (graphs : P.sourceFace.Elements → AccessiblePointedGraph.{u})
variable (transport : PowerClassPresheafDescent.MaterialTransport
  P.sourceFace P.classFace P.observation graphs)

abbrev domain := Families.displayed P graphs transport

/-- Abstraction of the actual material last variable gives a full
all-future function, with no right-Kan representative selection. -/
def identityFunction :
    (piFamily (domain P graphs transport)
      (reindex (projection (domain P graphs transport)) (domain P graphs transport))).sections :=
  piLambda (lastVariable (domain P graphs transport))

theorem identityFunction_future (first second : (Families.observedBase P).Elements)
    (step : first ⟶ second) (argument : (domain P graphs transport).obj second) :
    ((identityFunction P graphs transport).val first).app second step argument = argument :=
  piLambda_value (lastVariable (domain P graphs transport)) first second step argument

def constantFunction (term : (domain P graphs transport).sections) :
    (piFamily (domain P graphs transport)
      (reindex (projection (domain P graphs transport)) (domain P graphs transport))).sections :=
  piLambda (reindexSection (projection (domain P graphs transport)) (domain P graphs transport) term)

theorem constantFunction_future (term : (domain P graphs transport).sections)
    (first second : (Families.observedBase P).Elements)
    (step : first ⟶ second) (argument : (domain P graphs transport).obj second) :
    ((constantFunction P graphs transport term).val first).app second step argument = term.val second :=
  piLambda_value (reindexSection (projection (domain P graphs transport))
    (domain P graphs transport) term) first second step argument

/-- Actual contextual application decodes to the authored section's
material value. This instantiates the constructed all-future Pi itself. -/
theorem identityApplication_source_value
    (term : PowerClassPresheafDescent.RawSection P.sourceFace graphs)
    (compatible : PowerClassPresheafDescent.ContextualCompatible
      P.sourceFace P.classFace P.observation graphs transport term)
    (point : P.sourceFace.Elements) :
    (PowerClassPresheafDescent.contextualMemberEquiv P.sourceFace P.classFace P.observation graphs
      ⟨point.1, PowerClassFamilyDescent.classOf (P.observation.app point.1) point.2⟩
      ((piApply (identityFunction P graphs transport)
        (Families.descendedArgument P graphs transport term compatible)).val
        ⟨point.1, PowerClassFamilyDescent.classOf (P.observation.app point.1) point.2⟩)).1 =
      (term point).1 := by
  let observed : (Families.observedBase P).Elements :=
    ⟨point.1, PowerClassFamilyDescent.classOf (P.observation.app point.1) point.2⟩
  let argument := Families.descendedArgument P graphs transport term compatible
  have applies := piApply_value (identityFunction P graphs transport) argument observed
  have evaluates := identityFunction_future P graphs transport observed observed (𝟙 observed) (argument.val observed)
  exact (congrArg (fun member =>
    (PowerClassPresheafDescent.contextualMemberEquiv P.sourceFace P.classFace P.observation graphs observed member).1)
      (applies.trans evaluates)).trans (Families.descendedArgument_value P graphs transport term compatible point)

end ConstructiveFamilies

namespace GrowthControls

open PowerClassPresheafDescent.Controls
open AccessiblePointedGraph

/-- Each position runs a two-phase cyclic process. Context extension adds
positions and retains both the old position and its phase. -/
def flip {X : Stagesᵒᵖ} (state : growingSource.obj X) : growingSource.obj X := (state.1, !state.2)

def theory (X : Stagesᵒᵖ) : GSLT where
  Term := growingSource.obj X
  equations := ⟨Eq, Eq.refl, Eq.symm, Eq.trans⟩
  rewrites source target := target = flip source
  rewrites_resp_left := by
    intro left right target same step
    cases same
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step same
    cases same
    exact step

def system (X : Stagesᵒᵖ) : System (theory X) where
  Atom := Fin (stageIndex X + 1)
  observes atom state := state.1 = atom
  observes_resp := by intro atom left right same; cases same; rfl
  Label := Unit
  act _ source target := target = flip source
  act_resp_left := by
    intro label left right target same step
    cases same
    exact ⟨target, step, rfl⟩
  act_resp_right := by
    intro label source target target' step same
    cases same
    exact step

theorem position_isBisimulation (X : Stagesᵒᵖ) :
    (system X).IsBisimulation (fun left right => left.1 = right.1) := by
  constructor
  · intro left right same label target step
    refine ⟨flip right, rfl, ?_⟩
    change target.1 = right.1
    exact (congrArg Prod.fst step).trans same
  constructor
  · intro left right same label target step
    refine ⟨flip left, rfl, ?_⟩
    change left.1 = target.1
    exact same.trans (congrArg Prod.fst step).symm
  · intro left right same atom
    change (left.1 = atom) ↔ (right.1 = atom)
    exact ⟨fun held => same.symm.trans held, fun held => same.trans held⟩

theorem bisimilar_iff_position (X : Stagesᵒᵖ) (left right : (theory X).Term) :
    (system X).Bisimilar left right ↔ left.1 = right.1 := by
  constructor
  · rintro ⟨relation, bisimulation, related⟩
    exact ((bisimulation.2.2 related left.1).mp rfl).symm
  · intro same
    exact ⟨_, position_isBisimulation X, same⟩

def readings (X : Stagesᵒᵖ) : LabelReadings (system X) where
  atom atom := OutcomeLabels.chainValue atom.val
  action _ := ∅
  atomPresentation := ⟨fun atom => OutcomeLabels.chainGraph atom.val,
    fun atom => OutcomeLabels.mk_chainGraph atom.val⟩
  actionPresentation := ⟨fun _ => empty, fun _ => HSet.mk_empty⟩

theorem faithful (X : Stagesᵒᵖ) : (readings X).Faithful := by
  constructor
  · intro first second same
    exact Fin.ext (OutcomeLabels.chainValue_injective same)
  · intro first second same
    cases first
    cases second
    rfl

def profile : ContextualSystem Stages where
  theory := theory
  system := system
  readings := readings
  faithful := faithful
  restrict step := growingSource.map step
  restrict_id X term := growingSource.map_id_apply X term
  restrict_comp first second term := growingSource.map_comp_apply first second term
  bisim_restrict := by
    intro X Y step left right related
    apply (bisimilar_iff_position Y _ _).mpr
    exact congrArg (fun value => value.castLE (Nat.succ_le_succ (growthLe step)))
      ((bisimilar_iff_position X left right).mp related)

theorem value_eq_iff_position (X : Stagesᵒᵖ) (left right : (theory X).Term) :
    (readings X).value left = (readings X).value right ↔ left.1 = right.1 :=
  ((readings X).value_eq_iff_bisimilar (faithful X) left right).trans
    (bisimilar_iff_position X left right)

theorem growing_material_naturality {X Y : Stagesᵒᵖ} (step : X ⟶ Y) (source : (theory X).Term) :
    profile.materialFace.map step (ObservedFamilyEnclosure.valueMember (readings X) source) =
      ObservedFamilyEnclosure.valueMember (readings Y) (growingSource.map step source) :=
  profile.materialFace_valueMember step source

/-- Context extension preserves and reflects each old labelled transition,
and embeds its position observations into the larger context. -/
def restrictionCover {X Y : Stagesᵒᵖ} (step : X ⟶ Y) : SystemCover (system X) (system Y) where
  mapTerm := growingSource.map step
  mapAtom atom := atom.castLE (Nat.succ_le_succ (growthLe step))
  mapLabel := id
  mapEquiv := by
    intro left right same
    exact congrArg (growingSource.map step) same
  observes_iff atom state := by
    constructor
    · intro same
      exact congrArg (fun index => index.castLE (Nat.succ_le_succ (growthLe step))) same
    · intro same
      have indices : state.1.val = atom.val :=
        congrArg (fun position : Fin (stageIndex Y + 1) => position.val) same
      exact Fin.ext indices
  mapAct := by
    intro label source target step'
    exact congrArg (growingSource.map step) step'
  liftAct := by
    intro label source target' fires
    exact ⟨flip source, rfl, fires.symm⟩

/-- Full modal truth commutes with the material readout and the actual
context action, including negation. No image-finiteness is needed. -/
theorem material_modal_naturality {X Y : Stagesᵒᵖ} (step : X ⟶ Y)
    (formula : Formula (system X).Atom (system X).Label) (state : (theory X).Term) :
    (readings Y).materialSat
        (Formula.map (restrictionCover step).mapAtom (restrictionCover step).mapLabel formula)
        (profile.materialFace.map step (ObservedFamilyEnclosure.valueMember (readings X) state)).1 ↔
      (readings X).materialSat formula ((readings X).value state) := by
  rw [growing_material_naturality step state]
  exact ((readings Y).materialSat_value (faithful Y) _ _).trans
    (((restrictionCover step).sat_map formula state).trans
      ((readings X).materialSat_value (faithful X) formula state).symm)

def familyGraphs (point : profile.sourceFace.Elements) : AccessiblePointedGraph :=
  if point.2.1.val = 0 then empty else HSet.loop

def familyTransport : PowerClassPresheafDescent.MaterialTransport
    profile.sourceFace profile.classFace profile.observation familyGraphs where
  invariant X := by
    intro left right same
    have indices := (bisimilar_iff_position X left right).mp
      ((profile.observation_eq_iff X left right).mp same)
    exact congrArg (fun index => HSet.mk (if index.val = 0 then empty else HSet.loop)) indices
  map _ _ member := member
  map_id_value _ _ _ := rfl
  map_comp_value _ _ _ _ := rfl
  compatible _ := by intro _ _ _ _ _ same; exact same

def decodedFamilyAt (X : Stagesᵒᵖ) (source : (theory X).Term) : HSet :=
  PowerClassFamilyDescent.decodedFamily (fun value => familyGraphs ⟨X, value⟩)
    (PowerClassFamilyDescent.classOf (profile.observation.app X) source)

theorem decodedFamilyAt_beta (X : Stagesᵒᵖ) (source : (theory X).Term) :
    decodedFamilyAt X source = HSet.mk (familyGraphs ⟨X, source⟩) :=
  PowerClassFamilyDescent.family_beta _ _ (familyTransport.invariant X) source

theorem material_family_nonconstant :
    decodedFamilyAt (world 0) (stageValue 0 0 (by omega) false) ≠
      decodedFamilyAt (world 1) (stageValue 1 1 (by omega) true) := by
  rw [decodedFamilyAt_beta (world 0) (stageValue 0 0 (by omega) false),
    decodedFamilyAt_beta (world 1) (stageValue 1 1 (by omega) true)]
  change HSet.mk empty ≠ HSet.mk HSet.loop
  rw [HSet.mk_empty, HSet.mk_loop]
  exact HSet.empty_ne_quineAtom

theorem growing_material_new_position :
    ¬ ∃ source : (theory (world 0)).Term,
      profile.materialFace.map ((homOfLE (show 0 ≤ 1 by omega)).op.op)
          (ObservedFamilyEnclosure.valueMember (readings (world 0)) source) =
        ObservedFamilyEnclosure.valueMember (readings (world 1))
          (stageValue 1 1 (by omega) false) := by
  rintro ⟨source, same⟩
  have related := (profile.materialFace_source_kernel (world 1) _ _).mp
    ((profile.materialFace_valueMember _ source).symm.trans same)
  have indexEqual := congrArg Fin.val ((bisimilar_iff_position (world 1) _ _).mp related)
  have bound := source.1.isLt
  change source.1.val < 1 at bound
  change source.1.val = 1 at indexEqual
  omega

def grow : world 0 ⟶ world 1 := (homOfLE (show 0 ≤ 1 by omega)).op.op

def occurrences (X : Stagesᵒᵖ) : ActionOccurrences (system X) where
  Occurrence label source target := Bool × PLift ((system X).act label source target)
  erases _ _ _ :=
    ⟨fun ⟨receipt⟩ => receipt.2.down, fun fires => ⟨false, ⟨fires⟩⟩⟩

private theorem event_ext {X : Stagesᵒᵖ}
    {first second : ActionOccurrences.Event (occurrences X)}
    (source : first.source = second.source) (target : first.target = second.target)
    (provenance : first.occurrence.1 = second.occurrence.1) : first = second := by
  cases first with
  | mk label firstSource firstTarget firstOccurrence =>
    cases second with
    | mk label' secondSource secondTarget secondOccurrence =>
      cases label
      cases label'
      cases source
      cases target
      have receipts : firstOccurrence = secondOccurrence :=
        Prod.ext provenance (Subsingleton.elim _ _)
      cases receipts
      rfl

def restrictEvent {X Y : Stagesᵒᵖ} (step : X ⟶ Y)
    (event : ActionOccurrences.Event (occurrences X)) : ActionOccurrences.Event (occurrences Y) where
  label := ()
  source := growingSource.map step event.source
  target := growingSource.map step event.target
  occurrence := ⟨event.occurrence.1,
    ⟨congrArg (growingSource.map step) event.occurrence.2.down⟩⟩

def eventAction : Events.EventAction profile occurrences where
  restrict := restrictEvent
  source_comm _ _ := rfl
  target_comm _ _ := rfl
  restrict_id X event := by
    apply event_ext
    · exact growingSource.map_id_apply X event.source
    · exact growingSource.map_id_apply X event.target
    · rfl
  restrict_comp first second event := by
    apply event_ext
    · exact growingSource.map_comp_apply first second event.source
    · exact growingSource.map_comp_apply first second event.target
    · rfl

theorem restriction_preserves_provenance {X Y : Stagesᵒᵖ} (step : X ⟶ Y)
    (event : ActionOccurrences.Event (occurrences X)) :
    (restrictEvent step event).occurrence.1 = event.occurrence.1 := rfl

theorem restrictState_injective {X Y : Stagesᵒᵖ} (step : X ⟶ Y) :
    Function.Injective (growingSource.map step) := by
  intro first second same
  have phase : first.2 = second.2 := congrArg (fun state : growingSource.obj Y => state.2) same
  exact Prod.ext (Fin.ext (congrArg (fun state => state.1.val) same)) phase

theorem restrictEvent_injective {X Y : Stagesᵒᵖ} (step : X ⟶ Y) :
    Function.Injective (restrictEvent step) := by
  intro first second same
  exact event_ext (restrictState_injective step (congrArg ActionOccurrences.Event.source same))
    (restrictState_injective step (congrArg ActionOccurrences.Event.target same))
    (congrArg (fun event => event.occurrence.1) same)

/-- Every outgoing occurrence at an old position in the enlarged context
lifts with its authored provenance intact. -/
theorem restriction_sourceOccurrenceLifts {X Y : Stagesᵒᵖ} (step : X ⟶ Y) :
    (Events.sourceSpanMap profile occurrences eventAction step).SourceOccurrenceLifts := by
  intro state event source
  let lifted : ActionOccurrences.Event (occurrences X) :=
    ⟨(), state, flip state, event.occurrence.1, ⟨rfl⟩⟩
  refine ⟨lifted, rfl, event_ext source.symm ?_ rfl⟩
  exact (congrArg flip source).symm.trans event.occurrence.2.down.symm

theorem restriction_targetOccurrenceLifts {X Y : Stagesᵒᵖ} (step : X ⟶ Y) :
    (Events.sourceSpanMap profile occurrences eventAction step).TargetOccurrenceLifts := by
  intro state event target
  let lifted : ActionOccurrences.Event (occurrences X) :=
    ⟨(), flip state, state, event.occurrence.1, ⟨by
      change state = flip (flip state)
      exact Prod.ext rfl (Bool.not_not state.2).symm⟩⟩
  refine ⟨lifted, rfl, event_ext ?_ target.symm rfl⟩
  have source : flip event.target = event.source := by
    have fires : event.target = flip event.source := event.occurrence.2.down
    rw [fires]
    exact Prod.ext rfl (Bool.not_not event.source.2)
  exact (congrArg flip target).symm.trans source

/-- Outgoing material endpoints lift even when phase observation has
identified different authored source states. -/
theorem material_sourceLifts {X Y : Stagesᵒᵖ} (step : X ⟶ Y) :
    (Events.materialSpanMap profile occurrences eventAction step).SourceLifts := by
  intro member event source
  obtain ⟨raw, same⟩ := (ObservedFamilyEnclosure.mem_valueRange_iff (readings X) member.1).mp member.2
  have memberSame : member = ObservedFamilyEnclosure.valueMember (readings X) raw :=
    El.ext HSet.propositional same.symm
  have sourceSame := source.trans
    ((congrArg (profile.materialFace.map step) memberSame).trans (profile.materialFace_valueMember step raw))
  have indices := (bisimilar_iff_position Y _ _).mp
    ((profile.materialFace_source_kernel Y _ _).mp sourceSame)
  have fireIndices := congrArg (fun state : (theory Y).Term => state.1) event.occurrence.2.down
  let lifted : ActionOccurrences.Event (occurrences X) := ⟨(), raw, flip raw, event.occurrence.1, ⟨rfl⟩⟩
  refine ⟨lifted, memberSame.symm, ?_⟩
  exact (profile.materialFace_valueMember step (flip raw)).trans
    ((profile.materialFace_source_kernel Y _ _).mpr
      ((bisimilar_iff_position Y _ _).mpr
        (indices.symm.trans fireIndices.symm)))

theorem material_targetLifts {X Y : Stagesᵒᵖ} (step : X ⟶ Y) :
    (Events.materialSpanMap profile occurrences eventAction step).TargetLifts := by
  intro member event target
  obtain ⟨raw, same⟩ := (ObservedFamilyEnclosure.mem_valueRange_iff (readings X) member.1).mp member.2
  have memberSame : member = ObservedFamilyEnclosure.valueMember (readings X) raw :=
    El.ext HSet.propositional same.symm
  have targetSame := target.trans
    ((congrArg (profile.materialFace.map step) memberSame).trans (profile.materialFace_valueMember step raw))
  have indices := (bisimilar_iff_position Y _ _).mp
    ((profile.materialFace_source_kernel Y _ _).mp targetSame)
  have fireIndices := congrArg (fun state : (theory Y).Term => state.1) event.occurrence.2.down
  let lifted : ActionOccurrences.Event (occurrences X) :=
    ⟨(), flip raw, raw, event.occurrence.1, ⟨by
      change raw = flip (flip raw)
      exact Prod.ext rfl (Bool.not_not raw.2).symm⟩⟩
  refine ⟨lifted, memberSame.symm, ?_⟩
  exact (profile.materialFace_valueMember step (flip raw)).trans
    ((profile.materialFace_source_kernel Y _ _).mpr
      ((bisimilar_iff_position Y _ _).mpr
        (indices.symm.trans fireIndices)))

theorem material_diamond_naturality {X Y : Stagesᵒᵖ} (step : X ⟶ Y)
    (predicate : profile.materialFace.obj Y → Prop) (member : profile.materialFace.obj X) :
    Mettapedia.OSLF.Framework.DerivedModalities.derivedDiamond
      (ObservedFamilyEnclosure.Events.memberSpan (readings Y) (occurrences Y)) predicate
      (profile.materialFace.map step member) ↔
    Mettapedia.OSLF.Framework.DerivedModalities.derivedDiamond
      (ObservedFamilyEnclosure.Events.memberSpan (readings X) (occurrences X))
      (predicate ∘ profile.materialFace.map step) member :=
  (Events.materialSpanMap profile occurrences eventAction step).diamond_pullback (material_sourceLifts step) predicate member

theorem material_box_naturality {X Y : Stagesᵒᵖ} (step : X ⟶ Y)
    (predicate : profile.materialFace.obj Y → Prop) (member : profile.materialFace.obj X) :
    Mettapedia.OSLF.Framework.DerivedModalities.derivedBox
      (ObservedFamilyEnclosure.Events.memberSpan (readings Y) (occurrences Y)) predicate
      (profile.materialFace.map step member) ↔
    Mettapedia.OSLF.Framework.DerivedModalities.derivedBox
      (ObservedFamilyEnclosure.Events.memberSpan (readings X) (occurrences X))
      (predicate ∘ profile.materialFace.map step) member :=
  (Events.materialSpanMap profile occurrences eventAction step).box_pullback (material_targetLifts step) predicate member

/-- Context extension adds a cyclic alternative at every old position;
the initial context has only the empty alternative. -/
def nonWfChoices : AccessiblePointedGraph := sup (fun tag : Bool => if tag then HSet.loop else empty)

def positiveGraphs (point : profile.sourceFace.Elements) : AccessiblePointedGraph :=
  if stageIndex point.1 = 0 then OutcomeLabels.chainGraph 1 else nonWfChoices

def positiveTransport : PowerClassPresheafDescent.MaterialTransport
    profile.sourceFace profile.classFace profile.observation positiveGraphs where
  invariant _ := by intro _ _ _; rfl
  map {X Y} step _ member := ⟨member.1, by
    by_cases initialY : stageIndex Y = 0
    · have initialX : stageIndex X = 0 := by
        have below := growthLe step
        omega
      simpa only [positiveGraphs, initialX, initialY, if_pos] using member.2
    · simp only [positiveGraphs, initialY, if_false]
      by_cases initialX : stageIndex X = 0
      · have old : member.1 ∈ HSet.mk (OutcomeLabels.chainGraph 1) := by
          simpa only [positiveGraphs, initialX, if_pos] using member.2
        rw [OutcomeLabels.mk_chainGraph, OutcomeLabels.chainValue] at old
        rw [HSet.mem_singleton.mp old]
        exact HSet.mem_range.mpr ⟨false, HSet.mk_empty⟩
      · simpa only [positiveGraphs, initialX, if_false] using member.2⟩
  map_id_value _ _ _ := rfl
  map_comp_value _ _ _ _ := rfl
  compatible _ := by intro _ _ _ _ _ same; exact same

def positiveTerm (point : profile.sourceFace.Elements) : El (· ∈ ·) (HSet.mk (positiveGraphs point)) :=
  ⟨if point.2.1.val = 0 then ∅ else HSet.quineAtom, by
    by_cases initial : stageIndex point.1 = 0
    · have first : point.2.1.val = 0 := by
        have bound := point.2.1.isLt
        change point.2.1.val < stageIndex point.1 + 1 at bound
        omega
      simp only [positiveGraphs, initial, first, if_pos, OutcomeLabels.mk_chainGraph, OutcomeLabels.chainValue]
      exact HSet.mem_singleton_self ∅
    · simp only [positiveGraphs, initial, if_false]
      by_cases first : point.2.1.val = 0
      · simp only [first, if_pos]
        exact HSet.mem_range.mpr ⟨false, HSet.mk_empty⟩
      · simp only [first, if_false]
        exact HSet.mem_range.mpr ⟨true, HSet.mk_loop⟩⟩

theorem positiveTerm_compatible : PowerClassPresheafDescent.ContextualCompatible
    profile.sourceFace profile.classFace profile.observation positiveGraphs positiveTransport positiveTerm := by
  constructor
  · intro X left right same
    have indices := (bisimilar_iff_position X left right).mp
      ((profile.observation_eq_iff X left right).mp same)
    exact congrArg (fun index => if index.val = 0 then (∅ : HSet) else HSet.quineAtom) indices
  · intro X Y step source
    rfl

theorem positiveTerm_values_differ :
    (positiveTerm ⟨world 0, stageValue 0 0 (by omega) false⟩).1 ≠
      (positiveTerm ⟨world 1, stageValue 1 1 (by omega) true⟩).1 :=
  HSet.empty_ne_quineAtom

theorem positive_fibres_differ :
    HSet.mk (positiveGraphs ⟨world 0, stageValue 0 0 (by omega) false⟩) ≠
      HSet.mk (positiveGraphs ⟨world 1, stageValue 1 1 (by omega) true⟩) := by
  intro same
  have cyclicMember : HSet.quineAtom ∈ HSet.mk (positiveGraphs
      ⟨world 1, stageValue 1 1 (by omega) true⟩) := HSet.mem_range.mpr ⟨true, HSet.mk_loop⟩
  have member : HSet.quineAtom ∈ HSet.mk (OutcomeLabels.chainGraph 1) := same.symm ▸ cyclicMember
  rw [OutcomeLabels.mk_chainGraph, OutcomeLabels.chainValue] at member
  exact HSet.empty_ne_quineAtom (HSet.mem_singleton.mp member).symm

/-- The existing full contextual Pi is inhabited in this varying model;
its application recovers the authored nonconstant material section. -/
theorem varying_contextual_pi_beta :
    PowerClassPresheafDescent.pullContextualSection
      profile.sourceFace profile.classFace profile.observation positiveGraphs positiveTransport
      (PowerClassPresheafDescent.contextualIdentityApplication
        profile.sourceFace profile.classFace profile.observation positiveGraphs positiveTransport
        (PowerClassPresheafDescent.descendContextualSection
          profile.sourceFace profile.classFace profile.observation positiveGraphs positiveTransport
          positiveTerm positiveTerm_compatible)) = positiveTerm :=
  PowerClassPresheafDescent.contextualIdentity_source_beta _ _ _ _ _ positiveTerm positiveTerm_compatible

namespace FutureArguments

open PowerClassPresheafProducts

def emptyTerm (point : profile.sourceFace.Elements) : El (· ∈ ·) (HSet.mk (positiveGraphs point)) :=
  ⟨∅, by
    by_cases initial : stageIndex point.1 = 0
    · simp only [positiveGraphs, initial, if_pos, OutcomeLabels.mk_chainGraph, OutcomeLabels.chainValue]
      exact HSet.mem_singleton_self ∅
    · simp only [positiveGraphs, initial, if_false]
      exact HSet.mem_range.mpr ⟨false, HSet.mk_empty⟩⟩

theorem emptyTerm_compatible : PowerClassPresheafDescent.ContextualCompatible
    profile.sourceFace profile.classFace profile.observation positiveGraphs positiveTransport emptyTerm := by
  constructor
  · intro _ _ _ _
    rfl
  · intro _ _ _ _
    rfl

abbrev displayed := ConstructiveFamilies.domain profile positiveGraphs positiveTransport
abbrev base := Families.observedBase profile

def oldRaw : profile.sourceFace.Elements := ⟨world 0, stageValue 0 0 (by omega) false⟩
def laterRaw : profile.sourceFace.Elements := ⟨world 1, profile.restrict grow oldRaw.2⟩
def old : base.Elements :=
  (PowerClassPresheafDescent.classElements profile.sourceFace profile.classFace profile.observation).obj oldRaw
def later : base.Elements :=
  (PowerClassPresheafDescent.classElements profile.sourceFace profile.classFace profile.observation).obj laterRaw

def futureArrow : old ⟶ later :=
  (PowerClassPresheafDescent.classElements profile.sourceFace profile.classFace profile.observation).map
    (CategoryOfElements.homMk oldRaw laterRaw grow rfl)

def laterQuine : El (· ∈ ·) (HSet.mk (positiveGraphs laterRaw)) :=
  ⟨HSet.quineAtom, HSet.mem_range.mpr ⟨true, HSet.mk_loop⟩⟩

def futureArgument : displayed.obj later :=
  PowerClassPresheafDescent.sourceFibreEquiv profile.sourceFace profile.classFace profile.observation
    positiveGraphs positiveTransport laterRaw
      ((PowerClassPresheafDescent.sourceMaterialMemberEquiv profile.sourceFace positiveGraphs laterRaw).symm laterQuine)

def valueAt (point : base.Elements) (member : displayed.obj point) : HSet :=
  (PowerClassPresheafDescent.contextualMemberEquiv
    profile.sourceFace profile.classFace profile.observation positiveGraphs point member).1

theorem futureArgument_value : valueAt later futureArgument = HSet.quineAtom := by
  exact (PowerClassPresheafDescent.sourceFibreEquiv_value
    profile.sourceFace profile.classFace profile.observation positiveGraphs positiveTransport laterRaw
      ((PowerClassPresheafDescent.sourceMaterialMemberEquiv profile.sourceFace positiveGraphs laterRaw).symm laterQuine)).trans
        (congrArg PSigma.fst
          ((PowerClassPresheafDescent.sourceMaterialMemberEquiv profile.sourceFace positiveGraphs laterRaw).apply_symm_apply laterQuine))

theorem currentArgument_value (argument : displayed.obj old) : valueAt old argument = ∅ := by
  have member := (PowerClassPresheafDescent.contextualMemberEquiv
    profile.sourceFace profile.classFace profile.observation positiveGraphs old argument).2
  have family := PowerClassFamilyDescent.family_beta (profile.observation.app (world 0))
    (fun value => positiveGraphs ⟨world 0, value⟩) (positiveTransport.invariant (world 0)) oldRaw.2
  have original : valueAt old argument ∈ HSet.mk (OutcomeLabels.chainGraph 1) := family ▸ member
  rw [OutcomeLabels.mk_chainGraph, OutcomeLabels.chainValue] at original
  exact HSet.mem_singleton.mp original

abbrev emptyDisplayed := Families.descendedArgument
  profile positiveGraphs positiveTransport emptyTerm emptyTerm_compatible
abbrev identity := ConstructiveFamilies.identityFunction profile positiveGraphs positiveTransport
abbrev constantEmpty := ConstructiveFamilies.constantFunction
  profile positiveGraphs positiveTransport emptyDisplayed

theorem emptyDisplayed_value (point : profile.sourceFace.Elements) :
    valueAt ((PowerClassPresheafDescent.classElements
      profile.sourceFace profile.classFace profile.observation).obj point)
      (emptyDisplayed.val ((PowerClassPresheafDescent.classElements
        profile.sourceFace profile.classFace profile.observation).obj point)) = ∅ :=
  Families.descendedArgument_value profile positiveGraphs positiveTransport emptyTerm emptyTerm_compatible point

/-- The two functions agree on every material argument available in the
current fibre. The future family still retains their difference. -/
theorem current_applications_agree (argument : displayed.obj old) :
    (identity.val old).app old (𝟙 old) argument = (constantEmpty.val old).app old (𝟙 old) argument := by
  apply (PowerClassPresheafDescent.contextualMemberEquiv
    profile.sourceFace profile.classFace profile.observation positiveGraphs old).injective
  apply El.ext HSet.propositional
  have first := congrArg (valueAt old)
    (ConstructiveFamilies.identityFunction_future profile positiveGraphs positiveTransport old old (𝟙 old) argument)
  have second := congrArg (valueAt old)
    (ConstructiveFamilies.constantFunction_future profile positiveGraphs positiveTransport
      emptyDisplayed old old (𝟙 old) argument)
  exact (first.trans (currentArgument_value argument)).trans
    (second.trans (emptyDisplayed_value oldRaw)).symm

theorem future_applications_differ :
    valueAt later ((identity.val old).app later futureArrow futureArgument) ≠
      valueAt later ((constantEmpty.val old).app later futureArrow futureArgument) := by
  intro same
  have first := (congrArg (valueAt later)
    (ConstructiveFamilies.identityFunction_future profile positiveGraphs positiveTransport
      old later futureArrow futureArgument)).trans futureArgument_value
  have second := (congrArg (valueAt later)
    (ConstructiveFamilies.constantFunction_future profile positiveGraphs positiveTransport
      emptyDisplayed old later futureArrow futureArgument)).trans (emptyDisplayed_value laterRaw)
  exact HSet.empty_ne_quineAtom (second.symm.trans (same.symm.trans first))

theorem function_components_differ : identity.val old ≠ constantEmpty.val old := by
  intro same
  exact future_applications_differ (congrArg (fun function =>
    valueAt later (function.app later futureArrow futureArgument)) same)

/-- Evaluating only the present fibre loses genuine contextual functions,
even over an inhabited material family and an old observed base point. -/
theorem current_evaluation_not_injective :
    ¬ Function.Injective (fun function : (piFamily displayed (reindex (projection displayed) displayed)).obj old =>
      fun argument : displayed.obj old => function.app old (𝟙 old) argument) := by
  intro injective
  exact function_components_differ (injective (funext current_applications_agree))

end FutureArguments

def alternativeGraphs (_point : profile.sourceFace.Elements) : AccessiblePointedGraph :=
  PowerClassFamilyDescent.Controls.alternatives

def alternativeTransport : PowerClassPresheafDescent.MaterialTransport
    profile.sourceFace profile.classFace profile.observation alternativeGraphs where
  invariant _ := by intro _ _ _; rfl
  map _ _ member := member
  map_id_value _ _ _ := rfl
  map_comp_value _ _ _ _ := rfl
  compatible _ := by intro _ _ _ _ _ same; exact same

def phaseTerm (point : profile.sourceFace.Elements) : El (· ∈ ·) (HSet.mk (alternativeGraphs point)) :=
  ⟨HSet.mk (PowerClassFamilyDescent.Controls.selectedGraph point.2.2),
    HSet.mem_range.mpr ⟨⟨point.2.2⟩, rfl⟩⟩

theorem phaseTerm_natural {X Y : Stagesᵒᵖ} (step : X ⟶ Y) (state : (theory X).Term) :
    (alternativeTransport.map step state (phaseTerm ⟨X, state⟩)).1 =
      (phaseTerm ⟨Y, growingSource.map step state⟩).1 := rfl

theorem alternatives_support_descends (X : Stagesᵒᵖ) (left right : (theory X).Term) :
    Nonempty (El (· ∈ ·) (HSet.mk (alternativeGraphs ⟨X, left⟩))) ↔
      Nonempty (El (· ∈ ·) (HSet.mk (alternativeGraphs ⟨X, right⟩))) :=
  ⟨fun _ => ⟨phaseTerm ⟨X, right⟩⟩, fun _ => ⟨phaseTerm ⟨X, left⟩⟩⟩

private theorem phase_true (X : Stagesᵒᵖ) (position : Fin (stageIndex X + 1)) :
    (phaseTerm ⟨X, (position, true)⟩).1 = ({∅} : HSet) :=
  (picture_eq_mk _).symm.trans picture_oneChild_empty

private theorem phase_false (X : Stagesᵒᵖ) (position : Fin (stageIndex X + 1)) :
    (phaseTerm ⟨X, (position, false)⟩).1 = (∅ : HSet) := HSet.mk_empty

/-- The section is natural on raw contexts but distinguishes two phases
that the declared observer identifies. -/
theorem phaseTerm_not_compatible : ¬ PowerClassPresheafDescent.ContextualCompatible
    profile.sourceFace profile.classFace profile.observation alternativeGraphs alternativeTransport phaseTerm := by
  intro compatible
  let left := stageValue 0 0 (by omega) true
  let right := stageValue 0 0 (by omega) false
  have related := (bisimilar_iff_position (world 0) left right).mpr rfl
  have same := compatible.1 (world 0)
    ((profile.observation_eq_iff (world 0) left right).mpr related)
  exact HSet.empty_ne_singleton_empty ((phase_false (world 0) right.1).symm.trans
    (same.symm.trans (phase_true (world 0) left.1)))

theorem phaseTerm_no_observed_section :
    ¬ ∃ term : (Families.displayed profile alternativeGraphs alternativeTransport).sections,
      PowerClassPresheafDescent.pullContextualSection profile.sourceFace profile.classFace
        profile.observation alternativeGraphs alternativeTransport term = phaseTerm := by
  rintro ⟨term, same⟩
  have compatible := PowerClassPresheafDescent.pullContextualSection_compatible
    profile.sourceFace profile.classFace profile.observation alternativeGraphs alternativeTransport term
  rw [same] at compatible
  exact phaseTerm_not_compatible compatible

/-- One authored operation reads the retained phase, even though the
family's support and base observation ignore it. -/
def phaseOperation (state : (theory (world 0)).Term)
    (_member : El (· ∈ ·) (HSet.mk (alternativeGraphs ⟨world 0, state⟩))) :
    El (· ∈ ·) (HSet.mk (alternativeGraphs ⟨world 1, profile.restrict grow state⟩)) :=
  phaseTerm ⟨world 1, profile.restrict grow state⟩

theorem phaseOperation_not_compatible :
    ¬ PowerClassPresheafDescent.MapCompatible (profile.observation.app (world 0))
      (fun state => alternativeGraphs ⟨world 0, state⟩) (profile.restrict grow)
      (fun state => alternativeGraphs ⟨world 1, state⟩) phaseOperation := by
  intro compatible
  let left := stageValue 0 0 (by omega) true
  let right := stageValue 0 0 (by omega) false
  let leftMember : El (· ∈ ·) (HSet.mk (alternativeGraphs ⟨world 0, left⟩)) :=
    ⟨HSet.mk empty, HSet.mem_range.mpr ⟨⟨false⟩, rfl⟩⟩
  let rightMember : El (· ∈ ·) (HSet.mk (alternativeGraphs ⟨world 0, right⟩)) :=
    ⟨HSet.mk empty, HSet.mem_range.mpr ⟨⟨false⟩, rfl⟩⟩
  have related := (bisimilar_iff_position (world 0) left right).mpr rfl
  have same := compatible ((profile.observation_eq_iff (world 0) left right).mpr related)
    leftMember rightMember rfl
  exact HSet.empty_ne_singleton_empty
    ((phase_false (world 1) (profile.restrict grow right).1).symm.trans
      (same.symm.trans (phase_true (world 1) (profile.restrict grow left).1)))

theorem phaseOperation_no_material_map :
    ¬ ∃ descended : ∀ observed : PowerClassFamilyDescent.ObservationClass
        (profile.observation.app (world 0)),
      El (· ∈ ·) (PowerClassFamilyDescent.decodedFamily
        (fun state => alternativeGraphs ⟨world 0, state⟩) observed) →
      El (· ∈ ·) (PowerClassFamilyDescent.decodedFamily
        (fun state => alternativeGraphs ⟨world 1, state⟩)
        (PowerClassFamilyDescent.classMap (profile.observation.app (world 1))
          (profile.observation.app (world 0)) (profile.restrict grow) (profile.classFace.map grow)
          (PowerClassPresheafDescent.observationSquare profile.sourceFace profile.classFace profile.observation grow)
          observed)),
      ∀ state member,
        (descended (PowerClassFamilyDescent.classOf (profile.observation.app (world 0)) state)
          ((PowerClassFamilyDescent.familyFactorization (profile.observation.app (world 0))
            (fun state => alternativeGraphs ⟨world 0, state⟩)
            (alternativeTransport.invariant (world 0))).identify state member)).1 =
          (phaseOperation state member).1 := by
  intro factorization
  exact phaseOperation_not_compatible
    ((PowerClassPresheafDescent.mapCompatible_iff_exists_map
      (profile.observation.app (world 0)) (profile.observation.app (world 1))
      (profile.restrict grow) (profile.classFace.map grow)
      (PowerClassPresheafDescent.observationSquare profile.sourceFace profile.classFace profile.observation grow)
      (fun state => alternativeGraphs ⟨world 0, state⟩) (alternativeTransport.invariant (world 0))
      (fun state => alternativeGraphs ⟨world 1, state⟩) (alternativeTransport.invariant (world 1))
      phaseOperation).mpr factorization)

end GrowthControls

end Mettapedia.GSLT.ContextualObservedFamilyEnclosure
