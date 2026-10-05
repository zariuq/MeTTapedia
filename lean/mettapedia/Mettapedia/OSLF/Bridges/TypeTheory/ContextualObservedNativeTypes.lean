import Mettapedia.OSLF.Bridges.TypeTheory.ObservedNativeTypes
import Mettapedia.OSLF.Bridges.TypeTheory.DependentNativeTypes
import Mettapedia.GSLT.Logic.ContextualObservedFamilyEnclosure
import Mettapedia.GSLT.Topos.SubobjectClassifier

/-!
# Native classifiers for the observed contextual material model

These are the actual native predicate subfunctors of the contextual source,
observed class and material member presheaves. Their images are constructed
from source witnesses and the authored natural readout square. A source
classifier factors through that observation exactly when every contextual
fibre is constant on observed bisimilarity.

The sieve classifier retains restriction information, including arrows along
which a predicate first holds. Comprehension image is compared with w12's
native image/support construction. This predicate-level comparison does not
recover a selected section from inhabited fibres.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Bridges.TypeTheory.ContextualObservedNativeTypes

open _root_.CategoryTheory Opposite
open Mettapedia.GSLT Mettapedia.GSLT.HennessyMilner
open Mettapedia.GSLT.ContextualObservedFamilyEnclosure
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.MaterialSets
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open Mettapedia.GSLT.Topos.ConstructivePresheaf
open scoped Mettapedia.GSLT.Topos.ConstructivePresheaf

universe u
variable {C : Type u} [Category.{u} C]
variable (profile : ContextualSystem C)

/-- Existential native image on the actual observed-class presheaf. -/
def observedImage (predicate : Subfunctor profile.sourceFace) : Subfunctor profile.classFace where
  obj X := {observed | ∃ source, source ∈ predicate.obj X ∧ profile.observation.app X source = observed}
  map {X Y} step := by
    rintro observed ⟨source, holds, rfl⟩
    refine ⟨profile.sourceFace.map step source, predicate.map step holds, ?_⟩
    exact congrArg (fun map => map source) (profile.observation.naturality step)

/-- The same source image lands in actual material members, with all maps
derived from the authored material readout naturality theorem. -/
def materialImage (predicate : Subfunctor profile.sourceFace) : Subfunctor profile.materialFace where
  obj X := {member | ∃ source, source ∈ predicate.obj X ∧
    ObservedFamilyEnclosure.valueMember (profile.readings X) source = member}
  map {X Y} step := by
    rintro member ⟨source, holds, rfl⟩
    exact ⟨profile.sourceFace.map step source, predicate.map step holds,
      (profile.materialFace_valueMember step source).symm⟩

def liftPredicate (predicate : Subfunctor profile.sourceFace) : Subfunctor profile.liftedSourceFace where
  obj X := {source | source.down ∈ predicate.obj X}
  map step := by
    intro source holds
    exact predicate.map step holds

theorem observedImage_at (predicate : Subfunctor profile.sourceFace) (X : Cᵒᵖ)
    (source : profile.sourceFace.obj X) :
    profile.observation.app X source ∈ (observedImage profile predicate).obj X ↔
      ∃ other, other ∈ predicate.obj X ∧ (profile.system X).Bisimilar other source :=
  exists_congr fun other => and_congr Iff.rfl (profile.observation_eq_iff X other source)

theorem materialImage_at (predicate : Subfunctor profile.sourceFace) (X : Cᵒᵖ)
    (source : profile.sourceFace.obj X) :
    ObservedFamilyEnclosure.valueMember (profile.readings X) source ∈ (materialImage profile predicate).obj X ↔
      ∃ other, other ∈ predicate.obj X ∧ (profile.system X).Bisimilar other source :=
  exists_congr fun other => and_congr Iff.rfl (profile.materialFace_source_kernel X other source)

theorem observedImage_exact_iff (predicate : Subfunctor profile.sourceFace) :
    preimage profile.observation (observedImage profile predicate) = predicate ↔
      ∀ X left right, (profile.system X).Bisimilar left right →
        (left ∈ predicate.obj X ↔ right ∈ predicate.obj X) := by
  constructor
  · intro exactImage X left right related
    have reflects (source : profile.sourceFace.obj X) :
        profile.observation.app X source ∈ (observedImage profile predicate).obj X ↔ source ∈ predicate.obj X := by
      change source ∈ (preimage profile.observation (observedImage profile predicate)).obj X ↔ _
      rw [exactImage]
    constructor
    · intro holds
      exact (reflects right).mp ((observedImage_at profile predicate X right).mpr ⟨left, holds, related⟩)
    · intro holds
      exact (reflects left).mp ((observedImage_at profile predicate X left).mpr
        ⟨right, holds, (profile.system X).bisimilar_symm related⟩)
  · intro invariant
    ext X source
    exact (observedImage_at profile predicate X source).trans
      ⟨fun ⟨other, holds, related⟩ => (invariant X other source related).mp holds,
        fun holds => ⟨source, holds, (profile.system X).bisimilar_refl source⟩⟩

theorem materialImage_exact_iff (predicate : Subfunctor profile.sourceFace) :
    preimage profile.materialReadout (materialImage profile predicate) = liftPredicate profile predicate ↔
      ∀ X left right, (profile.system X).Bisimilar left right →
        (left ∈ predicate.obj X ↔ right ∈ predicate.obj X) := by
  constructor
  · intro exactImage X left right related
    have reflects (source : profile.sourceFace.obj X) :
        ObservedFamilyEnclosure.valueMember (profile.readings X) source ∈ (materialImage profile predicate).obj X ↔
          source ∈ predicate.obj X := by
      change (ULift.up source : profile.liftedSourceFace.obj X) ∈
        (preimage profile.materialReadout (materialImage profile predicate)).obj X ↔ _
      rw [exactImage]
      rfl
    constructor
    · intro holds
      exact (reflects right).mp ((materialImage_at profile predicate X right).mpr ⟨left, holds, related⟩)
    · intro holds
      exact (reflects left).mp ((materialImage_at profile predicate X left).mpr
        ⟨right, holds, (profile.system X).bisimilar_symm related⟩)
  · intro invariant
    ext X source
    exact (materialImage_at profile predicate X source.down).trans
      ⟨fun ⟨other, holds, related⟩ => (invariant X other source.down related).mp holds,
        fun holds => ⟨source.down, holds, (profile.system X).bisimilar_refl source.down⟩⟩

namespace Classifier

variable {P Q : Cᵒᵖ ⥤ Type u}

/-- The established presheaf Ω, with the characteristic map written as an
explicit natural transformation so its construction chooses no witnesses. -/
def characteristic (predicate : Subfunctor P) : NatTrans P (Mettapedia.GSLT.Topos.omegaFunctor (C := C)) where
  app X := TypeCat.ofHom fun source => predicate.sieveOfSection source
  naturality X Y step := by
    apply ConcreteCategory.hom_ext
    intro source
    change predicate.sieveOfSection (P.map step source) =
      Mettapedia.GSLT.Topos.sievePullback step.unop (predicate.sieveOfSection source)
    apply Sieve.ext
    intro Z arrow
    simp [Mettapedia.GSLT.Topos.sievePullback, Subfunctor.sieveOfSection_apply]

theorem characteristic_truth (predicate : Subfunctor P) (X : Cᵒᵖ) (source : P.obj X) :
    ((characteristic predicate).app X source).arrows (𝟙 X.unop) ↔ source ∈ predicate.obj X := by
  change P.map (𝟙 X) source ∈ predicate.obj X ↔ _
  rw [P.map_id_apply]

theorem characteristic_injective : Function.Injective (characteristic (P := P)) := by
  intro first second same
  ext X source
  have sieves := congrArg (fun classifier => classifier.app X source) same
  have truths := congrArg (fun sieve : Sieve X.unop => sieve.arrows (𝟙 X.unop)) sieves
  exact (characteristic_truth first X source).symm.trans
    ((Iff.of_eq truths).trans (characteristic_truth second X source))

theorem characteristic_reindex (change : NatTrans Q P) (predicate : Subfunctor P)
    (X : Cᵒᵖ) (source : Q.obj X) :
    (characteristic (preimage change predicate)).app X source =
      (characteristic predicate).app X (change.app X source) := by
  apply Sieve.ext
  intro Y arrow
  change change.app (op Y) (Q.map arrow.op source) ∈ predicate.obj (op Y) ↔
    P.map arrow.op (change.app X source) ∈ predicate.obj (op Y)
  have natural := congrArg (fun map => map source) (change.naturality arrow.op)
  change change.app (op Y) (Q.map arrow.op source) = P.map arrow.op (change.app X source) at natural
  rw [natural]

/-- A classifier supplies a predicate by truth at the identity arrow.
Its stability is derived from the actual naturality square and sieve
closure, without selecting source witnesses. -/
def decode (classifier : NatTrans P (Mettapedia.GSLT.Topos.omegaFunctor (C := C))) : Subfunctor P where
  obj X := {source | (classifier.app X source).arrows (𝟙 X.unop)}
  map {X Y} step := by
    intro source holds
    have natural : classifier.app Y (P.map step source) =
        Mettapedia.GSLT.Topos.sievePullback step.unop (classifier.app X source) :=
      congrArg (fun map => map source) (classifier.naturality step)
    change (classifier.app Y (P.map step source)).arrows (𝟙 Y.unop)
    rw [natural]
    change (classifier.app X source).arrows ((𝟙 Y.unop) ≫ step.unop)
    rw [Category.id_comp]
    simpa only [Category.comp_id] using (classifier.app X source).downward_closed holds step.unop

theorem decode_characteristic (predicate : Subfunctor P) : decode (characteristic predicate) = predicate := by
  ext X source
  exact characteristic_truth predicate X source

theorem characteristic_decode
    (classifier : NatTrans P (Mettapedia.GSLT.Topos.omegaFunctor (C := C))) :
    characteristic (decode classifier) = classifier := by
  ext X source
  apply Sieve.ext
  intro Z arrow
  change (classifier.app (op Z) (P.map arrow.op source)).arrows (𝟙 Z) ↔
    (classifier.app X source).arrows arrow
  have natural : classifier.app (op Z) (P.map arrow.op source) =
      Mettapedia.GSLT.Topos.sievePullback arrow (classifier.app X source) :=
    congrArg (fun map => map source) (classifier.naturality arrow.op)
  rw [natural]
  change (classifier.app X source).arrows ((𝟙 Z) ≫ arrow) ↔ _
  rw [Category.id_comp]

/-- The entire existing native Ω classifies the actual subfunctors, not
only the particular images used in the descent comparison. -/
def classifierEquiv : Subfunctor P ≃ NatTrans P (Mettapedia.GSLT.Topos.omegaFunctor (C := C)) where
  toFun := characteristic
  invFun := decode
  left_inv := decode_characteristic
  right_inv := characteristic_decode

theorem decode_reindex (change : NatTrans Q P)
    (classifier : NatTrans P (Mettapedia.GSLT.Topos.omegaFunctor (C := C))) :
    decode (Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.compose change classifier) =
      preimage change (decode classifier) := by
  ext X source
  rfl

theorem preimage_eq_native {P Q : Cᵒᵖ ⥤ Type u}
    (change : NatTrans Q P) (predicate : Subfunctor P) :
    preimage change predicate = predicate.preimage change := by
  ext X source
  rfl

end Classifier

/-- A native source classifier factors through the actual observed state
presheaf exactly when it cannot distinguish bisimilar source values. -/
theorem classifier_factors_iff (predicate : Subfunctor profile.sourceFace) :
    (∃ classifier : NatTrans profile.classFace (Mettapedia.GSLT.Topos.omegaFunctor (C := C)),
      ∀ X source, classifier.app X (profile.observation.app X source) =
        (Classifier.characteristic predicate).app X source) ↔
      ∀ X left right, (profile.system X).Bisimilar left right →
        (left ∈ predicate.obj X ↔ right ∈ predicate.obj X) := by
  constructor
  · rintro ⟨classifier, factors⟩ X left right related
    have same := (profile.observation_eq_iff X left right).mpr related
    have sieves := (factors X left).symm.trans
      ((congrArg (classifier.app X) same).trans (factors X right))
    have truths := congrArg (fun sieve : Sieve X.unop => sieve.arrows (𝟙 X.unop)) sieves
    exact (Classifier.characteristic_truth predicate X left).symm.trans
      ((Iff.of_eq truths).trans (Classifier.characteristic_truth predicate X right))
  · intro invariant
    refine ⟨Classifier.characteristic (observedImage profile predicate), ?_⟩
    intro X source
    have exactImage := (observedImage_exact_iff profile predicate).mpr invariant
    have reindexes := Classifier.characteristic_reindex profile.observation (observedImage profile predicate) X source
    rw [exactImage] at reindexes
    exact reindexes.symm

namespace Families

open Mettapedia.GSLT.Topos
open Mettapedia.TypeTheory.DisplayedPresheafTransport
open Mettapedia.TypeTheory.DisplayedPresheafComprehension

variable (graphs : profile.sourceFace.Elements → AccessiblePointedGraph.{u})
variable (transport : PowerClassPresheafDescent.MaterialTransport
  profile.sourceFace profile.classFace profile.observation graphs)

/-- The actual class readout is an explicit natural transformation; this
avoids the legacy abbreviation's functor-category identity proofs. -/
def familyReadout : NatTrans profile.sourceFace
    (PowerClassPresheafDescent.classFace profile.sourceFace profile.classFace profile.observation) :=
  PowerClassPresheafDescent.classObservation profile.sourceFace profile.classFace profile.observation

/-- The actual comprehension projection retains every member while its
image records precisely inhabitation of the contextual material family. -/
theorem image_eq_support (family : DisplayedFamily.{u, u, u, u} profile.sourceFace) :
    image (PowerClassPresheafProducts.projection family) ⊤ = support family := by
  ext X source
  constructor
  · rintro ⟨⟨other, evidence⟩, _, same⟩
    change other = source at same
    subst source
    exact ⟨evidence⟩
  · rintro ⟨evidence⟩
    exact ⟨⟨source, evidence⟩, trivial, rfl⟩

/-- This is the native image-comprehension endpoint of w12, on the actual
observed family. Categorical host infrastructure remains separate from
the explicit constructive maps used above. -/
theorem native_image_eq_observed_support :
    objectPredicate (ImageComprehension.imageFunctor.obj
      (Arrow.mk (PowerClassPresheafProducts.projection
        (Mettapedia.GSLT.ContextualObservedFamilyEnclosure.Families.displayed profile graphs transport)))) =
      support (Mettapedia.GSLT.ContextualObservedFamilyEnclosure.Families.displayed profile graphs transport) := by
  change Subfunctor.range (PowerClassPresheafProducts.projection
    (Mettapedia.GSLT.ContextualObservedFamilyEnclosure.Families.displayed profile graphs transport)) = _
  ext X source
  constructor
  · rintro ⟨⟨other, evidence⟩, same⟩
    change other = source at same
    subst source
    exact ⟨evidence⟩
  · rintro ⟨evidence⟩
    exact ⟨⟨source, evidence⟩, rfl⟩

theorem support_reindex {P Q : Cᵒᵖ ⥤ Type u} (change : NatTrans Q P)
    (family : DisplayedFamily.{u, u, u, u} P) :
    support (PowerClassPresheafProducts.reindex change family) = preimage change (support family) := by
  ext X source
  rfl

/-- The selected section is a stronger datum than the native image. This
comparison uses the actual small-member equivalence in each source fibre. -/
theorem source_observed_support :
    support (PowerClassPresheafDescent.nativeSourceDisplayed profile.sourceFace profile.classFace
      profile.observation graphs transport) =
        preimage (familyReadout profile)
          (support (Mettapedia.GSLT.ContextualObservedFamilyEnclosure.Families.displayed profile graphs transport)) := by
  ext X source
  change Nonempty _ ↔ Nonempty _
  exact (PowerClassPresheafDescent.sourceFibreEquiv profile.sourceFace profile.classFace
    profile.observation graphs transport ⟨X, source⟩).nonempty_congr

theorem source_support_kernel (X : Cᵒᵖ) (left right : profile.sourceFace.obj X)
    (related : (profile.system X).Bisimilar left right) :
    (left ∈ (support (PowerClassPresheafDescent.nativeSourceDisplayed profile.sourceFace profile.classFace
      profile.observation graphs transport)).obj X ↔
     right ∈ (support (PowerClassPresheafDescent.nativeSourceDisplayed profile.sourceFace profile.classFace
      profile.observation graphs transport)).obj X) := by
  rw [source_observed_support profile graphs transport]
  change PowerClassFamilyDescent.classOf (profile.observation.app X) left ∈
      (support (Mettapedia.GSLT.ContextualObservedFamilyEnclosure.Families.displayed profile graphs transport)).obj X ↔
    PowerClassFamilyDescent.classOf (profile.observation.app X) right ∈
      (support (Mettapedia.GSLT.ContextualObservedFamilyEnclosure.Families.displayed profile graphs transport)).obj X
  have same := (PowerClassFamilyDescent.classOf_eq_iff (profile.observation.app X) left right).mpr
    ((profile.observation_eq_iff X left right).mpr related)
  exact same ▸ Iff.rfl

/-- The classifier of the actual dependent source comprehension image has
a constructed factor through the observed presheaf. -/
theorem source_family_classifier_factors :
    ∃ classifier : NatTrans profile.classFace (Mettapedia.GSLT.Topos.omegaFunctor (C := C)),
      ∀ X source, classifier.app X (profile.observation.app X source) =
        (Classifier.characteristic (support (PowerClassPresheafDescent.nativeSourceDisplayed
          profile.sourceFace profile.classFace profile.observation graphs transport))).app X source :=
  (classifier_factors_iff profile _).mpr (source_support_kernel profile graphs transport)

theorem source_family_material_image_exact :
    preimage profile.materialReadout (materialImage profile (support (PowerClassPresheafDescent.nativeSourceDisplayed
      profile.sourceFace profile.classFace profile.observation graphs transport))) =
        liftPredicate profile (support (PowerClassPresheafDescent.nativeSourceDisplayed
          profile.sourceFace profile.classFace profile.observation graphs transport)) :=
  (materialImage_exact_iff profile _).mpr (source_support_kernel profile graphs transport)

end Families

namespace Modal

open Mettapedia.GSLT.Topos.ConstructivePresheaf
open Mettapedia.GSLT.Topos.PresheafEventModalities
open Mettapedia.GSLT.ObservationSpans.Presheaf

variable (occurrences : ∀ X, ObservedMaterialization.ActionOccurrences (profile.system X))
variable (action : Events.EventAction profile occurrences)

/-- The actual authored event presheaf, with its original endpoints. -/
def sourceGraph : EventGraph.{u, u, u} Cᵒᵖ where
  vertex := profile.sourceFace
  edge := Events.occurrenceFace profile occurrences action
  source := Events.source profile occurrences action
  target := Events.target profile occurrences action

/-- Only endpoint states are observed; the complete authored event presheaf
and its context action are retained. -/
def observedGraph : EventGraph.{u, u, u} Cᵒᵖ where
  vertex := profile.classFace
  edge := Events.occurrenceFace profile occurrences action
  source := Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.compose
    (Events.source profile occurrences action) profile.observation
  target := Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.compose
    (Events.target profile occurrences action) profile.observation

def observation : EventObservation (sourceGraph profile occurrences action) (observedGraph profile occurrences action) where
  states := profile.observation
  events := Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.identity _
  source_comm _ _ := rfl
  target_comm _ _ := rfl

/-- Faithful material readout yields actual source endpoint lifting at
every context; no modal commutation law is assumed. -/
theorem sourceLifts : (observation profile occurrences action).SourceLifts := by
  intro X source event same
  change profile.observation.app X event.source = profile.observation.app X source at same
  have values := (profile.readings X).value_eq_of_bisimilar ((profile.observation_eq_iff X _ _).mp same)
  obtain ⟨lift, sourceEq, targetEq⟩ := (occurrences X).sourceLifts (profile.readings X) (profile.faithful X) source event values
  exact ⟨lift, sourceEq, (profile.observation_eq_iff X _ _).mpr
    (((profile.readings X).value_eq_iff_bisimilar (profile.faithful X) _ _).mp targetEq)⟩

/-- Incoming matching is independent data about the actual authored spans,
not a consequence of forward observed bisimulation. -/
theorem targetLifts
    (incoming : ∀ X, ((occurrences X).observation (profile.readings X)).TargetLifts) :
    (observation profile occurrences action).TargetLifts := by
  intro X source event same
  change profile.observation.app X event.target = profile.observation.app X source at same
  have values := (profile.readings X).value_eq_of_bisimilar ((profile.observation_eq_iff X _ _).mp same)
  obtain ⟨lift, targetEq, sourceEq⟩ := incoming X source event values
  exact ⟨lift, targetEq, (profile.observation_eq_iff X _ _).mpr
    (((profile.readings X).value_eq_iff_bisimilar (profile.faithful X) _ _).mp sourceEq)⟩

theorem native_diamond_reindex (predicate : Subfunctor profile.classFace) :
    preimage profile.observation (diamond (observedGraph profile occurrences action) predicate) =
      diamond (sourceGraph profile occurrences action) (preimage profile.observation predicate) := by
  ext X source
  exact (observation profile occurrences action).diamond_pullback
    (sourceLifts profile occurrences action) predicate X source

/-- This is the actual internal native box: its universal quantifier ranges
over every further restriction and the incoming events there. -/
theorem native_box_reindex
    (incoming : ∀ X, ((occurrences X).observation (profile.readings X)).TargetLifts)
    (predicate : Subfunctor profile.classFace) :
    preimage profile.observation (box (observedGraph profile occurrences action) predicate) =
      box (sourceGraph profile occurrences action) (preimage profile.observation predicate) := by
  ext X source
  exact (observation profile occurrences action).box_pullback
    (targetLifts profile occurrences action incoming) predicate X source

/-- The native source predicate's exact image remains exact after diamond.
The witness retains all authored context and event data before support. -/
theorem diamond_image_exact (predicate : Subfunctor profile.sourceFace)
    (invariant : ∀ X left right, (profile.system X).Bisimilar left right →
      (left ∈ predicate.obj X ↔ right ∈ predicate.obj X)) :
    preimage profile.observation (diamond (observedGraph profile occurrences action) (observedImage profile predicate)) =
      diamond (sourceGraph profile occurrences action) predicate := by
  exact (native_diamond_reindex profile occurrences action (observedImage profile predicate)).trans
    (congrArg (diamond (sourceGraph profile occurrences action))
      ((observedImage_exact_iff profile predicate).mpr invariant))

theorem box_image_exact
    (incoming : ∀ X, ((occurrences X).observation (profile.readings X)).TargetLifts)
    (predicate : Subfunctor profile.sourceFace)
    (invariant : ∀ X left right, (profile.system X).Bisimilar left right →
      (left ∈ predicate.obj X ↔ right ∈ predicate.obj X)) :
    preimage profile.observation (box (observedGraph profile occurrences action) (observedImage profile predicate)) =
      box (sourceGraph profile occurrences action) predicate := by
  exact (native_box_reindex profile occurrences action incoming (observedImage profile predicate)).trans
    (congrArg (box (sourceGraph profile occurrences action))
      ((observedImage_exact_iff profile predicate).mpr invariant))

theorem sourceDiamond_native_step
    (agree : ∀ X, ObservedNativeTypes.ActionsPresentSteps (M := profile.system X))
    (predicate : Subfunctor profile.sourceFace) (X : Cᵒᵖ) (source : profile.sourceFace.obj X) :
    source ∈ (diamond (sourceGraph profile occurrences action) predicate).obj X ↔
      Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltDiamond (profile.theory X) (predicate.obj X) source := by
  refine Iff.trans ?_ (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltDiamond_spec (profile.theory X) (predicate.obj X) source).symm
  constructor
  · rintro ⟨event, holds, same⟩
    refine ⟨event.target, ?_, holds⟩
    exact (ObservedNativeTypes.actionSpan_step_iff (occurrences X) (agree X) source event.target).mp ⟨event, same, rfl⟩
  · rintro ⟨target, step, holds⟩
    obtain ⟨event, sourceEq, targetEq⟩ :=
      (ObservedNativeTypes.actionSpan_step_iff (occurrences X) (agree X) source target).mpr step
    refine ⟨event, ?_, sourceEq⟩
    change event.target ∈ predicate.obj X
    change event.target = target at targetEq
    exact targetEq.symm ▸ holds

end Modal

namespace Growing

open PowerClassPresheafDescent.Controls (Stages world stageValue stageIndex growthLe)
open Mettapedia.GSLT.ContextualObservedFamilyEnclosure.GrowthControls
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

abbrev model := Mettapedia.GSLT.ContextualObservedFamilyEnclosure.GrowthControls.profile

/-- A proper contextual predicate comes from an actual atomic native type;
the position label is retained by the observed material kernel. -/
def positionPredicate : Subfunctor model.sourceFace where
  obj _ := {source | source.1.val = 0}
  map _ := by
    intro source holds
    exact holds

theorem positionPredicate_is_formula_native (X : Stagesᵒᵖ) (source : model.sourceFace.obj X) :
    (gsltOSLF (theory X)).satisfies (S := ()) source
      (Mettapedia.OSLF.Framework.HennessyMilnerNativeTypes.formulaNativeType (system X)
        (.atom ⟨0, Nat.zero_lt_succ _⟩)).pred ↔ source ∈ positionPredicate.obj X := by
  change source.1 = ⟨0, Nat.zero_lt_succ _⟩ ↔ source.1.val = 0
  exact ⟨fun same => congrArg Fin.val same, fun same => Fin.ext same⟩

theorem positionPredicate_factors :
    ∃ classifier : NatTrans model.classFace (Mettapedia.GSLT.Topos.omegaFunctor (C := Stages)),
      ∀ X source, classifier.app X (model.observation.app X source) =
        (Classifier.characteristic positionPredicate).app X source := by
  apply (classifier_factors_iff model positionPredicate).mpr
  intro X left right related
  have same := congrArg Fin.val ((bisimilar_iff_position X left right).mp related)
  change left.1.val = 0 ↔ right.1.val = 0
  exact ⟨fun holds => same.symm.trans holds, fun holds => same.trans holds⟩

theorem positionPredicate_proper : positionPredicate ≠ ⊤ := by
  intro same
  have holds : stageValue 1 1 (by omega) false ∈ positionPredicate.obj (world 1) := by
    rw [same]
    trivial
  change 1 = 0 at holds
  omega

theorem actionsPresentSteps (X : Stagesᵒᵖ) :
    ObservedNativeTypes.ActionsPresentSteps (M := system X) := by
  intro source target
  exact ⟨fun fires => ⟨(), fires⟩, fun ⟨_, fires⟩ => fires⟩

/-- In this actual cyclic system incoming matching is constructed by
flipping the requested phase. The authored event's provenance is retained. -/
theorem incomingLifts (X : Stagesᵒᵖ) :
    ((occurrences X).observation (readings X)).TargetLifts := by
  intro state event same
  have positions := (value_eq_iff_position X event.target state).mp same
  have firePositions := congrArg (fun source : (theory X).Term => source.1) event.occurrence.2.down
  let lifted : ObservedMaterialization.ActionOccurrences.Event (occurrences X) :=
    ⟨(), flip state, state, event.occurrence.1, ⟨by
      change state = flip (flip state)
      exact Prod.ext rfl (Bool.not_not state.2).symm⟩⟩
  exact ⟨lifted, rfl, (value_eq_iff_position X (flip state) event.source).mpr
    (positions.symm.trans firePositions)⟩

theorem position_modal_image_exact :
    preimage model.observation (Mettapedia.GSLT.Topos.PresheafEventModalities.diamond
      (Modal.observedGraph model occurrences eventAction) (observedImage model positionPredicate)) =
        Mettapedia.GSLT.Topos.PresheafEventModalities.diamond
          (Modal.sourceGraph model occurrences eventAction) positionPredicate ∧
    preimage model.observation (Mettapedia.GSLT.Topos.PresheafEventModalities.box
      (Modal.observedGraph model occurrences eventAction) (observedImage model positionPredicate)) =
        Mettapedia.GSLT.Topos.PresheafEventModalities.box
          (Modal.sourceGraph model occurrences eventAction) positionPredicate := by
  have invariant := (classifier_factors_iff model positionPredicate).mp positionPredicate_factors
  exact ⟨Modal.diamond_image_exact model occurrences eventAction positionPredicate invariant,
    Modal.box_image_exact model occurrences eventAction incomingLifts positionPredicate invariant⟩

/-- This is a genuine native contextual predicate: authored restrictions
retain the phase, but the declared behavioural observation erases it. -/
def phasePredicate : Subfunctor model.sourceFace where
  obj _ := {source | source.2 = true}
  map _ := by
    intro source holds
    exact holds

theorem phasePredicate_is_native (X : Stagesᵒᵖ) :
    ∃ nativeType : GSLTNativeType (theory X),
      ∀ source, (gsltOSLF (theory X)).satisfies (S := ()) source nativeType.pred ↔
        source ∈ phasePredicate.obj X := by
  refine ⟨⟨(), ⟨fun source => source.2 = true, ?_⟩⟩, fun _ => Iff.rfl⟩
  intro left right same
  cases same
  rfl

theorem phasePredicate_no_classifier_factor :
    ¬ ∃ classifier : NatTrans model.classFace (Mettapedia.GSLT.Topos.omegaFunctor (C := Stages)),
      ∀ X source, classifier.app X (model.observation.app X source) =
        (Classifier.characteristic phasePredicate).app X source := by
  intro factors
  have invariant := (classifier_factors_iff model phasePredicate).mp factors
  have same := invariant (world 0) (stageValue 0 0 (by omega) true) (stageValue 0 0 (by omega) false)
    ((bisimilar_iff_position (world 0) _ _).mpr rfl)
  have impossible : false = true := same.mp rfl
  cases impossible

/-- The authored phase predicate detects a real next-phase transition.
The two starting states nevertheless have the same observed material value. -/
theorem native_diamond_distinguishes_erased_phase :
    Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltDiamond (theory (world 0))
      (phasePredicate.obj (world 0)) (stageValue 0 0 (by omega) false) ∧
    ¬ Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltDiamond (theory (world 0))
      (phasePredicate.obj (world 0)) (stageValue 0 0 (by omega) true) := by
  constructor
  · apply (gsltDiamond_spec (theory (world 0)) _ _).mpr
    exact ⟨flip (stageValue 0 0 (by omega) false), rfl, rfl⟩
  · intro holds
    obtain ⟨target, fires, supported⟩ := (gsltDiamond_spec (theory (world 0)) _ _).mp holds
    change target = flip (stageValue 0 0 (by omega) true) at fires
    change target.2 = true at supported
    have impossible : false = true := (congrArg Prod.snd fires).symm.trans supported
    cases impossible

theorem phase_diamond_image_not_exact :
    preimage model.observation (observedImage model (Mettapedia.GSLT.Topos.PresheafEventModalities.diamond
      (Modal.sourceGraph model occurrences eventAction) phasePredicate)) ≠
        Mettapedia.GSLT.Topos.PresheafEventModalities.diamond
          (Modal.sourceGraph model occurrences eventAction) phasePredicate := by
  intro exactImage
  have invariant := (observedImage_exact_iff model _).mp exactImage
  have iffPhase := invariant (world 0) (stageValue 0 0 (by omega) false)
    (stageValue 0 0 (by omega) true) ((bisimilar_iff_position (world 0) _ _).mpr rfl)
  have sourceFalse := (Modal.sourceDiamond_native_step model occurrences eventAction
    actionsPresentSteps phasePredicate (world 0) (stageValue 0 0 (by omega) false)).mpr
      native_diamond_distinguishes_erased_phase.1
  have sourceTrue := iffPhase.mp sourceFalse
  exact native_diamond_distinguishes_erased_phase.2
    ((Modal.sourceDiamond_native_step model occurrences eventAction actionsPresentSteps
      phasePredicate (world 0) (stageValue 0 0 (by omega) true)).mp sourceTrue)

/-- The classifier carries more than its present truth value: this stable
predicate first holds at a later world, and the sieve contains that arrow. -/
def futurePredicate : Subfunctor model.sourceFace where
  obj X := {_source | 0 < stageIndex X}
  map {X Y} step := by
    intro source holds
    have grows := growthLe step
    change 0 < stageIndex X at holds
    change 0 < stageIndex Y
    omega

theorem native_classifier_detects_future :
    ¬ ((Classifier.characteristic futurePredicate).app (world 0) (stageValue 0 0 (by omega) false)).arrows
        (𝟙 (world 0).unop) ∧
      ((Classifier.characteristic futurePredicate).app (world 0) (stageValue 0 0 (by omega) false)).arrows grow.unop := by
  constructor
  · intro present
    have impossible := (Classifier.characteristic_truth futurePredicate (world 0) _).mp present
    change 0 < 0 at impossible
    omega
  · change 0 < 1
    omega

/-- Every source fibre of the actual phase-sensitive family is supported.
The proof uses its retained material term and the actual member decoder. -/
theorem phaseFamily_support_top :
    Mettapedia.GSLT.Topos.support
      (PowerClassPresheafDescent.nativeSourceDisplayed model.sourceFace model.classFace
        model.observation alternativeGraphs alternativeTransport) = ⊤ := by
  ext X source
  constructor
  · intro _
    trivial
  · intro _
    exact ⟨(PowerClassPresheafDescent.sourceMaterialMemberEquiv model.sourceFace alternativeGraphs
      ⟨X, source⟩).symm (phaseTerm ⟨X, source⟩)⟩

/-- Native image support is total, while the authored natural section still
cannot be reified as a section of the observed family. -/
theorem supported_native_family_does_not_recover_section :
    Mettapedia.GSLT.Topos.support
      (PowerClassPresheafDescent.nativeSourceDisplayed model.sourceFace model.classFace
        model.observation alternativeGraphs alternativeTransport) = ⊤ ∧
      ¬ ∃ term : (Mettapedia.GSLT.ContextualObservedFamilyEnclosure.Families.displayed
          model alternativeGraphs alternativeTransport).sections,
        PowerClassPresheafDescent.pullContextualSection model.sourceFace model.classFace
          model.observation alternativeGraphs alternativeTransport term = phaseTerm :=
  ⟨phaseFamily_support_top, phaseTerm_no_observed_section⟩

end Growing

end Mettapedia.OSLF.Bridges.TypeTheory.ContextualObservedNativeTypes
