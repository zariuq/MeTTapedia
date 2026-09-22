import Mettapedia.TypeTheory.DisplayedPresheafTransport
import Mathlib.Logic.Equiv.Sum
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.Limits.Final.Type
import Mettapedia.Computability.ComputationalTrinityDependentDescent

/-!
# Proof-relevant points of a displayed presheaf family

The existing displayed-family construction is a functor on the category of
elements of a base presheaf. Its category of elements records a base value
together with an inhabitant of that displayed fibre. The canonical
projection and lifts below retain the actual evidence object and act
along contextual substitutions.

The total presheaf additionally collects the base values and their displayed
evidence at each context, with a natural value projection. This is semantic
context extension, not an authored dependent former or a complete CwF.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.DisplayedPresheafComprehension

open CategoryTheory
open Mettapedia.Computability.ComputationalTrinity
open Mettapedia.TypeTheory.DisplayedPresheafTransport
open Mettapedia.Computability.ComputationalTrinityDependentDescent

universe uContext vContext uBase uFibre

variable {Context : Type uContext} [Category.{vContext} Context]
variable {base : Face.{uContext, vContext, uBase} Context}
variable (family : DisplayedFamily.{uContext, vContext, uBase, uFibre} base)

/-- A point retains both the contextual base value and its actual displayed
evidence, rather than truncating the evidence to a proposition. -/
def point (value : base.Elements) (evidence : family.obj value) :
    family.Elements :=
  ⟨value, evidence⟩

/-- Forget only the displayed evidence while retaining the contextual base
value and its substitution action. -/
def projection : family.Elements ⥤ base.Elements :=
  CategoryOfElements.π family

@[simp] theorem projection_point (value : base.Elements)
    (evidence : family.obj value) :
    (projection family).obj (point family value evidence) = value := rfl

/-- Transport an actual displayed witness along one arrow of the base
category of elements. -/
def transportPoint {source target : base.Elements}
    (substitution : source ⟶ target) (evidence : family.obj source) :
    family.Elements :=
  point family target (family.map substitution evidence)

/-- The transported witness is accompanied by the exact base substitution
that produced it. -/
def transportArrow {source target : base.Elements}
    (substitution : source ⟶ target) (evidence : family.obj source) :
    point family source evidence ⟶
      transportPoint family substitution evidence :=
  CategoryOfElements.homMk _ _ substitution rfl

@[simp] theorem projection_transportArrow {source target : base.Elements}
    (substitution : source ⟶ target) (evidence : family.obj source) :
    (projection family).map (transportArrow family substitution evidence) =
      substitution := rfl

/-- Distinct evidence at one base point remains distinct in the extension. -/
theorem point_injective (value : base.Elements)
    {first second : family.obj value}
    (same : point family value first = point family value second) :
    first = second := by
  simpa [point] using (Sigma.mk.inj same).2

/-- The projection identifies the base point of two different evidence
values, but the evidence-bearing objects do not collapse. -/
theorem distinct_points_same_projection (value : base.Elements)
    {first second : family.obj value} (different : first ≠ second) :
    point family value first ≠ point family value second ∧
      (projection family).obj (point family value first) =
        (projection family).obj (point family value second) := by
  constructor
  · intro same
    exact different (point_injective family value same)
  · rfl

section TotalPresheaf

/-- Values and their dependent evidence at a fixed context. The total space
uses the maximum of the base and fibre universes. -/
abbrev TotalAt (context : Contextᵒᵖ) :=
  Σ value : base.obj context, family.obj ⟨context, value⟩

/-- Substitution changes the base value and transports its actual evidence
along the corresponding arrow of the category of elements. -/
def totalMap {source target : Contextᵒᵖ}
    (substitution : source ⟶ target) (receipt : TotalAt family source) :
    TotalAt family target :=
  ⟨base.map substitution receipt.1,
    family.map
      (CategoryOfElements.homMk _ _ substitution rfl) receipt.2⟩

private theorem map_apply_heq_of_base_arrow
    {source target otherTarget : base.Elements}
    (sameTarget : target = otherTarget)
    (first : source ⟶ target) (second : source ⟶ otherTarget)
    (sameArrow : HEq first.val second.val) (evidence : family.obj source) :
    HEq (family.map first evidence) (family.map second evidence) := by
  cases sameTarget
  have same : first = second := Subtype.ext (eq_of_heq sameArrow)
  cases same
  rfl

theorem totalMap_id (context : Contextᵒᵖ) (receipt : TotalAt family context) :
    totalMap family (𝟙 context) receipt = receipt := by
  rcases receipt with ⟨value, evidence⟩
  apply Sigma.ext (by simp [totalMap])
  have transported := map_apply_heq_of_base_arrow family
    (source := ⟨context, value⟩)
    (target := ⟨context, base.map (𝟙 context) value⟩)
    (otherTarget := ⟨context, value⟩)
    (congrArg (fun value => (⟨context, value⟩ : base.Elements))
      (base.map_id_apply context value))
    (CategoryOfElements.homMk _ _ (𝟙 context) rfl)
    (𝟙 _) (heq_of_eq rfl) evidence
  exact transported.trans (heq_of_eq (family.map_id_apply _ evidence))

theorem totalMap_comp {first middle last : Contextᵒᵖ}
    (earlier : first ⟶ middle) (later : middle ⟶ last)
    (receipt : TotalAt family first) :
    totalMap family (earlier ≫ later) receipt =
      totalMap family later (totalMap family earlier receipt) := by
  rcases receipt with ⟨value, evidence⟩
  apply Sigma.ext (by simp [totalMap])
  have transported := map_apply_heq_of_base_arrow family
    (source := ⟨first, value⟩)
    (target := ⟨last, base.map (earlier ≫ later) value⟩)
    (otherTarget := ⟨last, base.map later (base.map earlier value)⟩)
    (congrArg (fun value => (⟨last, value⟩ : base.Elements))
      (base.map_comp_apply earlier later value))
    (CategoryOfElements.homMk _ _ (earlier ≫ later) rfl)
    ((CategoryOfElements.homMk _
      (⟨middle, base.map earlier value⟩ : base.Elements) earlier rfl) ≫
        CategoryOfElements.homMk _ _ later rfl)
    (heq_of_eq rfl) evidence
  exact transported.trans (heq_of_eq (family.map_comp_apply _ _ evidence))

/-- Semantic comprehension as a total presheaf, retaining the displayed
evidence under every contextual substitution. -/
def totalSpace : Face.{uContext, vContext, max uBase uFibre} Context where
  obj := TotalAt family
  map substitution := TypeCat.ofHom (totalMap family substitution)
  map_id context := by
    apply ConcreteCategory.hom_ext
    exact totalMap_id family context
  map_comp earlier later := by
    apply ConcreteCategory.hom_ext
    exact totalMap_comp family earlier later

end TotalPresheaf

section SmallComprehension

variable {smallBase : Face.{uContext, vContext, uBase} Context}

/-- In a shared ambient universe, the total context has a natural projection
to its original contextual values. Only the evidence coordinate is erased. -/
def totalProjection
    (smallFamily : DisplayedFamily.{uContext, vContext, uBase, uBase} smallBase) :
    totalSpace smallFamily ⟶ smallBase where
  app _ := TypeCat.ofHom Sigma.fst
  naturality := by
    intro source target substitution
    apply ConcreteCategory.hom_ext
    intro receipt
    rfl

/-- A natural dependent section supplies a natural section of the total
context projection, retaining its selected evidence at each base value. -/
def sectionLift
    (smallFamily : DisplayedFamily.{uContext, vContext, uBase, uBase} smallBase)
    (sectionValue : smallFamily.sections) :
    smallBase ⟶ totalSpace smallFamily where
  app context := TypeCat.ofHom fun value =>
    ⟨value, sectionValue.val ⟨context, value⟩⟩
  naturality := by
    intro source target substitution
    apply ConcreteCategory.hom_ext
    intro value
    change (⟨smallBase.map substitution value,
      sectionValue.val ⟨target, smallBase.map substitution value⟩⟩ :
        TotalAt smallFamily target) =
      ⟨smallBase.map substitution value,
        smallFamily.map (CategoryOfElements.homMk _ _ substitution rfl)
          (sectionValue.val ⟨source, value⟩)⟩
    exact congrArg (fun evidence =>
      (⟨smallBase.map substitution value, evidence⟩ : TotalAt smallFamily target))
      (sectionValue.property
        (CategoryOfElements.homMk (F := smallBase)
          ⟨source, value⟩ ⟨target, smallBase.map substitution value⟩
          substitution rfl)).symm

/-- The first comprehension projection has its expected section equation. -/
theorem sectionLift_projection
    (smallFamily : DisplayedFamily.{uContext, vContext, uBase, uBase} smallBase)
    (sectionValue : smallFamily.sections) :
    sectionLift smallFamily sectionValue ≫ totalProjection smallFamily =
      𝟙 smallBase := by
  ext context value
  rfl

/-- No two different dependent sections become equal merely by pairing them
with their common base values. -/
theorem sectionLift_injective
    (smallFamily : DisplayedFamily.{uContext, vContext, uBase, uBase} smallBase) :
    Function.Injective (sectionLift smallFamily) := by
  intro first second same
  apply Subtype.ext
  funext point
  rcases point with ⟨context, value⟩
  have samePoint := congrArg (fun map => map.app context value) same
  exact eq_of_heq (Sigma.mk.inj samePoint).2

private def evidenceAt
    (smallFamily : DisplayedFamily.{uContext, vContext, uBase, uBase} smallBase)
    {context : Contextᵒᵖ} {value : smallBase.obj context}
    (receipt : TotalAt smallFamily context) (same : receipt.1 = value) :
    smallFamily.obj ⟨context, value⟩ :=
  same ▸ receipt.2

private theorem evidenceAt_pair
    (smallFamily : DisplayedFamily.{uContext, vContext, uBase, uBase} smallBase)
    {context : Contextᵒᵖ} {value : smallBase.obj context}
    (receipt : TotalAt smallFamily context) (same : receipt.1 = value) :
    (⟨value, evidenceAt smallFamily receipt same⟩ : TotalAt smallFamily context) =
      receipt := by
  rcases receipt with ⟨observed, evidence⟩
  dsimp only at same
  cases same
  rfl

private theorem lift_base_value
    (smallFamily : DisplayedFamily.{uContext, vContext, uBase, uBase} smallBase)
    (lift : smallBase ⟶ totalSpace smallFamily)
    (splits : lift ≫ totalProjection smallFamily = 𝟙 smallBase)
    (context : Contextᵒᵖ) (value : smallBase.obj context) :
    (lift.app context value).1 = value :=
  congrArg (fun map => map.app context value) splits

/-- A natural section of the total projection supplies a dependent section
of the original family. Its evidence is transported only along the proved
equality of its base coordinate. -/
def sectionOfLift
    (smallFamily : DisplayedFamily.{uContext, vContext, uBase, uBase} smallBase)
    (lift : smallBase ⟶ totalSpace smallFamily)
    (splits : lift ≫ totalProjection smallFamily = 𝟙 smallBase) :
    smallFamily.sections where
  val point := evidenceAt smallFamily (lift.app point.1 point.2)
    (lift_base_value smallFamily lift splits point.1 point.2)
  property := by
    rintro ⟨source, value⟩ ⟨target, otherValue⟩ ⟨substitution, follows⟩
    change source ⟶ target at substitution
    change smallBase.map substitution value = otherValue at follows
    subst otherValue
    have natural := congrArg (fun map => map value)
      (lift.naturality substitution)
    change lift.app target (smallBase.map substitution value) =
      totalMap smallFamily substitution (lift.app source value) at natural
    rw [← evidenceAt_pair smallFamily (lift.app target _)
      (lift_base_value smallFamily lift splits target _),
      ← evidenceAt_pair smallFamily (lift.app source value)
        (lift_base_value smallFamily lift splits source value)] at natural
    exact (eq_of_heq (Sigma.mk.inj natural).2).symm

/-- Reassembling a splitting recovers the very same natural transformation
into the extended context, not only an objectwise bijection. -/
theorem sectionLift_sectionOfLift
    (smallFamily : DisplayedFamily.{uContext, vContext, uBase, uBase} smallBase)
    (lift : smallBase ⟶ totalSpace smallFamily)
    (splits : lift ≫ totalProjection smallFamily = 𝟙 smallBase) :
    sectionLift smallFamily (sectionOfLift smallFamily lift splits) = lift := by
  ext context value
  exact evidenceAt_pair smallFamily (lift.app context value)
    (lift_base_value smallFamily lift splits context value)

/-- The semantic term/comprehension correspondence: dependent natural
sections are exactly natural splittings of the total-context projection. -/
def sectionEquivProjectionSplittings
    (smallFamily : DisplayedFamily.{uContext, vContext, uBase, uBase} smallBase) :
    smallFamily.sections ≃
      { lift : smallBase ⟶ totalSpace smallFamily //
        lift ≫ totalProjection smallFamily = 𝟙 smallBase } where
  toFun sectionValue :=
    ⟨sectionLift smallFamily sectionValue,
      sectionLift_projection smallFamily sectionValue⟩
  invFun lift := sectionOfLift smallFamily lift.val lift.property
  left_inv sectionValue := by
    apply sectionLift_injective smallFamily
    exact sectionLift_sectionOfLift smallFamily _ _
  right_inv lift :=
    Subtype.ext (sectionLift_sectionOfLift smallFamily lift.val lift.property)

end SmallComprehension

section ObservationComprehension

variable {source target : Face.{uContext, vContext, uBase} Context}
variable (observation : source ⟶ target)

/-- The total of the actual observation fibres recovers each original
source value, including its evidence, rather than merely its image. -/
def observationTotalEquiv (context : Contextᵒᵖ) :
    (totalSpace (observationFibreFamily observation)).obj context ≃
      source.obj context :=
  Equiv.sigmaFiberEquiv (observation.app context)

/-- Recovering retained evidence from its displayed total commutes with
every contextual substitution. -/
def observationTotalIso :
    totalSpace (observationFibreFamily observation) ≅ source := by
  refine NatIso.ofComponents
    (fun context => (observationTotalEquiv observation context).toIso) ?_
  intro first second substitution
  apply ConcreteCategory.hom_ext
  intro receipt
  rfl

/-- The recovered source followed by its original observation is precisely
the comprehension projection, not an unrelated map to the same base. -/
theorem observationTotalIso_projection :
    (observationTotalIso observation).hom ≫ observation =
      totalProjection (observationFibreFamily observation) := by
  ext context receipt
  exact receipt.2.property

end ObservationComprehension

section ChangeOfBase

variable {originalBase replacementBase : Face.{uContext, vContext, uBase} Context}
variable (change : replacementBase ⟶ originalBase)
variable (originalFamily :
  DisplayedFamily.{uContext, vContext, uBase, uBase} originalBase)

/-- Reindex a dependent family along an arbitrary natural map of base
presheaves. The underlying map of categories of elements is supplied by
Mathlib; no inverse for the base map is assumed. -/
def reindexDisplayed :
    DisplayedFamily.{uContext, vContext, uBase, uBase} replacementBase :=
  change.mapElements ⋙ originalFamily

/-- Identity base change leaves the displayed family unchanged. -/
@[simp] theorem reindexDisplayed_id
    {oneBase : Face.{uContext, vContext, uBase} Context}
    (oneFamily : DisplayedFamily.{uContext, vContext, uBase, uBase} oneBase) :
    reindexDisplayed (𝟙 oneBase) oneFamily = oneFamily := by
  rfl

/-- Successive base changes agree with their composite, including the
displayed action on contextual arrows. -/
@[simp] theorem reindexDisplayed_comp
    {finalBase : Face.{uContext, vContext, uBase} Context}
    (later : finalBase ⟶ replacementBase) :
    reindexDisplayed (later ≫ change) originalFamily =
      reindexDisplayed later (reindexDisplayed change originalFamily) := by
  rfl

/-- The total of the reindexed family maps to the original total by applying
the base change to its value while retaining its actual evidence object. -/
def totalReindexMap :
    totalSpace (reindexDisplayed change originalFamily) ⟶
      totalSpace originalFamily where
  app context := TypeCat.ofHom fun receipt =>
    ⟨change.app context receipt.1, receipt.2⟩
  naturality := by
    intro source target substitution
    apply ConcreteCategory.hom_ext
    rintro ⟨value, evidence⟩
    change (⟨change.app target (replacementBase.map substitution value),
      originalFamily.map
        (change.mapElements.map
          (CategoryOfElements.homMk (F := replacementBase)
            ⟨source, value⟩
            ⟨target, replacementBase.map substitution value⟩
            substitution rfl)) evidence⟩ :
        TotalAt originalFamily target) =
      ⟨originalBase.map substitution (change.app source value),
        originalFamily.map
          (CategoryOfElements.homMk (F := originalBase)
            ⟨source, change.app source value⟩
            ⟨target, originalBase.map substitution
              (change.app source value)⟩ substitution rfl) evidence⟩
    apply Sigma.ext (change.naturality_apply substitution value)
    exact map_apply_heq_of_base_arrow originalFamily
      (source := ⟨source, change.app source value⟩)
      (target := ⟨target,
        change.app target (replacementBase.map substitution value)⟩)
      (otherTarget := ⟨target,
        originalBase.map substitution (change.app source value)⟩)
      (congrArg (fun value => (⟨target, value⟩ : originalBase.Elements))
        (change.naturality_apply substitution value))
      (change.mapElements.map
        (CategoryOfElements.homMk (F := replacementBase)
          ⟨source, value⟩
          ⟨target, replacementBase.map substitution value⟩
          substitution rfl))
      (CategoryOfElements.homMk (F := originalBase)
        ⟨source, change.app source value⟩
        ⟨target, originalBase.map substitution
          (change.app source value)⟩ substitution rfl)
      (heq_of_eq rfl) evidence

/-- The map of extended contexts for the identity base change is the
identity natural transformation. -/
@[simp] theorem totalReindexMap_id
    {oneBase : Face.{uContext, vContext, uBase} Context}
    (oneFamily : DisplayedFamily.{uContext, vContext, uBase, uBase} oneBase) :
    totalReindexMap (𝟙 oneBase) oneFamily = 𝟙 (totalSpace oneFamily) := by
  ext context receipt
  rfl

/-- Changing an extended context in two steps equals changing it once by
the composite base map, with the evidence coordinate still retained. -/
theorem totalReindexMap_comp
    {finalBase : Face.{uContext, vContext, uBase} Context}
    (later : finalBase ⟶ replacementBase) :
    totalReindexMap later (reindexDisplayed change originalFamily) ≫
        totalReindexMap change originalFamily =
      totalReindexMap (later ≫ change) originalFamily := by
  ext context receipt
  rfl

/-- Reindexing semantic comprehension gives a commuting square with the
original context extension and the base change. -/
theorem totalReindexMap_square :
    totalReindexMap change originalFamily ≫
        totalProjection originalFamily =
      totalProjection (reindexDisplayed change originalFamily) ≫ change := by
  ext context receipt
  rfl

/-- The two maps out of the base changed total jointly determine an actual
evidence-bearing point. This supplies the uniqueness part of the pullback. -/
theorem totalReindexMap_jointly_injective
    (context : Contextᵒᵖ)
    {first second :
      (totalSpace (reindexDisplayed change originalFamily)).obj context}
    (sameBase :
      (totalProjection (reindexDisplayed change originalFamily)).app
        context first =
      (totalProjection (reindexDisplayed change originalFamily)).app
        context second)
    (sameTotal :
      (totalReindexMap change originalFamily).app context first =
      (totalReindexMap change originalFamily).app context second) :
    first = second := by
  rcases first with ⟨firstValue, firstEvidence⟩
  rcases second with ⟨secondValue, secondEvidence⟩
  change firstValue = secondValue at sameBase
  subst secondValue
  change (⟨change.app context firstValue, firstEvidence⟩ :
      TotalAt originalFamily context) =
    ⟨change.app context firstValue, secondEvidence⟩ at sameTotal
  have sameEvidence : firstEvidence = secondEvidence :=
    eq_of_heq (Sigma.mk.inj sameTotal).2
  cases sameEvidence
  rfl

private theorem compatible_base_value
    {probe : Face.{uContext, vContext, uBase} Context}
    (toReplacement : probe ⟶ replacementBase)
    (toTotal : probe ⟶ totalSpace originalFamily)
    (compatible : toReplacement ≫ change =
      toTotal ≫ totalProjection originalFamily)
    (context : Contextᵒᵖ) (value : probe.obj context) :
    (toTotal.app context value).1 =
      change.app context (toReplacement.app context value) :=
  (congrArg (fun map => map.app context value) compatible).symm

private def compatible_lift_at
    {probe : Face.{uContext, vContext, uBase} Context}
    (toReplacement : probe ⟶ replacementBase)
    (toTotal : probe ⟶ totalSpace originalFamily)
    (compatible : toReplacement ≫ change =
      toTotal ≫ totalProjection originalFamily)
    (context : Contextᵒᵖ) (value : probe.obj context) :
    (totalSpace (reindexDisplayed change originalFamily)).obj context :=
  ⟨toReplacement.app context value,
    evidenceAt originalFamily (toTotal.app context value)
      (compatible_base_value change originalFamily toReplacement
        toTotal compatible context value)⟩

private theorem compatible_lift_at_base
    {probe : Face.{uContext, vContext, uBase} Context}
    (toReplacement : probe ⟶ replacementBase)
    (toTotal : probe ⟶ totalSpace originalFamily)
    (compatible : toReplacement ≫ change =
      toTotal ≫ totalProjection originalFamily)
    (context : Contextᵒᵖ) (value : probe.obj context) :
    (totalProjection (reindexDisplayed change originalFamily)).app context
        (compatible_lift_at change originalFamily toReplacement
          toTotal compatible context value) =
      toReplacement.app context value :=
  rfl

private theorem compatible_lift_at_total
    {probe : Face.{uContext, vContext, uBase} Context}
    (toReplacement : probe ⟶ replacementBase)
    (toTotal : probe ⟶ totalSpace originalFamily)
    (compatible : toReplacement ≫ change =
      toTotal ≫ totalProjection originalFamily)
    (context : Contextᵒᵖ) (value : probe.obj context) :
    (totalReindexMap change originalFamily).app context
        (compatible_lift_at change originalFamily toReplacement
          toTotal compatible context value) =
      toTotal.app context value :=
  evidenceAt_pair originalFamily (toTotal.app context value)
    (compatible_base_value change originalFamily toReplacement
      toTotal compatible context value)

/-- Any compatible pair of contextual maps lifts to the base changed
evidence extension. Naturality uses joint injectivity and both original
natural transformations. -/
def baseChangeLift
    {probe : Face.{uContext, vContext, uBase} Context}
    (toReplacement : probe ⟶ replacementBase)
    (toTotal : probe ⟶ totalSpace originalFamily)
    (compatible : toReplacement ≫ change =
      toTotal ≫ totalProjection originalFamily) :
    probe ⟶ totalSpace (reindexDisplayed change originalFamily) where
  app context := TypeCat.ofHom fun value =>
    compatible_lift_at change originalFamily toReplacement
      toTotal compatible context value
  naturality := by
    intro source target substitution
    apply ConcreteCategory.hom_ext
    intro value
    apply totalReindexMap_jointly_injective change originalFamily target
    · change
        toReplacement.app target (probe.map substitution value) =
          replacementBase.map substitution
            (toReplacement.app source value)
      exact toReplacement.naturality_apply substitution value
    · calc
        (totalReindexMap change originalFamily).app target
            (compatible_lift_at change originalFamily toReplacement
              toTotal compatible target (probe.map substitution value)) =
            toTotal.app target (probe.map substitution value) :=
          compatible_lift_at_total change originalFamily toReplacement
            toTotal compatible target _
        _ = (totalSpace originalFamily).map substitution
            (toTotal.app source value) :=
          toTotal.naturality_apply substitution value
        _ = (totalSpace originalFamily).map substitution
            ((totalReindexMap change originalFamily).app source
              (compatible_lift_at change originalFamily toReplacement
                toTotal compatible source value)) := by
          rw [compatible_lift_at_total]
        _ = (totalReindexMap change originalFamily).app target
            ((totalSpace (reindexDisplayed change originalFamily)).map
              substitution
              (compatible_lift_at change originalFamily toReplacement
                toTotal compatible source value)) := by
          exact ((totalReindexMap change originalFamily).naturality_apply
            substitution _).symm

/-- The induced map has the specified replacement-base coordinate. -/
theorem baseChangeLift_base
    {probe : Face.{uContext, vContext, uBase} Context}
    (toReplacement : probe ⟶ replacementBase)
    (toTotal : probe ⟶ totalSpace originalFamily)
    (compatible : toReplacement ≫ change =
      toTotal ≫ totalProjection originalFamily) :
    baseChangeLift change originalFamily toReplacement toTotal compatible ≫
        totalProjection (reindexDisplayed change originalFamily) =
      toReplacement := by
  ext context value
  rfl

/-- The induced map retains the given original evidence-bearing total. -/
theorem baseChangeLift_total
    {probe : Face.{uContext, vContext, uBase} Context}
    (toReplacement : probe ⟶ replacementBase)
    (toTotal : probe ⟶ totalSpace originalFamily)
    (compatible : toReplacement ≫ change =
      toTotal ≫ totalProjection originalFamily) :
    baseChangeLift change originalFamily toReplacement toTotal compatible ≫
        totalReindexMap change originalFamily =
      toTotal := by
  ext context value
  exact compatible_lift_at_total change originalFamily toReplacement
    toTotal compatible context value

/-- A semantic dependent term restricts along the induced functor on
categories of elements. The term's actual evidence value is retained. -/
def reindexDisplayedSection (sectionValue : originalFamily.sections) :
    (reindexDisplayed change originalFamily).sections :=
  change.mapElements.sectionsPrecomp sectionValue

@[simp] theorem reindexDisplayedSection_value
    (sectionValue : originalFamily.sections)
    (context : Contextᵒᵖ) (value : replacementBase.obj context) :
    (reindexDisplayedSection change originalFamily sectionValue).val
      ⟨context, value⟩ =
    sectionValue.val ⟨context, change.app context value⟩ := rfl

@[simp] theorem reindexDisplayedSection_id
    {oneBase : Face.{uContext, vContext, uBase} Context}
    (oneFamily : DisplayedFamily.{uContext, vContext, uBase, uBase} oneBase)
    (sectionValue : oneFamily.sections) :
    reindexDisplayedSection (𝟙 oneBase) oneFamily sectionValue =
      sectionValue := by
  apply (Functor.sections_ext_iff).2
  intro point
  rfl

/-- A dependent term's reindexing is coherent with composition of base
substitutions, not merely with one substitution at a time. -/
theorem reindexDisplayedSection_comp
    {finalBase : Face.{uContext, vContext, uBase} Context}
    (later : finalBase ⟶ replacementBase)
    (sectionValue : originalFamily.sections) :
    reindexDisplayedSection (later ≫ change) originalFamily sectionValue =
      reindexDisplayedSection later (reindexDisplayed change originalFamily)
        (reindexDisplayedSection change originalFamily sectionValue) := by
  apply (Functor.sections_ext_iff).2
  intro point
  rfl

/-- Reindexing a term and then embedding it in the extended context
commutes with the base-change map on evidence-bearing totals. -/
theorem reindexDisplayedSection_lift
    (sectionValue : originalFamily.sections) :
    sectionLift (reindexDisplayed change originalFamily)
        (reindexDisplayedSection change originalFamily sectionValue) ≫
        totalReindexMap change originalFamily =
      change ≫ sectionLift originalFamily sectionValue := by
  ext context value
  rfl

/-- Semantic context extension is stable under every natural base change:
the displayed total is the categorical pullback, not only a commuting
square or an objectwise bijection. -/
theorem totalReindexMap_isPullback :
    IsPullback
      (totalProjection (reindexDisplayed change originalFamily))
      (totalReindexMap change originalFamily)
      change (totalProjection originalFamily) := by
  apply IsPullback.mk' (totalReindexMap_square change originalFamily).symm
  · intro probe first second sameBase sameTotal
    ext context value
    apply totalReindexMap_jointly_injective change originalFamily context
    · exact congrArg (fun map => map.app context value) sameBase
    · exact congrArg (fun map => map.app context value) sameTotal
  · intro probe toReplacement toTotal compatible
    exact ⟨baseChangeLift change originalFamily toReplacement toTotal compatible,
      baseChangeLift_base change originalFamily toReplacement toTotal compatible,
      baseChangeLift_total change originalFamily toReplacement toTotal compatible⟩

end ChangeOfBase

section SelfComparison

variable {source target : Face.{uContext, vContext, uBase} Context}
variable (observation : source ⟶ target)

/-- The base change of the observation-fibre projection along the same
observation (canonically the observation's self-pullback) holds two original
values, with an
explicit check that they have the same observed value. Neither original
value is identified with the other. -/
def selfComparisonPoint (context : Contextᵒᵖ)
    (first second : source.obj context)
    (sameObservation : observation.app context first =
      observation.app context second) :
    (totalSpace
      (reindexDisplayed observation
        (observationFibreFamily observation))).obj context :=
  ⟨first, ⟨second, sameObservation.symm⟩⟩

/-- The first projection of the self-comparison retains the first source. -/
theorem selfComparisonPoint_left (context : Contextᵒᵖ)
    (first second : source.obj context)
    (sameObservation : observation.app context first =
      observation.app context second) :
    (totalProjection
      (reindexDisplayed observation
        (observationFibreFamily observation))).app context
        (selfComparisonPoint observation context first second
          sameObservation) = first := rfl

/-- The second projection recovers the second source through the original
observation-fibre total isomorphism. -/
theorem selfComparisonPoint_right (context : Contextᵒᵖ)
    (first second : source.obj context)
    (sameObservation : observation.app context first =
      observation.app context second) :
    (totalReindexMap observation (observationFibreFamily observation) ≫
      (observationTotalIso observation).hom).app context
        (selfComparisonPoint observation context first second
          sameObservation) = second := rfl

/-- If an observation forgets a real distinction, its self-pullback has an
off-diagonal point. Observational equality does not become source equality. -/
theorem selfComparisonPoint_offDiagonal (context : Contextᵒᵖ)
    (first second : source.obj context)
    (sameObservation : observation.app context first =
      observation.app context second)
    (different : first ≠ second) :
    (totalProjection
      (reindexDisplayed observation
        (observationFibreFamily observation))).app context
        (selfComparisonPoint observation context first second
          sameObservation) ≠
      (totalReindexMap observation (observationFibreFamily observation) ≫
        (observationTotalIso observation).hom).app context
          (selfComparisonPoint observation context first second
            sameObservation) := by
  simpa only [selfComparisonPoint_left, selfComparisonPoint_right] using
    different

/-- The existing pointwise-injectivity criterion is precisely the condition
that every point of the observation's self-comparison is diagonal. It is the
licence needed before an observation can reflect ordinary source equality. -/
theorem pointwiseInjective_iff_selfComparison_diagonal :
    PointwiseInjective observation ↔
      ∀ (context : Contextᵒᵖ)
        (receipt :
          (totalSpace
            (reindexDisplayed observation
              (observationFibreFamily observation))).obj context),
        (totalProjection
          (reindexDisplayed observation
            (observationFibreFamily observation))).app context receipt =
          (totalReindexMap observation
              (observationFibreFamily observation) ≫
            (observationTotalIso observation).hom).app context receipt := by
  constructor
  · intro injective context receipt
    rcases receipt with ⟨first, ⟨second, sameObservation⟩⟩
    change first = second
    exact injective context sameObservation.symm
  · intro allDiagonal context first second sameObservation
    have same := allDiagonal context
      (selfComparisonPoint observation context first second sameObservation)
    simpa only [selfComparisonPoint_left, selfComparisonPoint_right] using same

end SelfComparison

#print axioms point
#print axioms projection
#print axioms transportArrow
#print axioms point_injective
#print axioms distinct_points_same_projection
#print axioms totalSpace
#print axioms sectionLift_projection
#print axioms sectionLift_injective
#print axioms sectionEquivProjectionSplittings
#print axioms observationTotalIso
#print axioms observationTotalIso_projection
#print axioms totalReindexMap
#print axioms totalReindexMap_square
#print axioms totalReindexMap_isPullback
#print axioms reindexDisplayed_comp
#print axioms totalReindexMap_comp
#print axioms reindexDisplayedSection_comp
#print axioms reindexDisplayedSection_lift
#print axioms selfComparisonPoint_offDiagonal
#print axioms pointwiseInjective_iff_selfComparison_diagonal

end Mettapedia.TypeTheory.DisplayedPresheafComprehension
