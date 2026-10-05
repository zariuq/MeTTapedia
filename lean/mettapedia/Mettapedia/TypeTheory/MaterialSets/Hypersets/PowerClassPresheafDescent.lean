import Mettapedia.TypeTheory.MaterialSets.Hypersets.PowerClassFamilyDescent
import Mettapedia.TypeTheory.DisplayedPresheafPi
import Mathlib.CategoryTheory.Category.Preorder

/-!
# Contextual material maps without choosing observation representatives

Restriction acts on actual material members in the source families. Its
descent criterion is equality of the output values for equal observations
and equal input values. The descended map is constructed by enumerating all
matching children of all output family graphs over one input class. This
retains the authored source action and proves its contextual comparison.

The decoder, displayed action, section equivalence, native comparison, and
comprehension map use no choice. The final CwF wrappers additionally inherit
the existing host reindexing and right-Kan product dependencies.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.PowerClassPresheafDescent

open AccessiblePointedGraph
open PowerClassFamilyDescent
open Mettapedia.TypeTheory.DependentFamilySectionDescent

universe u v w

section MemberMaps

variable {Source : Type u} {Target : Type v} {Source' : Type u} {Target' : Type w}

abbrev ClassSources {observe : Source → Target} (observed : ObservationClass observe) : Type u :=
  {source : Source // source ∈ observed.1}

def allClass {observe : Source → Target} (observed : ObservationClass observe) :
    ObservationClass (fun _ : ClassSources observed => (PUnit.unit : PUnit.{1})) :=
  ⟨Set.univ, by
    obtain ⟨source, same⟩ := observed.2
    refine ⟨⟨source, by rw [same]; rfl⟩, ?_⟩
    funext other
    exact propext ⟨fun _ => rfl, fun _ => trivial⟩⟩

theorem allClass_beta {observe : Source → Target} (observed : ObservationClass observe)
    (source : ClassSources observed) :
    allClass observed = classOf (fun _ : ClassSources observed => (PUnit.unit : PUnit.{1})) source := by
  apply Subtype.ext
  funext other
  exact propext ⟨fun _ => rfl, fun _ => trivial⟩

def memberAt (observe : Source → Target) (graphs : Source → AccessiblePointedGraph.{u})
    (invariant : FamilyInvariant observe graphs) (observed : ObservationClass observe)
    (member : El (· ∈ ·) (decodedFamily graphs observed)) (source : ClassSources observed) :
    El (· ∈ ·) (HSet.mk (graphs source.1)) :=
  equalityEquiv (congrArg (fun set => El (· ∈ ·) set)
    (family_at_class observe graphs invariant observed source.1 source.2)) member

private theorem transportValue {X Y : HSet.{u}} (same : X = Y) (member : El (· ∈ ·) X) :
    (equalityEquiv (congrArg (fun set => El (· ∈ ·) set) same) member).1 = member.1 := by
  cases same
  rfl

theorem memberAt_value (observe : Source → Target) (graphs : Source → AccessiblePointedGraph.{u})
    (invariant : FamilyInvariant observe graphs) (observed : ObservationClass observe)
    (member : El (· ∈ ·) (decodedFamily graphs observed)) (source : ClassSources observed) :
    (memberAt observe graphs invariant observed member source).1 = member.1 :=
  transportValue (family_at_class observe graphs invariant observed source.1 source.2) member

def MapCompatible (observe : Source → Target) (graphs : Source → AccessiblePointedGraph.{u})
    (baseMap : Source → Source') (graphs' : Source' → AccessiblePointedGraph.{u})
    (operation : ∀ source, El (· ∈ ·) (HSet.mk (graphs source)) →
      El (· ∈ ·) (HSet.mk (graphs' (baseMap source)))) : Prop :=
  ∀ ⦃left right⦄, observe left = observe right →
    ∀ (first : El (· ∈ ·) (HSet.mk (graphs left)))
      (second : El (· ∈ ·) (HSet.mk (graphs right))),
      first.1 = second.1 → (operation left first).1 = (operation right second).1

def localMappedTerm (observe : Source → Target) (graphs : Source → AccessiblePointedGraph.{u})
    (invariant : FamilyInvariant observe graphs) (baseMap : Source → Source')
    (graphs' : Source' → AccessiblePointedGraph.{u})
    (operation : ∀ source, El (· ∈ ·) (HSet.mk (graphs source)) →
      El (· ∈ ·) (HSet.mk (graphs' (baseMap source))))
    (observed : ObservationClass observe) (member : El (· ∈ ·) (decodedFamily graphs observed)) :
    SourceSection (fun source : ClassSources observed => graphs' (baseMap source.1)) :=
  fun source => operation source.1 (memberAt observe graphs invariant observed member source)

theorem localMappedTerm_compatible (observe : Source → Target) (graphs : Source → AccessiblePointedGraph.{u})
    (invariant : FamilyInvariant observe graphs) (baseMap : Source → Source')
    (graphs' : Source' → AccessiblePointedGraph.{u})
    (operation : ∀ source, El (· ∈ ·) (HSet.mk (graphs source)) →
      El (· ∈ ·) (HSet.mk (graphs' (baseMap source))))
    (compatible : MapCompatible observe graphs baseMap graphs' operation)
    (observed : ObservationClass observe) (member : El (· ∈ ·) (decodedFamily graphs observed)) :
    TermCompatible (fun _ : ClassSources observed => (PUnit.unit : PUnit.{1}))
      (fun source => graphs' (baseMap source.1))
      (localMappedTerm observe graphs invariant baseMap graphs' operation observed member) := by
  intro left right _
  have sameClass := (classOf_of_mem observe observed left.1 left.2).trans
    (classOf_of_mem observe observed right.1 right.2).symm
  exact compatible ((classOf_eq_iff observe left.1 right.1).mp sameClass) _ _
    ((memberAt_value observe graphs invariant observed member left).trans
      (memberAt_value observe graphs invariant observed member right).symm)

def mappedValue (observe : Source → Target) (graphs : Source → AccessiblePointedGraph.{u})
    (invariant : FamilyInvariant observe graphs) (baseMap : Source → Source')
    (graphs' : Source' → AccessiblePointedGraph.{u})
    (operation : ∀ source, El (· ∈ ·) (HSet.mk (graphs source)) →
      El (· ∈ ·) (HSet.mk (graphs' (baseMap source))))
    (observed : ObservationClass observe) (member : El (· ∈ ·) (decodedFamily graphs observed)) : HSet.{u} :=
  termValue (fun source : ClassSources observed => graphs' (baseMap source.1))
    (localMappedTerm observe graphs invariant baseMap graphs' operation observed member) (allClass observed)

theorem mappedValue_at (observe : Source → Target) (graphs : Source → AccessiblePointedGraph.{u})
    (invariant : FamilyInvariant observe graphs) (baseMap : Source → Source')
    (graphs' : Source' → AccessiblePointedGraph.{u})
    (operation : ∀ source, El (· ∈ ·) (HSet.mk (graphs source)) →
      El (· ∈ ·) (HSet.mk (graphs' (baseMap source))))
    (compatible : MapCompatible observe graphs baseMap graphs' operation)
    (observed : ObservationClass observe) (member : El (· ∈ ·) (decodedFamily graphs observed))
    (source : ClassSources observed) :
    mappedValue observe graphs invariant baseMap graphs' operation observed member =
      (operation source.1 (memberAt observe graphs invariant observed member source)).1 := by
  unfold mappedValue
  rw [allClass_beta observed source]
  exact termValue_beta _ _ _
    (localMappedTerm_compatible observe graphs invariant baseMap graphs' operation compatible observed member)
    source

/-- The raw member map descends to an actual material function. Its value is
computed from every matching output graph child, with no selected source. -/
def mapMember (observe : Source → Target) (observe' : Source' → Target')
    (baseMap : Source → Source') (targetMap : Target → Target')
    (square : ∀ source, observe' (baseMap source) = targetMap (observe source))
    (graphs : Source → AccessiblePointedGraph.{u}) (invariant : FamilyInvariant observe graphs)
    (graphs' : Source' → AccessiblePointedGraph.{u}) (invariant' : FamilyInvariant observe' graphs')
    (operation : ∀ source, El (· ∈ ·) (HSet.mk (graphs source)) →
      El (· ∈ ·) (HSet.mk (graphs' (baseMap source))))
    (compatible : MapCompatible observe graphs baseMap graphs' operation)
    (observed : ObservationClass observe) (member : El (· ∈ ·) (decodedFamily graphs observed)) :
    El (· ∈ ·) (decodedFamily graphs'
      (classMap observe' observe baseMap targetMap square observed)) :=
  ⟨mappedValue observe graphs invariant baseMap graphs' operation observed member, by
    obtain ⟨source, rfl⟩ := classOf_surjective observe observed
    rw [classMap_beta, family_beta observe' graphs' invariant',
      mappedValue_at observe graphs invariant baseMap graphs' operation compatible _ member ⟨source, rfl⟩]
    exact (operation source (memberAt observe graphs invariant _ member ⟨source, rfl⟩)).2⟩

theorem mapMember_value_at (observe : Source → Target) (observe' : Source' → Target')
    (baseMap : Source → Source') (targetMap : Target → Target')
    (square : ∀ source, observe' (baseMap source) = targetMap (observe source))
    (graphs : Source → AccessiblePointedGraph.{u}) (invariant : FamilyInvariant observe graphs)
    (graphs' : Source' → AccessiblePointedGraph.{u}) (invariant' : FamilyInvariant observe' graphs')
    (operation : ∀ source, El (· ∈ ·) (HSet.mk (graphs source)) →
      El (· ∈ ·) (HSet.mk (graphs' (baseMap source))))
    (compatible : MapCompatible observe graphs baseMap graphs' operation)
    (observed : ObservationClass observe) (member : El (· ∈ ·) (decodedFamily graphs observed))
    (source : ClassSources observed) :
    (mapMember observe observe' baseMap targetMap square graphs invariant graphs' invariant'
      operation compatible observed member).1 =
      (operation source.1 (memberAt observe graphs invariant observed member source)).1 :=
  mappedValue_at observe graphs invariant baseMap graphs' operation compatible observed member source

theorem mapMember_beta_value (observe : Source → Target) (observe' : Source' → Target')
    (baseMap : Source → Source') (targetMap : Target → Target')
    (square : ∀ source, observe' (baseMap source) = targetMap (observe source))
    (graphs : Source → AccessiblePointedGraph.{u}) (invariant : FamilyInvariant observe graphs)
    (graphs' : Source' → AccessiblePointedGraph.{u}) (invariant' : FamilyInvariant observe' graphs')
    (operation : ∀ source, El (· ∈ ·) (HSet.mk (graphs source)) →
      El (· ∈ ·) (HSet.mk (graphs' (baseMap source))))
    (compatible : MapCompatible observe graphs baseMap graphs' operation)
    (source : Source) (member : El (· ∈ ·) (HSet.mk (graphs source))) :
    (mapMember observe observe' baseMap targetMap square graphs invariant graphs' invariant'
      operation compatible (classOf observe source)
      ((familyFactorization observe graphs invariant).identify source member)).1 =
      (operation source member).1 := by
  have input :
      memberAt observe graphs invariant (classOf observe source)
        ((familyFactorization observe graphs invariant).identify source member) ⟨source, rfl⟩ = member :=
    El.ext HSet.propositional ((memberAt_value _ _ _ _ _ _).trans
      (identify_value observe graphs invariant source member))
  exact (mapMember_value_at observe observe' baseMap targetMap square graphs invariant graphs' invariant'
    operation compatible (classOf observe source)
    ((familyFactorization observe graphs invariant).identify source member) ⟨source, rfl⟩).trans
      (congrArg (fun candidate => (operation source candidate).1) input)

/-- The raw fibre law is also necessary for any material map with the exact
source comparison. The forward map is the explicit all-occurrences decoder. -/
theorem mapCompatible_iff_exists_map (observe : Source → Target) (observe' : Source' → Target')
    (baseMap : Source → Source') (targetMap : Target → Target')
    (square : ∀ source, observe' (baseMap source) = targetMap (observe source))
    (graphs : Source → AccessiblePointedGraph.{u}) (invariant : FamilyInvariant observe graphs)
    (graphs' : Source' → AccessiblePointedGraph.{u}) (invariant' : FamilyInvariant observe' graphs')
    (operation : ∀ source, El (· ∈ ·) (HSet.mk (graphs source)) →
      El (· ∈ ·) (HSet.mk (graphs' (baseMap source)))) :
    MapCompatible observe graphs baseMap graphs' operation ↔
      ∃ descended : ∀ observed : ObservationClass observe,
        El (· ∈ ·) (decodedFamily graphs observed) →
          El (· ∈ ·) (decodedFamily graphs' (classMap observe' observe baseMap targetMap square observed)),
      ∀ source member,
        (descended (classOf observe source)
          ((familyFactorization observe graphs invariant).identify source member)).1 =
          (operation source member).1 := by
  constructor
  · intro compatible
    exact ⟨mapMember observe observe' baseMap targetMap square graphs invariant graphs' invariant' operation compatible,
      mapMember_beta_value observe observe' baseMap targetMap square graphs invariant graphs' invariant' operation compatible⟩
  · rintro ⟨descended, reflects⟩ left right related first second sameValue
    have inputs := (totalObservation_eq_iff observe graphs invariant ⟨left, first⟩ ⟨right, second⟩).mpr
      ⟨related, sameValue⟩
    have outputs := congrArg (fun pair => (descended pair.1 pair.2).1) inputs
    exact (reflects left first).symm.trans (outputs.trans (reflects right second))

end MemberMaps

section Contextual

open CategoryTheory
open Mettapedia.TypeTheory.DisplayedPresheafTransport
open Mettapedia.TypeTheory.DisplayedPresheafComprehension

variable {C : Type u} [Category.{u} C]
variable (source target : Cᵒᵖ ⥤ Type u) (observation : NatTrans source target)

theorem observationSquare {X Y : Cᵒᵖ} (step : X ⟶ Y) (value : source.obj X) :
    observation.app Y (source.map step value) = target.map step (observation.app X value) :=
  congrArg (fun map => map value) (observation.naturality step)

/-- The observed contextual base consists of canonical nonempty predicates.
Its substitution maps complete the image to an entire observation fibre. -/
def classFace : Cᵒᵖ ⥤ Type u where
  obj X := ObservationClass (observation.app X)
  map {X Y} step := TypeCat.ofHom
    (classMap (observation.app Y) (observation.app X) (source.map step) (target.map step)
      (observationSquare source target observation step))
  map_id X := by
    apply ConcreteCategory.hom_ext
    intro observed
    obtain ⟨value, rfl⟩ := classOf_surjective (observation.app X) observed
    exact (classMap_beta (observation.app X) (observation.app X) (source.map (𝟙 X))
      (target.map (𝟙 X)) (observationSquare source target observation (𝟙 X)) value).trans
      (congrArg (classOf (observation.app X)) (source.map_id_apply X value))
  map_comp {X Y Z} first second := by
    apply ConcreteCategory.hom_ext
    intro observed
    obtain ⟨value, rfl⟩ := classOf_surjective (observation.app X) observed
    change classMap (observation.app Z) (observation.app X) (source.map (first ≫ second))
        (target.map (first ≫ second)) (observationSquare source target observation (first ≫ second))
        (classOf (observation.app X) value) =
      classMap (observation.app Z) (observation.app Y) (source.map second) (target.map second)
        (observationSquare source target observation second)
        (classMap (observation.app Y) (observation.app X) (source.map first) (target.map first)
          (observationSquare source target observation first)
          (classOf (observation.app X) value))
    rw [classMap_beta, classMap_beta, classMap_beta, source.map_comp_apply]

theorem classFace_map_class {X Y : Cᵒᵖ} (step : X ⟶ Y) (value : source.obj X) :
    (classFace source target observation).map step (classOf (observation.app X) value) =
      classOf (observation.app Y) (source.map step value) :=
  classMap_beta (observation.app Y) (observation.app X) (source.map step) (target.map step)
    (observationSquare source target observation step) value

def classObservation : NatTrans source (classFace source target observation) where
  app X := TypeCat.ofHom (classOf (observation.app X))
  naturality X Y step := by
    apply ConcreteCategory.hom_ext
    intro value
    exact (classFace_map_class source target observation step value).symm

variable (graphs : source.Elements → AccessiblePointedGraph.{u})

/-- Authored material restriction on the retained source occurrences.
The laws concern actual member values; no observed-family map is assumed. -/
structure MaterialTransport where
  invariant : ∀ X, FamilyInvariant (observation.app X) (fun value => graphs ⟨X, value⟩)
  map : ∀ {X Y} (step : X ⟶ Y) (value : source.obj X),
    El (· ∈ ·) (HSet.mk (graphs ⟨X, value⟩)) →
      El (· ∈ ·) (HSet.mk (graphs ⟨Y, source.map step value⟩))
  map_id_value : ∀ X (value : source.obj X) (member : El (· ∈ ·) (HSet.mk (graphs ⟨X, value⟩))),
    (map (𝟙 X) value member).1 = member.1
  map_comp_value : ∀ {X Y Z} (first : X ⟶ Y) (second : Y ⟶ Z)
    (value : source.obj X) (member : El (· ∈ ·) (HSet.mk (graphs ⟨X, value⟩))),
    (map (first ≫ second) value member).1 =
      (map second (source.map first value) (map first value member)).1
  compatible : ∀ {X Y} (step : X ⟶ Y),
    MapCompatible (observation.app X) (fun value => graphs ⟨X, value⟩)
      (source.map step) (fun value => graphs ⟨Y, value⟩) (map step)

variable (transport : MaterialTransport source target observation graphs)

def contextualMemberEquiv (point : (classFace source target observation).Elements) :
    FamilyMemberModel (fun value => graphs ⟨point.1, value⟩) point.2 ≃
      El (· ∈ ·) (decodedFamily (fun value => graphs ⟨point.1, value⟩) point.2) :=
  familyMemberEquiv _ _

def contextualMemberMap {first second : (classFace source target observation).Elements}
    (step : first ⟶ second)
    (member : FamilyMemberModel (fun value => graphs ⟨first.1, value⟩) first.2) :
    FamilyMemberModel (fun value => graphs ⟨second.1, value⟩) second.2 :=
  (contextualMemberEquiv source target observation graphs second).symm
    (equalityEquiv (congrArg (fun observed =>
        El (· ∈ ·) (decodedFamily (fun value => graphs ⟨second.1, value⟩) observed)) step.2)
      (mapMember (observation.app first.1) (observation.app second.1)
        (source.map step.1) (target.map step.1) (observationSquare source target observation step.1)
        (fun value => graphs ⟨first.1, value⟩) (transport.invariant first.1)
        (fun value => graphs ⟨second.1, value⟩) (transport.invariant second.1)
        (transport.map step.1) (transport.compatible step.1) first.2
        (contextualMemberEquiv source target observation graphs first member)))

theorem contextualMemberMap_value {first second : (classFace source target observation).Elements}
    (step : first ⟶ second)
    (member : FamilyMemberModel (fun value => graphs ⟨first.1, value⟩) first.2)
    (value : ClassSources first.2) :
    (contextualMemberEquiv source target observation graphs second
      (contextualMemberMap source target observation graphs transport step member)).1 =
      (transport.map step.1 value.1
        (memberAt (observation.app first.1) (fun candidate => graphs ⟨first.1, candidate⟩)
          (transport.invariant first.1) first.2
          (contextualMemberEquiv source target observation graphs first member) value)).1 := by
  let mapped := mapMember (observation.app first.1) (observation.app second.1)
    (source.map step.1) (target.map step.1) (observationSquare source target observation step.1)
    (fun candidate => graphs ⟨first.1, candidate⟩) (transport.invariant first.1)
    (fun candidate => graphs ⟨second.1, candidate⟩) (transport.invariant second.1)
    (transport.map step.1) (transport.compatible step.1) first.2
    (contextualMemberEquiv source target observation graphs first member)
  let result := equalityEquiv (congrArg (fun observed =>
    El (· ∈ ·) (decodedFamily (fun candidate => graphs ⟨second.1, candidate⟩) observed)) step.2) mapped
  change ((contextualMemberEquiv source target observation graphs second)
    ((contextualMemberEquiv source target observation graphs second).symm result)).1 = _
  have back := congrArg (fun output => output.1)
    ((contextualMemberEquiv source target observation graphs second).apply_symm_apply result)
  refine back.trans ?_
  exact (transportValue (congrArg (decodedFamily (fun candidate => graphs ⟨second.1, candidate⟩)) step.2) _).trans
    (mapMember_value_at _ _ _ _ _ _ _ _ _ _ _ _ _ value)

theorem contextualMemberMap_id (point : (classFace source target observation).Elements)
    (member : FamilyMemberModel (fun value => graphs ⟨point.1, value⟩) point.2) :
    contextualMemberMap source target observation graphs transport (𝟙 point) member = member := by
  apply (contextualMemberEquiv source target observation graphs point).injective
  apply El.ext HSet.propositional
  obtain ⟨value, same⟩ := classOf_surjective (observation.app point.1) point.2
  let atPoint : ClassSources point.2 := ⟨value, by rw [← same]; rfl⟩
  exact (contextualMemberMap_value source target observation graphs transport (𝟙 _) member atPoint).trans
    ((transport.map_id_value _ _ _).trans (memberAt_value _ _ _ _ _ _))

theorem contextualMemberMap_comp {first middle last : (classFace source target observation).Elements}
    (earlier : first ⟶ middle) (later : middle ⟶ last)
    (member : FamilyMemberModel (fun value => graphs ⟨first.1, value⟩) first.2) :
    contextualMemberMap source target observation graphs transport (earlier ≫ later) member =
      contextualMemberMap source target observation graphs transport later
        (contextualMemberMap source target observation graphs transport earlier member) := by
  apply (contextualMemberEquiv source target observation graphs last).injective
  apply El.ext HSet.propositional
  obtain ⟨value, same⟩ := classOf_surjective (observation.app first.1) first.2
  let atFirst : ClassSources first.2 := ⟨value, by
    rw [← same]
    rfl⟩
  have middleClass : classOf (observation.app middle.1) (source.map earlier.1 value) = middle.2 :=
    (classFace_map_class source target observation earlier.1 value).symm.trans
      ((congrArg ((classFace source target observation).map earlier.1) same).trans earlier.2)
  let atMiddle : ClassSources middle.2 := ⟨source.map earlier.1 value, by
    have predicates := congrArg Subtype.val middleClass
    rw [← predicates]
    rfl⟩
  let input := memberAt (observation.app first.1) (fun candidate => graphs ⟨first.1, candidate⟩)
    (transport.invariant first.1) first.2
    (contextualMemberEquiv source target observation graphs first member) atFirst
  have middleInput :
      memberAt (observation.app middle.1) (fun candidate => graphs ⟨middle.1, candidate⟩)
        (transport.invariant middle.1) middle.2
        (contextualMemberEquiv source target observation graphs middle
          (contextualMemberMap source target observation graphs transport earlier member)) atMiddle =
      transport.map earlier.1 value input :=
    El.ext HSet.propositional ((memberAt_value _ _ _ _ _ _).trans
      (contextualMemberMap_value source target observation graphs transport earlier member atFirst))
  exact (contextualMemberMap_value source target observation graphs transport (earlier ≫ later) member atFirst).trans
    ((transport.map_comp_value earlier.1 later.1 value input).trans
      ((congrArg (fun candidate => (transport.map later.1 (source.map earlier.1 value) candidate).1)
        middleInput).symm.trans
          (contextualMemberMap_value source target observation graphs transport later _ atMiddle).symm))

/-- A genuine displayed presheaf of actual material fibres, represented at
the original graph universe by their canonical member-class carriers. -/
def observedDisplayed : DisplayedFamily.{u, u, u, u} (classFace source target observation) where
  obj point := FamilyMemberModel (fun value => graphs ⟨point.1, value⟩) point.2
  map step := TypeCat.ofHom (contextualMemberMap source target observation graphs transport step)
  map_id point := by
    apply ConcreteCategory.hom_ext
    exact contextualMemberMap_id source target observation graphs transport point
  map_comp first second := by
    apply ConcreteCategory.hom_ext
    exact contextualMemberMap_comp source target observation graphs transport first second

abbrev RawSection := (point : source.Elements) → El (· ∈ ·) (HSet.mk (graphs point))

/-- Both the selected-value fibre law and authored restriction naturality are
required. Pointwise support, or family invariance alone, implies neither. -/
def ContextualCompatible (term : RawSection source graphs) : Prop :=
  (∀ X, TermCompatible (observation.app X) (fun value => graphs ⟨X, value⟩)
    (fun value => term ⟨X, value⟩)) ∧
  ∀ {X Y} (step : X ⟶ Y) (value : source.obj X),
    (transport.map step value (term ⟨X, value⟩)).1 = (term ⟨Y, source.map step value⟩).1

def pullContextualSection (term : (observedDisplayed source target observation graphs transport).sections) :
    RawSection source graphs :=
  fun point => pullSection (observation.app point.1) (fun value => graphs ⟨point.1, value⟩)
    (transport.invariant point.1)
    (fun observed => contextualMemberEquiv source target observation graphs ⟨point.1, observed⟩
      (term.val ⟨point.1, observed⟩)) point.2

theorem pullContextualSection_value
    (term : (observedDisplayed source target observation graphs transport).sections)
    (point : source.Elements) :
    (pullContextualSection source target observation graphs transport term point).1 =
      (contextualMemberEquiv source target observation graphs
        ⟨point.1, classOf (observation.app point.1) point.2⟩
        (term.val ⟨point.1, classOf (observation.app point.1) point.2⟩)).1 :=
  pullSection_value _ _ _ _ _

theorem pullContextualSection_compatible
    (term : (observedDisplayed source target observation graphs transport).sections) :
    ContextualCompatible source target observation graphs transport
      (pullContextualSection source target observation graphs transport term) := by
  constructor
  · intro X
    exact pullSection_compatible (observation.app X) (fun value => graphs ⟨X, value⟩)
      (transport.invariant X) (fun observed => contextualMemberEquiv source target observation graphs
        ⟨X, observed⟩ (term.val ⟨X, observed⟩))
  · intro X Y step value
    let first : (classFace source target observation).Elements := ⟨X, classOf (observation.app X) value⟩
    let second : (classFace source target observation).Elements :=
      ⟨Y, classOf (observation.app Y) (source.map step value)⟩
    let arrow : first ⟶ second :=
      ⟨step, classFace_map_class source target observation step value⟩
    have sourceInput :
        memberAt (observation.app X) (fun candidate => graphs ⟨X, candidate⟩)
          (transport.invariant X) first.2
          (contextualMemberEquiv source target observation graphs first (term.val first)) ⟨value, rfl⟩ =
        pullContextualSection source target observation graphs transport term ⟨X, value⟩ :=
      El.ext HSet.propositional ((memberAt_value _ _ _ _ _ _).trans
        (pullContextualSection_value source target observation graphs transport term ⟨X, value⟩).symm)
    have natural := congrArg (fun member =>
      (contextualMemberEquiv source target observation graphs second member).1) (term.property arrow)
    exact (congrArg (fun member => (transport.map step value member).1) sourceInput).symm.trans
      ((contextualMemberMap_value source target observation graphs transport arrow (term.val first)
        ⟨value, rfl⟩).symm.trans
          (natural.trans (pullContextualSection_value source target observation graphs transport term
            ⟨Y, source.map step value⟩).symm))

def decodedContextualTerm (term : RawSection source graphs)
    (compatible : ContextualCompatible source target observation graphs transport term)
    (point : (classFace source target observation).Elements) :
    El (· ∈ ·) (decodedFamily (fun value => graphs ⟨point.1, value⟩) point.2) :=
  descendTerm (observation.app point.1) (fun value => graphs ⟨point.1, value⟩)
    (transport.invariant point.1) (fun value => term ⟨point.1, value⟩) (compatible.1 point.1) point.2

theorem decodedContextualTerm_value_at (term : RawSection source graphs)
    (compatible : ContextualCompatible source target observation graphs transport term)
    (point : (classFace source target observation).Elements) (value : ClassSources point.2) :
    (decodedContextualTerm source target observation graphs transport term compatible point).1 =
      (term ⟨point.1, value.1⟩).1 := by
  have same := classOf_of_mem (observation.app point.1) point.2 value.1 value.2
  exact (congrArg (fun observed => (descendTerm (observation.app point.1)
    (fun candidate => graphs ⟨point.1, candidate⟩) (transport.invariant point.1)
    (fun candidate => term ⟨point.1, candidate⟩) (compatible.1 point.1) observed).1) same.symm).trans
      (descendTerm_beta_value _ _ _ _ _ value.1)

def contextualTermModel (term : RawSection source graphs)
    (compatible : ContextualCompatible source target observation graphs transport term)
    (point : (classFace source target observation).Elements) :
    (observedDisplayed source target observation graphs transport).obj point :=
  (contextualMemberEquiv source target observation graphs point).symm
    (decodedContextualTerm source target observation graphs transport term compatible point)

theorem contextualTermModel_value (term : RawSection source graphs)
    (compatible : ContextualCompatible source target observation graphs transport term)
    (point : (classFace source target observation).Elements) :
    contextualMemberEquiv source target observation graphs point
      (contextualTermModel source target observation graphs transport term compatible point) =
      decodedContextualTerm source target observation graphs transport term compatible point :=
  (contextualMemberEquiv source target observation graphs point).apply_symm_apply _

theorem contextualTermModel_natural (term : RawSection source graphs)
    (compatible : ContextualCompatible source target observation graphs transport term)
    {first second : (classFace source target observation).Elements} (step : first ⟶ second) :
    (observedDisplayed source target observation graphs transport).map step
        (contextualTermModel source target observation graphs transport term compatible first) =
      contextualTermModel source target observation graphs transport term compatible second := by
  apply (contextualMemberEquiv source target observation graphs second).injective
  apply El.ext HSet.propositional
  obtain ⟨value, same⟩ := classOf_surjective (observation.app first.1) first.2
  let atFirst : ClassSources first.2 := ⟨value, by rw [← same]; rfl⟩
  have secondClass : classOf (observation.app second.1) (source.map step.1 value) = second.2 :=
    (classFace_map_class source target observation step.1 value).symm.trans
      ((congrArg ((classFace source target observation).map step.1) same).trans step.2)
  let atSecond : ClassSources second.2 := ⟨source.map step.1 value, by
    have predicates := congrArg Subtype.val secondClass
    rw [← predicates]
    rfl⟩
  have sourceInput :
      memberAt (observation.app first.1) (fun candidate => graphs ⟨first.1, candidate⟩)
        (transport.invariant first.1) first.2
        (contextualMemberEquiv source target observation graphs first
          (contextualTermModel source target observation graphs transport term compatible first)) atFirst =
      term ⟨first.1, value⟩ :=
    El.ext HSet.propositional ((memberAt_value _ _ _ _ _ _).trans
      ((congrArg (fun member => member.1)
        (contextualTermModel_value source target observation graphs transport term compatible first)).trans
        (decodedContextualTerm_value_at source target observation graphs transport term compatible first atFirst)))
  exact (contextualMemberMap_value source target observation graphs transport step _ atFirst).trans
    ((congrArg (fun member => (transport.map step.1 value member).1) sourceInput).trans
      ((compatible.2 step.1 value).trans
        ((decodedContextualTerm_value_at source target observation graphs transport term compatible second atSecond).symm.trans
          (congrArg (fun member => member.1)
            (contextualTermModel_value source target observation graphs transport term compatible second)).symm)))

def descendContextualSection (term : RawSection source graphs)
    (compatible : ContextualCompatible source target observation graphs transport term) :
    (observedDisplayed source target observation graphs transport).sections :=
  ⟨contextualTermModel source target observation graphs transport term compatible,
    by
      intro _ _ step
      exact contextualTermModel_natural source target observation graphs transport term compatible step⟩

theorem pull_descendContextualSection (term : RawSection source graphs)
    (compatible : ContextualCompatible source target observation graphs transport term) :
    pullContextualSection source target observation graphs transport
      (descendContextualSection source target observation graphs transport term compatible) = term := by
  funext point
  apply El.ext HSet.propositional
  let observedPoint : (classFace source target observation).Elements :=
    ⟨point.1, classOf (observation.app point.1) point.2⟩
  exact (pullContextualSection_value source target observation graphs transport _ point).trans
    ((congrArg (fun member => member.1)
      (contextualTermModel_value source target observation graphs transport term compatible observedPoint)).trans
      (decodedContextualTerm_value_at source target observation graphs transport term compatible
        ⟨point.1, classOf (observation.app point.1) point.2⟩ ⟨point.2, rfl⟩))

theorem descend_pullContextualSection
    (term : (observedDisplayed source target observation graphs transport).sections) :
    descendContextualSection source target observation graphs transport
      (pullContextualSection source target observation graphs transport term)
      (pullContextualSection_compatible source target observation graphs transport term) = term := by
  apply Subtype.ext
  funext point
  apply (contextualMemberEquiv source target observation graphs point).injective
  apply El.ext HSet.propositional
  obtain ⟨value, same⟩ := classOf_surjective (observation.app point.1) point.2
  let atPoint : ClassSources point.2 := ⟨value, by rw [← same]; rfl⟩
  have observationPoint :
      (⟨point.1, classOf (observation.app point.1) value⟩ :
        (classFace source target observation).Elements) = point := by
    exact Sigma.ext rfl (heq_of_eq same)
  exact (congrArg (fun member => member.1)
    (contextualTermModel_value source target observation graphs transport
      (pullContextualSection source target observation graphs transport term)
      (pullContextualSection_compatible source target observation graphs transport term) point)).trans
    ((decodedContextualTerm_value_at source target observation graphs transport _ _ point atPoint).trans
      ((pullContextualSection_value source target observation graphs transport term ⟨point.1, value⟩).trans
        (congrArg (fun point => (contextualMemberEquiv source target observation graphs point (term.val point)).1)
          observationPoint)))

/-- Genuine natural sections of the constructed displayed family are exactly
source sections satisfying fibre compatibility and restriction naturality. -/
def contextualSectionEquiv :
    (observedDisplayed source target observation graphs transport).sections ≃
      {term : RawSection source graphs // ContextualCompatible source target observation graphs transport term} where
  toFun term := ⟨pullContextualSection source target observation graphs transport term,
    pullContextualSection_compatible source target observation graphs transport term⟩
  invFun term := descendContextualSection source target observation graphs transport term.1 term.2
  left_inv := descend_pullContextualSection source target observation graphs transport
  right_inv term := Subtype.ext (pull_descendContextualSection source target observation graphs transport term.1 term.2)

/-- Explicit source substitution on observation classes, with no selection
helper from the functor-category infrastructure. -/
def classElements : source.Elements ⥤ (classFace source target observation).Elements where
  obj point := ⟨point.1, classOf (observation.app point.1) point.2⟩
  map {first second} step := ⟨step.1,
    (classFace_map_class source target observation step.1 first.2).trans
      (congrArg (classOf (observation.app second.1)) step.2)⟩
  map_id _ := rfl
  map_comp _ _ := rfl

def sourceMaterialMemberEquiv (point : source.Elements) :
    PowerMemberClass (graphs point) ≃ El (· ∈ ·) (HSet.mk (graphs point)) :=
  (powerElEquiv (graphs point)).trans
    (equalityEquiv (congrArg (fun set => El (· ∈ ·) set) (picture_eq_mk (graphs point))))

/-- Native graph-member classes and the independently decoded observed
member classes have the same actual material inhabitants. -/
def sourceFibreEquiv (point : source.Elements) :
    PowerMemberClass (graphs point) ≃
      (observedDisplayed source target observation graphs transport).obj
        ((classElements source target observation).obj point) :=
  (sourceMaterialMemberEquiv source graphs point).trans
    (((familyFactorization (observation.app point.1) (fun value => graphs ⟨point.1, value⟩)
      (transport.invariant point.1)).identify point.2).trans
        (contextualMemberEquiv source target observation graphs
          ((classElements source target observation).obj point)).symm)

theorem sourceFibreEquiv_value (point : source.Elements) (member : PowerMemberClass (graphs point)) :
    (contextualMemberEquiv source target observation graphs
      ((classElements source target observation).obj point)
      (sourceFibreEquiv source target observation graphs transport point member)).1 =
      (sourceMaterialMemberEquiv source graphs point member).1 := by
  change ((contextualMemberEquiv source target observation graphs
    ((classElements source target observation).obj point))
    ((contextualMemberEquiv source target observation graphs
      ((classElements source target observation).obj point)).symm
      ((familyFactorization (observation.app point.1) (fun value => graphs ⟨point.1, value⟩)
        (transport.invariant point.1)).identify point.2
        (sourceMaterialMemberEquiv source graphs point member)))).1 = _
  exact (congrArg (fun result => result.1)
    ((contextualMemberEquiv source target observation graphs
      ((classElements source target observation).obj point)).apply_symm_apply _)).trans
        (identify_value _ _ _ _ _)

private def conjugateFamily {D : Type*} [Category D] (family : D ⥤ Type u)
    (fibres : D → Type u) (identify : ∀ point, fibres point ≃ family.obj point) : D ⥤ Type u where
  obj := fibres
  map {first second} step := TypeCat.ofHom
    (fun member => (identify second).symm (family.map step (identify first member)))
  map_id point := by
    apply ConcreteCategory.hom_ext
    intro member
    change (identify point).symm (family.map (𝟙 point) (identify point member)) = member
    rw [family.map_id_apply, Equiv.symm_apply_apply]
  map_comp {first middle last} earlier later := by
    apply ConcreteCategory.hom_ext
    intro member
    change (identify last).symm (family.map (earlier ≫ later) (identify first member)) =
      (identify last).symm
        (family.map later (identify middle ((identify middle).symm (family.map earlier (identify first member)))))
    rw [Equiv.apply_symm_apply, family.map_comp_apply]

/-- Reindex the independently decoded observed family with explicit maps. -/
def sourceObservedReindex : DisplayedFamily.{u, u, u, u} source where
  obj point := (observedDisplayed source target observation graphs transport).obj
    ((classElements source target observation).obj point)
  map step := (observedDisplayed source target observation graphs transport).map
    ((classElements source target observation).map step)
  map_id point := by
    rw [(classElements source target observation).map_id]
    exact (observedDisplayed source target observation graphs transport).map_id _
  map_comp first second := by
    rw [(classElements source target observation).map_comp]
    exact (observedDisplayed source target observation graphs transport).map_comp _ _

/- Explicit reindexing avoids the general Functor.comp wrapper's host choice
dependency; the action itself is exactly the category-of-elements action. -/
/-- The native displayed family has the original graph-member carriers.
Its action is conjugated through the proved actual decoder; the following
value comparison verifies it against the authored raw restrictions. -/
def nativeSourceDisplayed : DisplayedFamily.{u, u, u, u} source :=
  conjugateFamily
    (sourceObservedReindex source target observation graphs transport)
    (fun point => PowerMemberClass (graphs point))
    (sourceFibreEquiv source target observation graphs transport)

def nativeToObservedReindex : NatTrans (nativeSourceDisplayed source target observation graphs transport)
    (sourceObservedReindex source target observation graphs transport) where
  app point := TypeCat.ofHom (sourceFibreEquiv source target observation graphs transport point)
  naturality first second step := by
    apply ConcreteCategory.hom_ext
    intro member
    exact (sourceFibreEquiv source target observation graphs transport second).apply_symm_apply _

def nativeFromObservedReindex : NatTrans
    (sourceObservedReindex source target observation graphs transport)
    (nativeSourceDisplayed source target observation graphs transport) where
  app point := TypeCat.ofHom (sourceFibreEquiv source target observation graphs transport point).symm
  naturality first second step := by
    apply ConcreteCategory.hom_ext
    intro member
    exact congrArg (fun candidate =>
      (sourceFibreEquiv source target observation graphs transport second).symm
        ((observedDisplayed source target observation graphs transport).map
          ((classElements source target observation).map step) candidate))
      ((sourceFibreEquiv source target observation graphs transport first).apply_symm_apply member).symm

theorem nativeReindex_left_inverse (point : source.Elements) (member : PowerMemberClass (graphs point)) :
    (nativeFromObservedReindex source target observation graphs transport).app point
      ((nativeToObservedReindex source target observation graphs transport).app point member) = member :=
  (sourceFibreEquiv source target observation graphs transport point).symm_apply_apply member

theorem nativeReindex_right_inverse (point : source.Elements)
    (member : (observedDisplayed source target observation graphs transport).obj
      ((classElements source target observation).obj point)) :
    (nativeToObservedReindex source target observation graphs transport).app point
      ((nativeFromObservedReindex source target observation graphs transport).app point member) = member :=
  (sourceFibreEquiv source target observation graphs transport point).apply_symm_apply member

theorem nativeSourceDisplayed_map_value {first second : source.Elements} (step : first ⟶ second)
    (member : PowerMemberClass (graphs first)) :
    (sourceMaterialMemberEquiv source graphs second
      ((nativeSourceDisplayed source target observation graphs transport).map step member)).1 =
      (transport.map step.1 first.2 (sourceMaterialMemberEquiv source graphs first member)).1 := by
  have input :
      memberAt (observation.app first.1) (fun value => graphs ⟨first.1, value⟩)
        (transport.invariant first.1) (classOf (observation.app first.1) first.2)
        (contextualMemberEquiv source target observation graphs
          ((classElements source target observation).obj first)
          (sourceFibreEquiv source target observation graphs transport first member)) ⟨first.2, rfl⟩ =
      sourceMaterialMemberEquiv source graphs first member :=
    El.ext HSet.propositional ((memberAt_value _ _ _ _ _ _).trans
      (sourceFibreEquiv_value source target observation graphs transport first member))
  exact (sourceFibreEquiv_value source target observation graphs transport second _).symm.trans
    ((congrArg (fun result => (contextualMemberEquiv source target observation graphs
      ((classElements source target observation).obj second) result).1)
      (congrArg (fun map => map member)
        ((nativeToObservedReindex source target observation graphs transport).naturality step))).trans
      ((contextualMemberMap_value source target observation graphs transport
        ((classElements source target observation).map step)
        (sourceFibreEquiv source target observation graphs transport first member) ⟨first.2, rfl⟩).trans
          (congrArg (fun candidate => (transport.map step.1 first.2 candidate).1) input)))

private theorem observedMap_heq
    {first second other : (classFace source target observation).Elements}
    (same : second = other) (left : first ⟶ second) (right : first ⟶ other)
    (sameArrow : HEq left.1 right.1)
    (member : (observedDisplayed source target observation graphs transport).obj first) :
    HEq ((observedDisplayed source target observation graphs transport).map left member)
      ((observedDisplayed source target observation graphs transport).map right member) := by
  cases same
  have arrows : left = right := Subtype.ext (eq_of_heq sameArrow)
  cases arrows
  rfl

/-- Actual comprehension readout changes the base observation and carries
the decoded material member. The substitution proof retains both fields. -/
def comprehensionReadout : NatTrans
    (totalSpace (nativeSourceDisplayed source target observation graphs transport))
    (totalSpace (observedDisplayed source target observation graphs transport)) where
  app X := TypeCat.ofHom (fun receipt =>
    ⟨classOf (observation.app X) receipt.1,
      sourceFibreEquiv source target observation graphs transport ⟨X, receipt.1⟩ receipt.2⟩)
  naturality X Y step := by
    apply ConcreteCategory.hom_ext
    rintro ⟨value, member⟩
    let sourceArrow := CategoryOfElements.homMk (F := source)
      (source.elementsMk X value) (source.elementsMk Y (source.map step value)) step rfl
    let first : (classFace source target observation).Elements := ⟨X, classOf (observation.app X) value⟩
    let afterMap : (classFace source target observation).Elements :=
      ⟨Y, (classFace source target observation).map step first.2⟩
    let afterObserve : (classFace source target observation).Elements :=
      ⟨Y, classOf (observation.app Y) (source.map step value)⟩
    have same : afterMap = afterObserve :=
      Sigma.ext rfl (heq_of_eq (classFace_map_class source target observation step value))
    have transformed := observedMap_heq source target observation graphs transport same
      (CategoryOfElements.homMk _ _ step rfl)
      ((classElements source target observation).map sourceArrow)
      (heq_of_eq rfl) (sourceFibreEquiv source target observation graphs transport ⟨X, value⟩ member)
    have natural := congrArg (fun map => map member)
      ((nativeToObservedReindex source target observation graphs transport).naturality sourceArrow)
    exact Sigma.ext (classFace_map_class source target observation step value).symm
      ((heq_of_eq natural).trans transformed.symm)

theorem comprehensionReadout_projection (X : Cᵒᵖ)
    (receipt : TotalAt (nativeSourceDisplayed source target observation graphs transport) X) :
    ((comprehensionReadout source target observation graphs transport).app X receipt).1 =
      (classObservation source target observation).app X receipt.1 := rfl

theorem comprehensionReadout_member_value (X : Cᵒᵖ)
    (receipt : TotalAt (nativeSourceDisplayed source target observation graphs transport) X) :
    (contextualMemberEquiv source target observation graphs
      ⟨X, classOf (observation.app X) receipt.1⟩
      ((comprehensionReadout source target observation graphs transport).app X receipt).2).1 =
      (sourceMaterialMemberEquiv source graphs ⟨X, receipt.1⟩ receipt.2).1 :=
  sourceFibreEquiv_value source target observation graphs transport ⟨X, receipt.1⟩ receipt.2

theorem comprehensionReadout_eq_iff (X : Cᵒᵖ)
    (left right : TotalAt (nativeSourceDisplayed source target observation graphs transport) X) :
    (comprehensionReadout source target observation graphs transport).app X left =
        (comprehensionReadout source target observation graphs transport).app X right ↔
      observation.app X left.1 = observation.app X right.1 ∧
        (sourceMaterialMemberEquiv source graphs ⟨X, left.1⟩ left.2).1 =
          (sourceMaterialMemberEquiv source graphs ⟨X, right.1⟩ right.2).1 := by
  let decode := observedComprehensionEquiv (observation.app X) (fun value => graphs ⟨X, value⟩)
  have injective :
      decode ((comprehensionReadout source target observation graphs transport).app X left) =
        decode ((comprehensionReadout source target observation graphs transport).app X right) ↔
      (comprehensionReadout source target observation graphs transport).app X left =
        (comprehensionReadout source target observation graphs transport).app X right :=
    decode.injective.eq_iff
  refine injective.symm.trans ?_
  refine (totalElPair_eq_iff (decodedFamily (fun value => graphs ⟨X, value⟩)) _ _).trans ?_
  change classOf (observation.app X) left.1 = classOf (observation.app X) right.1 ∧
    (contextualMemberEquiv source target observation graphs ⟨X, classOf (observation.app X) left.1⟩
      ((comprehensionReadout source target observation graphs transport).app X left).2).1 =
    (contextualMemberEquiv source target observation graphs ⟨X, classOf (observation.app X) right.1⟩
      ((comprehensionReadout source target observation graphs transport).app X right).2).1 ↔ _
  rw [classOf_eq_iff, comprehensionReadout_member_value, comprehensionReadout_member_value]

end Contextual

section ExistingCwf

open CategoryTheory
open Mettapedia.TypeTheory.DisplayedPresheafTransport
open Mettapedia.TypeTheory.DisplayedPresheafComprehension
open Mettapedia.TypeTheory.DisplayedPresheafCwf
open Mettapedia.TypeTheory.DisplayedPresheafPi

variable {C : Type u} [Category.{u} C]
variable (source target : Cᵒᵖ ⥤ Type u) (observation : NatTrans source target)
variable (graphs : source.Elements → AccessiblePointedGraph.{u})
variable (transport : MaterialTransport source target observation graphs)

/-- The native carrier comparison also targets the actual existing CwF
reindexing operation. The latter uses Mathlib's mapElements wrapper. -/
def nativeToCwfReindex : NatTrans (nativeSourceDisplayed source target observation graphs transport)
    (reindexDisplayed (classObservation source target observation)
      (observedDisplayed source target observation graphs transport)) :=
  nativeToObservedReindex source target observation graphs transport

def nativeFromCwfReindex : NatTrans
    (reindexDisplayed (classObservation source target observation)
      (observedDisplayed source target observation graphs transport))
    (nativeSourceDisplayed source target observation graphs transport) :=
  nativeFromObservedReindex source target observation graphs transport

theorem identityApplicationFamily
    (argument : (observedDisplayed source target observation graphs transport).sections) :
    reindexDisplayed (sectionLift (observedDisplayed source target observation graphs transport) argument)
      (reindexDisplayed (totalProjection (observedDisplayed source target observation graphs transport))
        (observedDisplayed source target observation graphs transport)) =
      observedDisplayed source target observation graphs transport := by
  rw [← reindexDisplayed_comp, sectionLift_projection, reindexDisplayed_id]

/-- A concrete function in w12's full contextual dependent product. Its body
is the actual material last variable, not a pointwise function substituted
for the right-Kan product. -/
noncomputable def contextualIdentityFunction :
    (piDisplayed (observedDisplayed source target observation graphs transport)
      (reindexDisplayed (totalProjection (observedDisplayed source target observation graphs transport))
        (observedDisplayed source target observation graphs transport))).sections :=
  lamDisplayed (presheafVariable (observedDisplayed source target observation graphs transport))

noncomputable def contextualIdentityApplication
    (argument : (observedDisplayed source target observation graphs transport).sections) :
    (observedDisplayed source target observation graphs transport).sections :=
  identityApplicationFamily source target observation graphs transport argument ▸
    appDisplayed (contextualIdentityFunction source target observation graphs transport) argument

theorem contextualIdentityApplication_eq
    (argument : (observedDisplayed source target observation graphs transport).sections) :
    contextualIdentityApplication source target observation graphs transport argument = argument := by
  apply Subtype.ext
  funext point
  have castValue := sectionCast_value_heq
    (identityApplicationFamily source target observation graphs transport argument)
    (appDisplayed (contextualIdentityFunction source target observation graphs transport) argument) point
  have application := congrArg (fun sectionValue => sectionValue.val point)
    (pi_beta (presheafVariable (observedDisplayed source target observation graphs transport)) argument)
  exact eq_of_heq (castValue.trans (heq_of_eq application))

/-- The full contextual product's concrete lambda/application returns the
original compatible authored section, including its material member values. -/
theorem contextualIdentity_source_beta (term : RawSection source graphs)
    (compatible : ContextualCompatible source target observation graphs transport term) :
    pullContextualSection source target observation graphs transport
      (contextualIdentityApplication source target observation graphs transport
        (descendContextualSection source target observation graphs transport term compatible)) = term := by
  rw [contextualIdentityApplication_eq]
  exact pull_descendContextualSection source target observation graphs transport term compatible

end ExistingCwf

namespace Controls

open CategoryTheory
open PowerClassFamilyDescent.Controls

abbrev Stages := ℕᵒᵖ

def world (stage : ℕ) : Stagesᵒᵖ := Opposite.op (Opposite.op stage)

def stageIndex (point : Stagesᵒᵖ) : ℕ := point.unop.unop

theorem growthLe {first second : Stagesᵒᵖ} (step : first ⟶ second) :
    stageIndex first ≤ stageIndex second := leOfHom step.unop.unop

/-- New base values genuinely appear at later contexts. The second coordinate
retains a source tag, which the observation erases. -/
def growingSource : Stagesᵒᵖ ⥤ Type where
  obj point := Fin (stageIndex point + 1) × Bool
  map step := TypeCat.ofHom (fun value =>
    (value.1.castLE (Nat.succ_le_succ (growthLe step)), value.2))
  map_id _ := by
    apply ConcreteCategory.hom_ext
    intro value
    exact Prod.ext (Fin.ext rfl) rfl
  map_comp _ _ := by
    apply ConcreteCategory.hom_ext
    intro value
    exact Prod.ext (Fin.ext rfl) rfl

def growingTarget : Stagesᵒᵖ ⥤ Type where
  obj point := Fin (stageIndex point + 1)
  map step := TypeCat.ofHom (fun value => value.castLE (Nat.succ_le_succ (growthLe step)))
  map_id _ := by
    apply ConcreteCategory.hom_ext
    intro value
    exact Fin.ext rfl
  map_comp _ _ := by
    apply ConcreteCategory.hom_ext
    intro value
    exact Fin.ext rfl

def growingObservation : NatTrans growingSource growingTarget where
  app _ := TypeCat.ofHom Prod.fst
  naturality _ _ _ := rfl

def stageValue (level index : ℕ) (bound : index < level + 1) (tag : Bool) :
    growingSource.obj (world level) := (⟨index, bound⟩, tag)

def growingGraphs (point : growingSource.Elements) : AccessiblePointedGraph :=
  if point.2.1.val = 0 then empty else HSet.loop

def growingTransport : MaterialTransport growingSource growingTarget growingObservation growingGraphs where
  invariant point := by
    intro left right same
    exact congrArg (fun index => HSet.mk (if index.val = 0 then empty else HSet.loop)) same
  map _ _ member := member
  map_id_value _ _ _ := rfl
  map_comp_value _ _ _ _ := rfl
  compatible _ := by
    intro _ _ _ _ _ same
    exact same

theorem growing_empty :
    decodedFamily (fun value => growingGraphs ⟨world 0, value⟩)
      (classOf (growingObservation.app (world 0)) (stageValue 0 0 (by omega) true)) = ∅ := by
  exact (family_beta _ _ (growingTransport.invariant _) _).trans HSet.mk_empty

theorem growing_cyclic :
    decodedFamily (fun value => growingGraphs ⟨world 1, value⟩)
      (classOf (growingObservation.app (world 1)) (stageValue 1 1 (by omega) false)) = HSet.quineAtom := by
  exact (family_beta _ _ (growingTransport.invariant _) _).trans HSet.mk_loop

theorem growing_family_nonconstant :
    decodedFamily (fun value => growingGraphs ⟨world 0, value⟩)
        (classOf (growingObservation.app (world 0)) (stageValue 0 0 (by omega) true)) ≠
      decodedFamily (fun value => growingGraphs ⟨world 1, value⟩)
        (classOf (growingObservation.app (world 1)) (stageValue 1 1 (by omega) false)) := by
  rw [growing_empty, growing_cyclic]
  exact HSet.empty_ne_quineAtom

theorem new_value_not_old_image :
    ¬ ∃ value : growingSource.obj (world 0),
      growingSource.map ((homOfLE (show 0 ≤ 1 by omega)).op.op) value =
        stageValue 1 1 (by omega) false := by
  rintro ⟨value, same⟩
  have impossible := congrArg (fun value => value.1.val) same
  have bound := value.1.isLt
  change value.1.val < 1 at bound
  change value.1.val = 1 at impossible
  omega

def alternativeGraphs (_point : growingSource.Elements) : AccessiblePointedGraph := alternatives

def alternativeTransport :
    MaterialTransport growingSource growingTarget growingObservation alternativeGraphs where
  invariant _ := by intro _ _ _; rfl
  map _ _ member := member
  map_id_value _ _ _ := rfl
  map_comp_value _ _ _ _ := rfl
  compatible _ := by intro _ _ _ _ _ same; exact same

def tagTerm (point : growingSource.Elements) : El (· ∈ ·) (HSet.mk (alternativeGraphs point)) :=
  ⟨HSet.mk (selectedGraph point.2.2), HSet.mem_range.mpr ⟨⟨point.2.2⟩, rfl⟩⟩

theorem tagTerm_natural {first second : Stagesᵒᵖ} (step : first ⟶ second)
    (value : growingSource.obj first) :
    (alternativeTransport.map step value (tagTerm ⟨first, value⟩)).1 =
      (tagTerm ⟨second, growingSource.map step value⟩).1 := rfl

theorem tagTerm_not_contextually_compatible :
    ¬ ContextualCompatible growingSource growingTarget growingObservation alternativeGraphs
      alternativeTransport tagTerm := by
  intro compatible
  have same := compatible.1 (world 0)
    (left := stageValue 0 0 (by omega) true) (right := stageValue 0 0 (by omega) false) rfl
  have trueValue : (tagTerm ⟨world 0, stageValue 0 0 (by omega) true⟩).1 = ({∅} : HSet) :=
    (picture_eq_mk _).symm.trans picture_oneChild_empty
  have falseValue : (tagTerm ⟨world 0, stageValue 0 0 (by omega) false⟩).1 = (∅ : HSet) := HSet.mk_empty
  exact HSet.empty_ne_singleton_empty (falseValue.symm.trans (same.symm.trans trueValue))

def emptyTerm (point : growingSource.Elements) : El (· ∈ ·) (HSet.mk (alternativeGraphs point)) :=
  ⟨HSet.mk empty, HSet.mem_range.mpr ⟨⟨false⟩, rfl⟩⟩

theorem emptyTerm_compatible :
    ContextualCompatible growingSource growingTarget growingObservation alternativeGraphs
      alternativeTransport emptyTerm := by
  constructor
  · intro _ _ _ _
    rfl
  · intro _ _ _ _
    rfl

/-- The contextual function body is inhabited in this growing model; lambda
and application recover the actual empty member section at every context. -/
theorem inhabited_contextual_pi_beta :
    pullContextualSection growingSource growingTarget growingObservation alternativeGraphs alternativeTransport
      (contextualIdentityApplication growingSource growingTarget growingObservation alternativeGraphs alternativeTransport
        (descendContextualSection growingSource growingTarget growingObservation alternativeGraphs alternativeTransport
          emptyTerm emptyTerm_compatible)) = emptyTerm :=
  contextualIdentity_source_beta _ _ _ _ _ emptyTerm emptyTerm_compatible

end Controls

end Mettapedia.TypeTheory.MaterialSets.Hypersets.PowerClassPresheafDescent
