import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualSmallCoalgebraMaterialCarrier

/-!
# Material families constructed from stable authored readout graphs

The collecting graph of the actual small source gives a material carrier
at each context. Kernel stability makes the full range of transported
representatives a singleton; union constructs contextual transport without
choosing a representative. Full occurrence predicates give a class family
at the original small universe, with actual inverse member decoding.

The construction uses authored graphs and a proved stable kernel. It does
not identify contextual transport with constant ambient membership, or
choose an inverse into an arbitrary source occurrence quotient.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualMaterialReadoutFamilies

open _root_.CategoryTheory
open Mettapedia.TypeTheory.ContextualWitnessCover

universe u
variable {D : Type u} [Category.{u} D] (source : D ⥤ Type u)
variable (graphs : ∀ point, source.obj point → AccessiblePointedGraph.{u})

abbrev Stable : Prop := ∀ {first second : D} (step : first ⟶ second) {left right : source.obj first},
  HSet.mk (graphs first left) = HSet.mk (graphs first right) →
    HSet.mk (graphs second (source.map step left)) = HSet.mk (graphs second (source.map step right))

variable (stable : Stable source graphs)

def carrierGraph (point : D) : AccessiblePointedGraph.{u} := AccessiblePointedGraph.sup (graphs point)
def carrier (point : D) : HSet.{u} := HSet.mk (carrierGraph source graphs point)
abbrev Members (point : D) := {member : HSet.{u} // member ∈ carrier source graphs point}

theorem mem_carrier_iff (point : D) (member : HSet.{u}) :
    member ∈ carrier source graphs point ↔ ∃ argument, HSet.mk (graphs point argument) = member :=
  HSet.mem_range

def observe (point : D) (argument : source.obj point) : Members source graphs point :=
  ⟨HSet.mk (graphs point argument), (mem_carrier_iff source graphs point _).mpr ⟨argument, rfl⟩⟩

theorem observe_cover (point : D) : Function.Surjective (observe source graphs point) := by
  intro member
  obtain ⟨argument, same⟩ := (mem_carrier_iff source graphs point member.val).mp member.property
  exact ⟨argument, Subtype.ext same⟩

abbrev Representatives (point : D) (member : HSet.{u}) :=
  {argument : source.obj point // HSet.mk (graphs point argument) = member}

def transportRange {first second : D} (step : first ⟶ second) (member : HSet.{u}) : HSet.{u} :=
  HSet.range fun representative : Representatives source graphs first member =>
    graphs second (source.map step representative.val)

include stable in
theorem transportRange_singleton {first second : D} (step : first ⟶ second) (argument : source.obj first) :
    transportRange source graphs step (HSet.mk (graphs first argument)) =
      {HSet.mk (graphs second (source.map step argument))} := by
  apply HSet.ext
  intro member
  rw [transportRange, HSet.mem_range, HSet.mem_singleton]
  constructor
  · rintro ⟨representative, same⟩
    exact same.symm.trans (stable step representative.property)
  · intro same
    exact ⟨⟨argument, rfl⟩, same.symm⟩

def transportValue {first second : D} (step : first ⟶ second) (member : HSet.{u}) : HSet.{u} :=
  HSet.sUnion (transportRange source graphs step member)

include stable in
theorem transportValue_beta {first second : D} (step : first ⟶ second) (argument : source.obj first) :
    transportValue source graphs step (HSet.mk (graphs first argument)) =
      HSet.mk (graphs second (source.map step argument)) := by
  rw [transportValue, transportRange_singleton source graphs stable, HSet.sUnion_singleton]

include stable in
theorem transportValue_mem {first second : D} (step : first ⟶ second) (member : Members source graphs first) :
    transportValue source graphs step member.val ∈ carrier source graphs second := by
  obtain ⟨argument, same⟩ := (mem_carrier_iff source graphs first member.val).mp member.property
  rw [← same, transportValue_beta source graphs stable]
  exact (observe source graphs second (source.map step argument)).property

def transport {first second : D} (step : first ⟶ second) (member : Members source graphs first) :
    Members source graphs second :=
  ⟨transportValue source graphs step member.val, transportValue_mem source graphs stable step member⟩

theorem transport_observe {first second : D} (step : first ⟶ second) (argument : source.obj first) :
    transport source graphs stable step (observe source graphs first argument) =
      observe source graphs second (source.map step argument) :=
  Subtype.ext (transportValue_beta source graphs stable step argument)

theorem transport_identity (point : D) (member : Members source graphs point) :
    transport source graphs stable (𝟙 point) member = member := by
  obtain ⟨argument, rfl⟩ := observe_cover source graphs point member
  rw [transport_observe]
  exact congrArg (observe source graphs point) (source.map_id_apply point argument)

theorem transport_comp {first middle last : D} (earlier : first ⟶ middle) (later : middle ⟶ last)
    (member : Members source graphs first) : transport source graphs stable (earlier ≫ later) member =
      transport source graphs stable later (transport source graphs stable earlier member) := by
  obtain ⟨argument, rfl⟩ := observe_cover source graphs first member
  rw [transport_observe, transport_observe, transport_observe]
  exact congrArg (observe source graphs last) (source.map_comp_apply earlier later argument)

def family : D ⥤ Type (u + 1) where
  obj := Members source graphs
  map step := TypeCat.ofHom (transport source graphs stable step)
  map_id point := by
    apply ConcreteCategory.hom_ext
    exact transport_identity source graphs stable point
  map_comp earlier later := by
    apply ConcreteCategory.hom_ext
    exact transport_comp source graphs stable earlier later

def observation : NaturalHom source (family source graphs stable) where
  app := observe source graphs
  naturality := transport_observe source graphs stable

abbrev Classes (point : D) : Type u := AccessiblePointedGraph.PowerMemberClass (carrierGraph source graphs point)

def memberEquiv (point : D) : Classes source graphs point ≃ Members source graphs point where
  toFun memberClass :=
    let member := AccessiblePointedGraph.powerMemberEquiv (carrierGraph source graphs point) memberClass
    ⟨member.val, by
      change member.val ∈ HSet.mk (carrierGraph source graphs point)
      rw [← AccessiblePointedGraph.picture_eq_mk]
      exact member.property⟩
  invFun member := (AccessiblePointedGraph.powerMemberEquiv (carrierGraph source graphs point)).symm
    ⟨member.val, by rw [AccessiblePointedGraph.picture_eq_mk]; exact member.property⟩
  left_inv memberClass := by
    apply (AccessiblePointedGraph.powerMemberEquiv (carrierGraph source graphs point)).injective
    exact (AccessiblePointedGraph.powerMemberEquiv (carrierGraph source graphs point)).apply_symm_apply _
  right_inv member := by
    apply Subtype.ext
    change ((AccessiblePointedGraph.powerMemberEquiv (carrierGraph source graphs point))
      ((AccessiblePointedGraph.powerMemberEquiv (carrierGraph source graphs point)).symm
        ⟨member.val, by rw [AccessiblePointedGraph.picture_eq_mk]; exact member.property⟩)).val = member.val
    exact congrArg Subtype.val
      ((AccessiblePointedGraph.powerMemberEquiv (carrierGraph source graphs point)).apply_symm_apply
        ⟨member.val, by rw [AccessiblePointedGraph.picture_eq_mk]; exact member.property⟩)

def classFamily : D ⥤ Type u where
  obj := Classes source graphs
  map {first second} step := TypeCat.ofHom fun memberClass =>
    (memberEquiv source graphs second).symm
      (transport source graphs stable step ((memberEquiv source graphs first) memberClass))
  map_id point := by
    apply ConcreteCategory.hom_ext
    intro memberClass
    change (memberEquiv source graphs point).symm
      (transport source graphs stable (𝟙 point) ((memberEquiv source graphs point) memberClass)) = memberClass
    exact (congrArg (memberEquiv source graphs point).symm
      (transport_identity source graphs stable point _)).trans
        ((memberEquiv source graphs point).symm_apply_apply memberClass)
  map_comp {first middle last} earlier later := by
    apply ConcreteCategory.hom_ext
    intro memberClass
    change (memberEquiv source graphs last).symm
      (transport source graphs stable (earlier ≫ later) ((memberEquiv source graphs first) memberClass)) =
      (memberEquiv source graphs last).symm
        (transport source graphs stable later ((memberEquiv source graphs middle)
          ((memberEquiv source graphs middle).symm
            (transport source graphs stable earlier ((memberEquiv source graphs first) memberClass)))))
    rw [transport_comp, (memberEquiv source graphs middle).apply_symm_apply]

def decode : NaturalHom (classFamily source graphs stable) (family source graphs stable) where
  app := fun point => memberEquiv source graphs point
  naturality {_ second} _ _ :=
    ((memberEquiv source graphs second).apply_symm_apply _).symm

def encode : NaturalHom (family source graphs stable) (classFamily source graphs stable) where
  app := fun point => (memberEquiv source graphs point).symm
  naturality {first second} step member := by
    change (memberEquiv source graphs second).symm
      (transport source graphs stable step ((memberEquiv source graphs first)
        ((memberEquiv source graphs first).symm member))) = _
    exact congrArg (memberEquiv source graphs second).symm
      (congrArg (transport source graphs stable step) ((memberEquiv source graphs first).apply_symm_apply member))

theorem decode_encode (point : D) (member : Members source graphs point) :
    (decode source graphs stable).app point ((encode source graphs stable).app point member) = member :=
  (memberEquiv source graphs point).apply_symm_apply member

theorem encode_decode (point : D) (memberClass : Classes source graphs point) :
    (encode source graphs stable).app point ((decode source graphs stable).app point memberClass) = memberClass :=
  (memberEquiv source graphs point).symm_apply_apply memberClass

def classObservation : NaturalHom source (classFamily source graphs stable) :=
  (observation source graphs stable).comp (encode source graphs stable)

theorem classObservation_cover (point : D) : Function.Surjective ((classObservation source graphs stable).app point) := by
  intro memberClass
  obtain ⟨argument, same⟩ := observe_cover source graphs point ((memberEquiv source graphs point) memberClass)
  exact ⟨argument, (congrArg (memberEquiv source graphs point).symm same).trans
    ((memberEquiv source graphs point).symm_apply_apply memberClass)⟩

theorem classObservation_eq_iff (point : D) (left right : source.obj point) :
    (classObservation source graphs stable).app point left = (classObservation source graphs stable).app point right ↔
      HSet.mk (graphs point left) = HSet.mk (graphs point right) := by
  constructor
  · intro same
    exact congrArg Subtype.val ((memberEquiv source graphs point).symm.injective same)
  · intro same
    exact congrArg (memberEquiv source graphs point).symm (Subtype.ext same)

def sectionEquiv : (classFamily source graphs stable).sections ≃ (family source graphs stable).sections where
  toFun := (decode source graphs stable).mapSection
  invFun := (encode source graphs stable).mapSection
  left_inv term := Subtype.ext (funext fun point => encode_decode source graphs stable point (term.val point))
  right_inv term := Subtype.ext (funext fun point => decode_encode source graphs stable point (term.val point))

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualMaterialReadoutFamilies
