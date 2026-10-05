import Mettapedia.TypeTheory.MaterialSets.Hypersets.DisplayedPresheafIdentity
import Mettapedia.TypeTheory.MaterialSets.Hypersets.FamilyIdentity

/-!
# Material decoding of contextual observed identity

The small presheaf witness is an actual member class of a separated singleton
graph. Its decoding is compared, with inverse and value laws, to the actual
material identity set of the decoded endpoint members. This comparison is
natural along the observed family's authored restriction maps. Consequently
the displayed identity contexts and J constructed in `DisplayedPresheafIdentity`
apply to the observed material family, rather than to a replacement constant
family or a bare support predicate.

The identity interpretation here is discrete. It records equality of decoded
material members and does not identify presentation occurrences or add UIP to
a native intensional language. Decoded member carriers live in `Type (u+1)`;
their actual graph member-class models and identity contexts remain in `Type u`.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ObservedPresheafIdentity

open CategoryTheory
open AccessiblePointedGraph
open Mettapedia.TypeTheory.DisplayedPresheafTransport
open PowerClassPresheafDescent
open PowerClassPresheafProducts

universe u

section MaterialDecoding

variable {T : Type u} {X : HSet.{u}}

/-- The witness graph pictures the identity set of the actual decoded
endpoint values, including its membership predicate. -/
theorem graph_decode (decode : T ≃ FamilyCwf.Elements X) (left right : T) :
    HSet.mk (PresheafIdentityWitness.graph left right) =
      FamilyIdentity.identitySet (decode left) (decode right) := by
  rw [PresheafIdentityWitness.mk_graph]
  apply HSet.ext
  intro value
  rw [HSet.mem_sep, HSet.mem_singleton, FamilyIdentity.mem_identitySet_iff]
  exact and_congr Iff.rfl ⟨congrArg decode, fun same => decode.injective same⟩

def witnessMember (decode : T ≃ FamilyCwf.Elements X) {left right : T}
    (witness : PresheafIdentityWitness.Witness left right) :
    FamilyCwf.Elements (FamilyIdentity.identitySet (decode left) (decode right)) :=
  ⟨classValue (PresheafIdentityWitness.graph left right) witness.1, by
    have belongs : classValue (PresheafIdentityWitness.graph left right) witness.1 ∈
        picture (PresheafIdentityWitness.graph left right) :=
      (classMember (PresheafIdentityWitness.graph left right) witness).2
    rw [picture_eq_mk, graph_decode decode left right] at belongs
    exact belongs⟩

/-- Explicit inverses connect the small actual graph carrier to actual
material members, without choosing an occurrence representative. -/
def witnessMemberEquiv (decode : T ≃ FamilyCwf.Elements X) (left right : T) :
    PresheafIdentityWitness.Witness left right ≃
      FamilyCwf.Elements (FamilyIdentity.identitySet (decode left) (decode right)) where
  toFun := witnessMember decode
  invFun witness := PresheafIdentityWitness.encode
    (decode.injective (FamilyIdentity.identityDecode witness))
  left_inv _ := Subsingleton.elim _ _
  right_inv witness := by
    apply El.ext HSet.propositional
    exact (PresheafIdentityWitness.classValue_encode _).trans
      (FamilyIdentity.identityMember_value witness).symm

theorem witnessMemberEquiv_value (decode : T ≃ FamilyCwf.Elements X) {left right : T}
    (witness : PresheafIdentityWitness.Witness left right) :
    (witnessMemberEquiv decode left right witness).1 =
      classValue (PresheafIdentityWitness.graph left right) witness.1 := rfl

theorem witnessMemberEquiv_decode (decode : T ≃ FamilyCwf.Elements X) {left right : T}
    (witness : PresheafIdentityWitness.Witness left right) :
    FamilyIdentity.identityDecode (witnessMemberEquiv decode left right witness) =
      congrArg decode (PresheafIdentityWitness.decode witness) := rfl

theorem witnessMemberEquiv_reflexivity (decode : T ≃ FamilyCwf.Elements X) (endpoint : T) :
    witnessMemberEquiv decode endpoint endpoint (PresheafIdentityWitness.encode rfl) =
      FamilyIdentity.identityEncode rfl := by
  apply El.ext HSet.propositional
  exact PresheafIdentityWitness.classValue_encode rfl

end MaterialDecoding

variable {C : Type u} [Category.{u} C]
variable (source target : Cᵒᵖ ⥤ Type u) (observation : NatTrans source target)
variable (graphs : source.Elements → AccessiblePointedGraph.{u})
variable (transport : MaterialTransport source target observation graphs)

abbrev domain : DisplayedFamily.{u, u, u, u} (classFace source target observation) :=
  observedDisplayed source target observation graphs transport

variable (left right : (domain source target observation graphs transport).sections)

def materialIdentityAt (point : (classFace source target observation).Elements) : HSet.{u} :=
  FamilyIdentity.identitySet
    (contextualMemberEquiv source target observation graphs point (left.val point))
    (contextualMemberEquiv source target observation graphs point (right.val point))

def identityMemberEquiv (point : (classFace source target observation).Elements) :
    (DisplayedPresheafIdentity.identityFamily (domain source target observation graphs transport) left right).obj point ≃
      FamilyCwf.Elements (materialIdentityAt source target observation graphs transport left right point) :=
  witnessMemberEquiv (contextualMemberEquiv source target observation graphs point) (left.val point) (right.val point)

theorem materialIdentityAt_graph (point : (classFace source target observation).Elements) :
    HSet.mk (PresheafIdentityWitness.graph (left.val point) (right.val point)) =
      materialIdentityAt source target observation graphs transport left right point :=
  graph_decode (contextualMemberEquiv source target observation graphs point) _ _

/-- Actual decoded material identity restriction. The source and target
comparison equivalences retain the endpoint and member values. -/
def materialIdentity : DisplayedFamily.{u, u, u, u + 1} (classFace source target observation) where
  obj point := FamilyCwf.Elements (materialIdentityAt source target observation graphs transport left right point)
  map {first second} step := TypeCat.ofHom fun witness =>
    identityMemberEquiv source target observation graphs transport left right second
      ((DisplayedPresheafIdentity.identityFamily (domain source target observation graphs transport) left right).map step
        ((identityMemberEquiv source target observation graphs transport left right first).symm witness))
  map_id point := by
    apply ConcreteCategory.hom_ext
    intro witness
    change identityMemberEquiv _ _ _ _ _ _ _ point
      ((DisplayedPresheafIdentity.identityFamily (domain source target observation graphs transport) left right).map (𝟙 point)
        ((identityMemberEquiv _ _ _ _ _ _ _ point).symm witness)) = witness
    rw [(DisplayedPresheafIdentity.identityFamily (domain source target observation graphs transport) left right).map_id point]
    exact (identityMemberEquiv _ _ _ _ _ _ _ point).apply_symm_apply witness
  map_comp {first middle last} earlier later := by
    apply ConcreteCategory.hom_ext
    intro witness
    change identityMemberEquiv _ _ _ _ _ _ _ last
      ((DisplayedPresheafIdentity.identityFamily (domain source target observation graphs transport) left right).map (earlier ≫ later)
        ((identityMemberEquiv _ _ _ _ _ _ _ first).symm witness)) = _
    rw [Functor.map_comp]
    dsimp
    rw [Equiv.symm_apply_apply]

theorem identityMemberEquiv_natural {first second : (classFace source target observation).Elements}
    (step : first ⟶ second)
    (witness : (DisplayedPresheafIdentity.identityFamily (domain source target observation graphs transport) left right).obj first) :
    (materialIdentity source target observation graphs transport left right).map step
        (identityMemberEquiv source target observation graphs transport left right first witness) =
      identityMemberEquiv source target observation graphs transport left right second
        ((DisplayedPresheafIdentity.identityFamily (domain source target observation graphs transport) left right).map step witness) := by
  change identityMemberEquiv _ _ _ _ _ _ _ second
    ((DisplayedPresheafIdentity.identityFamily (domain source target observation graphs transport) left right).map step
      ((identityMemberEquiv _ _ _ _ _ _ _ first).symm
        (identityMemberEquiv _ _ _ _ _ _ _ first witness))) = _
  rw [Equiv.symm_apply_apply]

theorem materialIdentity_map_value {first second : (classFace source target observation).Elements}
    (step : first ⟶ second)
    (witness : (materialIdentity source target observation graphs transport left right).obj first) :
    ((materialIdentity source target observation graphs transport left right).map step witness).1 = witness.1 := by
  exact (FamilyIdentity.identityMember_value _).trans (FamilyIdentity.identityMember_value witness).symm

def materialReflexivity (term : (domain source target observation graphs transport).sections) :
    (materialIdentity source target observation graphs transport term term).sections :=
  ⟨fun _ => FamilyIdentity.identityEncode rfl, by
    intro first second step
    apply El.ext HSet.propositional
    exact materialIdentity_map_value source target observation graphs transport term term step _⟩

theorem identityMemberEquiv_reflexivity
    (term : (domain source target observation graphs transport).sections)
    (point : (classFace source target observation).Elements) :
    identityMemberEquiv source target observation graphs transport term term point
        ((DisplayedPresheafIdentity.reflexivity (domain source target observation graphs transport) term).val point) =
      (materialReflexivity source target observation graphs transport term).val point :=
  witnessMemberEquiv_reflexivity _ _

/-- The material witness of an actual full identity-context point uses its
two retained endpoint values, not only an external equality proposition. -/
def contextWitness
    (point : (DisplayedPresheafIdentity.identityContext (domain source target observation graphs transport)).Elements) :
    FamilyCwf.Elements (FamilyIdentity.identitySet
      (contextualMemberEquiv source target observation graphs ⟨point.1, point.2.1.1.1⟩ point.2.1.1.2)
      (contextualMemberEquiv source target observation graphs ⟨point.1, point.2.1.1.1⟩ point.2.1.2)) :=
  witnessMemberEquiv (contextualMemberEquiv source target observation graphs ⟨point.1, point.2.1.1.1⟩)
    point.2.1.1.2 point.2.1.2 point.2.2

theorem contextWitness_value
    (point : (DisplayedPresheafIdentity.identityContext (domain source target observation graphs transport)).Elements) :
    (contextWitness source target observation graphs transport point).1 = ∅ :=
  FamilyIdentity.identityMember_value _

namespace Controls

open PowerClassPresheafDescent.Controls
open PowerClassFamilyDescent

abbrev growingDomain :=
  domain growingSource growingTarget growingObservation growingGraphs growingTransport

def cyclicBase : (classFace growingSource growingTarget growingObservation).Elements :=
  ⟨world 1, classOf (growingObservation.app (world 1)) (stageValue 1 1 (by omega) false)⟩

def cyclicMember : FamilyCwf.Elements
    (decodedFamily (fun value => growingGraphs ⟨world 1, value⟩) cyclicBase.2) :=
  ⟨HSet.quineAtom, by
    change HSet.quineAtom ∈ decodedFamily _
      (classOf (growingObservation.app (world 1)) (stageValue 1 1 (by omega) false))
    rw [growing_cyclic]
    exact HSet.quineAtom_mem_self⟩

def cyclicEndpoint : growingDomain.obj cyclicBase :=
  (contextualMemberEquiv growingSource growingTarget growingObservation growingGraphs cyclicBase).symm cyclicMember

def cyclicIdentityPoint : (DisplayedPresheafIdentity.identityContext growingDomain).Elements :=
  ⟨world 1, (DisplayedPresheafIdentity.diagonal growingDomain).app (world 1) ⟨cyclicBase.2, cyclicEndpoint⟩⟩

/-- J for an endpoint-dependent natural motive returns the actual Quine
member in the nonconstant empty/Quine observed family. -/
theorem nonconstant_cyclic_J_value :
    (contextualMemberEquiv growingSource growingTarget growingObservation growingGraphs cyclicBase
      ((DisplayedPresheafIdentity.J growingDomain (DisplayedPresheafIdentity.endpointMotive growingDomain)
        (DisplayedPresheafIdentity.endpointMethod growingDomain)).val cyclicIdentityPoint)).1 = HSet.quineAtom := by
  rw [DisplayedPresheafIdentity.J_endpoint_value]
  exact congrArg (fun member => member.1)
    ((contextualMemberEquiv growingSource growingTarget growingObservation growingGraphs cyclicBase).apply_symm_apply cyclicMember)

abbrev alternativeDomain :=
  domain growingSource growingTarget growingObservation alternativeGraphs alternativeTransport

def alternativeBase : (classFace growingSource growingTarget growingObservation).Elements :=
  ⟨world 0, classOf (growingObservation.app (world 0)) (stageValue 0 0 (by omega) false)⟩

def alternativeMember (tag : Bool) : FamilyCwf.Elements
    (decodedFamily (fun value => alternativeGraphs ⟨world 0, value⟩) alternativeBase.2) :=
  ⟨HSet.mk (PowerClassFamilyDescent.Controls.selectedGraph tag), by
    change HSet.mk (PowerClassFamilyDescent.Controls.selectedGraph tag) ∈ decodedFamily _
      (classOf (growingObservation.app (world 0)) (stageValue 0 0 (by omega) false))
    rw [family_beta _ _ (alternativeTransport.invariant _) _]
    exact HSet.mem_range.mpr ⟨⟨tag⟩, rfl⟩⟩

def alternativeEndpoint (tag : Bool) : alternativeDomain.obj alternativeBase :=
  (contextualMemberEquiv growingSource growingTarget growingObservation alternativeGraphs alternativeBase).symm
    (alternativeMember tag)

theorem alternativeEndpoints_distinct : alternativeEndpoint false ≠ alternativeEndpoint true := by
  intro same
  have leftRead : contextualMemberEquiv growingSource growingTarget growingObservation alternativeGraphs alternativeBase
      (alternativeEndpoint false) = alternativeMember false := Equiv.apply_symm_apply _ _
  have rightRead : contextualMemberEquiv growingSource growingTarget growingObservation alternativeGraphs alternativeBase
      (alternativeEndpoint true) = alternativeMember true := Equiv.apply_symm_apply _ _
  have decodedSame := leftRead.symm.trans
    ((congrArg (contextualMemberEquiv growingSource growingTarget growingObservation alternativeGraphs alternativeBase) same).trans rightRead)
  have values := congrArg (fun member => member.1) decodedSame
  change HSet.mk empty = HSet.mk (oneChild empty) at values
  rw [HSet.mk_empty] at values
  have singleton : HSet.mk (oneChild empty) = ({∅} : HSet) :=
    (picture_eq_mk _).symm.trans picture_oneChild_empty
  exact HSet.empty_ne_singleton_empty (values.trans singleton)

/-- Actual distinct material endpoint values give an empty witness carrier,
even in a context where both endpoint members exist. -/
theorem actual_offDiagonal_empty :
    ¬ Nonempty ((DisplayedPresheafIdentity.witnessFamily alternativeDomain).obj
      ⟨world 0, ⟨⟨alternativeBase.2, alternativeEndpoint false⟩, alternativeEndpoint true⟩⟩) :=
  DisplayedPresheafIdentity.offDiagonal_empty alternativeDomain alternativeBase _ _ alternativeEndpoints_distinct

end Controls

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ObservedPresheafIdentity
