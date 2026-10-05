import Mettapedia.GSLT.Logic.HostChoiceContextualObservedHypersetSpans
import Mettapedia.OSLF.Bridges.TypeTheory.HostChoiceObservedHypersetNativePredicates
import Mettapedia.TypeTheory.ContextualSmallFamilyNativeAdjunction

/-!
# Contextual authored receipt families over both observed endpoints

An authored event functor and its two natural endpoint maps determine an
actual original-bound displayed receipt family over the structured endpoint
pair. Its comprehension is naturally isomorphic to the entire original
event functor. Thus the family retains receipts even when endpoint values
coincide. Its classifier decodes the complete family and actual context maps.

The existing presheaf event modalities are used after explicit universe
lifting, with unchanged event coordinates. Their predecessor box quantifies
over all future restrictions. Endpoint matching is stated against the actual
observed kernel; it is distinct from receipt recovery and term descent.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.HostChoiceContextualObservedHypersetReceipts

open _root_.CategoryTheory
open Mettapedia.TypeTheory ContextualWitnessCover
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open ContextualCoalgebraLabelledGraph ContextualObservedCoalgebra
open HostChoiceContextualObservedHypersetTriangle
open Mettapedia.GSLT.Topos.ConstructivePresheaf
open ObservationSpans.Presheaf

universe u h
variable {D : Type u} [Category.{u} D] {A E : D ⥤ Type u}
variable (source : NaturalHom A (CoveredFuturePowerFamilies.family A))
variable {Atom : Type u} (atoms : Atom → State A → Prop)
variable (worlds : ArgumentCoding D)
variable (arrows : (first second : D) → ArgumentCoding (first ⟶ second))
variable (atomCoding : ArgumentCoding Atom)
variable (left right : NaturalHom E A)

private theorem subtype_heq {X : Type u} {P Q : X → Prop} (same : P = Q)
    (first : Subtype P) (second : Subtype Q) (values : first.val = second.val) : HEq first second := by
  cases same
  exact heq_of_eq (Subtype.ext values)

abbrev endpointPairs := CoveredFuturePowerClassifier.product
  (structured source atoms worlds arrows atomCoding) (structured source atoms worlds arrows atomCoding)

noncomputable def endpoints : NaturalHom E (endpointPairs source atoms worlds arrows atomCoding) where
  app point event := ((structuredReadout source atoms worlds arrows atomCoding).app point (left.app point event),
    (structuredReadout source atoms worlds arrows atomCoding).app point (right.app point event))
  naturality step event := Prod.ext
    (((structuredReadout source atoms worlds arrows atomCoding).naturality step _).trans
      (congrArg ((structuredReadout source atoms worlds arrows atomCoding).app _) (left.naturality step event)))
    (((structuredReadout source atoms worlds arrows atomCoding).naturality step _).trans
      (congrArg ((structuredReadout source atoms worlds arrows atomCoding).app _) (right.naturality step event)))

noncomputable def family : (endpointPairs source atoms worlds arrows atomCoding).Elements ⥤ Type u where
  obj point := {event : E.obj point.1 // (endpoints source atoms worlds arrows atomCoding left right).app point.1 event = point.2}
  map {first second} step := TypeCat.ofHom fun receipt => ⟨E.map step.1 receipt.val,
    ((endpoints source atoms worlds arrows atomCoding left right).naturality step.1 receipt.val).symm.trans
      ((congrArg ((endpointPairs source atoms worlds arrows atomCoding).map step.1) receipt.property).trans step.2)⟩
  map_id point := by
    apply ConcreteCategory.hom_ext
    intro receipt
    exact Subtype.ext (E.map_id_apply point.1 receipt.val)
  map_comp earlier later := by
    apply ConcreteCategory.hom_ext
    intro receipt
    exact Subtype.ext (E.map_comp_apply earlier.1 later.1 receipt.val)

noncomputable def comprehensionForward : NaturalHom E
    (ContextualSmallFamilyUniverse.total (family source atoms worlds arrows atomCoding left right)) where
  app point event := ⟨(endpoints source atoms worlds arrows atomCoding left right).app point event, ⟨event, rfl⟩⟩
  naturality {first second} step event := by
    have same := (endpoints source atoms worlds arrows atomCoding left right).naturality step event
    apply Sigma.ext same
    exact subtype_heq (congrArg (fun pair => fun receipt : E.obj second =>
      (endpoints source atoms worlds arrows atomCoding left right).app second receipt = pair) same) _ _ rfl

noncomputable def comprehensionBackward : NaturalHom
    (ContextualSmallFamilyUniverse.total (family source atoms worlds arrows atomCoding left right)) E where
  app _ receipt := receipt.2.val
  naturality _ _ := rfl

theorem comprehension_left (point : D) (event : E.obj point) :
    (comprehensionBackward source atoms worlds arrows atomCoding left right).app point
      ((comprehensionForward source atoms worlds arrows atomCoding left right).app point event) = event := rfl

theorem comprehension_right (point : D)
    (receipt : (ContextualSmallFamilyUniverse.total (family source atoms worlds arrows atomCoding left right)).obj point) :
    (comprehensionForward source atoms worlds arrows atomCoding left right).app point
      ((comprehensionBackward source atoms worlds arrows atomCoding left right).app point receipt) = receipt := by
  apply Sigma.ext receipt.2.property
  exact subtype_heq (congrArg (fun pair => fun event : E.obj point =>
    (endpoints source atoms worlds arrows atomCoding left right).app point event = pair) receipt.2.property) _ _ rfl

noncomputable def comprehensionSections : E.sections ≃
    (ContextualSmallFamilyUniverse.total (family source atoms worlds arrows atomCoding left right)).sections where
  toFun := (comprehensionForward source atoms worlds arrows atomCoding left right).mapSection
  invFun := (comprehensionBackward source atoms worlds arrows atomCoding left right).mapSection
  left_inv term := Subtype.ext (funext fun point => comprehension_left source atoms worlds arrows atomCoding left right point (term.val point))
  right_inv term := Subtype.ext (funext fun point => comprehension_right source atoms worlds arrows atomCoding left right point (term.val point))

theorem comprehension_endpoint_square :
    (comprehensionForward source atoms worlds arrows atomCoding left right).comp
      (ContextualSmallFamilyUniverse.projection (family source atoms worlds arrows atomCoding left right)) =
        endpoints source atoms worlds arrows atomCoding left right := by
  apply NaturalHom.ext
  intro _ _
  rfl

theorem endpoint_kernel (point : D) (first second : E.obj point) :
    (endpoints source atoms worlds arrows atomCoding left right).app point first =
        (endpoints source atoms worlds arrows atomCoding left right).app point second ↔
      ObservedBisimilar source atoms point (left.app point first) (left.app point second) ∧
        ObservedBisimilar source atoms point (right.app point first) (right.app point second) := by
  constructor
  · intro same
    exact ⟨(structured_kernel source atoms worlds arrows atomCoding point _ _).mp (congrArg Prod.fst same),
      (structured_kernel source atoms worlds arrows atomCoding point _ _).mp (congrArg Prod.snd same)⟩
  · rintro ⟨starts, ends⟩
    exact Prod.ext ((structured_kernel source atoms worlds arrows atomCoding point _ _).mpr starts)
      ((structured_kernel source atoms worlds arrows atomCoding point _ _).mpr ends)

theorem classifier_full_family : ContextualSmallFamilyUniverse.decodedFamily
    (ContextualSmallFamilyUniverse.classifier (family source atoms worlds arrows atomCoding left right)) =
      family source atoms worlds arrows atomCoding left right := ContextualSmallFamilyUniverse.decoded_classifier_eq _

section DependentConsumers

variable (body : (family source atoms worlds arrows atomCoding left right).Elements ⥤ Type u)

noncomputable def nativeFunctions
    (point : (endpointPairs source atoms worlds arrows atomCoding).Elements) :
    WiderPresheafDependentFunctions.DependentSection (family source atoms worlds arrows atomCoding left right) body point ≃
      ContextualSmallFamilyTypeFormers.ProductAt (family source atoms worlds arrows atomCoding left right) body point :=
  ContextualSmallFamilyNativeAdjunction.nativeSmallEquiv _ _ point

noncomputable def nativeHom
    (consumer : (endpointPairs source atoms worlds arrows atomCoding).Elements ⥤ Type h) :
    WiderPresheafDependentFunctions.Hom
      (WiderPresheafDependentFunctions.over (family source atoms worlds arrows atomCoding left right) consumer) body ≃
        WiderPresheafDependentFunctions.Hom consumer
          (ContextualSmallFamilyTypeFormers.pi (family source atoms worlds arrows atomCoding left right) body) :=
  ContextualSmallFamilyNativeAdjunction.smallHomEquiv _ _ consumer

theorem native_evaluation
    (point : (endpointPairs source atoms worlds arrows atomCoding).Elements)
    (term : WiderPresheafDependentFunctions.DependentSection (family source atoms worlds arrows atomCoding left right) body point)
    (receipt : (family source atoms worlds arrows atomCoding left right).obj point) :
    ContextualSmallFamilyTypeFormers.evaluateValue (family source atoms worlds arrows atomCoding left right) body point
      (nativeFunctions source atoms worlds arrows atomCoding left right body point term) receipt =
        term.app point (𝟙 point) receipt :=
  ContextualSmallFamilyNativeAdjunction.evaluation_compression _ _ point term receipt

theorem sum_classifier : ContextualSmallFamilyUniverse.decodedFamily
    (ContextualSmallFamilyUniverse.classifier
      (ContextualSmallFamilyTypeFormers.sigma (family source atoms worlds arrows atomCoding left right) body)) =
    ContextualSmallFamilyTypeFormers.sigma (family source atoms worlds arrows atomCoding left right) body :=
  ContextualSmallFamilyUniverse.decoded_classifier_eq _

theorem product_classifier : ContextualSmallFamilyUniverse.decodedFamily
    (ContextualSmallFamilyUniverse.classifier
      (ContextualSmallFamilyTypeFormers.pi (family source atoms worlds arrows atomCoding left right) body)) =
    ContextualSmallFamilyTypeFormers.pi (family source atoms worlds arrows atomCoding left right) body :=
  ContextualSmallFamilyUniverse.decoded_classifier_eq _

end DependentConsumers

section ParameterSubstitution

variable {P : D ⥤ Type h} (change : NaturalHom P (endpointPairs source atoms worlds arrows atomCoding))

noncomputable def underFamily : P.Elements ⥤ Type u :=
  ContextualSmallFamilyUniverse.substitutedFamily (family source atoms worlds arrows atomCoding left right) change

noncomputable def underForward : NaturalHom (ContextualSmallFamilyUniverse.total
    (underFamily source atoms worlds arrows atomCoding left right change))
    (ContextualImageFactorization.pullback (endpoints source atoms worlds arrows atomCoding left right) change) where
  app _ receipt := ⟨(receipt.2.val, receipt.1), receipt.2.property⟩
  naturality _ _ := Subtype.ext rfl

noncomputable def underBackward : NaturalHom
    (ContextualImageFactorization.pullback (endpoints source atoms worlds arrows atomCoding left right) change)
    (ContextualSmallFamilyUniverse.total (underFamily source atoms worlds arrows atomCoding left right change)) where
  app _ receipt := ⟨receipt.val.2, ⟨receipt.val.1, receipt.property⟩⟩
  naturality _ _ := by
    apply Sigma.ext rfl
    exact heq_of_eq (Subtype.ext rfl)

theorem under_left (point : D) (receipt : (ContextualSmallFamilyUniverse.total
    (underFamily source atoms worlds arrows atomCoding left right change)).obj point) :
    (underBackward source atoms worlds arrows atomCoding left right change).app point
      ((underForward source atoms worlds arrows atomCoding left right change).app point receipt) = receipt := rfl

theorem under_right (point : D) (receipt : (ContextualImageFactorization.pullback
    (endpoints source atoms worlds arrows atomCoding left right) change).obj point) :
    (underForward source atoms worlds arrows atomCoding left right change).app point
      ((underBackward source atoms worlds arrows atomCoding left right change).app point receipt) = receipt :=
  Subtype.ext rfl

noncomputable def underSections : (ContextualSmallFamilyUniverse.total
    (underFamily source atoms worlds arrows atomCoding left right change)).sections ≃
    (ContextualImageFactorization.pullback (endpoints source atoms worlds arrows atomCoding left right) change).sections where
  toFun := (underForward source atoms worlds arrows atomCoding left right change).mapSection
  invFun := (underBackward source atoms worlds arrows atomCoding left right change).mapSection
  left_inv term := Subtype.ext (funext fun point => under_left source atoms worlds arrows atomCoding left right change point (term.val point))
  right_inv term := Subtype.ext (funext fun point => under_right source atoms worlds arrows atomCoding left right change point (term.val point))

theorem under_parameter_square :
    (underForward source atoms worlds arrows atomCoding left right change).comp
      (ContextualImageFactorization.pullbackSecond (endpoints source atoms worlds arrows atomCoding left right) change) =
        ContextualSmallFamilyUniverse.projection (underFamily source atoms worlds arrows atomCoding left right change) := by
  apply NaturalHom.ext
  intro _ _
  rfl

theorem under_actual_receipt (point : D) (receipt : (ContextualSmallFamilyUniverse.total
    (underFamily source atoms worlds arrows atomCoding left right change)).obj point) :
    ((underForward source atoms worlds arrows atomCoding left right change).app point receipt).val.1 = receipt.2.val := rfl

theorem under_classifier : ContextualSmallFamilyUniverse.decodedFamily
    (ContextualSmallFamilyUniverse.classifier (underFamily source atoms worlds arrows atomCoding left right change)) =
    underFamily source atoms worlds arrows atomCoding left right change := ContextualSmallFamilyUniverse.decoded_classifier_eq _

theorem under_identity : underFamily source atoms worlds arrows atomCoding left right
    (ContextualSmallMapConstructions.identity (endpointPairs source atoms worlds arrows atomCoding)) =
      family source atoms worlds arrows atomCoding left right := rfl

theorem under_composition {R : D ⥤ Type h} (earlier : NaturalHom R P) :
    underFamily source atoms worlds arrows atomCoding left right (earlier.comp change) =
      ContextualSmallFamilyUniverse.substitutedFamily
        (underFamily source atoms worlds arrows atomCoding left right change) earlier := rfl

end ParameterSubstitution

/-! ## The actual existing internal event modalities -/

def raise (input : D ⥤ Type u) : D ⥤ Type (u+1) where
  obj point := ULift.{u+1} (input.obj point)
  map step := TypeCat.ofHom fun value => ⟨input.map step value.down⟩
  map_id point := by
    apply ConcreteCategory.hom_ext
    intro value
    exact congrArg ULift.up (input.map_id_apply point value.down)
  map_comp first second := by
    apply ConcreteCategory.hom_ext
    intro value
    exact congrArg ULift.up (input.map_comp_apply first second value.down)

def raisedEndpoint (operation : NaturalHom E A) : NatTrans (raise E) (raise A) where
  app point := TypeCat.ofHom fun event => ⟨operation.app point event.down⟩
  naturality _ _ step := by
    apply ConcreteCategory.hom_ext
    intro event
    exact congrArg ULift.up (operation.naturality step event.down).symm

def sourceGraph : EventGraph D where
  vertex := raise A
  edge := raise E
  source := raisedEndpoint left
  target := raisedEndpoint right

noncomputable def structuredEndpoint (operation : NaturalHom E A) :
    NatTrans (raise E) (structured source atoms worlds arrows atomCoding) :=
  { app := fun point => TypeCat.ofHom fun event =>
      (structuredReadout source atoms worlds arrows atomCoding).app point (operation.app point event.down)
    naturality := by
      intro _ _ step
      apply ConcreteCategory.hom_ext
      intro event
      exact (((structuredReadout source atoms worlds arrows atomCoding).naturality step _).trans
        (congrArg ((structuredReadout source atoms worlds arrows atomCoding).app _) (operation.naturality step event.down))).symm }

noncomputable def observedGraph : EventGraph D where
  vertex := structured source atoms worlds arrows atomCoding
  edge := raise E
  source := structuredEndpoint source atoms worlds arrows atomCoding left
  target := structuredEndpoint source atoms worlds arrows atomCoding right

noncomputable def eventObservation : EventObservation (sourceGraph left right)
    (observedGraph source atoms worlds arrows atomCoding left right) where
  states := by
    refine { app := fun point => TypeCat.ofHom fun state =>
      (structuredReadout source atoms worlds arrows atomCoding).app point state.down, naturality := ?_ }
    intro _ _ step
    apply ConcreteCategory.hom_ext
    intro state
    exact ((structuredReadout source atoms worlds arrows atomCoding).naturality step state.down).symm
  events := { app := fun _ => TypeCat.ofHom id, naturality := by intro _ _ _; rfl }
  source_comm _ _ := rfl
  target_comm _ _ := rfl

def OutgoingMatches : Prop := ∀ point (state : A.obj point) (event : E.obj point),
  ObservedBisimilar source atoms point (left.app point event) state →
    ∃ matched : E.obj point, left.app point matched = state ∧
      ObservedBisimilar source atoms point (right.app point matched) (right.app point event)

def IncomingMatches : Prop := ∀ point (state : A.obj point) (event : E.obj point),
  ObservedBisimilar source atoms point (right.app point event) state →
    ∃ matched : E.obj point, right.app point matched = state ∧
      ObservedBisimilar source atoms point (left.app point matched) (left.app point event)

theorem outgoing_iff : (eventObservation source atoms worlds arrows atomCoding left right).SourceLifts ↔
    OutgoingMatches source atoms left right := by
  constructor
  · intro lifts point state event related
    obtain ⟨matched, starts, ends⟩ := lifts point ⟨state⟩ ⟨event⟩
      ((structured_kernel source atoms worlds arrows atomCoding point _ _).mpr related)
    exact ⟨matched.down, congrArg ULift.down starts,
      (structured_kernel source atoms worlds arrows atomCoding point _ _).mp ends⟩
  · intro matching point state event same
    obtain ⟨matched, starts, related⟩ := matching point state.down event.down
      ((structured_kernel source atoms worlds arrows atomCoding point _ _).mp same)
    exact ⟨⟨matched⟩, congrArg ULift.up starts,
      (structured_kernel source atoms worlds arrows atomCoding point _ _).mpr related⟩

theorem incoming_iff : (eventObservation source atoms worlds arrows atomCoding left right).TargetLifts ↔
    IncomingMatches source atoms left right := by
  constructor
  · intro lifts point state event related
    obtain ⟨matched, ends, starts⟩ := lifts point ⟨state⟩ ⟨event⟩
      ((structured_kernel source atoms worlds arrows atomCoding point _ _).mpr related)
    exact ⟨matched.down, congrArg ULift.down ends,
      (structured_kernel source atoms worlds arrows atomCoding point _ _).mp starts⟩
  · intro matching point state event same
    obtain ⟨matched, ends, related⟩ := matching point state.down event.down
      ((structured_kernel source atoms worlds arrows atomCoding point _ _).mp same)
    exact ⟨⟨matched⟩, congrArg ULift.up ends,
      (structured_kernel source atoms worlds arrows atomCoding point _ _).mpr related⟩

theorem contextual_diamond_square (matching : OutgoingMatches source atoms left right)
    (predicate : Subfunctor (structured source atoms worlds arrows atomCoding)) (point : D) (state : A.obj point) :
    (structuredReadout source atoms worlds arrows atomCoding).app point state ∈
        (Mettapedia.GSLT.Topos.PresheafEventModalities.diamond
          (observedGraph source atoms worlds arrows atomCoding left right) predicate).obj point ↔
      (ULift.up state : (raise A).obj point) ∈
        (Mettapedia.GSLT.Topos.PresheafEventModalities.diamond (sourceGraph left right)
          (preimage (eventObservation source atoms worlds arrows atomCoding left right).states predicate)).obj point :=
  (eventObservation source atoms worlds arrows atomCoding left right).diamond_pullback
    ((outgoing_iff source atoms worlds arrows atomCoding left right).mpr matching) predicate point ⟨state⟩

/-- This is the existing all-future predecessor box, including new receipts
at later restrictions. It is not a universal forward-step operator. -/
theorem contextual_box_square (matching : IncomingMatches source atoms left right)
    (predicate : Subfunctor (structured source atoms worlds arrows atomCoding)) (point : D) (state : A.obj point) :
    (structuredReadout source atoms worlds arrows atomCoding).app point state ∈
        (Mettapedia.GSLT.Topos.PresheafEventModalities.box
          (observedGraph source atoms worlds arrows atomCoding left right) predicate).obj point ↔
      (ULift.up state : (raise A).obj point) ∈
        (Mettapedia.GSLT.Topos.PresheafEventModalities.box (sourceGraph left right)
          (preimage (eventObservation source atoms worlds arrows atomCoding left right).states predicate)).obj point :=
  (eventObservation source atoms worlds arrows atomCoding left right).box_pullback
    ((incoming_iff source atoms worlds arrows atomCoding left right).mpr matching) predicate point ⟨state⟩

end Mettapedia.GSLT.HostChoiceContextualObservedHypersetReceipts
