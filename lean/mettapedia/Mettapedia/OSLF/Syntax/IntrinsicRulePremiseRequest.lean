import Mettapedia.OSLF.Syntax.IntrinsicRuleOccurrencePresheaf
import Mettapedia.OSLF.Syntax.CategoricalScopedEventPremise
import Mettapedia.OSLF.Syntax.CategoricalScopedRuleAction

/-!
# Actual authored premises as categorical event requests

Each ordered premise of an intrinsic authored rule has a presheaf of rule
occurrences, a natural pair of requested endpoints under its local binders,
and a presheaf of individual operational events. Its semantic premise object
is the pullback that keeps an event function exactly when its endpoints
match the authored request. Model maps preserve the individual event rather
than only the existence of a reduction.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.IntrinsicRulePremiseRequest

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding.CategoricalScopedEventPremise
open Mettapedia.OSLF.Binding.IntrinsicRuleOccurrencePresheaf
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalPolynomial
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalSubstitution
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalPresheaf
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalModelPresheaf
open Mettapedia.OSLF.Binding.ScopedOperationalEvidenceExponential
open Mettapedia.OSLF.Binding.MultiBinderPresheaf
open Mettapedia.OSLF.Binding.CategoricalScopedRuleAction

universe u
variable {S : Signature} {M : List (MetaArity S)}
variable (R : List (Rule S M))
variable {A : BindingCloneAlgebra.Algebra.{u} S}

/-- The natural endpoint pair of every individual event, in the explicit
pointwise product used by the authored reduction observation. -/
def modelEndpointPair (Y : SubstitutionModel R A) :
    modelEvents R Y ⟶ FunctorToTypes.prod (states A) (states A) where
  app X := TypeCat.ofHom fun event =>
    (⟨event.1, event.2.1.1⟩, ⟨event.1, event.2.1.2⟩)
  naturality X Z f := by
    apply ConcreteCategory.hom_ext
    rintro ⟨sort, ⟨source, target⟩, evidence⟩
    rfl

/-- The endpoint pair commutes with every ordinary operational-model map;
no target-event coverage or injectivity is assumed. -/
theorem modelEndpointPair_map {Y Z : SubstitutionModel R A}
    (h : SubstitutionModel.Hom R Y Z) :
    mapModelEvents R h ≫ modelEndpointPair R Z =
      modelEndpointPair R Y := by
  ext X event <;>
    rcases event with ⟨sort, ⟨source, target⟩, value⟩ <;>
    rfl

/-- A rule's particular premise at its original list position, with its
own binder context and endpoint sort, interpreted in a lawful model. -/
noncomputable def childRequest (index : Fin R.length)
    (position : Fin (R.get index).premises.length)
    (Y : SubstitutionModel R A) :
    Request (binders A ((R.get index).premises.get position).binders)
      (occurrencePresheaf R (A := A) index)
      (modelEvents R Y)
      (FunctorToTypes.prod (states A) (states A)) where
  endpoints := modelEndpointPair R Y
  required := childEndpointsNat R index position ≫
    (scopedEvidenceIso A
      ((R.get index).premises.get position).binders
      (FunctorToTypes.prod (states A) (states A))).inv

/-- A retained premise witness has the exact authored source and target
under its own binder extension, after the contextual-function comparison.
This equality keeps the event function on the left and the authored
occurrence on the right. -/
theorem childWitnessEndpoints (index : Fin R.length)
    (position : Fin (R.get index).premises.length)
    (Y : SubstitutionModel R A) :
    (event (childRequest R index position Y) ≫
      (ihom (binders A
        ((R.get index).premises.get position).binders)).map
          (modelEndpointPair R Y)) ≫
        (scopedEvidenceIso A
          ((R.get index).premises.get position).binders
          (FunctorToTypes.prod (states A) (states A))).hom =
      parameters (childRequest R index position Y) ≫
        childEndpointsNat R index position := by
  let request := childRequest R index position Y
  let comparison := scopedEvidenceIso A
    ((R.get index).premises.get position).binders
    (FunctorToTypes.prod (states A) (states A))
  have endpoint := endpoint_condition request
  change event request ≫
      (ihom (binders A
        ((R.get index).premises.get position).binders)).map
          (modelEndpointPair R Y) =
    parameters request ≫
      (childEndpointsNat R index position ≫ comparison.inv)
    at endpoint
  calc
    (event request ≫
        (ihom (binders A
          ((R.get index).premises.get position).binders)).map
            (modelEndpointPair R Y)) ≫ comparison.hom =
      (parameters request ≫
        (childEndpointsNat R index position ≫ comparison.inv)) ≫
          comparison.hom := by rw [endpoint]; rfl
    _ = parameters request ≫ childEndpointsNat R index position := by
      simp only [Category.assoc, comparison.inv_hom_id, Category.comp_id]

/-- An interpretation maps a premise witness's individual firing while
leaving the authored occurrence and requested endpoint pair fixed. -/
noncomputable def childRequestMap (index : Fin R.length)
    (position : Fin (R.get index).premises.length)
    {Y Z : SubstitutionModel R A}
    (h : SubstitutionModel.Hom R Y Z) :
    Map (childRequest R index position Y)
      (childRequest R index position Z) where
  parameter := 𝟙 _
  event := mapModelEvents R h
  endpoint := 𝟙 _
  endpoint_comm := by
    change mapModelEvents R h ≫ modelEndpointPair R Z =
      modelEndpointPair R Y ≫ 𝟙 _
    simpa only [Category.comp_id] using modelEndpointPair_map R h
  required_comm := by simp [childRequest]

/-- A complete authored premise request is functorial in lawful operational
models, using their actual event maps and no stronger comparison contract. -/
noncomputable def childRequestFunctor (index : Fin R.length)
    (position : Fin (R.get index).premises.length) :
    SubstitutionModel R A ⥤
      Package (binders A ((R.get index).premises.get position).binders) where
  obj Y := ⟨_, _, _, childRequest R index position Y⟩
  map h := childRequestMap R index position h
  map_id Y := by
    apply Map.ext
    · rfl
    · ext X event
      rfl
    · rfl
  map_comp f g := by
    apply Map.ext
    · rfl
    · ext X event
      rfl
    · rfl

/-- The actual premise-witness object, including its authored occurrence
and individual firing evidence, varies functorially with lawful models. -/
noncomputable def childWitnessFunctor (index : Fin R.length)
    (position : Fin (R.get index).premises.length) :
    SubstitutionModel R A ⥤ (Base A ⥤ Type u) :=
  childRequestFunctor R index position ⋙
    witnessFunctor
      (binders A ((R.get index).premises.get position).binders)

/-- Changing an operational interpretation transports the entire firing
function; its identity is not replaced by an endpoint-existence predicate. -/
theorem childWitnessTransport_event (index : Fin R.length)
    (position : Fin (R.get index).premises.length)
    {Y Z : SubstitutionModel R A}
    (h : SubstitutionModel.Hom R Y Z) :
    mapWitness (childRequest R index position Y)
        (childRequestMap R index position h) ≫
      event (childRequest R index position Z) =
    event (childRequest R index position Y) ≫
      (ihom (binders A
        ((R.get index).premises.get position).binders)).map
          (mapModelEvents R h) :=
  mapWitness_event _ _

/-- The actual ordered list of one rule's categorical premise requests.
Every entry carries its own binder object and original list position. -/
noncomputable def authoredPremises (index : Fin R.length)
    (Y : SubstitutionModel R A) :
    List (Premise
      (occurrencePresheaf R (A := A) index)
      (modelEvents R Y)
      (FunctorToTypes.prod (states A) (states A))) :=
  List.ofFn fun position : Fin (R.get index).premises.length =>
    ⟨binders A ((R.get index).premises.get position).binders,
      childRequest R index position Y⟩

/-- The exact categorical contract for interpreting one authored rule in
a model. The indexed rule action is constructed in
`IntrinsicRuleActionComparison.authoredRuleAction`. -/
abbrev AuthoredRuleAction (index : Fin R.length)
    (Y : SubstitutionModel R A) : Type _ :=
  RuleAction (authoredPremises R index Y)
    (modelEndpointPair R Y)
    (conclusionEndpointsNat R index)

theorem authoredPremises_length (index : Fin R.length)
    (Y : SubstitutionModel R A) :
    (authoredPremises R index Y).length =
      (R.get index).premises.length := by
  simp [authoredPremises]

/-- The original authored premise position, transported to the categorical
list without changing its numeric index. -/
def authoredPosition (index : Fin R.length)
    (Y : SubstitutionModel R A)
    (position : Fin (R.get index).premises.length) :
    Fin (authoredPremises R index Y).length :=
  ⟨position.1, by simp [authoredPremises]⟩

/-- The categorical premise at a given position is exactly the request
constructed from that authored premise's binder context and endpoints. -/
theorem authoredPremises_get (index : Fin R.length)
    (Y : SubstitutionModel R A)
    (position : Fin (R.get index).premises.length) :
    (authoredPremises R index Y).get
      (authoredPosition R index Y position) =
        ⟨binders A ((R.get index).premises.get position).binders,
          childRequest R index position Y⟩ := by
  simp [authoredPremises, authoredPosition]

/-- Every categorical list position recovers its intrinsic authored index
without reordering the rule's premises. -/
theorem authoredPremises_get_at (index : Fin R.length)
    (Y : SubstitutionModel R A)
    (position : Fin (authoredPremises R index Y).length) :
    (authoredPremises R index Y).get position =
      ⟨binders A
          ((R.get index).premises.get
            (position.cast (authoredPremises_length R index Y))).binders,
        childRequest R index
          (position.cast (authoredPremises_length R index Y)) Y⟩ := by
  let authored : Fin (R.get index).premises.length :=
    position.cast (authoredPremises_length R index Y)
  have samePosition : position = authoredPosition R index Y authored :=
    Fin.ext rfl
  rw [samePosition]
  exact authoredPremises_get R index Y authored

/-- Select the retained event witness at an authored premise position. The
equality transport changes only the presentation of the same list entry;
it neither chooses nor merges evidence. -/
noncomputable def authoredProject (index : Fin R.length)
    (position : Fin (R.get index).premises.length)
    (Y : SubstitutionModel R A) :
    Bundle (authoredPremises R index Y) ⟶
      Witness (childRequest R index position Y) :=
  project (authoredPremises R index Y)
      (authoredPosition R index Y position) ≫
    eqToHom (congrArg
      (fun premise : Premise
          (occurrencePresheaf R (A := A) index)
          (modelEvents R Y)
          (FunctorToTypes.prod (states A) (states A)) =>
        Witness premise.request)
      (authoredPremises_get R index Y position))

/-- Each selected premise witness uses the same ambient authored occurrence
as the complete ordered bundle. -/
theorem authoredProject_assignment (index : Fin R.length)
    (position : Fin (R.get index).premises.length)
    (Y : SubstitutionModel R A) :
    authoredProject R index position Y ≫
      parameters (childRequest R index position Y) =
        assignment (authoredPremises R index Y) := by
  unfold authoredProject
  rw [Category.assoc,
    premise_transport_parameters (authoredPremises_get R index Y position)]
  exact project_assignment _ _

/-- A map into an authored ordered premise bundle is determined by its
shared occurrence and every original-position retained witness. -/
theorem authoredBundle_hom_ext (index : Fin R.length)
    (Y : SubstitutionModel R A)
    {T : Base A ⥤ Type u}
    (first second : T ⟶ Bundle (authoredPremises R index Y))
    (sameAssignment :
      first ≫ assignment (authoredPremises R index Y) =
        second ≫ assignment (authoredPremises R index Y))
    (sameWitness : ∀ position : Fin (R.get index).premises.length,
      first ≫ authoredProject R index position Y =
        second ≫ authoredProject R index position Y) :
    first = second := by
  apply bundle_hom_ext (authoredPremises R index Y)
    first second sameAssignment
  intro selected
  let position : Fin (R.get index).premises.length :=
    selected.cast (authoredPremises_length R index Y)
  have selectedEq : selected = authoredPosition R index Y position :=
    Fin.ext rfl
  rw [selectedEq]
  have projected := sameWitness position
  unfold authoredProject at projected
  let transport := eqToHom (congrArg
    (fun premise : Premise
      (occurrencePresheaf R (A := A) index)
      (modelEvents R Y)
      (FunctorToTypes.prod (states A) (states A)) =>
      Witness premise.request)
    (authoredPremises_get R index Y position))
  have composed :
      (first ≫ project (authoredPremises R index Y)
        (authoredPosition R index Y position)) ≫ transport =
      (second ≫ project (authoredPremises R index Y)
        (authoredPosition R index Y position)) ≫ transport :=
    (Category.assoc _ _ _).trans
      (projected.trans (Category.assoc _ _ _).symm)
  exact (cancel_mono transport).mp composed

/-- A model map transports the retained firing at one target premise
position, keeping the original source bundle as its domain. -/
noncomputable def authoredWitnessMapAt (index : Fin R.length)
    {Y Z : SubstitutionModel R A}
    (h : SubstitutionModel.Hom R Y Z)
    (position : Fin (authoredPremises R index Z).length) :
    Bundle (authoredPremises R index Y) ⟶
      Witness ((authoredPremises R index Z).get position).request := by
  let authored : Fin (R.get index).premises.length :=
    position.cast (authoredPremises_length R index Z)
  exact (authoredProject R index authored Y ≫
    mapWitness (childRequest R index authored Y)
      (childRequestMap R index authored h)) ≫
    eqToHom (congrArg
      (fun premise : Premise
          (occurrencePresheaf R (A := A) index)
          (modelEvents R Z)
          (FunctorToTypes.prod (states A) (states A)) =>
        Witness premise.request)
      (authoredPremises_get_at R index Z position).symm)

/-- Mapping one retained premise firing through a model interpretation
does not change the rule's ambient parameter occurrence. -/
theorem authoredWitnessMapAt_assignment (index : Fin R.length)
    {Y Z : SubstitutionModel R A}
    (h : SubstitutionModel.Hom R Y Z)
    (position : Fin (authoredPremises R index Z).length) :
    authoredWitnessMapAt R index h position ≫
        parameters ((authoredPremises R index Z).get position).request =
      assignment (authoredPremises R index Y) := by
  let authored : Fin (R.get index).premises.length :=
    position.cast (authoredPremises_length R index Z)
  have targetGet := authoredPremises_get_at R index Z position
  change ((authoredProject R index authored Y ≫
    mapWitness (childRequest R index authored Y)
      (childRequestMap R index authored h)) ≫
    eqToHom (congrArg
      (fun premise : Premise
          (occurrencePresheaf R (A := A) index)
          (modelEvents R Z)
          (FunctorToTypes.prod (states A) (states A)) =>
        Witness premise.request) targetGet.symm)) ≫
      parameters ((authoredPremises R index Z).get position).request =
    assignment (authoredPremises R index Y)
  rw [Category.assoc,
    premise_transport_parameters targetGet.symm,
    Category.assoc, mapWitness_parameters]
  exact authoredProject_assignment R index authored Y

/-- Mapping a selected premise witness maps its individual event function.
The only final transport changes the presentation of the target list entry. -/
theorem authoredWitnessMapAt_event (index : Fin R.length)
    {Y Z : SubstitutionModel R A}
    (h : SubstitutionModel.Hom R Y Z)
    (position : Fin (authoredPremises R index Z).length) :
    let authored := position.cast (authoredPremises_length R index Z)
    authoredWitnessMapAt R index h position ≫
        event ((authoredPremises R index Z).get position).request =
      ((authoredProject R index authored Y ≫
          event (childRequest R index authored Y)) ≫
        (ihom (binders A
          ((R.get index).premises.get authored).binders)).map
            (mapModelEvents R h)) ≫
        eqToHom (congrArg
          (fun premise : Premise
              (occurrencePresheaf R (A := A) index)
              (modelEvents R Z)
              (FunctorToTypes.prod (states A) (states A)) =>
            (ihom premise.binder).obj (modelEvents R Z))
          (authoredPremises_get_at R index Z position).symm) := by
  let authored := position.cast (authoredPremises_length R index Z)
  change ((authoredProject R index authored Y ≫
      mapWitness (childRequest R index authored Y)
        (childRequestMap R index authored h)) ≫
      eqToHom (congrArg
        (fun premise : Premise
            (occurrencePresheaf R (A := A) index)
            (modelEvents R Z)
            (FunctorToTypes.prod (states A) (states A)) =>
          Witness premise.request)
        (authoredPremises_get_at R index Z position).symm)) ≫
      event ((authoredPremises R index Z).get position).request = _
  rw [Category.assoc,
    premise_transport_event
      (authoredPremises_get_at R index Z position).symm]
  change ((authoredProject R index authored Y ≫
      mapWitness (childRequest R index authored Y)
        (childRequestMap R index authored h)) ≫
      event (childRequest R index authored Z)) ≫
      eqToHom (congrArg
        (fun premise : Premise
            (occurrencePresheaf R (A := A) index)
            (modelEvents R Z)
            (FunctorToTypes.prod (states A) (states A)) =>
          (ihom premise.binder).obj (modelEvents R Z))
        (authoredPremises_get_at R index Z position).symm) = _
  rw [Category.assoc (authoredProject R index authored Y)
      (mapWitness (childRequest R index authored Y)
        (childRequestMap R index authored h))
      (event (childRequest R index authored Z)),
    mapWitness_event (childRequest R index authored Y)
      (childRequestMap R index authored h)]
  rfl

/-- A lawful model map transports the entire ordered conditional input.
Every premise retains its original position and individual firing witness;
the shared authored occurrence is unchanged. -/
noncomputable def authoredBundleMap (index : Fin R.length)
    {Y Z : SubstitutionModel R A}
    (h : SubstitutionModel.Hom R Y Z) :
    Bundle (authoredPremises R index Y) ⟶
      Bundle (authoredPremises R index Z) :=
  liftCone (authoredPremises R index Z) {
    parameter := assignment (authoredPremises R index Y)
    witness := authoredWitnessMapAt R index h
    agrees := authoredWitnessMapAt_assignment R index h
  }

theorem authoredBundleMap_assignment (index : Fin R.length)
    {Y Z : SubstitutionModel R A}
    (h : SubstitutionModel.Hom R Y Z) :
    authoredBundleMap R index h ≫
        assignment (authoredPremises R index Z) =
      assignment (authoredPremises R index Y) := by
  exact liftCone_assignment _ _

/-- At each contextual environment, interpreting all ordered premise
firings leaves the actual rule occurrence unchanged. -/
theorem authoredBundleMap_assignment_at (index : Fin R.length)
    {Y Z : SubstitutionModel R A}
    (h : SubstitutionModel.Hom R Y Z)
    (X : Base A)
    (input : (Bundle (authoredPremises R index Y)).obj X) :
    (assignment (authoredPremises R index Z)).app X
        ((authoredBundleMap R index h).app X input) =
      (assignment (authoredPremises R index Y)).app X input := by
  have atX := congrArg
    (fun transformation => transformation.app X)
    (authoredBundleMap_assignment R index h)
  exact ConcreteCategory.congr_hom atX input

theorem authoredBundleMap_project (index : Fin R.length)
    {Y Z : SubstitutionModel R A}
    (h : SubstitutionModel.Hom R Y Z)
    (position : Fin (authoredPremises R index Z).length) :
    authoredBundleMap R index h ≫
        project (authoredPremises R index Z) position =
      authoredWitnessMapAt R index h position := by
  exact liftCone_project _ _ position

/-- The bundle map at an original authored position is exactly the map of
that premise's retained witness. No permutation or identification of
premise occurrences is involved. -/
theorem authoredBundleMap_authoredProject (index : Fin R.length)
    (position : Fin (R.get index).premises.length)
    {Y Z : SubstitutionModel R A}
    (h : SubstitutionModel.Hom R Y Z) :
    authoredBundleMap R index h ≫ authoredProject R index position Z =
      authoredProject R index position Y ≫
        mapWitness (childRequest R index position Y)
          (childRequestMap R index position h) := by
  unfold authoredProject
  rw [← Category.assoc, authoredBundleMap_project]
  unfold authoredWitnessMapAt
  unfold authoredProject
  simp only [Category.assoc]
  simp only [eqToHom_trans]
  rfl

/-- The ordered premise bundle transport acts as the identity on every
individual witness when the model interpretation is the identity. -/
theorem authoredBundleMap_id (index : Fin R.length)
    (Y : SubstitutionModel R A) :
    authoredBundleMap R index (𝟙 Y) =
      𝟙 (Bundle (authoredPremises R index Y)) := by
  apply authoredBundle_hom_ext R index Y
  · simpa only [Category.id_comp] using
      authoredBundleMap_assignment R index (𝟙 Y)
  · intro position
    have hrequest : childRequestMap R index position (𝟙 Y) =
        Map.id (childRequest R index position Y) :=
      (childRequestFunctor R index position).map_id Y
    calc
      authoredBundleMap R index (𝟙 Y) ≫
          authoredProject R index position Y =
        authoredProject R index position Y ≫
          mapWitness (childRequest R index position Y)
            (childRequestMap R index position (𝟙 Y)) :=
              authoredBundleMap_authoredProject R index position (𝟙 Y)
      _ = authoredProject R index position Y ≫
          mapWitness (childRequest R index position Y)
            (Map.id (childRequest R index position Y)) := by rw [hrequest]
      _ = authoredProject R index position Y ≫
          𝟙 (Witness (childRequest R index position Y)) := by
            rw [mapWitness_id]
      _ = 𝟙 (Bundle (authoredPremises R index Y)) ≫
          authoredProject R index position Y := by simp

/-- Transport of ordered premise bundles respects composition of lawful
model interpretations, with the same occurrence and each firing retained. -/
theorem authoredBundleMap_comp (index : Fin R.length)
    {Y Z W : SubstitutionModel R A}
    (f : Y ⟶ Z) (g : Z ⟶ W) :
    authoredBundleMap R index (f ≫ g) =
      authoredBundleMap R index f ≫ authoredBundleMap R index g := by
  apply authoredBundle_hom_ext R index W
  · calc
      authoredBundleMap R index (f ≫ g) ≫
          assignment (authoredPremises R index W) =
        assignment (authoredPremises R index Y) :=
          authoredBundleMap_assignment R index (f ≫ g)
      _ = (authoredBundleMap R index f ≫
            authoredBundleMap R index g) ≫
          assignment (authoredPremises R index W) := by
        rw [Category.assoc, authoredBundleMap_assignment,
          authoredBundleMap_assignment]
  · intro position
    let reqY := childRequest R index position Y
    let reqZ := childRequest R index position Z
    let reqW := childRequest R index position W
    let mapF := childRequestMap R index position f
    let mapG := childRequestMap R index position g
    have hrequest : childRequestMap R index position (f ≫ g) =
        Map.comp mapF mapG :=
      (childRequestFunctor R index position).map_comp f g
    calc
      authoredBundleMap R index (f ≫ g) ≫
          authoredProject R index position W =
        authoredProject R index position Y ≫
          mapWitness reqY
            (childRequestMap R index position (f ≫ g)) :=
              authoredBundleMap_authoredProject R index position (f ≫ g)
      _ = authoredProject R index position Y ≫
          mapWitness reqY (Map.comp mapF mapG) := by rw [hrequest]
      _ = authoredProject R index position Y ≫
          (mapWitness reqY mapF ≫ mapWitness reqZ mapG) := by
            rw [mapWitness_comp]
      _ = (authoredProject R index position Y ≫
          mapWitness reqY mapF) ≫ mapWitness reqZ mapG :=
            (Category.assoc _ _ _).symm
      _ = (authoredBundleMap R index f ≫
          authoredProject R index position Z) ≫
            mapWitness reqZ mapG := by
              rw [authoredBundleMap_authoredProject]
      _ = authoredBundleMap R index f ≫
          (authoredProject R index position Z ≫
            mapWitness reqZ mapG) := Category.assoc _ _ _
      _ = authoredBundleMap R index f ≫
          (authoredBundleMap R index g ≫
            authoredProject R index position W) := by
              rw [authoredBundleMap_authoredProject]
      _ = (authoredBundleMap R index f ≫
          authoredBundleMap R index g) ≫
          authoredProject R index position W :=
            (Category.assoc _ _ _).symm

/-- The complete ordered conditional input varies functorially with the
lawful operational model, preserving individual scoped event witnesses. -/
noncomputable def authoredBundleFunctor (index : Fin R.length) :
    SubstitutionModel R A ⥤ (Base A ⥤ Type u) where
  obj Y := Bundle (authoredPremises R index Y)
  map h := authoredBundleMap R index h
  map_id Y := authoredBundleMap_id R index Y
  map_comp f g := authoredBundleMap_comp R index f g

/-- Each premise event in the mapped full bundle is the original event
mapped by the operational interpretation, with only its target list-entry
presentation transported. -/
theorem authoredBundleMap_project_event (index : Fin R.length)
    {Y Z : SubstitutionModel R A}
    (h : SubstitutionModel.Hom R Y Z)
    (position : Fin (authoredPremises R index Z).length) :
    let authored := position.cast (authoredPremises_length R index Z)
    (authoredBundleMap R index h ≫
        project (authoredPremises R index Z) position) ≫
        event ((authoredPremises R index Z).get position).request =
      ((authoredProject R index authored Y ≫
          event (childRequest R index authored Y)) ≫
        (ihom (binders A
          ((R.get index).premises.get authored).binders)).map
            (mapModelEvents R h)) ≫
        eqToHom (congrArg
          (fun premise : Premise
              (occurrencePresheaf R (A := A) index)
              (modelEvents R Z)
              (FunctorToTypes.prod (states A) (states A)) =>
            (ihom premise.binder).obj (modelEvents R Z))
          (authoredPremises_get_at R index Z position).symm) := by
  rw [authoredBundleMap_project R index h position]
  exact authoredWitnessMapAt_event R index h position

/-- Every projected firing in the complete ordered input bundle matches
the source and target requested by that authored premise, under its own
binders and the same ambient occurrence. -/
theorem authoredBundleChildEndpoints (index : Fin R.length)
    (position : Fin (R.get index).premises.length)
    (Y : SubstitutionModel R A) :
    ((authoredProject R index position Y ≫
      event (childRequest R index position Y)) ≫
      (ihom (binders A
        ((R.get index).premises.get position).binders)).map
          (modelEndpointPair R Y)) ≫
        (scopedEvidenceIso A
          ((R.get index).premises.get position).binders
          (FunctorToTypes.prod (states A) (states A))).hom =
      assignment (authoredPremises R index Y) ≫
        childEndpointsNat R index position := by
  let family := authoredPremises R index Y
  let selected := authoredPosition R index Y position
  have hselected := authoredPremises_get R index Y position
  have hchild := childWitnessEndpoints R index position Y
  have htransport := authoredProject_assignment R index position Y
  calc
    ((authoredProject R index position Y ≫
        event (childRequest R index position Y)) ≫
        (ihom (binders A
          ((R.get index).premises.get position).binders)).map
            (modelEndpointPair R Y)) ≫
          (scopedEvidenceIso A
            ((R.get index).premises.get position).binders
            (FunctorToTypes.prod (states A) (states A))).hom =
      authoredProject R index position Y ≫
        ((event (childRequest R index position Y) ≫
          (ihom (binders A
            ((R.get index).premises.get position).binders)).map
              (modelEndpointPair R Y)) ≫
          (scopedEvidenceIso A
            ((R.get index).premises.get position).binders
            (FunctorToTypes.prod (states A) (states A))).hom) := by
              rw [Category.assoc
                (authoredProject R index position Y)
                (event (childRequest R index position Y))
                ((ihom (binders A
                  ((R.get index).premises.get position).binders)).map
                    (modelEndpointPair R Y))]
              exact Category.assoc _ _ _
    _ = authoredProject R index position Y ≫
        (parameters (childRequest R index position Y) ≫
          childEndpointsNat R index position) := by rw [hchild]
    _ = assignment family ≫ childEndpointsNat R index position := by
          rw [← Category.assoc, htransport]

/-- The complete premise bundle retains the actual firing under the
premise's binder extension, rather than merely its endpoint predicate. -/
noncomputable def authoredChildFiring (index : Fin R.length)
    (position : Fin (R.get index).premises.length)
    (Y : SubstitutionModel R A) :
    Bundle (authoredPremises R index Y) ⟶
      scopedEvidence A ((R.get index).premises.get position).binders
        (modelEvents R Y) :=
  (authoredProject R index position Y ≫
    event (childRequest R index position Y)) ≫
      (scopedEvidenceIso A
        ((R.get index).premises.get position).binders
        (modelEvents R Y)).hom

/-- A model interpretation transports each authored child firing under its
own binder extension. This is equality of the retained event functions, not
only of their endpoint observations. -/
theorem authoredChildFiring_map (index : Fin R.length)
    (position : Fin (R.get index).premises.length)
    {Y Z : SubstitutionModel R A}
    (h : SubstitutionModel.Hom R Y Z) :
    authoredBundleMap R index h ≫ authoredChildFiring R index position Z =
      authoredChildFiring R index position Y ≫
        (scopedEvidenceFunctor A
          ((R.get index).premises.get position).binders).map
            (mapModelEvents R h) := by
  let scope := ((R.get index).premises.get position).binders
  have natural :=
    (scopedEvidenceFunctorIso A scope).hom.naturality (mapModelEvents R h)
  change (ihom (binders A scope)).map (mapModelEvents R h) ≫
      (scopedEvidenceIso A scope (modelEvents R Z)).hom =
    (scopedEvidenceIso A scope (modelEvents R Y)).hom ≫
      (scopedEvidenceFunctor A scope).map (mapModelEvents R h)
    at natural
  let sourceFiring : Bundle (authoredPremises R index Y) ⟶
      ((binders A scope).functorHom (modelEvents R Y)) :=
    authoredProject R index position Y ≫
      event (childRequest R index position Y)
  let targetFiring : Bundle (authoredPremises R index Z) ⟶
      ((binders A scope).functorHom (modelEvents R Z)) :=
    authoredProject R index position Z ≫
      event (childRequest R index position Z)
  change (authoredBundleMap R index h ≫ targetFiring) ≫
      (scopedEvidenceIso A scope (modelEvents R Z)).hom =
    (sourceFiring ≫
        (scopedEvidenceIso A scope (modelEvents R Y)).hom) ≫
      (scopedEvidenceFunctor A scope).map (mapModelEvents R h)
  have firingMap :
      authoredBundleMap R index h ≫ targetFiring =
        sourceFiring ≫
          (ihom (binders A scope)).map (mapModelEvents R h) := by
    let sourceProject := authoredProject R index position Y
    let targetProject := authoredProject R index position Z
    let sourceRequest := childRequest R index position Y
    let targetRequest := childRequest R index position Z
    let witnessMap := mapWitness sourceRequest
      (childRequestMap R index position h)
    change authoredBundleMap R index h ≫
        (targetProject ≫ event targetRequest) =
      (sourceProject ≫ event sourceRequest) ≫
        (ihom (binders A scope)).map (mapModelEvents R h)
    calc
      authoredBundleMap R index h ≫
          (targetProject ≫ event targetRequest) =
        (authoredBundleMap R index h ≫ targetProject) ≫
          event targetRequest := (Category.assoc _ _ _).symm
      _ = (sourceProject ≫ witnessMap) ≫ event targetRequest := by
        rw [show authoredBundleMap R index h ≫ targetProject =
          sourceProject ≫ witnessMap from
            authoredBundleMap_authoredProject R index position h]
      _ = sourceProject ≫ (witnessMap ≫ event targetRequest) :=
        Category.assoc _ _ _
      _ = sourceProject ≫
          (event sourceRequest ≫
            (ihom (binders A scope)).map (mapModelEvents R h)) := by
        rw [mapWitness_event]
        rfl
      _ = (sourceProject ≫ event sourceRequest) ≫
          (ihom (binders A scope)).map (mapModelEvents R h) :=
        (Category.assoc _ _ _).symm
  let mapped := (ihom (binders A scope)).map (mapModelEvents R h)
  let isoY := (scopedEvidenceIso A scope (modelEvents R Y)).hom
  let isoZ := (scopedEvidenceIso A scope (modelEvents R Z)).hom
  let scopedMap := (scopedEvidenceFunctor A scope).map (mapModelEvents R h)
  have first :
      (authoredBundleMap R index h ≫ targetFiring) ≫ isoZ =
        (sourceFiring ≫ mapped) ≫ isoZ :=
    congrArg (fun arrow => arrow ≫ isoZ) firingMap
  have second :
      (sourceFiring ≫ mapped) ≫ isoZ =
        sourceFiring ≫ (mapped ≫ isoZ) :=
    Category.assoc _ _ _
  have third :
      sourceFiring ≫ (mapped ≫ isoZ) =
        sourceFiring ≫ (isoY ≫ scopedMap) :=
    congrArg (fun arrow => sourceFiring ≫ arrow) natural
  have fourth :
      sourceFiring ≫ (isoY ≫ scopedMap) =
        (sourceFiring ≫ isoY) ≫ scopedMap :=
    (Category.assoc _ _ _).symm
  exact first.trans (second.trans (third.trans fourth))

/-- Observing the actual binder-extended firing gives exactly the authored
child endpoints. This is the square needed to extract typed recursive
evidence for the existing indexed rule algebra. -/
theorem authoredChildFiring_endpoints (index : Fin R.length)
    (position : Fin (R.get index).premises.length)
    (Y : SubstitutionModel R A) :
    authoredChildFiring R index position Y ≫
      (scopedEvidenceFunctor A
        ((R.get index).premises.get position).binders).map
          (modelEndpointPair R Y) =
      assignment (authoredPremises R index Y) ≫
        childEndpointsNat R index position := by
  let scope := ((R.get index).premises.get position).binders
  let observation := modelEndpointPair R Y
  let firing : Bundle (authoredPremises R index Y) ⟶
      ((binders A scope).functorHom (modelEvents R Y)) :=
    authoredProject R index position Y ≫
      event (childRequest R index position Y)
  let mapped :
      ((binders A scope).functorHom (modelEvents R Y)) ⟶
        ((binders A scope).functorHom
          (FunctorToTypes.prod (states A) (states A))) :=
    (ihom (binders A scope)).map observation
  have natural :=
    (scopedEvidenceFunctorIso A scope).hom.naturality observation
  change mapped ≫
      (scopedEvidenceIso A scope
        (FunctorToTypes.prod (states A) (states A))).hom =
    (scopedEvidenceIso A scope (modelEvents R Y)).hom ≫
      (scopedEvidenceFunctor A scope).map observation at natural
  change (firing ≫
      (scopedEvidenceIso A scope (modelEvents R Y)).hom) ≫
        (scopedEvidenceFunctor A scope).map observation = _
  have hWhisker :
      firing ≫ ((scopedEvidenceIso A scope (modelEvents R Y)).hom ≫
        (scopedEvidenceFunctor A scope).map observation) =
      firing ≫ (mapped ≫
        (scopedEvidenceIso A scope
          (FunctorToTypes.prod (states A) (states A))).hom) :=
    congrArg (fun arrow => firing ≫ arrow) natural.symm
  have hAssocFirst :
      (firing ≫ (scopedEvidenceIso A scope (modelEvents R Y)).hom) ≫
          (scopedEvidenceFunctor A scope).map observation =
        firing ≫ ((scopedEvidenceIso A scope (modelEvents R Y)).hom ≫
          (scopedEvidenceFunctor A scope).map observation) :=
    Category.assoc _ _ _
  have hAssocSecond :
      firing ≫ (mapped ≫
          (scopedEvidenceIso A scope
            (FunctorToTypes.prod (states A) (states A))).hom) =
        (firing ≫ mapped) ≫
          (scopedEvidenceIso A scope
            (FunctorToTypes.prod (states A) (states A))).hom :=
    (Category.assoc _ _ _).symm
  exact hAssocFirst.trans (hWhisker.trans
    (hAssocSecond.trans (authoredBundleChildEndpoints R index position Y)))

end Mettapedia.OSLF.Binding.IntrinsicRulePremiseRequest

#print axioms Mettapedia.OSLF.Binding.IntrinsicRulePremiseRequest.childRequest
#print axioms Mettapedia.OSLF.Binding.IntrinsicRulePremiseRequest.childWitnessEndpoints
#print axioms Mettapedia.OSLF.Binding.IntrinsicRulePremiseRequest.childRequestFunctor
#print axioms Mettapedia.OSLF.Binding.IntrinsicRulePremiseRequest.childWitnessTransport_event
#print axioms Mettapedia.OSLF.Binding.IntrinsicRulePremiseRequest.authoredPremises_length
#print axioms Mettapedia.OSLF.Binding.IntrinsicRulePremiseRequest.authoredPremises_get_at
#print axioms Mettapedia.OSLF.Binding.IntrinsicRulePremiseRequest.authoredBundle_hom_ext
#print axioms Mettapedia.OSLF.Binding.IntrinsicRulePremiseRequest.authoredWitnessMapAt_event
#print axioms Mettapedia.OSLF.Binding.IntrinsicRulePremiseRequest.authoredBundleMap
#print axioms Mettapedia.OSLF.Binding.IntrinsicRulePremiseRequest.authoredBundleMap_assignment
#print axioms Mettapedia.OSLF.Binding.IntrinsicRulePremiseRequest.authoredBundleMap_project
#print axioms Mettapedia.OSLF.Binding.IntrinsicRulePremiseRequest.authoredBundleMap_authoredProject
#print axioms Mettapedia.OSLF.Binding.IntrinsicRulePremiseRequest.authoredBundleFunctor
#print axioms Mettapedia.OSLF.Binding.IntrinsicRulePremiseRequest.authoredBundleMap_project_event
#print axioms Mettapedia.OSLF.Binding.IntrinsicRulePremiseRequest.authoredBundleChildEndpoints
#print axioms Mettapedia.OSLF.Binding.IntrinsicRulePremiseRequest.authoredChildFiring_map
#print axioms Mettapedia.OSLF.Binding.IntrinsicRulePremiseRequest.authoredChildFiring_endpoints
