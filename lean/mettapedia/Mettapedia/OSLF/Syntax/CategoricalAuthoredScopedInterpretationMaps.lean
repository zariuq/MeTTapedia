import Mettapedia.OSLF.Syntax.CategoricalAuthoredProgramCarrierMaps

/-!
# Varying-base maps of authored conditional premises

A map of binding models and common program carriers determines the ordinary
parameter and endpoint arrows. At a binder-local operational premise it
still needs a coherent map of contextual firing functions. This module
connects those explicit maps to the actual ordered authored-rule input.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.CategoricalAuthoredScopedInterpretationMaps

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open Mettapedia.OSLF.Binding.CategoricalBindingModel
open Mettapedia.OSLF.Binding.CategoricalScopedEventPremise
open Mettapedia.OSLF.Binding.CategoricalScopedRuleAction
open Mettapedia.OSLF.Binding.CategoricalScopedRuleActionMaps
open Mettapedia.OSLF.Binding.CategoricalAuthoredRuleInterpretation
open Mettapedia.OSLF.Binding.CategoricalAuthoredProgramCarrierMaps
open Mettapedia.OSLF.Binding.CategoricalScopedEventBaseChange

universe u v
variable {S : Signature} {schema : List (MetaArity S)}
variable {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D]
  [MonoidalClosed D] [HasPullbacks D]
variable {X Y : ModelWithPrograms S D}
variable (h : ModelWithPrograms.Hom X Y)
variable {E E' : D}
variable {endpoints : E ⟶ EndpointPairs X.binding X.carrier}
variable {endpoints' : E' ⟶ EndpointPairs Y.binding Y.carrier}
variable (eventMap : E ⟶ E')
variable (rule : IntrinsicScopedConditionalPolynomial.Rule S schema)

/-- Coherent contextual transport for every premise of one actual authored
rule. Its binder, event, endpoint and parameter components are required to
be the maps of the same global interpretation. -/
structure RulePremiseTransport where
  premise : (position : Fin rule.premises.length) →
    PointwiseMap
      (premiseRequest X.binding X.carrier E endpoints
        (rule.premises.get position))
      (premiseRequest Y.binding Y.carrier E' endpoints'
        (rule.premises.get position))
  binder_comm : ∀ position,
    (premise position).binder =
      Model.ctxMap h.binding.underlying.sort
        (rule.premises.get position).binders
  event_comm : ∀ position, (premise position).event = eventMap
  endpoint_comm : ∀ position,
    (premise position).endpoint = h.endpointMap
  parameter_comm : ∀ position,
    (premise position).contextual.parameter =
      h.parameterMap (schema := schema) rule.conclusion.ctx

namespace RulePremiseTransport

omit [HasPullbacks D] in
@[ext] theorem ext {X Y : ModelWithPrograms S D}
    {h : ModelWithPrograms.Hom X Y}
    {E E' : D}
    {endpoints : E ⟶ EndpointPairs X.binding X.carrier}
    {endpoints' : E' ⟶ EndpointPairs Y.binding Y.carrier}
    {eventMap : E ⟶ E'}
    {rule : IntrinsicScopedConditionalPolynomial.Rule S schema}
    {first second : RulePremiseTransport (endpoints := endpoints)
      (endpoints' := endpoints') h eventMap rule}
    (same : ∀ position, first.premise position = second.premise position) :
    first = second := by
  cases first
  cases second
  congr 1
  funext position
  exact same position

/-- Identity on all of an authored rule's scoped premises. -/
noncomputable def id (X : ModelWithPrograms S D)
    {E : D} (endpoints : E ⟶ EndpointPairs X.binding X.carrier)
    (rule : IntrinsicScopedConditionalPolynomial.Rule S schema) :
    RulePremiseTransport (endpoints := endpoints)
      (endpoints' := endpoints) (ModelWithPrograms.Hom.id X)
      (𝟙 E) rule where
  premise position := PointwiseMap.id
    (premiseRequest X.binding X.carrier E endpoints
      (rule.premises.get position))
  binder_comm := by
    intro position
    change 𝟙 (X.binding.ctx (rule.premises.get position).binders) =
      Model.ctxMap (M := X.binding) (N := X.binding)
        (fun s => 𝟙 (X.binding.sort s))
        (rule.premises.get position).binders
    exact (Model.ctxMap_id X.binding _).symm
  event_comm := by intro; rfl
  endpoint_comm := by
    intro position
    change 𝟙 _ =
      (ModelWithPrograms.Hom.id X).endpointMap
    exact (ModelWithPrograms.Hom.endpointMap_id X).symm
  parameter_comm := by
    intro position
    change 𝟙 _ =
      (ModelWithPrograms.Hom.id X).parameterMap
        (schema := schema) rule.conclusion.ctx
    exact (ModelWithPrograms.Hom.parameterMap_id
      (schema := schema) X rule.conclusion.ctx).symm

/-- Compose pointwise interpretations of every authored binder-local
premise, retaining their exact order and shared parameter assignment. -/
noncomputable def comp {X Y Z : ModelWithPrograms S D}
    (h : ModelWithPrograms.Hom X Y)
    (k : ModelWithPrograms.Hom Y Z)
    {E E' E'' : D}
    {endpoints : E ⟶ EndpointPairs X.binding X.carrier}
    {endpoints' : E' ⟶ EndpointPairs Y.binding Y.carrier}
    {endpoints'' : E'' ⟶ EndpointPairs Z.binding Z.carrier}
    (f : E ⟶ E') (g : E' ⟶ E'')
    (rule : IntrinsicScopedConditionalPolynomial.Rule S schema)
    (first : RulePremiseTransport (endpoints := endpoints)
      (endpoints' := endpoints') h f rule)
    (second : RulePremiseTransport (endpoints := endpoints')
      (endpoints' := endpoints'') k g rule) :
    RulePremiseTransport (endpoints := endpoints)
      (endpoints' := endpoints'') (h.comp k) (f ≫ g) rule where
  premise position := PointwiseMap.comp
    (first.premise position) (second.premise position)
  binder_comm := by
    intro position
    change (first.premise position).binder ≫
        (second.premise position).binder = _
    rw [first.binder_comm position, second.binder_comm position]
    exact (Model.ctxMap_comp h.binding.underlying.sort
      k.binding.underlying.sort _).symm
  event_comm := by
    intro position
    change (first.premise position).event ≫
        (second.premise position).event = f ≫ g
    rw [first.event_comm position, second.event_comm position]
  endpoint_comm := by
    intro position
    change (first.premise position).endpoint ≫
        (second.premise position).endpoint = (h.comp k).endpointMap
    rw [first.endpoint_comm position, second.endpoint_comm position]
    exact (ModelWithPrograms.Hom.endpointMap_comp h k).symm
  parameter_comm := by
    intro position
    change (first.premise position).contextual.parameter ≫
        (second.premise position).contextual.parameter =
      (h.comp k).parameterMap (schema := schema) rule.conclusion.ctx
    rw [first.parameter_comm position, second.parameter_comm position]
    exact (ModelWithPrograms.Hom.parameterMap_comp
      (schema := schema) h k rule.conclusion.ctx).symm

end RulePremiseTransport

variable (transport : RulePremiseTransport h eventMap rule)

/-- The witness at a concrete authored premise position is transported by
the pointwise contextual event map, with only equality casts reconciling
the list presentation. -/
noncomputable def witnessAt (position : Fin rule.premises.length) :
    Witness ((rulePremises X.binding X.carrier E endpoints rule).get
      (position.cast
        (rulePremises_length X.binding X.carrier E endpoints rule).symm)).request ⟶
    Witness ((rulePremises Y.binding Y.carrier E' endpoints' rule).get
      (position.cast
        (rulePremises_length Y.binding Y.carrier E' endpoints' rule).symm)).request := by
  let sourceEntry := rulePremises_get X.binding X.carrier E endpoints rule position
  let targetEntry := rulePremises_get Y.binding Y.carrier E' endpoints' rule position
  exact
    eqToHom (congrArg
      (fun premise : Premise
        (Parameters (schema := schema) X.binding rule.conclusion.ctx)
        E (EndpointPairs X.binding X.carrier) => Witness premise.request)
      sourceEntry) ≫
    mapWitness (transport.premise position).contextual ≫
    eqToHom (congrArg
      (fun premise : Premise
        (Parameters (schema := schema) Y.binding rule.conclusion.ctx)
        E' (EndpointPairs Y.binding Y.carrier) => Witness premise.request)
      targetEntry.symm)

/-- Identity transport fixes the actual firing occurrence selected by an
authored premise position. -/
theorem witnessAt_id (X : ModelWithPrograms S D)
    {E : D} (endpoints : E ⟶ EndpointPairs X.binding X.carrier)
    (rule : IntrinsicScopedConditionalPolynomial.Rule S schema)
    (position : Fin rule.premises.length) :
    witnessAt (endpoints := endpoints) (endpoints' := endpoints)
      (ModelWithPrograms.Hom.id X) (𝟙 E) rule
      (RulePremiseTransport.id X endpoints rule) position = 𝟙 _ := by
  unfold witnessAt
  dsimp only [RulePremiseTransport.id, PointwiseMap.id]
  rw [CategoricalScopedEventBaseChange.mapWitness_id]
  simp

/-- The same authored firing occurrence is followed through two changes of
binding model, program carrier, and event object. -/
theorem witnessAt_comp {X Y Z : ModelWithPrograms S D}
    (h : ModelWithPrograms.Hom X Y)
    (k : ModelWithPrograms.Hom Y Z)
    {E E' E'' : D}
    {endpoints : E ⟶ EndpointPairs X.binding X.carrier}
    {endpoints' : E' ⟶ EndpointPairs Y.binding Y.carrier}
    {endpoints'' : E'' ⟶ EndpointPairs Z.binding Z.carrier}
    (f : E ⟶ E') (g : E' ⟶ E'')
    (rule : IntrinsicScopedConditionalPolynomial.Rule S schema)
    (first : RulePremiseTransport (endpoints := endpoints)
      (endpoints' := endpoints') h f rule)
    (second : RulePremiseTransport (endpoints := endpoints')
      (endpoints' := endpoints'') k g rule)
    (position : Fin rule.premises.length) :
    witnessAt (endpoints := endpoints) (endpoints' := endpoints'')
      (h.comp k) (f ≫ g) rule
      (RulePremiseTransport.comp h k f g rule first second) position =
    witnessAt h f rule first position ≫
      witnessAt k g rule second position := by
  unfold witnessAt
  dsimp only [RulePremiseTransport.comp, PointwiseMap.comp]
  rw [CategoricalScopedEventBaseChange.mapWitness_comp]
  simp [Category.assoc]

/-- Every selected witness uses the same mapped parameter assignment as
the full authored rule, despite carrying its own local binder context. -/
theorem witnessAt_parameters (position : Fin rule.premises.length) :
    witnessAt h eventMap rule transport position ≫
      parameters ((rulePremises Y.binding Y.carrier E' endpoints' rule).get
        (position.cast
          (rulePremises_length Y.binding Y.carrier E' endpoints' rule).symm)).request =
    parameters ((rulePremises X.binding X.carrier E endpoints rule).get
      (position.cast
        (rulePremises_length X.binding X.carrier E endpoints rule).symm)).request ≫
      h.parameterMap (schema := schema) rule.conclusion.ctx := by
  let sourceEntry := rulePremises_get X.binding X.carrier E endpoints rule position
  let targetEntry := rulePremises_get Y.binding Y.carrier E' endpoints' rule position
  change ((eqToHom (congrArg
      (fun premise : Premise
        (Parameters (schema := schema) X.binding rule.conclusion.ctx)
        E (EndpointPairs X.binding X.carrier) => Witness premise.request)
      sourceEntry) ≫
    mapWitness (transport.premise position).contextual ≫
    eqToHom (congrArg
      (fun premise : Premise
        (Parameters (schema := schema) Y.binding rule.conclusion.ctx)
        E' (EndpointPairs Y.binding Y.carrier) => Witness premise.request)
      targetEntry.symm))) ≫ _ = _
  rw [Category.assoc, Category.assoc,
    premise_transport_parameters targetEntry.symm,
    CategoricalScopedEventBaseChange.mapWitness_parameters]
  rw [transport.parameter_comm position]
  rw [← Category.assoc]
  exact congrArg (fun arrow => arrow ≫
    h.parameterMap (schema := schema) rule.conclusion.ctx)
    (premise_transport_parameters sourceEntry)

/-- The actual authored premise list yields an ordered input map of
pullback bundles across varying semantic binding models. -/
noncomputable def inputMap :
    InputMap
      (rulePremises X.binding X.carrier E endpoints rule)
      (rulePremises Y.binding Y.carrier E' endpoints' rule) where
  sameLength :=
    (rulePremises_length X.binding X.carrier E endpoints rule).trans
      (rulePremises_length Y.binding Y.carrier E' endpoints' rule).symm
  index position :=
    (position.cast
      (rulePremises_length Y.binding Y.carrier E' endpoints' rule)).cast
        (rulePremises_length X.binding X.carrier E endpoints rule).symm
  indexVal position := rfl
  parameter := h.parameterMap (schema := schema) rule.conclusion.ctx
  witness position := witnessAt h eventMap rule transport
    (position.cast
      (rulePremises_length Y.binding Y.carrier E' endpoints' rule))
  preservesParameters := by
    intro position
    simpa only [Fin.cast] using
      witnessAt_parameters h eventMap rule transport
        (position.cast
          (rulePremises_length Y.binding Y.carrier E' endpoints' rule))

/-- Identity fixes the complete ordered authored premise bundle, including
two distinct occurrences that happen to have the same endpoints. -/
theorem mapInput_id (X : ModelWithPrograms S D)
    {E : D} (endpoints : E ⟶ EndpointPairs X.binding X.carrier)
    (rule : IntrinsicScopedConditionalPolynomial.Rule S schema) :
    CategoricalScopedRuleActionMaps.mapInput
      (inputMap (endpoints := endpoints) (endpoints' := endpoints)
        (ModelWithPrograms.Hom.id X) (𝟙 E) rule
        (RulePremiseTransport.id X endpoints rule)) =
      𝟙 (Bundle (rulePremises X.binding X.carrier E endpoints rule)) := by
  apply bundle_hom_ext (rulePremises X.binding X.carrier E endpoints rule)
  · rw [CategoricalScopedRuleActionMaps.mapInput_assignment]
    simp [inputMap, ModelWithPrograms.Hom.parameterMap_id]
  · intro position
    rw [CategoricalScopedRuleActionMaps.mapInput_project]
    change project (rulePremises X.binding X.carrier E endpoints rule) position ≫
      witnessAt (endpoints := endpoints) (endpoints' := endpoints)
        (ModelWithPrograms.Hom.id X) (𝟙 E) rule
        (RulePremiseTransport.id X endpoints rule)
        (position.cast
          (rulePremises_length X.binding X.carrier E endpoints rule)) = _
    rw [witnessAt_id]
    simp

/-- Authored ordered inputs compose over two changes of binding model and
event object, retaining a separate transport for every premise position. -/
theorem mapInput_comp {X Y Z : ModelWithPrograms S D}
    (h : ModelWithPrograms.Hom X Y)
    (k : ModelWithPrograms.Hom Y Z)
    {E E' E'' : D}
    {endpoints : E ⟶ EndpointPairs X.binding X.carrier}
    {endpoints' : E' ⟶ EndpointPairs Y.binding Y.carrier}
    {endpoints'' : E'' ⟶ EndpointPairs Z.binding Z.carrier}
    (f : E ⟶ E') (g : E' ⟶ E'')
    (rule : IntrinsicScopedConditionalPolynomial.Rule S schema)
    (first : RulePremiseTransport (endpoints := endpoints)
      (endpoints' := endpoints') h f rule)
    (second : RulePremiseTransport (endpoints := endpoints')
      (endpoints' := endpoints'') k g rule) :
    CategoricalScopedRuleActionMaps.mapInput
      (inputMap (endpoints := endpoints) (endpoints' := endpoints'')
        (h.comp k) (f ≫ g) rule
        (RulePremiseTransport.comp h k f g rule first second)) =
      CategoricalScopedRuleActionMaps.mapInput
        (inputMap h f rule first) ≫
      CategoricalScopedRuleActionMaps.mapInput
        (inputMap k g rule second) := by
  apply bundle_hom_ext (rulePremises Z.binding Z.carrier E'' endpoints'' rule)
  · simp [Category.assoc,
      CategoricalScopedRuleActionMaps.mapInput_assignment,
      inputMap, ModelWithPrograms.Hom.parameterMap_comp]
    rw [← Category.assoc]
    simpa only [inputMap, Category.assoc, Fin.cast] using congrArg
      (fun arrow => arrow ≫
        k.parameterMap (schema := schema) rule.conclusion.ctx)
      (CategoricalScopedRuleActionMaps.mapInput_assignment
        (inputMap h f rule first)).symm
  · intro position
    rw [CategoricalScopedRuleActionMaps.mapInput_project,
      Category.assoc,
      CategoricalScopedRuleActionMaps.mapInput_project]
    rw [← Category.assoc,
      CategoricalScopedRuleActionMaps.mapInput_project]
    change
      project (rulePremises X.binding X.carrier E endpoints rule)
          ((position.cast
            (rulePremises_length Z.binding Z.carrier E'' endpoints'' rule)).cast
              (rulePremises_length X.binding X.carrier E endpoints rule).symm) ≫
        witnessAt (endpoints := endpoints) (endpoints' := endpoints'')
          (h.comp k) (f ≫ g) rule
          (RulePremiseTransport.comp h k f g rule first second)
          (position.cast
            (rulePremises_length Z.binding Z.carrier E'' endpoints'' rule)) =
      (project (rulePremises X.binding X.carrier E endpoints rule)
          ((position.cast
            (rulePremises_length Z.binding Z.carrier E'' endpoints'' rule)).cast
              (rulePremises_length X.binding X.carrier E endpoints rule).symm) ≫
        witnessAt h f rule first
          (position.cast
            (rulePremises_length Z.binding Z.carrier E'' endpoints'' rule))) ≫
        witnessAt k g rule second
          (position.cast
            (rulePremises_length Z.binding Z.carrier E'' endpoints'' rule))
    rw [witnessAt_comp h k f g rule first second]
    simp [Category.assoc]

end Mettapedia.OSLF.Binding.CategoricalAuthoredScopedInterpretationMaps
