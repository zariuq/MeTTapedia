import Mettapedia.OSLF.Syntax.CategoricalScopedRuleActionMaps
import Mettapedia.OSLF.Syntax.CategoricalBindingFunctor
import Mettapedia.OSLF.Syntax.IntrinsicScopedConditionalPolynomial
import Mathlib.CategoryTheory.Limits.Shapes.Images

/-!
# Authored scoped rules in a closed semantic target

An operational interpretation chooses a program object and maps each sort
into it. This supplies a common endpoint object for rules whose premise sorts
may differ. It is independent data: finite limits do not construct a sum of
all sorts. Authored terms and premise-local binders determine endpoint arrows;
the action on individual events remains the additional model structure.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.CategoricalAuthoredRuleInterpretation

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.CategoryTheory.CartesianMonoidalCategory
open Mettapedia.OSLF.Binding.CategoricalBindingModel
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalPolynomial (Rule)
open Mettapedia.OSLF.Binding.BinderLocalPremise
open Mettapedia.OSLF.Binding.CategoricalScopedEventPremise
open Mettapedia.OSLF.Binding.CategoricalScopedRuleAction
open Mettapedia.OSLF.Binding.CategoricalScopedRuleActionMaps

universe u v
variable {S : Signature} {schema : List (MetaArity S)}
variable {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D]
  [MonoidalClosed D] [HasPullbacks D]
variable (M : Model S D)

/-- The distinguished observable program object, with a map from every
authored sort. These maps may identify states; injectivity is not required. -/
structure ProgramCarrier where
  program : D
  embedSort : ∀ sort : S.Srt, M.sort sort ⟶ program

variable (P : ProgramCarrier M)

/-- Source-target observations of all authored sorts share this object. -/
abbrev EndpointPairs : D := P.program ⊗ P.program

/-- The parameters of a rule are its ordinary context variables together
with its contextual metavariable assignment. -/
abbrev Parameters (Γ : Ctx S) : D := M.ctx Γ ⊗ M.family schema

/-- The two endpoints of a term pair, embedded in the common program object. -/
def termPair {Γ : Ctx S} {sort : S.Srt}
    (source target : Term (withMetas S schema) Γ sort) :
    Parameters (schema := schema) M Γ ⟶ EndpointPairs M P :=
  lift (M.generic schema source ≫ P.embedSort sort)
    (M.generic schema target ≫ P.embedSort sort)

/-- The generic stage for a premise under its own binder context. -/
abbrev LocalStage (Γ binders : Ctx S) : D :=
  M.ctx binders ⊗ Parameters (schema := schema) M Γ

/-- Interpret a term beneath premise-local binders without flattening its
context or substituting under unrelated quotations. -/
def localTerm {Γ binders : Ctx S} {sort : S.Srt}
    (term : Term (withMetas S schema) (binders ++ Γ) sort) :
    LocalStage (schema := schema) M Γ binders ⟶ M.sort sort :=
  (M.interp schema term).value
    (LocalStage (schema := schema) M Γ binders)
    (snd _ _ ≫ snd _ _)
    (M.extendEnv binders (M.genericEnv Γ (M.family schema)))

/-- The requested endpoints of an authored scoped premise before currying. -/
def localPair {Γ : Ctx S}
    (premise : LocalStepPremise (withMetas S schema) Γ) :
    LocalStage (schema := schema) M Γ premise.binders ⟶
      EndpointPairs M P :=
  lift (localTerm (schema := schema) M premise.source ≫ P.embedSort premise.sort)
    (localTerm (schema := schema) M premise.target ≫ P.embedSort premise.sort)

/-- A binder-local premise requests a function of its binder context into
the common endpoint-pair object. -/
noncomputable def premiseRequest {Γ : Ctx S} (event : D)
    (endpoints : event ⟶ EndpointPairs M P)
    (premise : LocalStepPremise (withMetas S schema) Γ) :
    Request (M.ctx premise.binders)
      (Parameters (schema := schema) M Γ) event (EndpointPairs M P) where
  endpoints := endpoints
  required := MonoidalClosed.curry (localPair M P premise)

/-- An event map preserving endpoints transports each authored premise's
individual binder-local firing, without requiring target-event coverage. -/
noncomputable def premiseRequestMap {Γ : Ctx S}
    {E E' : D} {endpoints : E ⟶ EndpointPairs M P}
    {endpoints' : E' ⟶ EndpointPairs M P}
    (f : E ⟶ E') (commutes : f ≫ endpoints' = endpoints)
    (premise : LocalStepPremise (withMetas S schema) Γ) :
    Map (premiseRequest M P E endpoints premise)
      (premiseRequest M P E' endpoints' premise) where
  parameter := 𝟙 _
  event := f
  endpoint := 𝟙 _
  endpoint_comm := by
    change f ≫ endpoints' = endpoints ≫ 𝟙 _
    simpa only [Category.comp_id] using commutes
  required_comm := by simp [premiseRequest]

omit [HasPullbacks D] in
/-- The induced premise map at the identity event map is the identity
premise map, including its scoped event function. -/
theorem premiseRequestMap_id {Γ : Ctx S}
    {E : D} (endpoints : E ⟶ EndpointPairs M P)
    (same : (𝟙 E) ≫ endpoints = endpoints)
    (premise : LocalStepPremise (withMetas S schema) Γ) :
    premiseRequestMap M P (𝟙 E) same premise =
      Map.id (premiseRequest M P E endpoints premise) := by
  apply Map.ext <;> simp [premiseRequestMap, Map.id]

omit [HasPullbacks D] in
/-- Composing event maps composes the induced maps of each authored scoped
premise request. -/
theorem premiseRequestMap_comp {Γ : Ctx S}
    {E E' E'' : D}
    {endpoints : E ⟶ EndpointPairs M P}
    {endpoints' : E' ⟶ EndpointPairs M P}
    {endpoints'' : E'' ⟶ EndpointPairs M P}
    (f : E ⟶ E') (g : E' ⟶ E'')
    (hf : f ≫ endpoints' = endpoints)
    (hg : g ≫ endpoints'' = endpoints')
    (hfg : (f ≫ g) ≫ endpoints'' = endpoints)
    (premise : LocalStepPremise (withMetas S schema) Γ) :
    Map.comp (premiseRequestMap M P f hf premise)
      (premiseRequestMap M P g hg premise) =
    premiseRequestMap M P (f ≫ g) hfg premise := by
  apply Map.ext <;> simp [premiseRequestMap, Map.comp]

/-- The complete ordered list of authored conditional-premise requests. -/
noncomputable def rulePremises (event : D)
    (endpoints : event ⟶ EndpointPairs M P)
    (rule : Rule S schema) :
    List (Premise (Parameters (schema := schema) M rule.conclusion.ctx)
      event (EndpointPairs M P)) :=
  rule.premises.map fun premise =>
    ⟨M.ctx premise.binders, premiseRequest M P event endpoints premise⟩

omit [HasPullbacks D] in
theorem rulePremises_length (event : D)
    (endpoints : event ⟶ EndpointPairs M P)
    (rule : Rule S schema) :
    (rulePremises M P event endpoints rule).length =
      rule.premises.length := by
  simp [rulePremises]

omit [HasPullbacks D] in
/-- The selected categorical request is the interpretation of the premise
at precisely the same authored list position. -/
theorem rulePremises_get (event : D)
    (endpoints : event ⟶ EndpointPairs M P)
    (rule : Rule S schema)
    (position : Fin rule.premises.length) :
    (rulePremises M P event endpoints rule).get
      (position.cast (rulePremises_length M P event endpoints rule).symm) =
      ⟨M.ctx (rule.premises.get position).binders,
        premiseRequest M P event endpoints (rule.premises.get position)⟩ := by
  simp [rulePremises, Fin.cast]

/-- The conclusion endpoint arrow is determined by the authored rule, not
chosen independently by an operational model. -/
def ruleConclusion (rule : Rule S schema) :
    Parameters (schema := schema) M rule.conclusion.ctx ⟶
      EndpointPairs M P :=
  termPair M P rule.conclusion.lhs rule.conclusion.rhs

/-- Interpreting one authored conditional rule means supplying a firing
arrow from the exact ordered premise bundle, with the declared endpoints. -/
abbrev InterpretsRule (event : D)
    (endpoints : event ⟶ EndpointPairs M P)
    (rule : Rule S schema) : Type _ :=
  RuleAction (rulePremises M P event endpoints rule)
    endpoints (ruleConclusion M P rule)

/-- Independent operational-model data for a list of intrinsic authored
rules. Every rule has one action, including rules with no premises. -/
structure OperationalModel (rules : List (Rule S schema)) where
  event : D
  endpoints : event ⟶ EndpointPairs M P
  action : (index : Fin rules.length) →
    InterpretsRule M P event endpoints (rules.get index)

/-- Transport the witness at one authored rule-premise position along an
endpoint-preserving event map. The casts only reconcile the list presentation
with its intrinsic position; they do not identify distinct occurrences. -/
noncomputable def ruleWitnessAt {E E' : D}
    {endpoints : E ⟶ EndpointPairs M P}
    {endpoints' : E' ⟶ EndpointPairs M P}
    (f : E ⟶ E') (commutes : f ≫ endpoints' = endpoints)
    (rule : Rule S schema) (position : Fin rule.premises.length) :
    Witness ((rulePremises M P E endpoints rule).get
      (position.cast (rulePremises_length M P E endpoints rule).symm)).request ⟶
    Witness ((rulePremises M P E' endpoints' rule).get
      (position.cast (rulePremises_length M P E' endpoints' rule).symm)).request := by
  let sourceEntry := rulePremises_get M P E endpoints rule position
  let targetEntry := rulePremises_get M P E' endpoints' rule position
  exact
    eqToHom (congrArg
      (fun premise : Premise (Parameters (schema := schema) M rule.conclusion.ctx)
        E (EndpointPairs M P) => Witness premise.request) sourceEntry) ≫
    mapWitness (premiseRequest M P E endpoints (rule.premises.get position))
      (premiseRequestMap M P f commutes (rule.premises.get position)) ≫
    eqToHom (congrArg
      (fun premise : Premise (Parameters (schema := schema) M rule.conclusion.ctx)
        E' (EndpointPairs M P) => Witness premise.request) targetEntry.symm)

/-- Identity transport preserves the exact authored firing at each premise
position. -/
theorem ruleWitnessAt_id {E : D}
    (endpoints : E ⟶ EndpointPairs M P)
    (same : (𝟙 E) ≫ endpoints = endpoints)
    (rule : Rule S schema) (position : Fin rule.premises.length) :
    ruleWitnessAt M P (𝟙 E) same rule position = 𝟙 _ := by
  unfold ruleWitnessAt
  rw [premiseRequestMap_id, mapWitness_id]
  simp

/-- The same authored premise occurrence is followed through two event
interpretations; the middle presentation transport cancels. -/
theorem ruleWitnessAt_comp {E E' E'' : D}
    {endpoints : E ⟶ EndpointPairs M P}
    {endpoints' : E' ⟶ EndpointPairs M P}
    {endpoints'' : E'' ⟶ EndpointPairs M P}
    (f : E ⟶ E') (g : E' ⟶ E'')
    (hf : f ≫ endpoints' = endpoints)
    (hg : g ≫ endpoints'' = endpoints')
    (hfg : (f ≫ g) ≫ endpoints'' = endpoints)
    (rule : Rule S schema) (position : Fin rule.premises.length) :
    ruleWitnessAt M P (f ≫ g) hfg rule position =
      ruleWitnessAt M P f hf rule position ≫
        ruleWitnessAt M P g hg rule position := by
  unfold ruleWitnessAt
  rw [← premiseRequestMap_comp M P f g hf hg hfg
    (rule.premises.get position), mapWitness_comp]
  simp [Category.assoc]

/-- The transported witness keeps the rule's unchanged parameter assignment. -/
theorem ruleWitnessAt_parameters {E E' : D}
    {endpoints : E ⟶ EndpointPairs M P}
    {endpoints' : E' ⟶ EndpointPairs M P}
    (f : E ⟶ E') (commutes : f ≫ endpoints' = endpoints)
    (rule : Rule S schema) (position : Fin rule.premises.length) :
    ruleWitnessAt M P f commutes rule position ≫
      parameters ((rulePremises M P E' endpoints' rule).get
        (position.cast (rulePremises_length M P E' endpoints' rule).symm)).request =
    parameters ((rulePremises M P E endpoints rule).get
      (position.cast (rulePremises_length M P E endpoints rule).symm)).request := by
  let sourceEntry := rulePremises_get M P E endpoints rule position
  let targetEntry := rulePremises_get M P E' endpoints' rule position
  change ((eqToHom (congrArg
      (fun premise : Premise (Parameters (schema := schema) M rule.conclusion.ctx)
        E (EndpointPairs M P) => Witness premise.request) sourceEntry) ≫
    mapWitness (premiseRequest M P E endpoints (rule.premises.get position))
      (premiseRequestMap M P f commutes (rule.premises.get position)) ≫
    eqToHom (congrArg
      (fun premise : Premise (Parameters (schema := schema) M rule.conclusion.ctx)
        E' (EndpointPairs M P) => Witness premise.request) targetEntry.symm))) ≫ _ = _
  rw [Category.assoc, Category.assoc,
    premise_transport_parameters targetEntry.symm,
    mapWitness_parameters]
  simp only [premiseRequestMap, Category.comp_id]
  exact premise_transport_parameters sourceEntry

/-- Every authored premise is mapped at the same position, with its own
retained event function. No event-surjectivity hypothesis is needed. -/
noncomputable def ruleInputMap {E E' : D}
    {endpoints : E ⟶ EndpointPairs M P}
    {endpoints' : E' ⟶ EndpointPairs M P}
    (f : E ⟶ E') (commutes : f ≫ endpoints' = endpoints)
    (rule : Rule S schema) :
    InputMap (rulePremises M P E endpoints rule)
      (rulePremises M P E' endpoints' rule) where
  sameLength := (rulePremises_length M P E endpoints rule).trans
    (rulePremises_length M P E' endpoints' rule).symm
  index position :=
    (position.cast (rulePremises_length M P E' endpoints' rule)).cast
      (rulePremises_length M P E endpoints rule).symm
  indexVal position := rfl
  parameter := 𝟙 _
  witness position := ruleWitnessAt M P f commutes rule
    (position.cast (rulePremises_length M P E' endpoints' rule))
  preservesParameters := by
    intro position
    simpa only [Category.comp_id, Fin.cast] using
      ruleWitnessAt_parameters M P f commutes rule
        (position.cast (rulePremises_length M P E' endpoints' rule))

/-- The derived ordered input map of the identity event map is identity
on the complete bundle, including duplicate premise occurrences. -/
theorem mapInput_ruleInputMap_id {E : D}
    (endpoints : E ⟶ EndpointPairs M P)
    (same : (𝟙 E) ≫ endpoints = endpoints)
    (rule : Rule S schema) :
    mapInput (ruleInputMap M P (𝟙 E) same rule) =
      𝟙 (Bundle (rulePremises M P E endpoints rule)) := by
  apply bundle_hom_ext (rulePremises M P E endpoints rule)
  · rw [mapInput_assignment]
    simp [ruleInputMap]
  · intro position
    rw [mapInput_project]
    change project (rulePremises M P E endpoints rule) position ≫
      ruleWitnessAt M P (𝟙 E) same rule
        (position.cast (rulePremises_length M P E endpoints rule)) = _
    rw [ruleWitnessAt_id]
    simp

/-- Ordered premise bundles transport functorially through successive event
maps, without merging repeated firings at equal endpoint pairs. -/
theorem mapInput_ruleInputMap_comp {E E' E'' : D}
    {endpoints : E ⟶ EndpointPairs M P}
    {endpoints' : E' ⟶ EndpointPairs M P}
    {endpoints'' : E'' ⟶ EndpointPairs M P}
    (f : E ⟶ E') (g : E' ⟶ E'')
    (hf : f ≫ endpoints' = endpoints)
    (hg : g ≫ endpoints'' = endpoints')
    (hfg : (f ≫ g) ≫ endpoints'' = endpoints)
    (rule : Rule S schema) :
    mapInput (ruleInputMap M P (f ≫ g) hfg rule) =
      mapInput (ruleInputMap M P f hf rule) ≫
        mapInput (ruleInputMap M P g hg rule) := by
  apply bundle_hom_ext (rulePremises M P E'' endpoints'' rule)
  · simp [Category.assoc, mapInput_assignment, ruleInputMap]
  · intro position
    rw [mapInput_project, Category.assoc, mapInput_project]
    rw [← Category.assoc, mapInput_project]
    change
      project (rulePremises M P E endpoints rule)
          ((position.cast (rulePremises_length M P E'' endpoints'' rule)).cast
            (rulePremises_length M P E endpoints rule).symm) ≫
        ruleWitnessAt M P (f ≫ g) hfg rule
          (position.cast (rulePremises_length M P E'' endpoints'' rule)) =
      (project (rulePremises M P E endpoints rule)
          ((position.cast (rulePremises_length M P E'' endpoints'' rule)).cast
            (rulePremises_length M P E endpoints rule).symm) ≫
        ruleWitnessAt M P f hf rule
          (position.cast (rulePremises_length M P E'' endpoints'' rule))) ≫
        ruleWitnessAt M P g hg rule
          (position.cast (rulePremises_length M P E'' endpoints'' rule))
    rw [ruleWitnessAt_comp M P f g hf hg hfg rule
      (position.cast (rulePremises_length M P E'' endpoints'' rule))]
    simp [Category.assoc]

namespace OperationalModel

variable {rules : List (Rule S schema)}
variable {X Y : OperationalModel M P rules}

/-- A map of operational interpretations preserves individual events and
their endpoints, then commutes with every actual authored rule action. Its
ordered input map is derived from the event map rather than chosen again. -/
structure Hom (X Y : OperationalModel M P rules) where
  event : X.event ⟶ Y.event
  endpoints : event ≫ Y.endpoints = X.endpoints
  action : ∀ index : Fin rules.length,
    mapInput (ruleInputMap M P event endpoints (rules.get index)) ≫
      (Y.action index).fire = (X.action index).fire ≫ event

/-- Every authored action of an operational interpretation map satisfies
the general action-map contract at its original rule-list position. -/
noncomputable def Hom.actionMap (f : Hom M P X Y)
    (index : Fin rules.length) :
    ActionMap (X.action index) (Y.action index) where
  input := ruleInputMap M P f.event f.endpoints (rules.get index)
  event := f.event
  endpoint := 𝟙 _
  endpoint_comm := by simpa only [Category.comp_id] using f.endpoints
  conclusion_comm := by simp [ruleInputMap]
  action_comm := f.action index

/-- Identity maps every retained firing to itself. -/
noncomputable def Hom.id (X : OperationalModel M P rules) : Hom M P X X where
  event := 𝟙 X.event
  endpoints := by simp
  action index := by
    rw [mapInput_ruleInputMap_id]
    simp

/-- Composition preserves the actual authored firing arrows, with their
ordered premise witnesses transported in sequence. -/
noncomputable def Hom.comp {X Y Z : OperationalModel M P rules}
    (f : Hom M P X Y) (g : Hom M P Y Z) : Hom M P X Z := by
  have hfg : (f.event ≫ g.event) ≫ Z.endpoints = X.endpoints := by
    calc
      (f.event ≫ g.event) ≫ Z.endpoints =
          f.event ≫ (g.event ≫ Z.endpoints) := Category.assoc _ _ _
      _ = f.event ≫ Y.endpoints := by rw [g.endpoints]
      _ = X.endpoints := f.endpoints
  exact {
    event := f.event ≫ g.event
    endpoints := hfg
    action := by
      intro index
      rw [mapInput_ruleInputMap_comp M P f.event g.event
        f.endpoints g.endpoints hfg (rules.get index)]
      calc
        (mapInput (ruleInputMap M P f.event f.endpoints (rules.get index)) ≫
            mapInput (ruleInputMap M P g.event g.endpoints (rules.get index))) ≫
            (Z.action index).fire =
          mapInput (ruleInputMap M P f.event f.endpoints (rules.get index)) ≫
            (mapInput (ruleInputMap M P g.event g.endpoints (rules.get index)) ≫
              (Z.action index).fire) := Category.assoc _ _ _
        _ = mapInput (ruleInputMap M P f.event f.endpoints (rules.get index)) ≫
              ((Y.action index).fire ≫ g.event) := by rw [g.action index]
        _ = (mapInput (ruleInputMap M P f.event f.endpoints (rules.get index)) ≫
              (Y.action index).fire) ≫ g.event :=
            (Category.assoc _ _ _).symm
        _ = ((X.action index).fire ≫ f.event) ≫ g.event := by
            rw [f.action index]
        _ = (X.action index).fire ≫ (f.event ≫ g.event) :=
            Category.assoc _ _ _
  }

/-- An operational map is determined by its map on individual events;
endpoint and action preservation are propositions. -/
@[ext] theorem Hom.ext {X Y : OperationalModel M P rules}
    {f g : Hom M P X Y} (same : f.event = g.event) : f = g := by
  cases f with
  | mk fe fp fa =>
    cases g with
    | mk ge gp ga =>
      cases same
      rfl

noncomputable instance : Category (OperationalModel M P rules) where
  Hom := Hom M P
  id := Hom.id M P
  comp := Hom.comp M P
  id_comp := by
    intro X Y f
    apply Hom.ext
    simp [Hom.comp, Hom.id]
  comp_id := by
    intro X Y f
    apply Hom.ext
    simp [Hom.comp, Hom.id]
  assoc := by
    intro X Y Z W f g h
    apply Hom.ext
    simp [Hom.comp, Category.assoc]

/-- Forgetting the identity of a firing gives only the image of its pair of
endpoints. The event object remains part of the operational model. -/
noncomputable def reductionImage [HasImages D]
    (X : OperationalModel M P rules) : D :=
  image X.endpoints

/-- The reduction observation as a subobject of the program-pair object. -/
noncomputable def reductionMono [HasImages D]
    (X : OperationalModel M P rules) :
    reductionImage M P X ⟶ EndpointPairs M P :=
  image.ι X.endpoints

/-- Every actual authored firing is observed by the reduction image. -/
theorem event_factors_reduction [HasImages D]
    (X : OperationalModel M P rules) :
    factorThruImage X.endpoints ≫ reductionMono M P X =
      X.endpoints :=
  image.fac X.endpoints

/-- An operational model map gives a commutative square on its event graph.
The endpoint-pair object stays fixed in this fibre. -/
noncomputable def Hom.endpointSquare {X Y : OperationalModel M P rules}
    (f : Hom M P X Y) :
    Arrow.mk X.endpoints ⟶ Arrow.mk Y.endpoints :=
  Arrow.homMk f.event (𝟙 _) (by simpa using f.endpoints)

/-- In a target with images and image maps, an authored operational map
preserves the existence of a firing in the forward direction. It need not
reflect target firings or preserve their multiplicity after observation. -/
theorem reductionImage_forward [HasImages D] [HasImageMaps D]
    {X Y : OperationalModel M P rules} (f : Hom M P X Y) :
    image.map (f.endpointSquare M P) ≫ reductionMono M P Y =
      reductionMono M P X ≫ (𝟙 (EndpointPairs M P)) := by
  exact image.map_ι (f.endpointSquare M P)

end OperationalModel

end Mettapedia.OSLF.Binding.CategoricalAuthoredRuleInterpretation

#print axioms Mettapedia.OSLF.Binding.CategoricalAuthoredRuleInterpretation.ruleConclusion
#print axioms Mettapedia.OSLF.Binding.CategoricalAuthoredRuleInterpretation.rulePremises_get
#print axioms Mettapedia.OSLF.Binding.CategoricalAuthoredRuleInterpretation.ruleWitnessAt_comp
#print axioms Mettapedia.OSLF.Binding.CategoricalAuthoredRuleInterpretation.mapInput_ruleInputMap_comp
#print axioms Mettapedia.OSLF.Binding.CategoricalAuthoredRuleInterpretation.OperationalModel.Hom.comp
#print axioms Mettapedia.OSLF.Binding.CategoricalAuthoredRuleInterpretation.OperationalModel.reductionImage_forward
