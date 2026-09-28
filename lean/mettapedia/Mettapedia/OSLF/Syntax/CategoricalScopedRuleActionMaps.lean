import Mettapedia.OSLF.Syntax.CategoricalScopedRuleAction

/-!
# Maps of ordered scoped-rule inputs

The parameter object, event object, and endpoint object may all change under
an interpretation map. A map of a conditional rule must still transport each
premise witness at its original position and carry their common parameter
assignment to the new parameter object. The iterated pullback has exactly
the universal property needed to assemble that map.

The witness maps here are explicit data. Establishing them from a particular
authored signature and its semantic interpretation is a separate comparison.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.CategoricalScopedRuleActionMaps

open CategoryTheory CategoryTheory.Limits
open Mettapedia.OSLF.Binding.CategoricalScopedEventPremise
open Mettapedia.OSLF.Binding.CategoricalScopedRuleAction

universe u v
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
  [MonoidalClosed D] [HasPullbacks D]
variable {X E Q X' E' Q' : D}

/-- A position-preserving map between two ordered families of scoped premise
requests. The binder objects may differ; the individual witness maps record
the required transport between their scoped event-function objects. -/
structure InputMap (source : List (Premise X E Q))
    (target : List (Premise X' E' Q')) where
  sameLength : source.length = target.length
  index : Fin target.length → Fin source.length
  indexVal : ∀ position, (index position).val = position.val
  parameter : X ⟶ X'
  witness : (position : Fin target.length) →
    Witness (source.get (index position)).request ⟶
      Witness (target.get position).request
  preservesParameters : ∀ position,
    witness position ≫ parameters (target.get position).request =
      parameters (source.get (index position)).request ≫ parameter

variable {source : List (Premise X E Q)}
  {target : List (Premise X' E' Q')}

/-- The stored index map cannot permute premise positions: it is the
canonical cast along the equality of list lengths. -/
theorem InputMap.index_eq_cast (f : InputMap source target)
    (position : Fin target.length) :
    f.index position = position.cast f.sameLength.symm := by
  apply Fin.ext
  exact f.indexVal position

/-- Assemble the mapped ordered witnesses using the pullback universal
property. Duplicate premises retain different projections. -/
noncomputable def mapInput (f : InputMap source target) :
    Bundle source ⟶ Bundle target :=
  liftCone target {
    parameter := assignment source ≫ f.parameter
    witness position :=
      project source (f.index position) ≫ f.witness position
    agrees position := by
      rw [Category.assoc, f.preservesParameters]
      rw [← Category.assoc, project_assignment source
        (f.index position)]
  }

/-- The assembled rule-input map carries the shared authored assignment
through the selected parameter map. -/
theorem mapInput_assignment (f : InputMap source target) :
    mapInput f ≫ assignment target = assignment source ≫ f.parameter :=
  liftCone_assignment target _

/-- Each ordered premise projection is transported by its own witness map;
equal endpoint pairs do not merge occurrences. -/
theorem mapInput_project (f : InputMap source target)
    (position : Fin target.length) :
    mapInput f ≫ project target position =
      project source (f.index position) ≫ f.witness position :=
  liftCone_project target _ position

/-- Identity interpretation preserves every authored premise position. -/
noncomputable def InputMap.id (source : List (Premise X E Q)) :
    InputMap source source where
  sameLength := rfl
  index := fun position => position
  indexVal := by intro; rfl
  parameter := 𝟙 X
  witness _ := 𝟙 _
  preservesParameters := by intro position; simp

theorem mapInput_id (source : List (Premise X E Q)) :
    mapInput (InputMap.id source) = 𝟙 (Bundle source) := by
  apply bundle_hom_ext source
  · rw [mapInput_assignment]
    simp [InputMap.id]
  · intro position
    rw [mapInput_project]
    simp [InputMap.id]

variable {X'' E'' Q'' : D}

/-- Composition follows the same premise positions through both maps. -/
noncomputable def InputMap.comp {first : List (Premise X E Q)}
    {middle : List (Premise X' E' Q')}
    {last : List (Premise X'' E'' Q'')}
    (f : InputMap first middle) (g : InputMap middle last) :
    InputMap first last where
  sameLength := f.sameLength.trans g.sameLength
  index position := f.index (g.index position)
  indexVal position := (f.indexVal (g.index position)).trans (g.indexVal position)
  parameter := f.parameter ≫ g.parameter
  witness position := f.witness (g.index position) ≫ g.witness position
  preservesParameters := by
    intro position
    calc
      (f.witness (g.index position) ≫ g.witness position) ≫
          parameters (last.get position).request =
        f.witness (g.index position) ≫
          (g.witness position ≫ parameters (last.get position).request) :=
          Category.assoc _ _ _
      _ = f.witness (g.index position) ≫
          (parameters (middle.get (g.index position)).request ≫
            g.parameter) := by rw [g.preservesParameters position]
      _ = (f.witness (g.index position) ≫
          parameters (middle.get (g.index position)).request) ≫
            g.parameter := (Category.assoc _ _ _).symm
      _ = (parameters (first.get (f.index (g.index position))).request ≫
          f.parameter) ≫ g.parameter := by
            rw [f.preservesParameters (g.index position)]
      _ = parameters (first.get (f.index (g.index position))).request ≫
          (f.parameter ≫ g.parameter) := Category.assoc _ _ _

/-- The universal pullback map respects composition of ordered premise
interpretations, including their individual witness maps. -/
theorem mapInput_comp {first : List (Premise X E Q)}
    {middle : List (Premise X' E' Q')}
    {last : List (Premise X'' E'' Q'')}
    (f : InputMap first middle) (g : InputMap middle last) :
    mapInput (InputMap.comp f g) = mapInput f ≫ mapInput g := by
  apply bundle_hom_ext last
  · calc
      mapInput (InputMap.comp f g) ≫ assignment last =
          assignment first ≫ (f.parameter ≫ g.parameter) :=
            mapInput_assignment _
      _ = (assignment first ≫ f.parameter) ≫ g.parameter :=
            (Category.assoc _ _ _).symm
      _ = (mapInput f ≫ assignment middle) ≫ g.parameter := by
            rw [mapInput_assignment]
      _ = mapInput f ≫ (assignment middle ≫ g.parameter) :=
            Category.assoc _ _ _
      _ = mapInput f ≫ (mapInput g ≫ assignment last) := by
            rw [mapInput_assignment]
      _ = (mapInput f ≫ mapInput g) ≫ assignment last :=
            (Category.assoc _ _ _).symm
  · intro position
    rw [mapInput_project, Category.assoc, mapInput_project]
    dsimp only [InputMap.comp]
    calc
      project first (f.index (g.index position)) ≫
          (f.witness (g.index position) ≫ g.witness position) =
        (project first (f.index (g.index position)) ≫
          f.witness (g.index position)) ≫ g.witness position :=
          (Category.assoc _ _ _).symm
      _ = (mapInput f ≫ project middle (g.index position)) ≫
          g.witness position := by rw [mapInput_project]
      _ = mapInput f ≫
          (project middle (g.index position) ≫ g.witness position) :=
          Category.assoc _ _ _

/-- A map of rule actions preserves the conclusion event itself. Its
endpoint and conclusion squares are separate from the action square, so an
ordinary map need not cover all target events. -/
structure ActionMap {source : List (Premise X E Q)}
    {target : List (Premise X' E' Q')}
    {sourceEndpoints : E ⟶ Q} {targetEndpoints : E' ⟶ Q'}
    {sourceConclusion : X ⟶ Q} {targetConclusion : X' ⟶ Q'}
    (sourceAction : RuleAction source sourceEndpoints sourceConclusion)
    (targetAction : RuleAction target targetEndpoints targetConclusion) where
  input : InputMap source target
  event : E ⟶ E'
  endpoint : Q ⟶ Q'
  endpoint_comm : event ≫ targetEndpoints = sourceEndpoints ≫ endpoint
  conclusion_comm : input.parameter ≫ targetConclusion =
    sourceConclusion ≫ endpoint
  action_comm : mapInput input ≫ targetAction.fire = sourceAction.fire ≫ event

namespace ActionMap

/-- Identity preserves the conditional firing action and every premise. -/
noncomputable def id {premises : List (Premise X E Q)}
    {endpoints : E ⟶ Q} {conclusion : X ⟶ Q}
    (action : RuleAction premises endpoints conclusion) :
    ActionMap action action where
  input := InputMap.id premises
  event := 𝟙 E
  endpoint := 𝟙 Q
  endpoint_comm := by simp
  conclusion_comm := by simp [InputMap.id]
  action_comm := by rw [mapInput_id]; simp

variable {X'' E'' Q'' : D}
variable {first : List (Premise X E Q)}
  {middle : List (Premise X' E' Q')}
  {last : List (Premise X'' E'' Q'')}
variable {firstEndpoints : E ⟶ Q} {middleEndpoints : E' ⟶ Q'}
  {lastEndpoints : E'' ⟶ Q''}
variable {firstConclusion : X ⟶ Q} {middleConclusion : X' ⟶ Q'}
  {lastConclusion : X'' ⟶ Q''}
variable {firstAction : RuleAction first firstEndpoints firstConclusion}
  {middleAction : RuleAction middle middleEndpoints middleConclusion}
  {lastAction : RuleAction last lastEndpoints lastConclusion}

/-- Composing rule-action interpretations retains their event maps and the
original order of recursive premise firings. -/
noncomputable def comp (f : ActionMap firstAction middleAction)
    (g : ActionMap middleAction lastAction) :
    ActionMap firstAction lastAction where
  input := InputMap.comp f.input g.input
  event := f.event ≫ g.event
  endpoint := f.endpoint ≫ g.endpoint
  endpoint_comm := by
    calc
      (f.event ≫ g.event) ≫ lastEndpoints =
        f.event ≫ (g.event ≫ lastEndpoints) := Category.assoc _ _ _
      _ = f.event ≫ (middleEndpoints ≫ g.endpoint) := by
        rw [g.endpoint_comm]
      _ = (f.event ≫ middleEndpoints) ≫ g.endpoint :=
        (Category.assoc _ _ _).symm
      _ = (firstEndpoints ≫ f.endpoint) ≫ g.endpoint := by
        rw [f.endpoint_comm]
      _ = firstEndpoints ≫ (f.endpoint ≫ g.endpoint) :=
        Category.assoc _ _ _
  conclusion_comm := by
    calc
      (f.input.parameter ≫ g.input.parameter) ≫ lastConclusion =
        f.input.parameter ≫ (g.input.parameter ≫ lastConclusion) :=
          Category.assoc _ _ _
      _ = f.input.parameter ≫ (middleConclusion ≫ g.endpoint) := by
        rw [g.conclusion_comm]
      _ = (f.input.parameter ≫ middleConclusion) ≫ g.endpoint :=
        (Category.assoc _ _ _).symm
      _ = (firstConclusion ≫ f.endpoint) ≫ g.endpoint := by
        rw [f.conclusion_comm]
      _ = firstConclusion ≫ (f.endpoint ≫ g.endpoint) :=
        Category.assoc _ _ _
  action_comm := by
    calc
      mapInput (InputMap.comp f.input g.input) ≫ lastAction.fire =
        (mapInput f.input ≫ mapInput g.input) ≫ lastAction.fire := by
          rw [mapInput_comp]
      _ = mapInput f.input ≫ (mapInput g.input ≫ lastAction.fire) :=
        Category.assoc _ _ _
      _ = mapInput f.input ≫ (middleAction.fire ≫ g.event) := by
        rw [g.action_comm]
      _ = (mapInput f.input ≫ middleAction.fire) ≫ g.event :=
        (Category.assoc _ _ _).symm
      _ = (firstAction.fire ≫ f.event) ≫ g.event := by
        rw [f.action_comm]
      _ = firstAction.fire ≫ (f.event ≫ g.event) :=
        Category.assoc _ _ _

end ActionMap

/-- The rule-action comparison respects observed endpoints. The proof uses
the actual premise-input and event maps, rather than identifying events by
their endpoints. -/
theorem ActionMap.endpoint_consistency
    {source : List (Premise X E Q)}
    {target : List (Premise X' E' Q')}
    {sourceEndpoints : E ⟶ Q} {targetEndpoints : E' ⟶ Q'}
    {sourceConclusion : X ⟶ Q} {targetConclusion : X' ⟶ Q'}
    {sourceAction : RuleAction source sourceEndpoints sourceConclusion}
    {targetAction : RuleAction target targetEndpoints targetConclusion}
    (f : ActionMap sourceAction targetAction) :
    (sourceAction.fire ≫ f.event) ≫ targetEndpoints =
      (assignment source ≫ f.input.parameter) ≫ targetConclusion := by
  rw [Category.assoc, f.endpoint_comm, ← Category.assoc,
    sourceAction.endpoint_law, Category.assoc, ← f.conclusion_comm,
    ← Category.assoc]

end Mettapedia.OSLF.Binding.CategoricalScopedRuleActionMaps

#print axioms Mettapedia.OSLF.Binding.CategoricalScopedRuleActionMaps.mapInput_project
#print axioms Mettapedia.OSLF.Binding.CategoricalScopedRuleActionMaps.mapInput_id
#print axioms Mettapedia.OSLF.Binding.CategoricalScopedRuleActionMaps.mapInput_comp
#print axioms Mettapedia.OSLF.Binding.CategoricalScopedRuleActionMaps.ActionMap.comp
#print axioms Mettapedia.OSLF.Binding.CategoricalScopedRuleActionMaps.ActionMap.endpoint_consistency
