import Mettapedia.OSLF.Syntax.CategoricalAuthoredScopedInterpretationMaps
import Mettapedia.OSLF.Syntax.CategoricalBindingQuotientEquivalence

/-!
# Operational models of authored binding, equations, and conditional rules

The model data retain individual firing events. Each authored rule has an
action on its ordered bundle of scoped premise witnesses. A morphism carries
the binding interpretation, program states, event evidence, and every
premise-local contextual event map together. No coverage or injectivity is
required of an ordinary model morphism.

This is the semantic model category. Its free classifier and comparison with
structured functors require separate construction.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.CategoricalAuthoredOperationalModels

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open Mettapedia.OSLF.Binding.CategoricalBindingModel
open Mettapedia.OSLF.Binding.CategoricalAuthoredRuleInterpretation
open Mettapedia.OSLF.Binding.CategoricalAuthoredProgramCarrierMaps
open Mettapedia.OSLF.Binding.CategoricalAuthoredScopedInterpretationMaps
open Mettapedia.OSLF.Binding.CategoricalScopedRuleActionMaps
open Mettapedia.OSLF.Binding.SecondOrderContext

universe u v
variable {S : Signature} {schema : List (MetaArity S)}
variable {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D]
  [MonoidalClosed D] [HasPullbacks D]

/-- An independently specified interpretation of authored equations and
conditional rules in a closed semantic target. The rule actions are extra
data; they do not turn an operational step into a program equation. -/
structure PresentedModel (equations : EquationPresentation S schema)
    (rules : List (IntrinsicScopedConditionalPolynomial.Rule S schema)) where
  base : ModelWithPrograms S D
  satisfies : base.binding.Satisfies equations
  event : D
  endpoints : event ⟶ EndpointPairs base.binding base.carrier
  action : (index : Fin rules.length) →
    InterpretsRule base.binding base.carrier event endpoints
      (rules.get index)

namespace PresentedModel

variable {equations : EquationPresentation S schema}
variable {rules : List (IntrinsicScopedConditionalPolynomial.Rule S schema)}
variable {X Y Z : PresentedModel (D := D) equations rules}

/-- A genuine model map preserves authored substitutions and equations via
its binding map, then transports each individual firing and each ordered
scoped premise. Endpoint and action squares are recorded independently. -/
structure Hom (X Y : PresentedModel (D := D) equations rules) where
  base : ModelWithPrograms.Hom X.base Y.base
  event : X.event ⟶ Y.event
  endpoints_comm : event ≫ Y.endpoints =
    X.endpoints ≫ base.endpointMap
  premiseMap : (index : Fin rules.length) →
    RulePremiseTransport (endpoints := X.endpoints)
      (endpoints' := Y.endpoints) base event (rules.get index)
  conclusion_comm : ∀ index : Fin rules.length,
    base.parameterMap (schema := schema) (rules.get index).conclusion.ctx ≫
      ruleConclusion Y.base.binding Y.base.carrier (rules.get index) =
    ruleConclusion X.base.binding X.base.carrier (rules.get index) ≫
      base.endpointMap
  action_comm : ∀ index : Fin rules.length,
    mapInput (CategoricalAuthoredScopedInterpretationMaps.inputMap
      base event (rules.get index) (premiseMap index)) ≫
      (Y.action index).fire =
    (X.action index).fire ≫ event

/-- An authored rule map satisfies the generic action-map contract, with
the premise map derived from the same global interpretation. -/
noncomputable def Hom.actionMap (f : Hom X Y)
    (index : Fin rules.length) :
    ActionMap (X.action index) (Y.action index) where
  input := CategoricalAuthoredScopedInterpretationMaps.inputMap
    f.base f.event (rules.get index) (f.premiseMap index)
  event := f.event
  endpoint := f.base.endpointMap
  endpoint_comm := f.endpoints_comm
  conclusion_comm := f.conclusion_comm index
  action_comm := f.action_comm index

/-- The identity preserves all authored operations, equations, premise
positions, and event occurrences. -/
noncomputable def Hom.id (X : PresentedModel (D := D) equations rules) :
    Hom X X where
  base := ModelWithPrograms.Hom.id X.base
  event := 𝟙 X.event
  endpoints_comm := by
    simp [ModelWithPrograms.Hom.endpointMap_id]
  premiseMap index := RulePremiseTransport.id X.base X.endpoints
    (rules.get index)
  conclusion_comm := by
    intro index
    simp [ModelWithPrograms.Hom.parameterMap_id,
      ModelWithPrograms.Hom.endpointMap_id]
  action_comm := by
    intro index
    rw [CategoricalAuthoredScopedInterpretationMaps.mapInput_id]
    simp

/-- Successive interpretation maps compose without losing duplicate firing
witnesses or permuting ordered conditional premises. -/
noncomputable def Hom.comp (f : Hom X Y) (g : Hom Y Z) : Hom X Z where
  base := f.base.comp g.base
  event := f.event ≫ g.event
  endpoints_comm := by
    calc
      (f.event ≫ g.event) ≫ Z.endpoints =
        f.event ≫ (g.event ≫ Z.endpoints) := Category.assoc _ _ _
      _ = f.event ≫ (Y.endpoints ≫ g.base.endpointMap) := by
        rw [g.endpoints_comm]
      _ = (f.event ≫ Y.endpoints) ≫ g.base.endpointMap :=
        (Category.assoc _ _ _).symm
      _ = (X.endpoints ≫ f.base.endpointMap) ≫ g.base.endpointMap := by
        rw [f.endpoints_comm]
      _ = X.endpoints ≫ (f.base.comp g.base).endpointMap := by
        rw [ModelWithPrograms.Hom.endpointMap_comp]
        exact Category.assoc _ _ _
  premiseMap index := RulePremiseTransport.comp
    f.base g.base f.event g.event (rules.get index)
    (f.premiseMap index) (g.premiseMap index)
  conclusion_comm := by
    intro index
    rw [ModelWithPrograms.Hom.parameterMap_comp,
      ModelWithPrograms.Hom.endpointMap_comp]
    calc
      (f.base.parameterMap (schema := schema) (rules.get index).conclusion.ctx ≫
          g.base.parameterMap (schema := schema) (rules.get index).conclusion.ctx) ≫
          ruleConclusion Z.base.binding Z.base.carrier (rules.get index) =
        f.base.parameterMap (schema := schema) (rules.get index).conclusion.ctx ≫
          (g.base.parameterMap (schema := schema) (rules.get index).conclusion.ctx ≫
            ruleConclusion Z.base.binding Z.base.carrier (rules.get index)) :=
          Category.assoc _ _ _
      _ = f.base.parameterMap (schema := schema) (rules.get index).conclusion.ctx ≫
          (ruleConclusion Y.base.binding Y.base.carrier (rules.get index) ≫
            g.base.endpointMap) := by rw [g.conclusion_comm index]
      _ = (f.base.parameterMap (schema := schema) (rules.get index).conclusion.ctx ≫
          ruleConclusion Y.base.binding Y.base.carrier (rules.get index)) ≫
            g.base.endpointMap := (Category.assoc _ _ _).symm
      _ = (ruleConclusion X.base.binding X.base.carrier (rules.get index) ≫
          f.base.endpointMap) ≫ g.base.endpointMap := by
            rw [f.conclusion_comm index]
      _ = ruleConclusion X.base.binding X.base.carrier (rules.get index) ≫
          (f.base.endpointMap ≫ g.base.endpointMap) := Category.assoc _ _ _
  action_comm := by
    intro index
    rw [CategoricalAuthoredScopedInterpretationMaps.mapInput_comp]
    calc
      (mapInput (CategoricalAuthoredScopedInterpretationMaps.inputMap
          f.base f.event (rules.get index) (f.premiseMap index)) ≫
        mapInput (CategoricalAuthoredScopedInterpretationMaps.inputMap
          g.base g.event (rules.get index) (g.premiseMap index))) ≫
          (Z.action index).fire =
        mapInput (CategoricalAuthoredScopedInterpretationMaps.inputMap
          f.base f.event (rules.get index) (f.premiseMap index)) ≫
          (mapInput (CategoricalAuthoredScopedInterpretationMaps.inputMap
            g.base g.event (rules.get index) (g.premiseMap index)) ≫
            (Z.action index).fire) := Category.assoc _ _ _
      _ = mapInput (CategoricalAuthoredScopedInterpretationMaps.inputMap
          f.base f.event (rules.get index) (f.premiseMap index)) ≫
          ((Y.action index).fire ≫ g.event) := by
            rw [g.action_comm index]
      _ = (mapInput (CategoricalAuthoredScopedInterpretationMaps.inputMap
          f.base f.event (rules.get index) (f.premiseMap index)) ≫
          (Y.action index).fire) ≫ g.event :=
        (Category.assoc _ _ _).symm
      _ = ((X.action index).fire ≫ f.event) ≫ g.event := by
            rw [f.action_comm index]
      _ = (X.action index).fire ≫ (f.event ≫ g.event) :=
        Category.assoc _ _ _

/-- All remaining fields of an operational map are laws: its data consist
of the binding/program map, event map, and contextual premise transports. -/
@[ext] theorem Hom.ext {f g : Hom X Y}
    (base : f.base = g.base)
    (event : f.event = g.event)
    (premiseMap : HEq f.premiseMap g.premiseMap) : f = g := by
  cases f
  cases g
  cases base
  cases event
  cases premiseMap
  rfl

/-- Pointwise equality of the scoped maps is sufficient even when the
global binding and event maps were written by different compositions. -/
theorem Hom.ext_of_pointwise {f g : Hom X Y}
    (base : f.base = g.base)
    (event : f.event = g.event)
    (premises : ∀ index position,
      (f.premiseMap index).premise position =
        (g.premiseMap index).premise position) : f = g := by
  cases f with
  | mk firstBase firstEvent firstEndpoints firstPremises firstConclusions firstActions =>
    cases g with
    | mk secondBase secondEvent secondEndpoints secondPremises secondConclusions secondActions =>
      dsimp at base event premises
      cases base
      cases event
      have same : firstPremises = secondPremises := by
        funext index
        apply RulePremiseTransport.ext
        exact premises index
      cases same
      rfl

noncomputable instance : Category (PresentedModel (D := D) equations rules) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := by
    intro X Y f
    apply Hom.ext_of_pointwise
    · exact ModelWithPrograms.Hom.id_comp f.base
    · exact Category.id_comp f.event
    · intro index position
      exact CategoricalScopedEventBaseChange.PointwiseMap.id_comp
        ((f.premiseMap index).premise position)
  comp_id := by
    intro X Y f
    apply Hom.ext_of_pointwise
    · exact ModelWithPrograms.Hom.comp_id f.base
    · exact Category.comp_id f.event
    · intro index position
      exact CategoricalScopedEventBaseChange.PointwiseMap.comp_id
        ((f.premiseMap index).premise position)
  assoc := by
    intro W X Y Z f g h
    apply Hom.ext_of_pointwise
    · exact ModelWithPrograms.Hom.comp_assoc f.base g.base h.base
    · exact Category.assoc f.event g.event h.event
    · intro index position
      exact CategoricalScopedEventBaseChange.PointwiseMap.comp_assoc
        ((f.premiseMap index).premise position)
        ((g.premiseMap index).premise position)
        ((h.premiseMap index).premise position)

theorem Hom.id_comp (f : Hom X Y) :
    (Hom.id X).comp f = f :=
  Category.id_comp (show X ⟶ Y from f)

theorem Hom.comp_id (f : Hom X Y) :
    f.comp (Hom.id Y) = f :=
  Category.comp_id (show X ⟶ Y from f)

theorem Hom.comp_assoc (f : Hom X Y) (g : Hom Y Z)
    {W : PresentedModel (D := D) equations rules} (h : Hom Z W) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  Category.assoc (show X ⟶ Y from f)
    (show Y ⟶ Z from g) (show Z ⟶ W from h)

/-- Forgetting operational evidence returns the independently classified
binding and equation interpretation, on both models and all model maps. -/
noncomputable def forgetEquations
    (equations : EquationPresentation S schema)
    (rules : List (IntrinsicScopedConditionalPolynomial.Rule S schema)) :
    PresentedModel (D := D) equations rules ⥤
      CategoricalBindingEquationEquivalence.SatisfyingInterpretation
        (D := D) equations where
  obj X := ⟨⟨X.base.binding⟩, X.satisfies⟩
  map f := f.base.binding
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The checked binding/equation equivalence is the restriction of every
operational interpretation; adding events has not changed its judgment. -/
noncomputable def bindingEquationRestriction
    (equations : EquationPresentation S schema)
    (rules : List (IntrinsicScopedConditionalPolynomial.Rule S schema)) :
    PresentedModel (D := D) equations rules ⥤
      CategoricalBindingQuotientEquivalence.QuotientStructuredFunctor
        (D := D) equations :=
  forgetEquations (D := D) equations rules ⋙
    (CategoricalBindingQuotientEquivalence.bindingEquationEquivalence
      (D := D) equations).functor

/-- The predicate observation forgets which authored firing occurred. Its
construction requires images in the target; the event object does not. -/
noncomputable def reductionImage [HasImages D]
    (X : PresentedModel (D := D) equations rules) : D :=
  image X.endpoints

noncomputable def reductionMono [HasImages D]
    (X : PresentedModel (D := D) equations rules) :
    reductionImage X ⟶ EndpointPairs X.base.binding X.base.carrier :=
  image.ι X.endpoints

theorem event_factors_reduction [HasImages D]
    (X : PresentedModel (D := D) equations rules) :
    factorThruImage X.endpoints ≫ reductionMono X = X.endpoints :=
  image.fac X.endpoints

/-- A varying-base operational map determines the actual square of event
and program-pair objects, before any image observation. -/
noncomputable def Hom.endpointSquare (f : Hom X Y) :
    Arrow.mk X.endpoints ⟶ Arrow.mk Y.endpoints :=
  Arrow.homMk f.event f.base.endpointMap
    (by simpa using f.endpoints_comm)

theorem Hom.endpointSquare_id (X : PresentedModel (D := D) equations rules) :
    (Hom.id X).endpointSquare = 𝟙 (Arrow.mk X.endpoints) := by
  apply Arrow.hom_ext
  · simp [Hom.endpointSquare, Hom.id]
  · simp [Hom.endpointSquare, Hom.id,
      CategoricalAuthoredProgramCarrierMaps.ModelWithPrograms.Hom.endpointMap_id]

theorem Hom.endpointSquare_comp (f : Hom X Y) (g : Hom Y Z) :
    (f.comp g).endpointSquare = f.endpointSquare ≫ g.endpointSquare := by
  apply Arrow.hom_ext
  · simp [Hom.endpointSquare, Hom.comp]
  · simp [Hom.endpointSquare, Hom.comp,
      CategoricalAuthoredProgramCarrierMaps.ModelWithPrograms.Hom.endpointMap_comp]

/-- Image observation is forward natural for ordinary interpretation maps.
No reflection, event injectivity, or coverage conclusion follows. -/
theorem reductionImage_forward [HasImages D] [HasImageMaps D]
    (f : Hom X Y) :
    image.map f.endpointSquare ≫ reductionMono Y =
      reductionMono X ≫ f.base.endpointMap := by
  exact image.map_ι f.endpointSquare

end PresentedModel
end Mettapedia.OSLF.Binding.CategoricalAuthoredOperationalModels
