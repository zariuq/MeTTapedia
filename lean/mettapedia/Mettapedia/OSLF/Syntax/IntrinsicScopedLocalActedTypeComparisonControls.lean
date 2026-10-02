import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedTypeComparisonNaturality
import Mettapedia.OSLF.Syntax.IntrinsicLambdaFourRulePresentation

/-!
# A Boolean function model with an abstraction-congruence firing

The existing four Lambda rules are read through the rule-local interface
without changing their schemas. Programs are Boolean functions of their
context variables. Application uses exclusive disjunction and abstraction
evaluates its body at `false`. Events are endpoint pairs, giving a total
relation on programs. The comparison is exercised on the actual LamCong
constructor and its premise under a term binder.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedTypeComparisonControls

open _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory
open Mettapedia.OSLF.Binding.CategoricalBindingModel
open Mettapedia.OSLF.Binding.CategoricalBindingEquationEquivalence
open Mettapedia.OSLF.Binding.SecondOrderContext
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalPolynomial
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedClassifier
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedCategoricalModels
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedSetSemantics
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedTypeComparison
open Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial (Judgment mapJudgment)

namespace EndpointPairs

variable {S : Signature} (P : Model S Type)

/-- The actual ordered endpoint pairs of the represented program carriers. -/
def objects : EventObjects P where
  event Γ s := P.power Γ s × P.power Γ s
  source _ _ := TypeCat.ofHom Prod.fst
  target _ _ := TypeCat.ofHom Prod.snd

/-- A generalized pair with the requested endpoints. -/
def event (Z : Type) (j : Judgment (P.stage Z)) : (objects P).StageEvent Z j :=
  ⟨TypeCat.ofHom (fun z => ⟨P.elemEquiv j.2.2.1 z, P.elemEquiv j.2.2.2 z⟩), rfl, rfl⟩

theorem event_heq {Z : Type} {first second : Judgment (P.stage Z)}
    (same : first = second) : HEq (event P Z first) (event P Z second) := by
  cases same
  rfl

instance stageSubsingleton (Z : Type) (j : Judgment (P.stage Z)) :
    Subsingleton ((objects P).StageEvent Z j) := by
  constructor
  intro first second
  apply Subtype.ext
  apply TypeCat.Hom.ext
  apply TypeCat.Fun.ext
  funext z
  apply Prod.ext
  · exact (congrArg (fun f : Z ⟶ P.power j.1 j.2.1 => f z) first.2.1).trans
      (congrArg (fun f : Z ⟶ P.power j.1 j.2.1 => f z) second.2.1).symm
  · exact (congrArg (fun f : Z ⟶ P.power j.1 j.2.1 => f z) first.2.2).trans
      (congrArg (fun f : Z ⟶ P.power j.1 j.2.1 => f z) second.2.2).symm

variable (R : List (LocalRule S)) {schema : List (MetaArity S)}
  (E : List (EqAxiom S schema))
  (sat : P.Satisfies (authoredEquationPresentation S E))

/-- Every authored rule acts on endpoint pairs by its actual conclusion.
This is the total relation model, with the given nontrivial binding model. -/
def model : CategoricalModel R E (D := Type) where
  program := ⟨⟨P⟩, sat⟩
  objects := objects P
  act := fun Z _ _ _ _ target _ => event P Z target
  act_identity := fun Z => by
    intro j e h
    exact Subsingleton.elim _ _
  act_comp := fun Z => by
    intro j e Δ Θ σ τ target hSecond hDirect
    exact Subsingleton.elim _ _
  rules := fun Z => ⟨fun _ j _ => event P Z j⟩
  act_rules := fun Z => by
    intro j shape children Δ σ target h
    exact Subsingleton.elim _ _
  act_restage := by intros; exact Subsingleton.elim _ _
  rules_restage := by intros; exact Subsingleton.elim _ _

end EndpointPairs

open Mettapedia.OSLF.Binding.LambdaContextualRung (sig Srt Op)

/-- The unchanged existing Lambda schemas with their existing telescope. -/
abbrev lambdaRules : List (LocalRule sig) :=
  IntrinsicLambdaFourRulePresentation.rules.map
    (fun rule => ⟨IntrinsicLambdaFourRulePresentation.metas, rule⟩)

abbrev noEquations : List (EqAxiom sig ([] : List (MetaArity sig))) := []

/-- The term sort has two distinct values. -/
def boolSort : Srt → Type := fun _ => Bool

/-- The selected powers are ordinary functions on the context product. -/
def boolPrograms : Model sig Type where
  sort := boolSort
  power Γ s := contextOf boolSort Γ → boolSort s
  eval := fun _ _ => TypeCat.ofHom (fun p => p.2 p.1)
  curry := fun f => TypeCat.ofHom (fun z x => f (x, z))
  curry_eval := fun _ => rfl
  curry_unique := by
    intro Γ s Z f g h
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext z x
    exact (congrArg (fun k : contextOf boolSort Γ ⊗ Z ⟶ boolSort s => k (x, z)) h).symm
  op := fun {s} op => by
    cases s
    cases op with
    | app => exact TypeCat.ofHom (fun p => Bool.xor (p.1 PUnit.unit) (p.2.1 PUnit.unit))
    | lam => exact TypeCat.ofHom (fun p => p.1 (false, PUnit.unit))

theorem boolPrograms_satisfies :
    boolPrograms.Satisfies (authoredEquationPresentation sig noEquations) := by
  intro X i
  exact Fin.elim0 i

/-- A concrete categorical interpretation of all four existing Lambda rules. -/
def boolModel : CategoricalModel lambdaRules noEquations (D := Type) :=
  EndpointPairs.model (P := boolPrograms) lambdaRules noEquations boolPrograms_satisfies

theorem bool_sort_nontrivial : (false : boolPrograms.sort .term) ≠ true := by decide

/-- A body which reads the variable bound by the abstraction. -/
def leftBody : boolPrograms.power [.term] .term := fun p => p.1

/-- A second body with different behavior at both Boolean inputs. -/
def rightBody : boolPrograms.power [.term] .term := fun p => !p.1

theorem bodies_distinct : leftBody ≠ rightBody := by
  intro same
  have atFalse := congrFun same (false, PUnit.unit)
  change false = true at atFalse
  cases atFalse

def bodyValues : SemanticContextualMetavariables.Valuation
    (M := IntrinsicLambdaFourRulePresentation.metas) (boolPrograms.stage PUnit) []
  | ⟨0, _⟩ => (TypeModel.carrierEquiv boolModel _ _).symm leftBody
  | ⟨1, _⟩ => (TypeModel.carrierEquiv boolModel _ _).symm rightBody
  | ⟨2, _⟩ => (TypeModel.carrierEquiv boolModel _ _).symm (fun _ => false)
  | ⟨3, _⟩ => (TypeModel.carrierEquiv boolModel _ _).symm (fun _ => true)
  | ⟨4, _⟩ => (TypeModel.carrierEquiv boolModel _ _).symm (fun _ => true)
  | ⟨_ + 5, impossible⟩ => by
      simp [IntrinsicLambdaFourRulePresentation.metas] at impossible

abbrev lamIndex : Fin lambdaRules.length := ⟨3, by decide⟩

/-- An occurrence of the existing authored LamCong rule. -/
def lamOccurrence : Instance lambdaRules (boolPrograms.stage PUnit) where
  index := lamIndex
  ambient := []
  valuation := bodyValues
  close := fun _ var => nomatch var

theorem lam_firing_child_context :
    (childJudgment lambdaRules _ lamOccurrence ⟨0, by decide⟩).1 = [.term] := rfl

theorem lam_conclusion_source :
    TypeModel.carrierEquiv boolModel [] .term
      (conclusionJudgment lambdaRules _ lamOccurrence).2.2.1 = (fun _ => false) := by
  rfl

theorem lam_conclusion_target :
    TypeModel.carrierEquiv boolModel [] .term
      (conclusionJudgment lambdaRules _ lamOccurrence).2.2.2 = (fun _ => true) := by
  rfl

theorem lam_child_source :
    TypeModel.carrierEquiv boolModel [.term] .term
      (childJudgment lambdaRules _ lamOccurrence ⟨0, by decide⟩).2.2.1 = leftBody := by
  rfl

theorem lam_child_target :
    TypeModel.carrierEquiv boolModel [.term] .term
      (childJudgment lambdaRules _ lamOccurrence ⟨0, by decide⟩).2.2.2 = rightBody := by
  rfl

abbrev lamObject : Classifier lambdaRules noEquations :=
  ruleObject lambdaRules noEquations lamIndex []

/-- The actual program point and ordered event witness for this firing. -/
def lamValuation : boolModel.StageValuation PUnit lamObject where
  point := boolPrograms.rulePoint lambdaRules lamOccurrence
  event := fun position => EndpointPairs.event boolPrograms PUnit
    (mapJudgment ((boolModel.stageTarget PUnit).program
      (boolPrograms.rulePoint lambdaRules lamOccurrence))
        ((events lambdaRules noEquations lamObject).listed.label position))

theorem lam_program_occurrence_comparison :
    mapInstance lambdaRules ((boolModel.stageTarget PUnit).program lamValuation.point)
      (ruleInstance lambdaRules noEquations lamIndex []) = lamOccurrence :=
  boolPrograms.mapInstance_rulePoint lambdaRules noEquations boolPrograms_satisfies lamOccurrence

def lamChildren (position : Fin (lambdaRules.get lamIndex).2.premises.length) :
    boolModel.objects.StageEvent PUnit (childJudgment lambdaRules _ lamOccurrence position) :=
  EndpointPairs.event boolPrograms PUnit (childJudgment lambdaRules _ lamOccurrence position)

theorem lam_child_endpoint_pair :
    (lamChildren ⟨0, by decide⟩).1 PUnit.unit = (leftBody, rightBody) := by
  rfl

theorem lam_firing_endpoint_pair :
    ((boolModel.rules PUnit).act () (conclusionJudgment lambdaRules _ lamOccurrence)
      ⟨⟨lamOccurrence, rfl⟩, lamChildren⟩).1 PUnit.unit =
        ((fun _ => false), (fun _ => true)) := by
  rfl

/-- The model does not identify the two programs of this interpreted firing. -/
theorem lam_firing_not_diagonal :
    (((boolModel.rules PUnit).act () (conclusionJudgment lambdaRules _ lamOccurrence)
      ⟨⟨lamOccurrence, rfl⟩, lamChildren⟩).1 PUnit.unit).1 ≠
    (((boolModel.rules PUnit).act () (conclusionJudgment lambdaRules _ lamOccurrence)
      ⟨⟨lamOccurrence, rfl⟩, lamChildren⟩).1 PUnit.unit).2 := by
  intro same
  have atUnit := congrFun same PUnit.unit
  change false = true at atUnit
  cases atUnit

/-- Evaluation consumes the ordered witness of the authored premise and
returns the model's action at this actual LamCong occurrence. -/
theorem lam_rule_firing_comparison :
    HEq (lamValuation.evaluate _ (ruleTree lambdaRules noEquations lamIndex []))
      ((boolModel.rules PUnit).act () (conclusionJudgment lambdaRules _ lamOccurrence)
        ⟨⟨lamOccurrence, rfl⟩, lamChildren⟩) := by
  apply lamValuation.evaluate_ruleTree_of_instance lamOccurrence
    lam_program_occurrence_comparison lamChildren
  intro p q same
  have sameIndex : p = q := eq_of_heq same
  subst q
  apply EndpointPairs.event_heq
  exact (childJudgment_congr lambdaRules lam_program_occurrence_comparison.symm
      p p HEq.rfl).trans
    (mapInstance_child lambdaRules ((boolModel.stageTarget PUnit).program lamValuation.point)
      (ruleInstance lambdaRules noEquations lamIndex []) p)

/-- The corresponding actual value of the categorical classifying object. -/
def lamValue : boolModel.classifyingObject lamObject :=
  (TypeModel.stageValueEquiv boolModel lamObject).symm lamValuation

theorem lam_program_event_value_comparison :
    TypeModel.valueEquiv boolModel lamObject lamValue =
      TypeModel.valuationEquiv boolModel lamObject lamValuation :=
  congrArg (TypeModel.valuationEquiv boolModel lamObject)
    ((TypeModel.stageValueEquiv boolModel lamObject).apply_symm_apply lamValuation)

/-- The actual classifying map of the authored LamCong node is ordinary
valuation transport on its Boolean program and its binder-local event. -/
theorem lam_classifying_map_comparison :
    TypeModel.valueEquiv boolModel _
      (boolModel.classifyingFunctor.map
        (ruleRep lambdaRules noEquations lamIndex []) lamValue) =
      (TypeModel.valueEquiv boolModel lamObject lamValue).transport
        (ruleRep lambdaRules noEquations lamIndex []) :=
  TypeModel.valueEquiv_map boolModel _ lamValue

end Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedTypeComparisonControls

end
