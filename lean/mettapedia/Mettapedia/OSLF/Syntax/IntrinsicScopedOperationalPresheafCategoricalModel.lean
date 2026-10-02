import Mettapedia.OSLF.Syntax.IntrinsicScopedOperationalPresheafRuleSubstitution
import Mettapedia.OSLF.Syntax.IntrinsicScopedOperationalPresheafProgramModel
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalCarrierTransportProjections

/-!
# The actual categorical operational model in clone presheaves

The original lawful local operational model supplies all retained event objects,
substitution actions and ordered rule actions in the clone presheaf category.
Full contextual equation satisfaction of the chosen clone supplies its program
interpretation. Arbitrary maps of presheaf stages preserve both actual actions.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.OSLF.Binding.IntrinsicScopedOperationalPresheafCategoricalModel

open _root_.CategoryTheory
open BindingSubstitutionAlgebra
open IntrinsicScopedOperationalPresheafPrograms (target model)
open IntrinsicScopedOperationalPresheafActions (naturalAction)
open IntrinsicScopedOperationalPresheafRuleFirings (naturalRules)
open IntrinsicScopedOperationalPresheafRuleSubstitution (naturalRules_act_rules)
open IntrinsicScopedOperationalPresheafRuleNaturality (naturalRules_stageRestage restageChildren)
open IntrinsicScopedOperationalPresheafEventPowers (objects)
open IntrinsicScopedOperationalPresheafEventFunctions (stageEventEquiv stageEventEquiv_restage)
open IntrinsicScopedLocalPolynomial (LocalRule Shape childJudgment mapShape mapInstance mapInstance_child)
open IntrinsicScopedLocalSubstitutionModel (SubstitutionModel)
open IntrinsicScopedLocalActedCategoricalModels (CategoricalModel)
open IntrinsicScopedConditionalSubstitution (substJudgment mapJudgment_substJudgment)
open AuthoredPositionedRulePolynomial (Judgment mapJudgment)

universe u
variable {S : Signature} {A : BindingCloneAlgebra.Algebra.{u} S}
variable (R : List (LocalRule S)) (Y : SubstitutionModel.{u,u} R A)

/-- The actual natural-evidence substitution model at every generalized stage. -/
def naturalStage (Z : target A) : SubstitutionModel R ((model A).stage Z) where
  toAction := naturalAction Y.toAction Z
  rules := naturalRules R Y Z
  act_rules := naturalRules_act_rules R Y Z

/-- The original retained-event function equivalence changes only evidence representation. -/
def actualStage (Z : target A) : SubstitutionModel R ((model A).stage Z) :=
  (naturalStage R Y Z).transportCarrier (fun j => (stageEventEquiv Y.toAction Z j).symm)

/-- The transported action uses the checked actual categorical event substitution. -/
theorem actualStage_act (Z : target A) :
    (actualStage R Y Z).act = IntrinsicScopedOperationalPresheafActions.act Y.toAction Z := rfl

/-- The actual rule algebra with its categorical event carrier explicit. -/
def stageRules (Z : target A) :
    (IntrinsicScopedLocalPolynomial.rules R ((model A).stage Z)).Algebra
      (fun _ j => (objects Y.toAction).StageEvent Z j) :=
  (naturalStage R Y Z).carrierRules (fun j => (stageEventEquiv Y.toAction Z j).symm)

/-- The explicit categorical rule carrier is the transported stage algebra. -/
theorem stageRules_eq (Z : target A) : stageRules R Y Z = (actualStage R Y Z).rules := rfl

/-- The checked natural-evidence law transfers to the actual categorical event carrier. -/
theorem stageRulesLaw (Z : target A) :
    IntrinsicScopedLocalSubstitutionModel.RulesLaw R ((model A).stage Z)
      (IntrinsicScopedOperationalPresheafActions.act Y.toAction Z) (stageRules R Y Z) := by
  have law : IntrinsicScopedLocalSubstitutionModel.RulesLaw R ((model A).stage Z)
      (actualStage R Y Z).act (actualStage R Y Z).rules := (actualStage R Y Z).act_rules
  rw [actualStage_act] at law
  exact @law

/-- The original retained-event comparison preserves every implemented rule firing. -/
theorem actualStage_rules_comparison (Z : target A) (j : Judgment ((model A).stage Z))
    (shape : Shape R ((model A).stage Z) j)
    (children : ∀ position : Fin (R.get shape.1.index).2.premises.length,
      (objects Y.toAction).StageEvent Z (childJudgment R ((model A).stage Z) shape.1 position)) :
    stageEventEquiv Y.toAction Z j ((actualStage R Y Z).rules.act () j ⟨shape, children⟩) =
      (naturalRules R Y Z).act () j
        ⟨shape, fun position => stageEventEquiv Y.toAction Z _ (children position)⟩ :=
  (stageEventEquiv Y.toAction Z j).apply_symm_apply _

/-- The event comparison respects each endpoint-index transport. -/
theorem stageEventEquiv_transport {Z : target A}
    {j j' : Judgment ((model A).stage Z)} (same : j = j')
    (event : (objects Y.toAction).StageEvent Z j) :
    stageEventEquiv Y.toAction Z j' (same ▸ event) =
      same ▸ stageEventEquiv Y.toAction Z j event := by
  cases same
  rfl

/-- Each restaged ordered child is compared with the same retained natural evidence. -/
theorem restagedChild_comparison {Z Z' : target A} (h : Z' ⟶ Z)
    {j : Judgment ((model A).stage Z)} (shape : Shape R ((model A).stage Z) j)
    (children : ∀ position : Fin (R.get shape.1.index).2.premises.length,
      (objects Y.toAction).StageEvent Z (childJudgment R ((model A).stage Z) shape.1 position))
    (position : Fin (R.get shape.1.index).2.premises.length) :
    stageEventEquiv Y.toAction Z' _
        ((mapInstance_child R ((model A).stageRestage h) shape.1 position).symm ▸
          (objects Y.toAction).restage h (children position)) =
      restageChildren R Y h shape.1
        (fun position => stageEventEquiv Y.toAction Z _ (children position)) position :=
  (stageEventEquiv_transport R Y
    (mapInstance_child R ((model A).stageRestage h) shape.1 position).symm _).trans
      (congrArg (fun value =>
        (mapInstance_child R ((model A).stageRestage h) shape.1 position).symm ▸ value)
        (stageEventEquiv_restage Y.toAction h (children position)))

/-- Arbitrary stage maps are genuine maps of the natural-evidence operational models. -/
def naturalRestageHom {Z Z' : target A} (h : Z' ⟶ Z) :
    SubstitutionModel.Hom R _ (naturalStage R Y Z)
      ((naturalStage R Y Z').pullback ((model A).stageRestage h)) :=
  SubstitutionModel.Hom.ofIsHom R _
    (fun _ event => IntrinsicScopedOperationalPresheafNaturalEvidence.restage h event)
    (IntrinsicScopedLocalSubstitutionModel.isHom_of_along
      (h := (model A).stageRestage h) (model := naturalStage R Y Z) (target := naturalStage R Y Z')
      (image := fun _ event => IntrinsicScopedOperationalPresheafNaturalEvidence.restage h event)
      (by
        intro j event Δ σ
        exact IntrinsicScopedOperationalPresheafNaturalEvidence.act_restage h j event σ
          (substJudgment j σ) rfl)
      (by
        intro j shape children
        exact naturalRules_stageRestage R Y h shape children))

/-- Transporting both endpoints of the natural stage-model map retains its full operational laws. -/
def actualRestageHom {Z Z' : target A} (h : Z' ⟶ Z) :
    SubstitutionModel.Hom R _ (actualStage R Y Z)
      ((actualStage R Y Z').pullback ((model A).stageRestage h)) :=
  SubstitutionModel.Hom.comp R _
    (SubstitutionModel.Hom.comp R _
      ((naturalStage R Y Z).transportCarrierInvHom (fun j => (stageEventEquiv Y.toAction Z j).symm))
      (naturalRestageHom R Y h))
    (SubstitutionModel.Hom.pullback ((model A).stageRestage h)
      ((naturalStage R Y Z').transportCarrierHom (fun j => (stageEventEquiv Y.toAction Z' j).symm)))

/-- The actual stage-model map acts by the original event object's precomposition. -/
theorem actualRestageHom_apply {Z Z' : target A} (h : Z' ⟶ Z)
    (j : Judgment ((model A).stage Z)) (event : (objects Y.toAction).StageEvent Z j) :
    (actualRestageHom R Y h).evidence.toFun () j event = (objects Y.toAction).restage h event := by
  apply (stageEventEquiv Y.toAction Z' (mapJudgment ((model A).stageRestage h) j)).injective
  change stageEventEquiv Y.toAction Z' _
      ((stageEventEquiv Y.toAction Z' _).symm
        (IntrinsicScopedOperationalPresheafNaturalEvidence.restage h
          (stageEventEquiv Y.toAction Z j event))) = _
  exact ((stageEventEquiv Y.toAction Z' _).apply_symm_apply _).trans
    (stageEventEquiv_restage Y.toAction h event).symm

/-- Ordinary precomposition preserves both actual categorical operational actions. -/
theorem actualRestageIsHom {Z Z' : target A} (h : Z' ⟶ Z) :
    SubstitutionModel.IsHom R _ (actualStage R Y Z)
      ((actualStage R Y Z').pullback ((model A).stageRestage h))
      (fun _ event => (objects Y.toAction).restage h event) :=
  SubstitutionModel.IsHom.congr R _ (actualRestageHom_apply R Y h)
    (actualRestageHom R Y h).isHom

set_option backward.isDefEq.respectTransparency false in
/-- The actual categorical rule action preserves every generalized stage map. -/
theorem actualStage_rules_restage {Z Z' : target A} (h : Z' ⟶ Z)
    {j : Judgment ((model A).stage Z)} (shape : Shape R ((model A).stage Z) j)
    (children : ∀ position : Fin (R.get shape.1.index).2.premises.length,
      (objects Y.toAction).StageEvent Z (childJudgment R ((model A).stage Z) shape.1 position)) :
    (objects Y.toAction).restage h ((stageRules R Y Z).act () j ⟨shape, children⟩) =
      (stageRules R Y Z').act () (mapJudgment ((model A).stageRestage h) j)
        ⟨mapShape R ((model A).stageRestage h) shape, fun position =>
          ((mapInstance_child R ((model A).stageRestage h) shape.1 position).symm ▸
            (objects Y.toAction).restage h (children position) :
              (objects Y.toAction).StageEvent Z' (childJudgment R ((model A).stage Z')
                (mapInstance R ((model A).stageRestage h) shape.1) position))⟩ := by
  have law := IntrinsicScopedLocalSubstitutionModel.rulesAlong_of_isHom
    (actualStage R Y Z) ((model A).stageRestage h) (actualStage R Y Z')
    (fun _ event => (objects Y.toAction).restage h event)
    (actualRestageIsHom R Y h) j shape children
  rw [stageRules_eq, stageRules_eq]
  simp only [] at law
  with_reducible exact law

set_option backward.isDefEq.respectTransparency false in
/-- A fully contextual lawful clone and its genuine local operational model
supply the actual categorical operational model in the presheaf target. -/
def categoricalModel {N : List (MetaArity S)} (equations : List (EqAxiom S N))
    (satisfies : BindingEquationInterpretation.Satisfies A equations) :
    CategoricalModel R equations (D := target A) where
  program := ⟨⟨model A⟩, IntrinsicScopedOperationalPresheafEquations.model_satisfies A equations satisfies⟩
  objects := objects Y.toAction
  act := IntrinsicScopedOperationalPresheafActions.act Y.toAction
  act_identity := IntrinsicScopedOperationalPresheafActions.act_identity Y.toAction
  act_comp := IntrinsicScopedOperationalPresheafActions.act_comp Y.toAction
  rules := stageRules R Y
  act_rules := by
    intro Z
    with_reducible exact @stageRulesLaw S A R Y Z
  act_restage := by
    intro Z Z' h j event Δ σ result same
    exact IntrinsicScopedOperationalPresheafActions.act_restage Y.toAction h j event σ result same
  rules_restage := by
    intro Z Z' h j shape children
    with_reducible exact actualStage_rules_restage R Y h shape children

end Mettapedia.OSLF.Binding.IntrinsicScopedOperationalPresheafCategoricalModel
