import Mettapedia.OSLF.Syntax.IntrinsicScopedOperationalPresheafEventFunctions

/-!
# Actual generalized substitution actions on retained events

Every categorical stage carries the original retained event objects with a
lawful contextual substitution action. The construction transports the real
context-arrow action through the endpoint-preserving event comparison, and
commutes with every map of generalized stages.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.OSLF.Binding.IntrinsicScopedOperationalPresheafActions

open _root_.CategoryTheory
open IntrinsicScopedJudgmentAction (JudgmentAction ActionOn)
open IntrinsicScopedOperationalPresheafEvents (sortEvents)
open IntrinsicScopedOperationalPresheafEventPowers (objects source)
open IntrinsicScopedOperationalPresheafPrograms (model)
open IntrinsicScopedOperationalPresheafEventFunctions (stageEventEquiv stageEventEquiv_restage)
open AuthoredPositionedRulePolynomial (Judgment mapJudgment)
open IntrinsicScopedConditionalSubstitution (substJudgment mapJudgment_substJudgment)

universe u
variable {S : Signature} {A : BindingCloneAlgebra.Algebra.{u} S}

/-- The context-arrow substitution action on natural retained evidence. -/
def naturalAction (Y : JudgmentAction.{u,u} A)
    (Z : IntrinsicScopedOperationalPresheafPrograms.target A) : JudgmentAction ((model A).stage Z) :=
  IntrinsicScopedOperationalPresheafNaturalEvidence.judgmentAction
    (M := model A) (F := sortEvents Y) (source := source Y)
    (target := IntrinsicScopedOperationalPresheafEventPowers.target Y) Z

/-- Actual substitution of categorical generalized retained events. -/
def act (Y : JudgmentAction.{u,u} A)
    (Z : IntrinsicScopedOperationalPresheafPrograms.target A) :
    ActionOn ((model A).stage Z) ((objects Y).StageEvent Z) :=
  fun judgment event _ σ result same => (stageEventEquiv Y Z result).symm
    ((naturalAction Y Z).act judgment (stageEventEquiv Y Z judgment event) σ result same)

/-- The actual event comparison preserves the implemented substitution action. -/
theorem act_comparison (Y : JudgmentAction.{u,u} A)
    (Z : IntrinsicScopedOperationalPresheafPrograms.target A)
    (judgment : Judgment ((model A).stage Z)) (event : (objects Y).StageEvent Z judgment)
    {Δ : Ctx S}
    (σ : BindingSubstitutionAlgebra.Environment S ((model A).stage Z).substitution.Carrier judgment.1 Δ)
    (result : Judgment ((model A).stage Z)) (same : substJudgment judgment σ = result) :
    stageEventEquiv Y Z result (act Y Z judgment event σ result same) =
      (naturalAction Y Z).act judgment (stageEventEquiv Y Z judgment event) σ result same :=
  (stageEventEquiv Y Z result).apply_symm_apply _

/-- Identity substitution fixes every actual categorical event. -/
theorem act_identity (Y : JudgmentAction.{u,u} A)
    (Z : IntrinsicScopedOperationalPresheafPrograms.target A) : ActionOn.IdentityLaw (act Y Z) := by
  intro judgment event same
  apply (stageEventEquiv Y Z judgment).injective
  rw [act_comparison]
  exact (naturalAction Y Z).act_identity judgment (stageEventEquiv Y Z judgment event) same

/-- Composition holds for actual event objects and arbitrary semantic substitutions. -/
theorem act_comp (Y : JudgmentAction.{u,u} A)
    (Z : IntrinsicScopedOperationalPresheafPrograms.target A) : ActionOn.CompLaw (act Y Z) := by
  intro judgment event Δ Θ σ τ result hSecond hDirect
  apply (stageEventEquiv Y Z result).injective
  have first := act_comparison Y Z judgment event σ (substJudgment judgment σ) rfl
  have second := act_comparison Y Z (substJudgment judgment σ)
    (act Y Z judgment event σ (substJudgment judgment σ) rfl) τ result hSecond
  have direct := act_comparison Y Z judgment event
    (fun s var => ((model A).stage Z).substitution.substitute τ (σ s var)) result hDirect
  exact second.trans ((congrArg (fun value =>
    (naturalAction Y Z).act (substJudgment judgment σ) value τ result hSecond) first).trans
      (((naturalAction Y Z).act_comp judgment (stageEventEquiv Y Z judgment event)
        σ τ result hSecond hDirect).trans direct.symm))

/-- The actual retained-event objects form a judgment action at every categorical stage. -/
def stageAction (Y : JudgmentAction.{u,u} A)
    (Z : IntrinsicScopedOperationalPresheafPrograms.target A) : JudgmentAction ((model A).stage Z) where
  carrier := (objects Y).StageEvent Z
  act := act Y Z
  act_identity := act_identity Y Z
  act_comp := act_comp Y Z

/-- Actual contextual substitution and every generalized stage map commute. -/
theorem act_restage (Y : JudgmentAction.{u,u} A)
    {Z Z' : IntrinsicScopedOperationalPresheafPrograms.target A} (h : Z' ⟶ Z)
    (judgment : Judgment ((model A).stage Z)) (event : (objects Y).StageEvent Z judgment)
    {Δ : Ctx S}
    (σ : BindingSubstitutionAlgebra.Environment S ((model A).stage Z).substitution.Carrier judgment.1 Δ)
    (result : Judgment ((model A).stage Z)) (same : substJudgment judgment σ = result) :
    (objects Y).restage h (act Y Z judgment event σ result same) =
      act Y Z' (mapJudgment ((model A).stageRestage h) judgment) ((objects Y).restage h event)
        (fun s var => ((model A).stageRestage h).raw.map (σ s var))
        (mapJudgment ((model A).stageRestage h) result)
        ((mapJudgment_substJudgment _ judgment σ).symm.trans (congrArg _ same)) := by
  apply (stageEventEquiv Y Z' (mapJudgment ((model A).stageRestage h) result)).injective
  have first := act_comparison Y Z judgment event σ result same
  have second := act_comparison Y Z'
    (mapJudgment ((model A).stageRestage h) judgment) ((objects Y).restage h event)
    (fun s var => ((model A).stageRestage h).raw.map (σ s var))
    (mapJudgment ((model A).stageRestage h) result)
    ((mapJudgment_substJudgment _ judgment σ).symm.trans (congrArg _ same))
  have natural := IntrinsicScopedOperationalPresheafNaturalEvidence.act_restage h judgment
    (stageEventEquiv Y Z judgment event) σ result same
  exact (stageEventEquiv_restage Y h (act Y Z judgment event σ result same)).trans
    ((congrArg (IntrinsicScopedOperationalPresheafNaturalEvidence.restage h) first).trans
      (natural.trans ((congrArg (fun value =>
        (naturalAction Y Z').act (mapJudgment ((model A).stageRestage h) judgment) value
          (fun s var => ((model A).stageRestage h).raw.map (σ s var))
          (mapJudgment ((model A).stageRestage h) result)
          ((mapJudgment_substJudgment _ judgment σ).symm.trans (congrArg _ same)))
        (stageEventEquiv_restage Y h event).symm).trans second.symm)))

end Mettapedia.OSLF.Binding.IntrinsicScopedOperationalPresheafActions
