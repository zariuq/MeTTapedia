import Mettapedia.OSLF.Syntax.IntrinsicScopedOperationalPresheafSubstitution
import Mettapedia.OSLF.Syntax.IntrinsicScopedJudgmentAction

/-!
# Substitution of natural retained evidence

Evidence over a generalized contextual judgment is an arrow out of its
context product, with the original endpoint conditions. Semantic substitution
acts by precomposition with the actual context arrow.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.IntrinsicScopedOperationalPresheafNaturalEvidence

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.CategoryTheory.CartesianMonoidalCategory
open CategoricalBindingModel
open AuthoredPositionedRulePolynomial (Judgment)
open IntrinsicScopedJudgmentAction (ActionOn JudgmentAction)
open IntrinsicScopedConditionalSubstitution (substJudgment)
open IntrinsicScopedOperationalPresheafSubstitution

universe u v
variable {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D]
variable {S : Signature} (M : Model S D) (F : S.Srt → D)
variable (source target : ∀ s, F s ⟶ M.sort s)

/-- Natural evidence retains its actual arrow and both program endpoints. -/
def Evidence (Z : D) (judgment : Judgment (M.stage Z)) : Type v :=
  {event : M.ctx judgment.1 ⊗ Z ⟶ F judgment.2.1 //
    event ≫ source judgment.2.1 = M.elemValue judgment.2.2.1 ∧
      event ≫ target judgment.2.1 = M.elemValue judgment.2.2.2}

variable {M F source target}

/-- Substitution acts on the full evidence arrow; no event is identified by its endpoints. -/
def substitute {Z : D} (judgment : Judgment (M.stage Z))
    (event : Evidence M F source target Z judgment) {Δ : Ctx S}
    (σ : BindingSubstitutionAlgebra.Environment S (M.stage Z).substitution.Carrier judgment.1 Δ) :
    Evidence M F source target Z (substJudgment judgment σ) :=
  ⟨substitutionArrow M σ ≫ event.1,
    (Category.assoc _ _ _).trans ((congrArg (substitutionArrow M σ ≫ ·) event.2.1).trans
      (substitutionArrow_value M σ judgment.2.2.1).symm),
    (Category.assoc _ _ _).trans ((congrArg (substitutionArrow M σ ≫ ·) event.2.2).trans
      (substitutionArrow_value M σ judgment.2.2.2).symm)⟩

/-- The substitution action indexed by its actual resulting judgment. -/
def act (Z : D) : ActionOn (M.stage Z) (Evidence M F source target Z) :=
  fun judgment event _ σ _result same => same ▸ substitute judgment event σ

/-- Transporting the judgment index retains the substituted evidence arrow. -/
theorem act_val {Z : D} (judgment : Judgment (M.stage Z))
    (event : Evidence M F source target Z judgment) {Δ : Ctx S}
    (σ : BindingSubstitutionAlgebra.Environment S (M.stage Z).substitution.Carrier judgment.1 Δ)
    (result : Judgment (M.stage Z)) (same : substJudgment judgment σ = result) :
    HEq ((act Z judgment event σ result same).1) (substitutionArrow M σ ≫ event.1) := by
  cases same
  rfl

/-- Identity substitution fixes every retained natural evidence value. -/
theorem act_identity (Z : D) : ActionOn.IdentityLaw (@act _ _ _ _ M F source target Z) := by
  intro judgment event same
  apply Subtype.ext
  have value := act_val judgment event (fun _ var => (M.stage Z).substitution.injectVar var)
    judgment same
  exact (eq_of_heq value).trans (by rw [substitutionArrow_identity, Category.id_comp])

/-- Consecutive substitutions compose on the actual evidence arrow. -/
theorem act_comp (Z : D) : ActionOn.CompLaw (@act _ _ _ _ M F source target Z) := by
  intro judgment event Δ Θ σ τ result hSecond hDirect
  subst result
  apply Subtype.ext
  rw [eq_of_heq (act_val (substJudgment judgment σ)
    (act Z judgment event σ (substJudgment judgment σ) rfl) τ _ rfl)]
  rw [eq_of_heq (act_val judgment event _ _ hDirect)]
  change substitutionArrow M τ ≫ (substitutionArrow M σ ≫ event.1) =
    substitutionArrow M (fun s var => (M.stage Z).substitution.substitute τ (σ s var)) ≫ event.1
  change (s : S.Srt) → Var judgment.1 s → M.ElemOver Z Δ s at σ
  change (s : S.Srt) → Var Δ s → M.ElemOver Z Θ s at τ
  change substitutionArrow M τ ≫ (substitutionArrow M σ ≫ event.1) =
    substitutionArrow M (fun s var => substituteElem M τ (σ s var)) ≫ event.1
  rw [substitutionArrow_comp, Category.assoc]

/-- Changing the stage retains the entire evidence arrow. -/
def restage {Z Z' : D} (h : Z' ⟶ Z) {judgment : Judgment (M.stage Z)}
    (event : Evidence M F source target Z judgment) :
    Evidence M F source target Z'
      (AuthoredPositionedRulePolynomial.mapJudgment (M.stageRestage h) judgment) :=
  ⟨(M.ctx judgment.1 ◁ h) ≫ event.1,
    (Category.assoc _ _ _).trans ((congrArg ((M.ctx judgment.1 ◁ h) ≫ ·) event.2.1).trans
      (elemValue_restage M h judgment.2.2.1).symm),
    (Category.assoc _ _ _).trans ((congrArg ((M.ctx judgment.1 ◁ h) ≫ ·) event.2.2).trans
      (elemValue_restage M h judgment.2.2.2).symm)⟩

/-- Stage change and actual contextual substitution commute on retained evidence. -/
theorem act_restage {Z Z' : D} (h : Z' ⟶ Z) (judgment : Judgment (M.stage Z))
    (event : Evidence M F source target Z judgment) {Δ : Ctx S}
    (σ : BindingSubstitutionAlgebra.Environment S (M.stage Z).substitution.Carrier judgment.1 Δ)
    (result : Judgment (M.stage Z)) (same : substJudgment judgment σ = result) :
    restage h (act Z judgment event σ result same) =
      act Z' (AuthoredPositionedRulePolynomial.mapJudgment (M.stageRestage h) judgment)
        (restage h event) (fun s var => (M.stageRestage h).raw.map (σ s var))
        (AuthoredPositionedRulePolynomial.mapJudgment (M.stageRestage h) result)
        ((IntrinsicScopedConditionalSubstitution.mapJudgment_substJudgment _ judgment σ).symm.trans
          (congrArg _ same)) := by
  cases same
  apply Subtype.ext
  change (s : S.Srt) → Var judgment.1 s → M.ElemOver Z Δ s at σ
  have image := act_val
    (AuthoredPositionedRulePolynomial.mapJudgment (M.stageRestage h) judgment)
    (restage h event) (fun s var => (M.stageRestage h).raw.map (σ s var))
    (AuthoredPositionedRulePolynomial.mapJudgment (M.stageRestage h) (substJudgment judgment σ))
    ((IntrinsicScopedConditionalSubstitution.mapJudgment_substJudgment _ judgment σ).symm)
  have maps : (M.ctx Δ ◁ h) ≫ (substitutionArrow M σ ≫ event.1) =
      substitutionArrow M (fun s var => M.restageElem h (σ s var)) ≫
        ((M.ctx judgment.1 ◁ h) ≫ event.1) := by
    rw [← Category.assoc, ← Category.assoc, substitutionArrow_restage]
  exact maps.trans (eq_of_heq image).symm

/-- At each categorical stage retained natural evidence is a genuine judgment action. -/
def judgmentAction (Z : D) : JudgmentAction (M.stage Z) where
  carrier := Evidence M F source target Z
  act := act Z
  act_identity := act_identity Z
  act_comp := act_comp Z

end Mettapedia.OSLF.Binding.IntrinsicScopedOperationalPresheafNaturalEvidence
