import Mettapedia.AutoBooks.Codex.Henkin1950.Syntax
import Mettapedia.Logic.HOL.Semantics.Henkin

namespace Mettapedia.AutoBooks.Codex.Henkin1950

open Mettapedia.Logic.HOL

/-!
Henkin's paper semantics constrain the distinguished description constant:
if a predicate has a witness, applying `iota` to that predicate must return a
witness. We record that condition explicitly in the paper-facing model classes.
-/

/-- Henkin's paper-general models are Henkin models whose `iota` constants satisfy the
description condition on admissible predicates. -/
structure GeneralModel extends HenkinModel.{0, 0, 0} Atom Primitive where
  iota_sound :
    ∀ (α : HTy) (p : @Ty.denote.{0, 0} Atom Carrier (Pred α)),
      adm (Pred α) p →
      (∃ x : @Ty.denote.{0, 0} Atom Carrier α, adm α x ∧ (p x).down) →
        (p (constDen (.iota α) p)).down

/-- A paper-standard model interprets `iota` as a genuine witness chooser. -/
structure StandardModel where
  Carrier : Atom → Type 1
  constDen : {τ : HTy} → Primitive τ → @Ty.denote.{0, 0} Atom Carrier τ
  iota_sound :
    ∀ (α : HTy) (p : @Ty.denote.{0, 0} Atom Carrier (Pred α)),
      (∃ x : @Ty.denote.{0, 0} Atom Carrier α, (p x).down) →
        (p (constDen (.iota α) p)).down

/-- Every paper-standard model induces a paper-general model by taking all values admissible. -/
def StandardModel.toGeneralModel (M : StandardModel) : GeneralModel :=
  { toHenkinModel :=
      @HenkinModel.standard.{0, 0, 0} Atom Primitive
        (StandardModel.Carrier M) (StandardModel.constDen M)
    iota_sound := by
      intro α p _ hp
      rcases hp with ⟨x, _, hx⟩
      exact M.iota_sound α p ⟨x, hx⟩ }

/-- In a paper-standard model every ambient value is admissible. -/
theorem standardModel_adm (M : StandardModel)
    {τ : HTy} (x : @Ty.denote.{0, 0} Atom M.Carrier τ) :
    (StandardModel.toGeneralModel M).adm τ x := by
  trivial

/-- In a paper-standard model, extensional equality collapses to actual equality
because admissibility is total. -/
theorem eqv_eq_of_standardModel (M : StandardModel) :
    ∀ {τ : HTy} {x y : @Ty.denote.{0, 0} Atom M.Carrier τ},
      HenkinModel.Eqv (StandardModel.toGeneralModel M).toHenkinModel τ x y →
        x = y
  | .prop, ⟨p⟩, ⟨q⟩, h => by
      apply congrArg ULift.up
      exact propext h
  | .base _, x, y, h => h
  | .arr σ τ, f, g, h => by
      funext x
      apply eqv_eq_of_standardModel M
      exact h x (standardModel_adm M x)

/-- General validity of a closed Henkin formula. -/
def ValidInGeneral (φ : Sentence) : Prop :=
  ∀ M : GeneralModel, HenkinModel.models M.toHenkinModel φ

/-- Standard validity of a closed Henkin formula. -/
def ValidInStandard (φ : Sentence) : Prop :=
  ∀ M : StandardModel, HenkinModel.models (StandardModel.toGeneralModel M).toHenkinModel φ

/-- Satisfiability of a closed theory in a general model. -/
def Satisfiable (T : ClosedTheorySet) : Prop :=
  ∃ M : GeneralModel, ∀ φ : Sentence, φ ∈ T → HenkinModel.models M.toHenkinModel φ

/-- Extra higher-order congruence principle needed for the full extensional
overlay: if a function value is admissible, then extensionally equal admissible
arguments map to extensionally equal results. This is exactly the semantic
strength used by the `eqAppArg` rule and quoted result 21. -/
def EqAppArgSound (M : GeneralModel) : Prop :=
  ∀ {σ τ : HTy}
    (f : @Ty.denote.{0, 0} Atom M.Carrier (σ ⇒ τ)),
      M.adm (σ ⇒ τ) f →
      ∀ {x y : @Ty.denote.{0, 0} Atom M.Carrier σ},
        M.adm σ x →
        M.adm σ y →
        HenkinModel.Eqv M.toHenkinModel σ x y →
          HenkinModel.Eqv M.toHenkinModel τ (f x) (f y)

/-- Paper-standard models satisfy the higher-order argument-congruence
principle isolated as `EqAppArgSound`. -/
theorem eqAppArgSound_of_standardModel (M : StandardModel) :
    EqAppArgSound (StandardModel.toGeneralModel M) := by
  intro σ τ f _ x y _ _ hxy
  have hEq : x = y := eqv_eq_of_standardModel M hxy
  subst y
  exact HenkinModel.eqv_refl (StandardModel.toGeneralModel M).toHenkinModel
    (standardModel_adm M (f x))

/-- Closed-theory form of Henkin's finite satisfiability condition: every finite
closed subtheory is satisfiable in a general model. -/
def FiniteSubsetSatisfiable (T : ClosedTheorySet) : Prop :=
  ∀ Δ : ClosedTheory,
    (∀ φ : Sentence, φ ∈ Δ → φ ∈ T) →
      ∃ M : GeneralModel,
        ∀ φ : Sentence, φ ∈ Δ → HenkinModel.models M.toHenkinModel φ

/-- Validity of an open formula in all paper-general models under all admissible valuations. -/
def ValidInGeneralCtx {Γ : Ctx Atom} (φ : Formula Γ) : Prop :=
  ∀ (M : GeneralModel) (ρ : HenkinModel.Valuation M.toHenkinModel Γ),
    HenkinModel.ValuationAdmissible M.toHenkinModel ρ →
      (HenkinModel.denote M.toHenkinModel φ ρ).down

/-- Every general-valid formula is standard-valid. -/
theorem validInStandard_of_validInGeneral {φ : Sentence} :
    ValidInGeneral φ → ValidInStandard φ := by
  intro h M
  exact h (StandardModel.toGeneralModel M)

/-- Theorem 3, forward closed-theory direction: a satisfiable closed theory has
all of its finite closed subtheories satisfiable in the same general model. -/
theorem theorem3_forward_finiteSubsets {T : ClosedTheorySet} :
    Satisfiable T → FiniteSubsetSatisfiable T := by
  intro hT Δ hΔ
  rcases hT with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  intro φ hφ
  exact hM φ (hΔ φ hφ)

/-- A recursively defined default inhabitant for every Henkin type over a one-point carrier. -/
def defaultValue :
    (τ : HTy) → @Ty.denote.{0, 0} Atom (fun _ : Atom => ULift.{1, 0} PUnit) τ
  | .prop => .up False
  | .base .ind => .up PUnit.unit
  | .arr _ τ => fun _ => defaultValue τ

/-- A default witness selector for the one-point paper-standard model. -/
noncomputable def defaultIota (α : HTy) :
    @Ty.denote.{0, 0} Atom (fun _ : Atom => ULift.{1, 0} PUnit) (Pred α ⇒ α) :=
  by
    classical
    intro p
    exact if h : ∃ x, (p x).down then Classical.choose h else defaultValue α

/-- A tiny paper-standard model witnessing that `⊥` is not valid. -/
noncomputable def defaultStandardModel : StandardModel where
  Carrier _ := ULift.{1, 0} PUnit
  constDen := by
    intro τ c
    cases c with
    | iota α =>
        exact defaultIota α
  iota_sound := by
    classical
    intro α p hp
    unfold defaultIota
    simp [hp]
    exact Classical.choose_spec hp

/-- Negative canary: falsity is not standard-valid. -/
theorem not_validInStandard_bot : ¬ ValidInStandard (.bot : Sentence) := by
  intro h
  exact (HenkinModel.models_bot (StandardModel.toGeneralModel defaultStandardModel).toHenkinModel)
    (h defaultStandardModel)

/-- Negative canary: falsity is not general-valid. -/
theorem not_validInGeneral_bot : ¬ ValidInGeneral (.bot : Sentence) := by
  intro h
  exact not_validInStandard_bot (validInStandard_of_validInGeneral h)

end Mettapedia.AutoBooks.Codex.Henkin1950
