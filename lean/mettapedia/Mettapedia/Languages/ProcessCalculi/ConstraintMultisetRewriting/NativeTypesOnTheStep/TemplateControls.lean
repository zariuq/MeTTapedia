import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.TemplateConversion
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.ComputableControls

/-!
# Where conversion at the type is not enough: an application learned by matching

Over the frame `X : U₁, f : X, a : U₀`, the firing `gapFiring` tells `X ≐ Π (y : U₀). U₀` and makes the
row `f a` at `U₀`.

* **The code has no typing in its frame** (`gap_no_frame_typing`): `f` has the variable type `X`, and a
  variable type is no function type. So it converts along no substitution (`gap_not_convertsAlong`),
  and the converting step refuses the firing for every settler (`gap_converting_refused`).
* **It is typed after the match** (`gap_typedAfterMatch`), through its template `y z` over
  `y : Π (x : U₀). U₀, z : U₀` (`gapTemplate`), whose rule holds along the initial solution
  `X ↦ Π (y : U₀). U₀, f ↦ f', a ↦ a'` (`gapAnswer_initial`, `gapTemplate_holds`).
* **The templating step admits it** with the semantic settler (`gap_templated`); the converting step
  and the present step refuse it (`gap_separation`).
* **Control**: the templating step refuses the η firing for every settler (`eta_templating_refused`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace NativeTypesOnTheStep.TemplateControls

open _root_.CategoryTheory Opposite Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta
open Interface.DependentFull Interface.DependentFull.Controls
open UnificationWithLevels (Agree InitialSolution)
open NativeTypesOnTheStep.ComputableControls (bigUniverse)

/-! ## The frame `X : U₁, f : X, a : U₀` -/

/-- `Π (y : U₀). U₀`. -/
def smallArrow {n : Nat} : Tower.Tm n := .pi (.head (.sort Tower.zero)) (.head (.sort Tower.zero))

theorem collapseOne :
    Tower.rules.cumulative (.sort (.max (.succ Tower.zero) (.succ Tower.zero))) (.sort (.succ Tower.zero)) := by
  change LevelTower.Cumulative (.sort (.max (.succ Tower.zero) (.succ Tower.zero))) (.sort (.succ Tower.zero))
  intro valuation
  simp [LevelExpr.eval]

/-- `Π (y : U₀). U₀ : U₁`. -/
theorem smallArrow_typed {n : Nat} (Γ : Tower.Ctx n) :
    Typed Tower.rules Γ smallArrow (.head (.sort (.succ Tower.zero))) :=
  .cumul (.piForm (.headType (.sort _)) (.sort _) (.headType (.sort _)) (.sort _) (.sorts _ _)) collapseOne

/-- `X`, as the type of `f`. -/
def xBig : TypeOver (extend (empty Tower.rules) (bigUniverse _)) :=
  ⟨.var 0, .sort (.succ Tower.zero), .sort _, Derivable.var 0⟩

/-- **The frame `X : U₁, f : X, a : U₀`.** -/
abbrev gapFrame : Context Tower.rules :=
  extend (extend (extend (empty Tower.rules) (bigUniverse _)) xBig) (smallUniverse _)

/-- **The made row**: `f a` at `U₀`. -/
def gapRow : Make gapFrame := ⟨smallUniverse _, .app (.var 1) (.var 0)⟩

/-- `X`, as a term of `U₁`. -/
def xTerm : TotalTerm gapFrame := ⟨bigUniverse _, ⟨.var 2, Derivable.var 2⟩⟩

/-- `Π (y : U₀). U₀`, as a term of `U₁`. -/
def arrowTerm : TotalTerm gapFrame := ⟨bigUniverse _, ⟨smallArrow, smallArrow_typed _⟩⟩

/-- Make the helpers `X : U₁`, `f : X`, `a : U₀`, tell `X ≐ Π (y : U₀). U₀`, and make `1 : f a : U₀`. -/
def gapFiring : Firing setting.levels emptyState where
  helpers := .cons (bigUniverse _) (.cons xBig (.cons (smallUniverse _) (.nil _)))
  taken := []
  read := []
  takes := []
  reads := []
  makes := [(1, gapRow)]
  tells := [(xTerm, arrowTerm)]
  guards := []
  queries := []

theorem gapFiring_information : gapFiring.information = [(xTerm, arrowTerm)] := rfl

/-! ## Conversion at the type refuses it -/

/-- **`f a` has no typing in its frame**: `f` has the variable type `X`, which is no function type. -/
theorem gap_no_frame_typing (B : TypeOver gapFrame) : ¬ FrameTypedAt gapRow B := by
  intro typed
  have formed : CtxFormed Tower.rules gapFrame.raw := gapFrame.formed
  obtain ⟨A, B', typedF, -, -⟩ := Typed.generation typed
  have le : TypeLe Tower.rules gapFrame.raw (.var 2) (.pi A B') := Typed.generation typedF
  have isPi : IsType Tower.rules gapFrame.raw (.pi A B') := Typed.isType (S := setting) typedF formed
  obtain ⟨A₀, B₀, eX, -, -⟩ := Below.pi_inv (S := setting) TowerModel.facts (TypeLe.toBelow le isPi) formed
    (IsType.refl isPi)
  have neutral : Neutral (TowerModel.roles (L := Nat)) (.var 2 : Tower.Tm 3) := .var 2
  exact (TypeEq.neutral_form (TowerModel.facts (L := Nat)) eX formed neutral
    (.inr (.inl ⟨A₀, B₀, rfl⟩))).not_former.2.1 A₀ B₀ rfl

/-- **It converts along no substitution.** -/
theorem gap_not_convertsAlong {M : Context Tower.rules} (σ : M ⟶ gapFrame) : ¬ ConvertsAlong gapRow σ :=
  fun ⟨B, typed, _⟩ => gap_no_frame_typing B typed

/-- **The converting step refuses the gap firing for every settler.** -/
theorem gap_converting_refused (settler : Settler setting.levels) :
    ¬ (convertingStep setting.levels Nat settler).Admits gapFiring := by
  intro admitted
  obtain ⟨⟨-, -, -, -, rows⟩, -⟩ := converting_admitsByConversion setting.levels settler admitted
  obtain ⟨B, typed, -⟩ := rows (1, gapRow) (List.mem_singleton_self _)
  exact gap_no_frame_typing B typed

/-! ## The initial solution -/

/-- `f' : Π (y : U₀). U₀`, over the empty frame. -/
def arrowType : TypeOver (empty Tower.rules) :=
  ⟨smallArrow, .sort (.succ Tower.zero), .sort _, smallArrow_typed _⟩

/-- **The frame of the answer**: `f' : Π (y : U₀). U₀, a' : U₀`. -/
abbrev gapTarget : Context Tower.rules := extend (extend (empty Tower.rules) arrowType) (smallUniverse _)

/-- **The answer** `X ↦ Π (y : U₀). U₀`, `f ↦ f'`, `a ↦ a'`. -/
def gapAnswer : gapTarget ⟶ gapFrame :=
  pair (pair (pair (toEmpty gapTarget) ⟨smallArrow, smallArrow_typed _⟩) ⟨.var 1, Derivable.var 1⟩)
    ⟨.var 0, Derivable.var 0⟩

theorem gapAnswer_solves : (frames setting.levels).Models gapAnswer gapFiring.information := by
  intro e member
  rw [gapFiring_information] at member
  obtain rfl := List.mem_singleton.mp member
  show (frames setting.levels).E (xTerm.reindex gapAnswer) (arrowTerm.reindex gapAnswer)
  rw [show xTerm.reindex gapAnswer = arrowTerm.reindex gapAnswer from totalTerm_ext rfl rfl]
  exact ((frames setting.levels).equivalence _).refl _

/-- **The answer is principal**: every solution sends `X` to a type equal to `Π (y : U₀). U₀`, so `f` to a
function, and agrees with its factor `f' ↦ f, a' ↦ a`. -/
theorem gapAnswer_principal : (frames setting.levels).Principal gapFiring.information gapAnswer := by
  refine ⟨gapAnswer_solves, fun Θ (τ : Θ ⟶ gapFrame) solved => ?_⟩
  obtain ⟨-, eTerms⟩ := tell_heterogeneous setting.levels gapFiring solved (List.mem_singleton_self _)
  have eX : Equal Tower.rules Θ.raw (τ.substitution 2) smallArrow (.head (.sort (.succ Tower.zero))) := eTerms
  have fTyped : Typed Tower.rules Θ.raw (τ.substitution 1) smallArrow :=
    Derivable.conv (τ.typed 1) eX (.sort _)
  let g : Θ ⟶ gapTarget := pair (pair (toEmpty Θ) ⟨τ.substitution 1, fTyped⟩) ⟨τ.substitution 0, τ.typed 0⟩
  refine ⟨g, ?_⟩
  have same : homTypedEquality Tower.rules τ (g ≫ gapAnswer) := by
    refine ⟨τ.typed, fun index => ?_⟩
    fin_cases index
    · exact .refl (τ.typed 0)
    · exact .refl (τ.typed 1)
    · exact eX
  exact fun t => act_equal_of_substEq setting.levels same t

theorem gapAnswer_cover : VariableCover gapAnswer := by decide +kernel

/-- **The answer is the initial solution.** -/
theorem gapAnswer_initial : InitialSolution (frames setting.levels) gapFiring.information gapAnswer :=
  initial_of_cover setting.levels gapAnswer_principal gapAnswer_cover

/-! ## The template rule admits it -/

theorem u0_below_self {n : Nat} (Γ : Tower.Ctx n) : Below Tower.rules Γ Eta.u0 Eta.u0 :=
  below_refl_of_isType (rules := Tower.rules) (Γ := Γ) (A := Eta.u0)
    ⟨.sort (.succ Tower.zero), LevelTower.IsUniverse.sort _, Derivable.headType (LevelTower.HeadTyping.sort _)⟩

theorem arrow_below_self {n : Nat} (Γ : Tower.Ctx n) : Below Tower.rules Γ smallArrow smallArrow :=
  below_refl_of_isType ⟨_, LevelTower.IsUniverse.sort _, smallArrow_typed _⟩

/-- **The template of the gap row**: `y z` over `y : Π (x : U₀). U₀, z : U₀`, at `U₀`, filled by `f`
and `a`. -/
def gapTemplate : Template gapRow where
  frame := gapTarget
  code := .app (.var 1) (.var 0)
  type := smallUniverse _
  fill := Fin.castSucc
  typed := .appElim (A := Eta.u0) (B := Eta.u0) (.var 1) (.var 0)
  filled := rfl

/-- **The template rule holds along the answer**: `X ↦ Π (y : U₀). U₀` makes `f`'s declared type the
template's function type. -/
theorem gapTemplate_holds : gapTemplate.Holds gapAnswer := by
  refine ⟨fun j => ?_, u0_below_self _⟩
  fin_cases j
  · exact u0_below_self _
  · exact arrow_below_self _

/-- **The gap row is typed after the match**, by the soundness of the template rule. -/
theorem gap_typedAfterMatch : TypedAfterMatch setting.levels gapFiring.information gapRow :=
  typedAfterMatch_of_template setting.levels gapAnswer_principal gapTemplate gapTemplate_holds

/-- **The templating step with the semantic settler admits the gap firing.** -/
theorem gap_templated :
    (templatingStep setting.levels Nat (Settler.ideal setting.levels)).Admits gapFiring := by
  refine ideal_templating_admits setting.levels ⟨List.nodup_nil, List.nodup_singleton _, rfl, rfl⟩
    (fun m member => ?_)
    ((DependentFull.enabled_iff gapFiring).mpr ⟨fun _ member => absurd member List.not_mem_nil,
      fun _ member => absurd member List.not_mem_nil, fun _ member => absurd member List.not_mem_nil,
      fun o made present => ?_⟩)
    (fun _ _ _ => ⟨fun _ member => absurd member List.not_mem_nil, fun _ member => absurd member List.not_mem_nil⟩)
    gapAnswer_initial
  · obtain rfl := List.mem_singleton.mp member
    exact ⟨gapTemplate,
      (template_iff_of_principal setting.levels gapAnswer_principal gapTemplate).mp gapTemplate_holds⟩
  · have one : o = 1 := List.mem_singleton.mp made
    have zero : o = 0 := Finset.mem_singleton.mp present
    exact absurd (one.symm.trans zero) (by decide)

/-- **The separation**: the templating step admits the gap firing; the converting step, for every
settler, and the present step refuse it. -/
theorem gap_separation :
    (templatingStep setting.levels Nat (Settler.ideal setting.levels)).Admits gapFiring ∧
      (∀ settler : Settler setting.levels, ¬ (convertingStep setting.levels Nat settler).Admits gapFiring) ∧
      ¬ (step setting.levels Nat).Admits gapFiring :=
  ⟨gap_templated, gap_converting_refused,
    fun admitted => gap_no_frame_typing _ (admitted.1.2.2.2.2 (1, gapRow) (List.mem_singleton_self _))⟩

/-- **Control: the templating step refuses the η firing for every settler.** -/
theorem eta_templating_refused (settler : Settler setting.levels) :
    ¬ (templatingStep setting.levels Nat settler).Admits Eta.etaFiring :=
  fun admitted => Eta.eta_gap.2
    (templating_typedAfterMatch setting.levels settler admitted (1, Eta.etaRow) (List.mem_singleton_self _))

end NativeTypesOnTheStep.TemplateControls

#print axioms NativeTypesOnTheStep.TemplateControls.gap_no_frame_typing
#print axioms NativeTypesOnTheStep.TemplateControls.gap_not_convertsAlong
#print axioms NativeTypesOnTheStep.TemplateControls.gap_converting_refused
#print axioms NativeTypesOnTheStep.TemplateControls.gapAnswer_principal
#print axioms NativeTypesOnTheStep.TemplateControls.gapAnswer_cover
#print axioms NativeTypesOnTheStep.TemplateControls.gapAnswer_initial
#print axioms NativeTypesOnTheStep.TemplateControls.gapTemplate_holds
#print axioms NativeTypesOnTheStep.TemplateControls.gap_typedAfterMatch
#print axioms NativeTypesOnTheStep.TemplateControls.gap_templated
#print axioms NativeTypesOnTheStep.TemplateControls.gap_separation
#print axioms NativeTypesOnTheStep.TemplateControls.eta_templating_refused

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
