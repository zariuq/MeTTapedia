import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentStrengthening
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSelectionCompatibility
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentPruningControls
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerDecidability
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.TypedContextualControls

/-!
# Strengthening dependent certificates and the injection boundary

The actual selector drops an unused declaration while retaining A and x:A.
A checking certificate in the original context supplies the recovered
body's typing. A nonlinear root rule reflects injections but not arbitrary
renamings, showing why the weaker root contract is useful.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentStrengthening.Controls

open CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open TypedEquality.StrongNormalization
open ContextualDependentReductionReflection

abbrev setting := ContextualDependentInversion.Controls.setting
abbrev large := ContextualDependentInversion.Controls.large

instance : DecidableRel Tower.rules.headEq := fun left right => LevelTower.instDecidableHeadEq left right
instance : DecidableRel Tower.rules.cumulative := fun left right => LevelTower.instDecidableCumulative left right
instance (head : Tower.Head) : Decidable (Tower.rules.isUniverse head) :=
  inferInstanceAs (Decidable (Tower.IsUniverse head))

def selected := (ContextualDependentPruning.Controls.run 16 ContextualDependentPruning.Controls.requested).get
  (by decide +kernel)

theorem selected_arity : selected.source.arity = 2 := by rfl'
def typeIndex : Fin selected.source.arity := ⟨1, by rw [selected_arity]; decide⟩
def valueIndex : Fin selected.source.arity := ⟨0, by rw [selected_arity]; decide⟩

theorem selected_compatible : CtxRen selected.source.raw large.raw selected.inclusion.forward :=
  ContextualDependentSelectionCompatibility.select_compatible (S := setting)
    TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer 16 large.raw large.formed
    ContextualDependentPruning.Controls.requested selected (by rfl')

def expected : TypeOver selected.source := ⟨.var typeIndex, .sort Tower.zero, .sort _, .var typeIndex⟩

theorem targetCertificate : CheckingAlgorithm Tower.rules .check large.raw (.var 0)
    (Presentation.rename selected.inclusion.forward expected.code) :=
  ((ExecutableChecking.check Tower.rules ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer
    16 large.raw (.var 0) (Presentation.rename selected.inclusion.forward expected.code)).get (by decide +kernel)).down

def recovered := recover (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
  (RootReflectsInjections.of_all RootReflectsRename.empty)
  ContextualDependentInversion.Controls.declarations_formed selected.inclusion selected_compatible expected
  (.var 0) targetCertificate

theorem computed_dependent_body : recovered.map (fun result => result.body.code) = some (.var valueIndex) := by rfl'

theorem source_typing_reconstructed : ∃ body : Term selected.source expected, body.code = .var valueIndex := by
  obtain ⟨result, _, code⟩ := Option.map_eq_some_iff.mp computed_dependent_body
  exact ⟨result.body, code⟩

theorem dependency_not_silently_dropped :
    ContextualDependentPruning.Controls.run 16 (fun index => decide (index.val = 0)) = none :=
  ContextualDependentPruning.Controls.dropping_the_required_type_fails

namespace Eta

open Examples.TypedContextualControls

def sourceFunction := newest closed functionType
def sourceEta : Term functionContext (functionType.reindex (projectionHom closed functionType)) :=
  ⟨.lam (.app (.var 1) (.var 0)), .lamIntro (function_formed _) (.sort _)
    (Derivable.appElim (A := sort0) (B := sort0) (.var 1) (.var 0))⟩

theorem reflected_function_eta : Equal Tower.rules functionContext.raw sourceFunction.code sourceEta.code functionCode :=
  equal_reflects (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    (RootReflectsInjections.of_all RootReflectsRename.empty) TowerModel.complete
    (Fin.succ_injective _) (CtxRen.wk functionContext.raw familyType.code)
    functionContext.formed familyContext.formed sourceFunction.typed sourceEta.typed function_eta

theorem reflected_endpoints_have_distinct_codes : sourceFunction.code ≠ sourceEta.code := by decide +kernel

end Eta

namespace NonlinearRoot

def duplicate {n : Nat} (value : Tm Tower.Head n) : Tm Tower.Head n :=
  .app (.app (.const .anonymous) value) value

def computation : RootComputation Tower.Head where
  step := fun first second => ∃ value, first = duplicate value ∧ second = value
  rename := by
    rintro n m rho first second ⟨value, firstSame, secondSame⟩
    subst first; subst second
    exact ⟨Presentation.rename rho value, rfl, rfl⟩
  substitute := by
    rintro n m substitution first second ⟨value, firstSame, secondSame⟩
    subst first; subst second
    exact ⟨subst substitution value, rfl, rfl⟩

theorem term_rename_injective {n m : Nat} {rho : Ren n m} (injective : Function.Injective rho)
    {first second : Tm Tower.Head n} (same : Presentation.rename rho first = Presentation.rename rho second) :
    first = second := by
  have one := ContextualDependentInversion.invert_rename first rho _
    (ContextualDependentInversion.lookup_exact rho injective)
  have two := ContextualDependentInversion.invert_rename second rho _
    (ContextualDependentInversion.lookup_exact rho injective)
  rw [same] at one
  exact Option.some.inj (one.symm.trans two)

theorem reflects_injections : RootReflectsInjections computation := by
  rintro n m rho injective term result ⟨value, image, rfl⟩
  obtain ⟨function, argument, rfl, functionImage, argumentImage⟩ :=
    TypedEquality.StrongNormalization.rename_eq_app image
  obtain ⟨constant, first, rfl, constantImage, firstImage⟩ :=
    TypedEquality.StrongNormalization.rename_eq_app functionImage
  obtain rfl := TypedEquality.StrongNormalization.rename_eq_const constantImage
  have same := term_rename_injective injective (firstImage.trans argumentImage.symm)
  subst first
  exact ⟨argument, ⟨argument, rfl, rfl⟩, argumentImage.symm⟩

def collapse : Ren 2 1 := fun _ => 0
def distinct : Tower.Tm 2 := .app (.app (.const .anonymous) (.var 0)) (.var 1)

theorem collapse_preserves_declarations :
    CtxRen ContextualDependentInversion.Controls.withExtra.raw
      ContextualDependentInversion.Controls.typeContext.raw collapse := by
  intro index
  fin_cases index <;> rfl

theorem not_all_renamings : ¬ RootReflectsRename computation := by
  intro reflects
  have reduced : computation.step (Presentation.rename collapse distinct) (.var 0) := ⟨.var 0, rfl, rfl⟩
  obtain ⟨result, ⟨value, image, _⟩, _⟩ := reflects collapse reduced
  have outer := Tm.app.inj image
  have inner := Tm.app.inj outer.1
  have same : (Tm.var (0 : Fin 2) : Tower.Tm 2) = .var 1 := inner.2.trans outer.2.symm
  exact (by decide : (0 : Fin 2) ≠ 1) (Tm.var.inj same)

theorem actual_contraction : computation.step (duplicate (.head .legacyGround : Tower.Tm 0)) (.head .legacyGround) :=
  ⟨_, rfl, rfl⟩

end NonlinearRoot

theorem collapsing_variables_can_create_neutral_equality :
    Algorithm Tower.rules (.neutral ContextualDependentInversion.Controls.typeContext.raw
      (Presentation.rename NonlinearRoot.collapse (.var 0))
      (Presentation.rename NonlinearRoot.collapse (.var 1))
      (Ctx.lookup ContextualDependentInversion.Controls.typeContext.raw 0)) ∧
    ¬ ∃ type, Algorithm Tower.rules (.neutral ContextualDependentInversion.Controls.withExtra.raw
      (.var 0) (.var 1) type) := by
  refine ⟨.var 0, ?_⟩
  rintro ⟨type, impossible⟩
  cases impossible

end ContextualDependentStrengthening.Controls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
