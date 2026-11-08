import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentGeneralPatternReplacement
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentPiSpineControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentStrengtheningControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentEqualizerControls

/-!
# General pattern replacement on concrete dependent telescopes

The outer context is `T : U0`; the metavariable is `F : (a b : T) → U0`.
Under rigid local arguments `x y : T`, the equation `F x y ≐ Id T y x`
computes the principal answer `F := λ a b. Id T b a`. The order-preserving
candidate `λ a b. Id T a b` is proved not to be a solution. A second
equation with a three-binder dependent telescope `T : U0, x : T,
p : Id T x x` keeps every dependent annotation and returns the supplied
proof argument. Neither control chooses an inhabitant of `T`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentGeneralPattern.Controls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentPiShape ContextualDependentPiSpine ContextualDependentScope
open ContextualDependentReductionReflection TypedEquality.StrongNormalization

abbrev setting := ContextualDependentPiSpine.Controls.setting
abbrev types := ContextualDependentPiSpine.Controls.types
abbrev element := ContextualDependentPiSpine.Controls.element

def universeAt (Γ : Context Tower.rules) : TypeOver Γ :=
  ⟨.head (.sort Tower.zero), .sort (.succ Tower.zero), .sort _, .headType (.sort _)⟩

abbrev oneArgument := extend types element
def elementOne : TypeOver oneArgument := ⟨.var 1, .sort Tower.zero, .sort _, .var 1⟩
abbrev twoArguments := extend oneArgument elementOne

def innerWhole : TypeOver oneArgument :=
  ⟨.pi elementOne.code (universeAt twoArguments).code, .sort (.max Tower.zero (.succ Tower.zero)), .sort _,
    .piForm elementOne.formed elementOne.universeWitness (universeAt twoArguments).formed
      (universeAt twoArguments).universeWitness (.sorts _ _)⟩
def inner : Shape oneArgument := ⟨elementOne, universeAt twoArguments, innerWhole, rfl⟩

def outerWhole : TypeOver types :=
  ⟨.pi element.code innerWhole.code, .sort (.max Tower.zero (.max Tower.zero (.succ Tower.zero))), .sort _,
    .piForm element.formed element.universeWitness innerWhole.formed innerWhole.universeWitness (.sorts _ _)⟩
def outer : Shape types := ⟨element, innerWhole, outerWhole, rfl⟩

/-- `F : (a b : T) → U0` over `T : U0`. -/
def spine : Spine outerWhole := .bind outer (.bind inner (.stop (universeAt twoArguments)))

/-- The local telescope `x y : T` over `T : U0, F`. -/
abbrev scope := lifted spine

theorem local_context : scope.target.raw =
    .snoc (.snoc (.snoc (.snoc .nil (.head (.sort Tower.zero))) outerWhole.code) (.var 1)) (.var 2) := by rfl'

def straight : Pattern spine scope where
  args := fun position => position
  injective := fun _ _ same => same
  compatible := by unfold CtxRen; decide +kernel

/-- The right side `Id T y x` in `T, F, x, y`. -/
def swapped : Term scope.target (scope.result.reindex straight.map.hom) :=
  ⟨(.id (.var 3) (.var 0) (.var 1) : Tower.Tm 4), .idForm (.var (3 : Fin 4)) (.sort _) (.var (0 : Fin 4)) (.var (1 : Fin 4))⟩

/-- The body `Id T b a` over `F`'s own telescope `T, a, b`. -/
def swappedBody : Term spine.target spine.result :=
  ⟨(.id (.var 2) (.var 0) (.var 1) : Tower.Tm 3), .idForm (.var (2 : Fin 3)) (.sort _) (.var (0 : Fin 3)) (.var (1 : Fin 3))⟩

theorem swapped_is_image : swapped.code = Presentation.rename straight.bodyRen swappedBody.code := by rfl'

theorem pattern_application_code : straight.application.code = (.app (.app (.var 2) (.var 1)) (.var 0) : Tower.Tm 4) := by rfl'

def result := straight.replace (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
  (RootReflectsInjections.of_all RootReflectsRename.empty) TowerModel.complete swappedBody swapped swapped_is_image

theorem computed_answer :
    result.update.answer.substitution 0 = (.lam (.lam (.id (.var 2) (.var 0) (.var 1))) : Tower.Tm 1) := by rfl'

theorem outer_type_retained : result.update.answer.substitution 1 = (.var 0 : Tower.Tm 1) := by rfl'

theorem finished : result.update.remaining = [] := rfl

theorem principal :
    ContextualDependentScopedDispatch.Holds [straight.constraint swapped] result.update.answer ∧
      ∀ (Δ : Context Tower.rules) (solution : Δ ⟶ extend types outerWhole),
        ContextualDependentScopedDispatch.Holds [straight.constraint swapped] solution →
          ∃ residual : Δ ⟶ result.update.target, ∀ term : TotalTerm (extend types outerWhole),
            (frames setting.levels).E (term.reindex solution) (term.reindex (residual ≫ result.update.answer)) :=
  straight.replace_principal (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    (RootReflectsInjections.of_all RootReflectsRename.empty) TowerModel.complete swappedBody swapped swapped_is_image

/-! The order-preserving candidate is not a solution. -/

def orderedBody : Term spine.target spine.result :=
  ⟨(.id (.var 2) (.var 1) (.var 0) : Tower.Tm 3), .idForm (.var (2 : Fin 3)) (.sort _) (.var (1 : Fin 3)) (.var (0 : Fin 3))⟩

def swapLast : Ren 3 3 := fun index => if index = 0 then 1 else if index = 1 then 0 else index

theorem ordered_is_swapped_rename : orderedBody.code = Presentation.rename swapLast swappedBody.code := by rfl'
theorem swapped_is_identity_rename : swappedBody.code = Presentation.rename idRen swappedBody.code := by rfl'

theorem ordered_candidate_fails :
    ¬ (straight.constraint swapped).Holds (Elimination.instantiate types (spine.abstractBody orderedBody)) := by
  intro solved
  have defined := (straight.holds_iff_definition (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
    TowerModel.algebra (RootReflectsInjections.of_all RootReflectsRename.empty) TowerModel.complete
    swappedBody swapped swapped_is_image _).mp solved
  have functions : Equal Tower.rules types.raw (spine.abstractBody orderedBody).code
      (spine.abstractBody swappedBody).code outerWhole.code := defined
  have bodies := (spine.abstractBody_equal_iff orderedBody swappedBody).mp functions
  have renamed : Equal Tower.rules spine.target.raw (Presentation.rename swapLast swappedBody.code)
      (Presentation.rename idRen swappedBody.code) spine.result.code := bodies
  have agreement := ContextualDependentNormalEqualizer.equal_agreement (S := setting)
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete spine.target.formed swappedBody.code swapLast idRen renamed
    (ContextualDependentPiSpine.Controls.normal _ (by rfl'))
  have used : (0 : Fin 3) ∈ swappedBody.code.support := by
    change (0 : Fin 3) ∈ ({2} ∪ {0} ∪ {1} : Finset (Fin 3))
    decide
  have mismatch : swapLast (0 : Fin 3) = idRen (0 : Fin 3) := agreement (0 : Fin 3) used
  exact absurd mismatch (by decide)

/-! A three-binder dependent telescope keeps every annotation. -/

namespace Dependent

abbrev full := ContextualDependentPiSpine.Controls.full
abbrev dependentScope := lifted full

def same : Pattern full dependentScope where
  args := fun position => position
  injective := fun _ _ same => same
  compatible := by unfold CtxRen; decide +kernel

/-- The right side `p` in `F, T, x, p`. -/
def proof : Term dependentScope.target (dependentScope.result.reindex same.map.hom) :=
  ⟨(.var 0 : Tower.Tm 4), .var (0 : Fin 4)⟩

theorem proof_is_image :
    proof.code = Presentation.rename same.bodyRen ContextualDependentPiSpine.Controls.suppliedProof.code := by rfl'

theorem dependent_annotation : (dependentScope.result.reindex same.map.hom).code = (.id (.var 2) (.var 1) (.var 1) : Tower.Tm 4) := by
  rfl'

def result := same.replace (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
  (RootReflectsInjections.of_all RootReflectsRename.empty) TowerModel.complete
  ContextualDependentPiSpine.Controls.suppliedProof proof proof_is_image

theorem computed_answer : result.update.answer.substitution 0 = (.lam (.lam (.lam (.var 0))) : Tower.Tm 0) := by rfl'

theorem finished : result.update.remaining = [] := rfl

theorem every_solution_factors (Δ : Context Tower.rules)
    (solution : Δ ⟶ extend (empty Tower.rules) ContextualDependentPiSpine.Controls.outerWhole)
    (solved : (same.constraint proof).Holds solution) :
    ∃ residual : Δ ⟶ empty Tower.rules, ∀ term : TotalTerm (extend (empty Tower.rules) ContextualDependentPiSpine.Controls.outerWhole),
      (frames setting.levels).E (term.reindex solution)
        (term.reindex (residual ≫ Elimination.instantiate (empty Tower.rules)
          (full.abstractBody ContextualDependentPiSpine.Controls.suppliedProof))) :=
  same.no_solution_lost (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    (RootReflectsInjections.of_all RootReflectsRename.empty) TowerModel.complete
    ContextualDependentPiSpine.Controls.suppliedProof proof proof_is_image solution solved

/-- The closed context has a closed point; the answer needs no inhabitant
of any local type. -/
theorem closed_solution_exists :
    ∃ solution : empty Tower.rules ⟶ extend (empty Tower.rules) ContextualDependentPiSpine.Controls.outerWhole,
      (same.constraint proof).Holds solution :=
  (same.fixed_point_solutions_iff (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    (RootReflectsInjections.of_all RootReflectsRename.empty) TowerModel.complete
    ContextualDependentPiSpine.Controls.suppliedProof proof proof_is_image (empty Tower.rules)).mpr
    ⟨𝟙 _⟩

end Dependent

end ContextualDependentGeneralPattern.Controls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
