import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentGeneralPatternDispatch
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentGeneralPatternControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentNormalizationTower
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentInversionControls

/-!
# The general pattern step on concrete equations

The actual step solves `F x y ≐ Id T y x` by inversion and checking. For
`F : T → T` under `x y : T`, the equation `F x ≐ y` is refuted at every
future context, and the actual step returns that refutation. A repeated
argument `F x x` has no injective argument assignment, so it is not a
pattern. A zero checker budget on a solvable pattern equation stays
pending; it is not refuted. The tower supplies the normal-form theorem used
by the refutation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentGeneralPattern.DispatchControls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentPiShape ContextualDependentPiSpine ContextualDependentScope
open ContextualDependentReductionReflection TypedEquality.StrongNormalization
open ContextualDependentGeneralPattern.Controls

theorem tower_normalizes {Θ : Context Tower.rules} {type : TypeOver Θ} (term : Term Θ type) :
    ∃ code : Tower.Tm Θ.arity, ContextualDependentNormalChecking.Normal (S := setting) code ∧
      Equal Tower.rules Θ.raw term.code code type.code := by
  obtain ⟨fuel, normal⟩ :=
    ContextualDependentNormalizationTower.term_eventually_normal (fun _ => (0 : Nat)) (⟨type, term⟩ : TotalTerm Θ)
  have same := ContextualDependentNormalization.termAt_equivalent (S := setting) (fun _ => none)
    TowerModel.facts TowerModel.roots TowerModel.heads fuel (⟨type, term⟩ : TotalTerm Θ)
  exact ⟨_, (normal fuel le_rfl).2, same.2⟩

def certifyNormal {n : Nat} (term : Tower.Tm n) :
    Option (PLift (ContextualDependentNormalChecking.Normal (S := setting) term)) :=
  if stopped : ExecutableReduction.step Tower.rules (fun _ => none) term = none then
    some ⟨ContextualDependentNormalSupport.Controls.stopped_normal term stopped⟩
  else none

def run (fuel : Nat) {Γ : Context Tower.rules} {type : TypeOver Γ} {spine : Spine type}
    {scopeType : TypeOver (extend Γ type)} {scope : Spine scopeType} (pattern : Pattern spine scope)
    (right : Term scope.target ((lifted spine).result.reindex pattern.map.hom)) :=
  Pattern.step (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentInversion.Controls.declarations_formed (RootReflectsInjections.of_all RootReflectsRename.empty)
    TowerModel.complete ContextualDependentPiSpine.Controls.rigid tower_normalizes certifyNormal
    ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer fuel pattern right

def tag {Γ : Context Tower.rules} {type : TypeOver Γ} {spine : Spine type}
    {scopeType : TypeOver (extend Γ type)} {scope : Spine scopeType} {pattern : Pattern spine scope}
    {right : Term scope.target ((lifted spine).result.reindex pattern.map.hom)} :
    Pattern.Outcome (S := setting) pattern right → Nat
  | .solved _ _ => 0
  | .refuted _ => 1
  | .pending => 2

/-! ## The actual step solves the swapped equation. -/

theorem swapped_step_solves : tag (run 16 straight swapped) = 0 := by rfl'

theorem swapped_zero_budget_pending : tag (run 0 straight swapped) = 2 := by rfl'

/-! ## `F x ≐ y` is refuted. -/

namespace Outside

def unaryWhole : TypeOver types :=
  ⟨.pi element.code elementOne.code, .sort (.max Tower.zero Tower.zero), .sort _,
    .piForm element.formed element.universeWitness elementOne.formed elementOne.universeWitness (.sorts _ _)⟩
def unary : Shape types := ⟨element, elementOne, unaryWhole, rfl⟩

/-- `F : T → T` over `T : U0`. -/
def unarySpine : Spine unaryWhole := .bind unary (.stop elementOne)

/-- The local telescope `x y : T` over `T : U0, F`. -/
def scope := Controls.spine.reindex (projectionHom types unaryWhole)

theorem local_context : scope.target.raw =
    .snoc (.snoc (.snoc (.snoc .nil (.head (.sort Tower.zero))) unaryWhole.code) (.var 1)) (.var 2) := by rfl'

def first : Pattern unarySpine scope where
  args := fun _ => Sum.inl ()
  injective := by
    intro one two _
    cases one with
    | inl u => cases two with
      | inl v => rfl
      | inr impossible => exact impossible.elim
    | inr impossible => exact impossible.elim
  compatible := by unfold CtxRen; decide +kernel

/-- The right side `y`. -/
def outsideVariable : Term scope.target ((lifted unarySpine).result.reindex first.map.hom) :=
  ⟨(.var 0 : Tower.Tm 4), .var (0 : Fin 4)⟩

def second : scope.Local := Sum.inr (Sum.inl ())

theorem second_is_y : scope.localIndex second = (0 : Fin 4) := by rfl'

theorem refuted {Δ : Context Tower.rules} (solution : Δ ⟶ extend types unaryWhole) :
    ¬ (first.constraint outsideVariable).Holds solution :=
  first.refuted (S := setting) ContextualDependentPiSpine.Controls.rigid TowerModel.complete tower_normalizes
    outsideVariable second (fun _ same => by cases same)
    (by show (0 : Fin 4) ∈ ({(0 : Fin 4)} : Finset (Fin 4)); decide)
    (fun index member => ⟨second, second_is_y.trans
      (Finset.mem_singleton.mp (show index ∈ ({(0 : Fin 4)} : Finset (Fin 4)) from member)).symm⟩)
    (ContextualDependentPiSpine.Controls.normal _ (by rfl')) solution

theorem no_closed_solution :
    ¬ ∃ solution : empty Tower.rules ⟶ extend types unaryWhole, (first.constraint outsideVariable).Holds solution :=
  fun ⟨solution, held⟩ => refuted solution held

theorem actual_step_refutes : tag (run 16 first outsideVariable) = 1 := by rfl'

/-- The right side `x` is solved instead: `F := λ a. a`. -/
def insideVariable : Term scope.target ((lifted unarySpine).result.reindex first.map.hom) :=
  ⟨(.var 1 : Tower.Tm 4), .var (1 : Fin 4)⟩

theorem actual_step_solves_inside : tag (run 16 first insideVariable) = 0 := by rfl'

end Outside

/-! ## A repeated argument is not a pattern. -/

theorem repeated_argument_not_injective :
    ¬ Function.Injective (fun _ : spine.Local => (Sum.inl () : scope.Local)) := by
  intro injective
  have same := injective (a₁ := Sum.inl ()) (a₂ := Sum.inr (Sum.inl ())) rfl
  cases same

end ContextualDependentGeneralPattern.DispatchControls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
