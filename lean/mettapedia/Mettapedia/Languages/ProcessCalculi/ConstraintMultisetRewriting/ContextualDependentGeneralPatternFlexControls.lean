import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentGeneralPatternControls

/-!
# A flex-flex pattern solved by its newer metavariable

The outer context is `T : U0, F : T → U0`; the newer metavariable is
`G : (a b : T) → U0`. Under rigid `x y : T`, the equation `F x ≐ G x y`
oriented at `G` is a pattern whose right side `F x` uses only arguments of
`G` and the older metavariable `F`. Its principal answer is
`G := λ a b. F a`, with `F` left open. Every solution factors through it; up
to naming the shared function, this is the pruned pair
`F := λ a. H a, G := λ a b. H a`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentGeneralPattern.FlexControls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentPiShape ContextualDependentPiSpine ContextualDependentScope
open ContextualDependentReductionReflection TypedEquality.StrongNormalization
open ContextualDependentGeneralPattern.Controls

def familyWhole : TypeOver types :=
  ⟨.pi element.code (universeAt oneArgument).code, .sort (.max Tower.zero (.succ Tower.zero)), .sort _,
    .piForm element.formed element.universeWitness (universeAt oneArgument).formed
      (universeAt oneArgument).universeWitness (.sorts _ _)⟩

/-- The outer context `T : U0, F : T → U0`. -/
abbrev outerContext := extend types familyWhole

/-- `G : (a b : T) → U0` over `T, F`. -/
def newerSpine := Controls.spine.reindex (projectionHom types familyWhole)

abbrev newerScope := lifted newerSpine

def newer : Pattern newerSpine newerScope where
  args := fun position => position
  injective := fun _ _ same => same
  compatible := by unfold CtxRen; decide +kernel

/-- The right side `F x` in `T, F, G, x, y`. -/
def olderApplication : Term newerScope.target (newerScope.result.reindex newer.map.hom) :=
  ⟨(.app (.var 3) (.var 1) : Tower.Tm 5),
    .appElim (A := (.var 4 : Tower.Tm 5)) (B := (.head (.sort Tower.zero) : Tower.Tm 6))
      (.var (3 : Fin 5)) (.var (1 : Fin 5))⟩

/-- The body `F a` over `T, F, a, b`. -/
def olderBody : Term newerSpine.target newerSpine.result :=
  ⟨(.app (.var 2) (.var 1) : Tower.Tm 4),
    .appElim (A := (.var 3 : Tower.Tm 4)) (B := (.head (.sort Tower.zero) : Tower.Tm 5))
      (.var (2 : Fin 4)) (.var (1 : Fin 4))⟩

theorem older_is_image : olderApplication.code = Presentation.rename newer.bodyRen olderBody.code := by rfl'

theorem newer_application_code : newer.application.code = (.app (.app (.var 2) (.var 1)) (.var 0) : Tower.Tm 5) := by
  rfl'

def result := newer.replace (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
  (RootReflectsInjections.of_all RootReflectsRename.empty) TowerModel.complete olderBody olderApplication older_is_image

theorem computed_answer : result.update.answer.substitution 0 = (.lam (.lam (.app (.var 2) (.var 1))) : Tower.Tm 2) := by
  rfl'

theorem older_metavariable_open : result.update.answer.substitution 1 = (.var 0 : Tower.Tm 2) := by rfl'

theorem type_open : result.update.answer.substitution 2 = (.var 1 : Tower.Tm 2) := by rfl'

theorem finished : result.update.remaining = [] := rfl

theorem principal :
    ContextualDependentScopedDispatch.Holds [newer.constraint olderApplication] result.update.answer ∧
      ∀ (Δ : Context Tower.rules) (solution : Δ ⟶ extend outerContext (outerWhole.reindex (projectionHom types familyWhole))),
        ContextualDependentScopedDispatch.Holds [newer.constraint olderApplication] solution →
          ∃ residual : Δ ⟶ result.update.target,
            ∀ term : TotalTerm (extend outerContext (outerWhole.reindex (projectionHom types familyWhole))),
              (frames setting.levels).E (term.reindex solution) (term.reindex (residual ≫ result.update.answer)) :=
  result.completed finished

end ContextualDependentGeneralPattern.FlexControls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
