import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentPruneIntersection
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentGeneralPatternFlexControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentGeneralPatternDispatchControls

/-!
# Pruning `F x y ≐ G y z` to the intersection `{y}`

The outer context is `T : U0, F : (a b : T) → U0`; the newest metavariable is
`G : (a b : T) → U0`. Under rigid `x y z : T`, the equation `G y z ≐ F x y` forces every
solution, in every future context, to give `G` a value that ignores its second argument: the
arguments of `G` are `y z`, those of `F` are `x y`, and the intersection is `{y}`.

The restriction keeps the first binder of `G` and introduces `H : T → U0`. The actual pruning
answer is `G := λ a b. H a`; `F` and `T` stay open. Every solution of the store factors through
it. `H`'s type does not mention `F`, so the actual exchange then makes `F` the newest
metavariable, ready to be solved by the pattern step (`F := λ a b. H b`).

A restriction that does not cover the intersection is not accepted: keeping no binder of `G`
leaves the covering obligation for `y` unprovable, and it is refuted below.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentPrune.Controls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentPiShape ContextualDependentPiSpine ContextualDependentScope
open ContextualDependentReductionReflection TypedEquality.StrongNormalization
open ContextualDependentGeneralPattern ContextualDependentGeneralPattern.Controls

/-- `T : U0, F : (a b : T) → U0`. -/
abbrev outerContext := extend types outerWhole
abbrev newerType : TypeOver outerContext := outerWhole.reindex (projectionHom types outerWhole)

/-- `G : (a b : T) → U0` over `T, F`. -/
def newerSpine : Spine newerType := Controls.spine.reindex (projectionHom types outerWhole)

/-- `T, F, G`. -/
abbrev metas := extend outerContext newerType

/-! ## The local telescope `x y z : T` -/

def firstLocal : TypeOver metas := ⟨.var 2, .sort Tower.zero, .sort _, .var 2⟩
abbrev afterFirst := extend metas firstLocal
def secondLocal : TypeOver afterFirst := ⟨.var 3, .sort Tower.zero, .sort _, .var 3⟩
abbrev afterSecond := extend afterFirst secondLocal
def thirdLocal : TypeOver afterSecond := ⟨.var 4, .sort Tower.zero, .sort _, .var 4⟩
abbrev afterThird := extend afterSecond thirdLocal

def thirdWhole : TypeOver afterSecond :=
  ⟨.pi thirdLocal.code (universeAt afterThird).code, .sort (.max Tower.zero (.succ Tower.zero)), .sort _,
    .piForm thirdLocal.formed thirdLocal.universeWitness (universeAt afterThird).formed
      (universeAt afterThird).universeWitness (.sorts _ _)⟩
def secondWhole : TypeOver afterFirst :=
  ⟨.pi secondLocal.code thirdWhole.code, .sort (.max Tower.zero (.max Tower.zero (.succ Tower.zero))), .sort _,
    .piForm secondLocal.formed secondLocal.universeWitness thirdWhole.formed thirdWhole.universeWitness (.sorts _ _)⟩
def firstWhole : TypeOver metas :=
  ⟨.pi firstLocal.code secondWhole.code,
    .sort (.max Tower.zero (.max Tower.zero (.max Tower.zero (.succ Tower.zero)))), .sort _,
    .piForm firstLocal.formed firstLocal.universeWitness secondWhole.formed secondWhole.universeWitness (.sorts _ _)⟩

def localScope : Spine firstWhole :=
  .bind ⟨firstLocal, secondWhole, firstWhole, rfl⟩
    (.bind ⟨secondLocal, thirdWhole, secondWhole, rfl⟩
      (.bind ⟨thirdLocal, universeAt afterThird, thirdWhole, rfl⟩ (.stop (universeAt afterThird))))

/-! ## The two applications -/

/-- `G y z`. -/
def newerPattern : Pattern newerSpine localScope where
  args := fun position => match position with
    | .inl _ => .inr (.inl ())
    | .inr (.inl _) => .inr (.inr (.inl ()))
    | .inr (.inr impossible) => impossible.elim
  injective := by
    intro one two same
    rcases one with ⟨⟩ | ⟨⟩ | impossible <;> rcases two with ⟨⟩ | ⟨⟩ | other
    all_goals first | rfl | cases same | exact impossible.elim | exact other.elim
  compatible := by unfold CtxRen; decide +kernel

theorem newer_application_code :
    newerPattern.application.code = (.app (.app (.var 3) (.var 1)) (.var 0) : Tower.Tm 6) := by rfl'

/-- The older metavariable `F`, in `T, F, G`. -/
def olderFunction : Term metas (newerType.reindex (projectionHom outerContext newerType)) :=
  (newest types outerWhole).reindex (projectionHom outerContext newerType)

/-- `F x y`. -/
def olderApplication : Application localScope where
  functionType := newerType.reindex (projectionHom outerContext newerType)
  function := olderFunction
  spine := (Controls.spine.reindex (projectionHom types outerWhole)).reindex (projectionHom outerContext newerType)
  args := fun position => match position with
    | .inl _ => .inl ()
    | .inr (.inl _) => .inr (.inl ())
    | .inr (.inr impossible) => impossible.elim
  injective := by
    intro one two same
    rcases one with ⟨⟩ | ⟨⟩ | impossible <;> rcases two with ⟨⟩ | ⟨⟩ | other
    all_goals first | rfl | cases same | exact impossible.elim | exact other.elim
  compatible := by unfold CtxRen; decide +kernel

theorem older_application_code :
    olderApplication.term.code = (.app (.app (.var 4) (.var 2)) (.var 1) : Tower.Tm 6) := by rfl'

theorem sameType : olderApplication.spine.result.reindex olderApplication.map.hom =
    (lifted newerSpine).result.reindex newerPattern.map.hom :=
  TypeOver.ext (by rfl') (by rfl')

/-- The scoped equation `G y z ≐ F x y` under `x y z : T`. -/
def flexFlex : Scoped metas := newerPattern.constraint (olderApplication.term.cast sameType)

/-! ## The restriction to `{y}` -/

/-- `H : T → U0` over `T, F`; it does not mention `F`. -/
abbrev prunedType : TypeOver outerContext :=
  ContextualDependentParameterExchange.second outerWhole FlexControls.familyWhole

def unarySpine : Spine FlexControls.familyWhole :=
  .bind ⟨element, universeAt oneArgument, FlexControls.familyWhole, rfl⟩ (.stop (universeAt oneArgument))

def prunedSpine : Spine prunedType := unarySpine.reindex (projectionHom types outerWhole)

/-- `H`'s only binder is `G`'s first binder. -/
def restriction : Restriction newerSpine prunedSpine where
  keep := fun position => match position with
    | .inl _ => .inl ()
    | .inr impossible => impossible.elim
  injective := by
    intro one two _
    rcases one with ⟨⟩ | impossible <;> rcases two with ⟨⟩ | other
    all_goals first | rfl | exact impossible.elim | exact other.elim
  compatible := by unfold CtxRen; decide +kernel
  resultCode := by rfl'
  resultLevel := by rfl'

/-- The intersection `{y}` is covered: `G`'s first argument `y` is an argument of `F`; its second
argument `z` is not. -/
theorem covers : ∀ position : newerSpine.Local,
    (∃ other, olderApplication.args other = newerPattern.args position) →
      ∃ chosen, restriction.keep chosen = position := by
  intro position found
  rcases position with ⟨⟩ | ⟨⟩ | impossible
  · exact ⟨.inl (), rfl⟩
  · obtain ⟨other, same⟩ := found
    rcases other with ⟨⟩ | ⟨⟩ | impossible
    all_goals first | cases same | exact impossible.elim
  · exact impossible.elim

/-- Negative control: no restriction of `G` that drops its first binder covers the intersection. -/
theorem first_binder_forced (keep : prunedSpine.Local → newerSpine.Local)
    (avoids : ∀ chosen, keep chosen ≠ .inl ()) :
    ¬ ∀ position : newerSpine.Local,
      (∃ other, olderApplication.args other = newerPattern.args position) → ∃ chosen, keep chosen = position := by
  intro covering
  obtain ⟨chosen, hit⟩ := covering (.inl ()) ⟨.inr (.inl ()), rfl⟩
  exact avoids chosen hit

/-! ## The actual pruning update -/

noncomputable def store : EquationStore (TotalTerm metas) := [(flexFlex.close setting.levels).equation]

theorem store_holds {Δ : Context Tower.rules} (solution : Δ ⟶ metas)
    (solved : (frames setting.levels).Models solution store) : flexFlex.Holds solution :=
  (Scoped.close_models_iff setting.levels flexFlex solution).mp solved

noncomputable def pruned : ContextualDependentUpdate.Update setting.levels store :=
  pruneFlexFlex (S := setting) ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    DispatchControls.tower_normalizes TowerModel.facts TowerModel.algebra
    ContextualDependentNormalCheckingTower.head_typing_unique TowerModel.roots TowerModel.heads
    ContextualDependentInversion.Controls.declarations_formed newerPattern olderApplication sameType
    restriction covers store store_holds

/-- `H` replaces `G`: the context is `T, F, H`. -/
theorem pruned_target : pruned.target = extend outerContext prunedType := rfl

/-- **The computed answer** `G := λ a b. H a`. -/
theorem answer_code : restriction.answer.substitution 0 = (.lam (.lam (.app (.var 2) (.var 1))) : Tower.Tm 3) := by
  rfl'

theorem older_open : restriction.answer.substitution 1 = (.var 1 : Tower.Tm 3) := rfl
theorem type_open : restriction.answer.substitution 2 = (.var 2 : Tower.Tm 3) := rfl

/-- **No solution is lost**: every solution of the store, into every future context, factors
through the pruning answer on all annotated terms. -/
theorem every_solution_factors {Δ : Context Tower.rules} (solution : Δ ⟶ metas)
    (solved : (frames setting.levels).Models solution store) :
    ∃ residual : Δ ⟶ extend outerContext prunedType,
      (frames setting.levels).Models residual pruned.remaining ∧
        ∀ term : TotalTerm metas, (frames setting.levels).E (term.reindex solution)
          (term.reindex (residual ≫ restriction.answer)) :=
  pruned.complete Δ solution solved

/-- The store is kept: its equation is instantiated, not discarded. -/
theorem remaining_length : pruned.remaining.length = 1 := rfl

/-! ## Exchange: `F` becomes the newest metavariable -/

noncomputable def exchanged : ContextualDependentUpdate.Update setting.levels pruned.remaining :=
  exchange setting.levels outerWhole FlexControls.familyWhole pruned.remaining

/-- After the exchange the context is `T, H, F`. -/
theorem exchanged_target :
    exchanged.target = ContextualDependentParameterExchange.context FlexControls.familyWhole outerWhole := rfl

/-- The composite of pruning and exchange still loses no solution of the original store. -/
theorem composite_factors {Δ : Context Tower.rules} (solution : Δ ⟶ metas)
    (solved : (frames setting.levels).Models solution store) :
    ∃ residual : Δ ⟶ (pruned.then exchanged).target,
      (frames setting.levels).Models residual (pruned.then exchanged).remaining ∧
        ∀ term : TotalTerm metas, (frames setting.levels).E (term.reindex solution)
          (term.reindex (residual ≫ (pruned.then exchanged).answer)) :=
  (pruned.then exchanged).complete Δ solution solved

end ContextualDependentPrune.Controls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
