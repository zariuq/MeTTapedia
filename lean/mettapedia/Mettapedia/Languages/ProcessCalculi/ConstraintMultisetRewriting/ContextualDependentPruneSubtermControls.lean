import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentPruneSubterm
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentPruneControls

/-!
# Pruning a flexible subterm: `F c x ≐ c (G x y)`

The outer context is `T : U0, F : (c : T → T) (x : T) → T`; the newest metavariable is
`G : (a b : T) → T`. Under rigid `c : T → T, x y : T`, the equation `c (G x y) ≐ F c x` has the
flexible subterm `G x y` under the rigid head `c`. Every solution, in every future context, gives
`G` a value that ignores its second argument, because `y` is not an argument of `F`. The actual
pruning answer is `G := λ a b. H a` with `H : T → T`; `F` and `T` stay open.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentPrune.SubtermControls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentPiShape ContextualDependentPiSpine ContextualDependentScope
open ContextualDependentGeneralPattern ContextualDependentGeneralPattern.Controls

/-! ## Types over `T : U0` -/

/-- `T → T`. -/
def arrow : TypeOver types :=
  ⟨.pi element.code elementOne.code, .sort (.max Tower.zero Tower.zero), .sort _,
    .piForm element.formed element.universeWitness elementOne.formed elementOne.universeWitness (.sorts _ _)⟩

def arrowSpine : Spine arrow := .bind ⟨element, elementOne, arrow, rfl⟩ (.stop elementOne)

abbrev withC := extend types arrow
def cElement : TypeOver withC := ⟨.var 1, .sort Tower.zero, .sort _, .var 1⟩
abbrev withCX := extend withC cElement
def cxElement : TypeOver withCX := ⟨.var 2, .sort Tower.zero, .sort _, .var 2⟩

def olderInner : TypeOver withC :=
  ⟨.pi cElement.code cxElement.code, .sort (.max Tower.zero Tower.zero), .sort _,
    .piForm cElement.formed cElement.universeWitness cxElement.formed cxElement.universeWitness (.sorts _ _)⟩

/-- `F : (c : T → T) (x : T) → T`. -/
def olderWhole : TypeOver types :=
  ⟨.pi arrow.code olderInner.code, .sort (.max (.max Tower.zero Tower.zero) (.max Tower.zero Tower.zero)), .sort _,
    .piForm arrow.formed arrow.universeWitness olderInner.formed olderInner.universeWitness (.sorts _ _)⟩

def olderSpine : Spine olderWhole :=
  .bind ⟨arrow, olderInner, olderWhole, rfl⟩ (.bind ⟨cElement, cxElement, olderInner, rfl⟩ (.stop cxElement))

def twoElement : TypeOver twoArguments := ⟨.var 2, .sort Tower.zero, .sort _, .var 2⟩

def newerInner : TypeOver oneArgument :=
  ⟨.pi elementOne.code twoElement.code, .sort (.max Tower.zero Tower.zero), .sort _,
    .piForm elementOne.formed elementOne.universeWitness twoElement.formed twoElement.universeWitness (.sorts _ _)⟩

/-- `(a b : T) → T`. -/
def newerWhole : TypeOver types :=
  ⟨.pi element.code newerInner.code, .sort (.max Tower.zero (.max Tower.zero Tower.zero)), .sort _,
    .piForm element.formed element.universeWitness newerInner.formed newerInner.universeWitness (.sorts _ _)⟩

def newerSpine0 : Spine newerWhole :=
  .bind ⟨element, newerInner, newerWhole, rfl⟩ (.bind ⟨elementOne, twoElement, newerInner, rfl⟩ (.stop twoElement))

/-! ## Metavariables `T, F, G` -/

abbrev outerContext := extend types olderWhole
abbrev newerType : TypeOver outerContext := newerWhole.reindex (projectionHom types olderWhole)
def newerSpine : Spine newerType := newerSpine0.reindex (projectionHom types olderWhole)
abbrev metas := extend outerContext newerType

/-! ## The local telescope `c : T → T, x y : T` -/

def metaElement : TypeOver metas := ⟨.var 2, .sort Tower.zero, .sort _, .var 2⟩
def metaElementOne : TypeOver (extend metas metaElement) := ⟨.var 3, .sort Tower.zero, .sort _, .var 3⟩
def localArrow : TypeOver metas :=
  ⟨.pi metaElement.code metaElementOne.code, .sort (.max Tower.zero Tower.zero), .sort _,
    .piForm metaElement.formed metaElement.universeWitness metaElementOne.formed metaElementOne.universeWitness (.sorts _ _)⟩
abbrev afterC := extend metas localArrow
def xType : TypeOver afterC := ⟨.var 3, .sort Tower.zero, .sort _, .var 3⟩
abbrev afterX := extend afterC xType
def yType : TypeOver afterX := ⟨.var 4, .sort Tower.zero, .sort _, .var 4⟩
abbrev afterY := extend afterX yType
def resultType : TypeOver afterY := ⟨.var 5, .sort Tower.zero, .sort _, .var 5⟩

def yWhole : TypeOver afterX :=
  ⟨.pi yType.code resultType.code, .sort (.max Tower.zero Tower.zero), .sort _,
    .piForm yType.formed yType.universeWitness resultType.formed resultType.universeWitness (.sorts _ _)⟩
def xWhole : TypeOver afterC :=
  ⟨.pi xType.code yWhole.code, .sort (.max Tower.zero (.max Tower.zero Tower.zero)), .sort _,
    .piForm xType.formed xType.universeWitness yWhole.formed yWhole.universeWitness (.sorts _ _)⟩
def cWhole : TypeOver metas :=
  ⟨.pi localArrow.code xWhole.code, .sort (.max (.max Tower.zero Tower.zero) (.max Tower.zero (.max Tower.zero Tower.zero))),
    .sort _, .piForm localArrow.formed localArrow.universeWitness xWhole.formed xWhole.universeWitness (.sorts _ _)⟩

def localScope : Spine cWhole :=
  .bind ⟨localArrow, xWhole, cWhole, rfl⟩
    (.bind ⟨xType, yWhole, xWhole, rfl⟩ (.bind ⟨yType, resultType, yWhole, rfl⟩ (.stop resultType)))

/-! ## The equation `c (G x y) ≐ F c x` -/

/-- `G x y`. -/
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

/-- `F c x`. -/
def olderApplication : Application localScope where
  functionType := (olderWhole.reindex (projectionHom types olderWhole)).reindex (projectionHom outerContext newerType)
  function := (newest types olderWhole).reindex (projectionHom outerContext newerType)
  spine := (olderSpine.reindex (projectionHom types olderWhole)).reindex (projectionHom outerContext newerType)
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

/-- The rigid head `c`. -/
def head : localScope.Local := .inl ()

def equation : Active localScope.target where
  type := resultType
  left := ⟨(.app (.var 2) newerPattern.application.code : Tower.Tm 6),
    .appElim (A := (.var 5 : Tower.Tm 6)) (B := (.var 6 : Tower.Tm 7)) (.var (2 : Fin 6))
      newerPattern.application.typed⟩
  right := ⟨olderApplication.term.code, olderApplication.term.typed⟩

theorem headType : Ctx.lookup localScope.target.raw (localScope.localIndex head) =
    .pi ((lifted newerSpine).result.reindex newerPattern.map.hom).code (Presentation.rename wk equation.type.code) := by
  rfl'

theorem rightType : (olderApplication.spine.result.reindex olderApplication.map.hom).code = equation.type.code := by
  rfl'

/-! ## The restriction and the pruning update -/

/-- `H : T → T` over `T, F`; it does not mention `F`. -/
abbrev prunedType : TypeOver outerContext := ContextualDependentParameterExchange.second olderWhole arrow

def prunedSpine : Spine prunedType := arrowSpine.reindex (projectionHom types olderWhole)

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

/-- `G`'s first argument `x` is an argument of `F`; its second argument `y` is not. -/
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

noncomputable def store : EquationStore (TotalTerm metas) :=
  [((localScope.toScoped equation).close setting.levels).equation]

noncomputable def pruned : ContextualDependentUpdate.Update setting.levels store :=
  pruneRigidContext (S := setting) ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    DispatchControls.tower_normalizes TowerModel.facts TowerModel.algebra
    ContextualDependentNormalCheckingTower.head_typing_unique TowerModel.roots TowerModel.heads
    ContextualDependentInversion.Controls.declarations_formed newerPattern olderApplication head equation rfl rfl
    rightType headType restriction covers store
    (fun solution solved => (Scoped.close_models_iff setting.levels _ solution).mp solved)

theorem pruned_target : pruned.target = extend outerContext prunedType := rfl

/-- **The computed answer** `G := λ a b. H a`: the second argument is pruned. -/
theorem answer_code : restriction.answer.substitution 0 = (.lam (.lam (.app (.var 2) (.var 1))) : Tower.Tm 3) := by
  rfl'

theorem older_open : restriction.answer.substitution 1 = (.var 1 : Tower.Tm 3) := by rfl'

/-- **No solution is lost.** -/
theorem every_solution_factors {Δ : Context Tower.rules} (solution : Δ ⟶ metas)
    (solved : (frames setting.levels).Models solution store) :
    ∃ residual : Δ ⟶ extend outerContext prunedType,
      (frames setting.levels).Models residual pruned.remaining ∧
        ∀ term : TotalTerm metas, (frames setting.levels).E (term.reindex solution)
          (term.reindex (residual ≫ restriction.answer)) :=
  pruned.complete Δ solution solved

end ContextualDependentPrune.SubtermControls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
