import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentClosedBoundary
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentEtaLongControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentWorklistControls

/-!
# The symbolic/closed boundary: controls in the cumulative tower

* **No closed value of `Ground`.** In the empty context, an η-long normal form of type `Ground`
  would be a neutral term, whose head is a variable or a constant; the empty context has no
  variable and the tower declares no constant (`ground_uninhabited`).
* **A solvable store whose type has no closed inhabitant.** Over `x : Ground`, the store
  `x ≐ x` is solved by the identity frame (`point_solvable`), and has no closed solution
  (`point_not_closedSolvable`). Its principal answer, the identity, lands in a frame without a
  closed point (`point_principal`, `points_no_closedPoint`).
* **A pending store that has no closed solution.** The rigid clash `Ground ≐ U0` is suspended by
  the actual step at budget zero (`clash_pending`) and refuted, with a certificate, at budget one;
  it has no solution at all, so in particular no closed one (`clash_not_closedSolvable`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentClosedBoundary.Controls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentEtaLong ContextualDependentEtaLong.Controls
open ContextualDependentWorklist

/-- Neutral terms of the empty context. -/
def ClosedSpine : LongStatement Tower.Head → Prop
  | @LongStatement.spine _ 0 _ _ _ => False
  | _ => True

/-- **The empty context has no neutral term** in the tower: no variable, no declared constant. -/
theorem closedSpine {st : LongStatement Tower.Head} (long : Long Tower.rules TowerModel.roles st) :
    ClosedSpine st := by
  induction long with
  | @var n _ _ i _ =>
      cases n with
      | zero => exact i.elim0
      | succ => trivial
  | @const n _ _ _ _ _ declared _ _ =>
      cases n with
      | zero => cases declared
      | succ => trivial
  | @app n _ _ _ _ _ _ _ _ _ _ _ ihf _ =>
      cases n with
      | zero => exact ihf
      | succ => trivial
  | @fst n _ _ _ _ _ _ _ _ _ ih =>
      cases n with
      | zero => exact ih
      | succ => trivial
  | @snd n _ _ _ _ _ _ _ _ _ ih =>
      cases n with
      | zero => exact ih
      | succ => trivial
  | _ => trivial

/-- **`Ground` has no closed value.** -/
theorem ground_uninhabited {t : Tower.Tm 0} : ¬ Typed Tower.rules .nil t ground := by
  intro typed
  obtain ⟨v, lv, _⟩ := long_exists (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
    TowerModel.algebra rigid TowerModel.complete .nil typed
  cases lv with
  | univ hu e _ _ =>
      have same := TypeEq.head_injective TowerModel.facts e .nil
      have groundUniverse := (HeadSame.level setting.levels same).1.mpr hu
      cases groundUniverse
  | lam e _ _ _ => exact TypeEq.pi_ne_head TowerModel.facts .nil e.symm
  | pair e _ _ _ => exact TypeEq.sigma_ne_head TowerModel.facts .nil e.symm
  | refl e _ _ => exact TypeEq.id_ne_head TowerModel.facts .nil e.symm
  | neutral ls _ _ _ => exact closedSpine ls

/-! ## A solvable store without a closed solution -/

/-- The frame `x : Ground`. -/
def pointFrame : Context setting.R := ⟨1, points, points_formed⟩

def groundType : TypeOver pointFrame :=
  ⟨ground, .sort Tower.zero, .sort _, ground_typed _⟩

/-- The judged term `x : Ground`. -/
def pointTerm : TotalTerm pointFrame := ⟨groundType, ⟨.var (0 : Fin 1), Derivable.var (0 : Fin 1)⟩⟩

/-- The store `x ≐ x`. -/
def pointStore : EquationStore (TotalTerm pointFrame) := [(pointTerm, pointTerm)]

theorem point_solvable : (frames setting.levels).Solvable pointStore :=
  solvable_of_equivalent setting.levels _ _ (((frames setting.levels).equivalence _).refl _)

/-- **No closed solution**: a closed solution would give `x` a closed value of type `Ground`. -/
theorem point_not_closedSolvable : ¬ ClosedSolvable (S := setting) pointStore := by
  rintro ⟨σ, _⟩
  have typed := σ.typed (0 : Fin 1)
  exact ground_uninhabited typed

theorem points_no_closedPoint : ¬ ClosedPoint (S := setting) pointFrame := by
  rintro ⟨σ⟩
  exact ground_uninhabited (σ.typed (0 : Fin 1))

/-- The identity is a principal answer of `x ≐ x`. -/
theorem point_principal :
    (frames setting.levels).Principal (a := pointFrame) (m := pointFrame) pointStore
      ((frames setting.levels).id pointFrame) where
  sound := by
    intro e member
    obtain rfl := List.mem_singleton.mp member
    exact ((frames setting.levels).equivalence _).refl _
  factors := by
    intro b τ _
    refine ⟨τ, fun t => ?_⟩
    rw [(frames setting.levels).act_comp, (frames setting.levels).act_id]
    exact ((frames setting.levels).equivalence _).refl _

/-- The principal answer accounts for the missing closed solution. -/
theorem point_closed_iff :
    ClosedSolvable (S := setting) pointStore ↔ ClosedPoint (S := setting) pointFrame :=
  principal_closed_iff point_principal

/-! ## A pending store without a closed solution -/

/-- **Pending asserts nothing**: the actual step suspends the clash at budget zero. -/
theorem clash_pending :
    (run ContextualDependentWorklist.Controls.step ContextualDependentWorklist.Controls.clash 0).readout =
      Search.Outcome.Verdict.suspended := rfl

/-- The same store is refuted with a certificate at budget one. -/
theorem clash_refuted_later :
    (run ContextualDependentWorklist.Controls.step ContextualDependentWorklist.Controls.clash 1).readout =
      Search.Outcome.Verdict.refuted :=
  ContextualDependentWorklist.Controls.clash_run_refutes

/-- **The pending store has no closed solution**, nor any solution at all. -/
theorem clash_not_closedSolvable :
    ¬ ClosedSolvable (S := ContextualDependentWorklist.Controls.setting)
      ContextualDependentWorklist.Controls.clash :=
  not_closedSolvable_of_not_solvable ContextualDependentWorklist.Controls.clash_refuted

end ContextualDependentClosedBoundary.Controls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
