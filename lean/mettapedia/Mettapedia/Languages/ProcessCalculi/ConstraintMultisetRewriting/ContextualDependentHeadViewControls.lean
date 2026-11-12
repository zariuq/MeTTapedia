import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentHeadRows

/-!
# Controls of the view and of the classification

Over four variables, the two older ones unknowns and the two newer ones bound locals (`flexible`):

* **views.** `fst (g X)` is the local `g` under an application and a projection (`neutral_view`); a pair under an
  application has no view (`blocked_none`), and it is the only kind of code without one: it is an introduction under
  an elimination (`blocked_shape`).
* **rows.** One control for each kind of row: the same local under eliminations of one shape (`row_sameRigid`), of
  different shapes (`row_shapeClash`), two locals (`row_headClash`), an unknown against a local
  (`row_patternLeft`, `row_patternRight`), the same unknown and two unknowns (`row_sameUnknown`, `row_twoUnknowns`),
  a pair against a local (`row_etaPair`), a universe against a local (`row_introductionRigid`), two universes
  (`row_universes`), a function type against a pair type (`row_formerClash`), an abstraction against a pair
  (`row_illTyped`).
* **the side test of the spine row is needed.** With the same sides, `g X` against `g A`, the clash row does not
  hold (`spine_not_clash`), and with eliminations of different shapes the spine row does not hold
  (`clash_not_spine`): the two rows are told apart by the shapes of the eliminations, and reading the second pair
  as a spine would compare an application with a projection.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentHeadView.Controls

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation
open ContextualDependentDynamicFragment ContextualDependentEtaDepth

/-- Four variables: `0`, `1` bound locals, `2`, `3` unknowns. -/
abbrev flexible : Fin 4 → Bool := openedFlexible 2

/-- `fst (g X)`, with `g` the local `0` and `X` the unknown `2`. -/
def projected : Tower.Tm 4 := .fst (.app (.var 0) (.var 2))

theorem neutral_view : (view? projected).map View.code = some projected := rfl

theorem neutral_shapes :
    (view? projected).map (fun view => match view with
      | .neutral index eliminations => (index.val, shapes eliminations)
      | _ => (4, [])) = some (0, [.app, .fst]) := by decide

/-- A pair under an application. -/
def blocked : Tower.Tm 4 := .app (.pair (.var 0) (.var 1)) (.var 2)

theorem blocked_none : (view? blocked).isSome = false := rfl

theorem blocked_shape : isIntroduction (unwind blocked).1 = true ∧ (unwind blocked).2.length = 1 := by decide

/-! ### Rows -/

/-- The local `g` under an application to `argument` and a projection. -/
def spine (argument : Fin 4) : View Tower.Head 4 := .neutral 0 [.app (.var argument), .fst]

theorem row_sameRigid : classify (Head := Tower.Head) flexible (spine 2) (spine 3) = .sameRigid := by decide

theorem row_shapeClash :
    classify (Head := Tower.Head) flexible (spine 2) (.neutral 0 [.fst, .app (.var 3)]) = .shapeClash := by decide

theorem row_headClash : classify (Head := Tower.Head) flexible (spine 2) (.neutral 1 [.app (.var 2), .fst]) = .headClash := by decide

theorem row_patternLeft : classify (Head := Tower.Head) flexible (.neutral 2 [.app (.var 0)]) (spine 3) = .patternLeft := by decide

theorem row_patternRight : classify (Head := Tower.Head) flexible (spine 3) (.neutral 2 [.app (.var 0)]) = .patternRight := by decide

theorem row_sameUnknown :
    classify (Head := Tower.Head) flexible (.neutral 2 [.app (.var 0)]) (.neutral 2 [.app (.var 1)]) = .sameUnknown := by decide

theorem row_twoUnknowns :
    classify (Head := Tower.Head) flexible (.neutral 2 [.app (.var 0)]) (.neutral 3 [.app (.var 1)]) = .twoUnknowns := by decide

theorem row_etaPair : classify (Head := Tower.Head) flexible (.pair (.var 2) (.var 3)) (spine 2) = .etaPair := by decide

theorem row_introductionRigid :
    classify (Head := Tower.Head) flexible (.sort (.sort Tower.zero)) (spine 2) = .introductionRigid := by decide

theorem row_universes :
    classify (Head := Tower.Head) flexible (.sort (.sort Tower.zero)) (.sort (.sort Tower.zero) : View Tower.Head 4) = .universes := by
  decide

theorem row_formerClash :
    classify (Head := Tower.Head) flexible (.pi (.var 2) (.var 3)) (.sigma (.var 2) (.var 3) : View Tower.Head 4) = .formerClash := by
  decide

theorem row_illTyped :
    classify (Head := Tower.Head) flexible (.lam (.var 0)) (.pair (.var 2) (.var 3) : View Tower.Head 4) = .illTyped := by decide

/-! ### The two rows read are told apart by the shapes of the eliminations -/

/-- `g X` against `g A` is in the spine row. -/
theorem spine_row : SpineRow 2 (.neutral (0 : Fin 4) [.app (.var 2)] : View Tower.Head 4)
    (.neutral 0 [.app (.var 3)]) :=
  ⟨0, [.var 2], [.var 3], by decide, by simp, rfl, .inl ⟨rfl, rfl⟩⟩

/-- `g X` against `g A` is not in the clash row: the skeletons are the same. -/
theorem spine_not_clash : ¬ ClashRow 2 (.neutral (0 : Fin 4) [.app (.var 2)] : View Tower.Head 4)
    (.neutral 0 [.app (.var 3)]) := by
  rintro ⟨s, s', left, right, differ⟩
  simp only [rigidSkeleton, shapes, List.map_cons, List.map_nil] at left right
  exact differ (Option.some.inj (left.symm.trans right))

/-- `g X` against `fst g` is in the clash row. -/
theorem clash_row : ClashRow 2 (.neutral (0 : Fin 4) [.app (.var 2)] : View Tower.Head 4) (.neutral 0 [.fst]) :=
  clashRow_of_classify (by decide) (by decide) (.inr (by decide))

/-- `g X` against `fst g` is not in the spine row. -/
theorem clash_not_spine : ¬ SpineRow 2 (.neutral (0 : Fin 4) [.app (.var 2)] : View Tower.Head 4)
    (.neutral 0 [.fst]) := by
  rintro ⟨index, as, bs, _, nonempty, same, shape⟩
  rcases shape with ⟨left, right⟩ | ⟨first, left, right⟩
  · have shapesRight := congrArg (fun view : View Tower.Head 4 => match view with
      | .neutral _ eliminations => shapes eliminations
      | _ => []) right
    simp only [shapes, List.map_cons, List.map_nil, List.map_map] at shapesRight
    cases bs with
    | nil => exact nonempty (List.length_eq_zero_iff.mp (by simpa using same))
    | cons b rest => simp [Elimination.shape] at shapesRight
  · have shapesLeft := congrArg (fun view : View Tower.Head 4 => match view with
      | .neutral _ eliminations => (shapes eliminations).length
      | _ => 0) left
    simp only [shapes, List.map_cons, List.map_nil, List.map_append, List.length_append, List.length_map,
      List.length_cons, List.length_nil] at shapesLeft
    cases as with
    | nil => exact nonempty rfl
    | cons a rest => simp at shapesLeft

end ContextualDependentHeadView.Controls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
