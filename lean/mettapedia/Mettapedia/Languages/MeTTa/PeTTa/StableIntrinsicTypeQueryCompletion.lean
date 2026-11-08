import Mettapedia.Languages.MeTTa.PeTTa.StableIntrinsicTypeQuery

/-! Completion stability for the corrected intrinsic-query boundary. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.StableIntrinsicTypeQuery.Completion

open Mettapedia.Logic.LP
open IntrinsicTypeFacts (signature TypeTerm Declaration)
open IndependentTypeOutput (Path Supply Query collect arguments structural callParts declarations)
open IndependentTypeOutput.Completion (Extends QueryExtends extends_refl extends_trans
  collect_extends arguments_extends structural_extends)

private theorem bind_extends {α β : Type} {before after : Option α}
    {left right : α → Option β} (input : Extends before after)
    (body : ∀ item, Extends (left item) (right item)) :
    Extends (before.bind left) (after.bind right) := by
  intro answer returned
  cases initial : before with
  | none => simp [initial] at returned
  | some item =>
    rw [input item initial]
    exact body item answer (by simpa [initial] using returned)

theorem functions_extends (library : List Declaration) (supply : Supply)
    (left right : Query) (same : QueryExtends left right)
    (path : Path) (items : List TypeTerm) (required : Option TypeTerm) :
    Extends (functions library supply left path items required)
      (functions library supply right path items required) := by
  cases items with
  | nil => exact extends_refl _
  | cons head actuals =>
    apply collect_extends
    intro scheme
    cases split : callParts actuals.length scheme with
    | none => exact extends_refl _
    | some pair =>
      rcases pair with ⟨domains, result⟩
      cases required with
      | none => exact arguments_extends left right same path 0 _ result _
      | some target =>
        dsimp only
        cases unifyTotal [(result, target)] with
        | none => exact extends_refl _
        | some initial => exact arguments_extends left right same path 0 _ result initial

theorem candidates_extends (library : List Declaration) (supply : Supply)
    (left right : Query) (same : QueryExtends left right) :
    QueryExtends (candidates library supply left) (candidates library supply right) := by
  intro path subject required
  simp only [candidates]
  split
  · exact extends_refl _
  · split
    · exact extends_refl _
    · split
      · exact extends_refl _
      · apply bind_extends (functions_extends library supply left right same _ _ _)
        intro functionAnswers
        apply bind_extends
        · cases required with
          | none => exact extends_refl _
          | some target =>
            dsimp only
            split
            · exact functions_extends library supply left right same _ _ _
            · exact extends_refl _
        · intro allFunctions
          apply bind_extends
          · split
            · exact structural_extends supply left right same _ _ _
            · exact extends_refl _
          · intro rowAnswers
            exact extends_refl _

theorem step_extends (library : List Declaration) (supply : Supply)
    (left right : Query) (same : QueryExtends left right) :
    QueryExtends (step library supply left) (step library supply right) := by
  intro path subject required
  simp only [step]
  split
  · apply bind_extends (candidates_extends library supply left right same _ _ _)
    intro answers
    exact extends_refl _
  · apply bind_extends (candidates_extends library supply left right same _ _ _)
    intro answers
    exact extends_refl _
  · apply bind_extends (candidates_extends library supply left right same _ _ _)
    intro answers
    split
    · apply bind_extends (candidates_extends library supply left right same _ _ _)
      intro all
      exact extends_refl _
    · exact extends_refl _

theorem run_succ_extends (library : List Declaration) (supply : Supply) (fuel : Nat) :
    QueryExtends (run library supply fuel) (run library supply (fuel + 1)) := by
  induction fuel with
  | zero => intro path subject required answer returned; simp [run] at returned
  | succ fuel ih => exact step_extends library supply _ _ ih

/-- More approximation depth cannot add an answer to a completed empty
query, change an answer order, or duplicate an existing occurrence. -/
theorem run_add_extends (library : List Declaration) (supply : Supply) (fuel extra : Nat) :
    QueryExtends (run library supply fuel) (run library supply (fuel + extra)) := by
  induction extra with
  | zero => intro path subject required; exact extends_refl _
  | succ extra ih =>
    intro path subject required
    exact extends_trans (ih path subject required)
      (run_succ_extends library supply (fuel + extra) path subject required)

end Mettapedia.Languages.MeTTa.PeTTa.StableIntrinsicTypeQuery.Completion
