import Mettapedia.Machines.Cursor.ListCells

/-!
# Candidate selection for list-cell patterns

A structural index must not read an internal list cell as a three-element
expression. Closed spines can be indexed through their flat reading. If a
partial or nested cell remains, offering every occurrence is complete; the
original pattern still decides unification. This projection never changes
variables or merges equal occurrences.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.MatchIndexProjection

open Cursor.ListCells
open Tm (TagFree)

mutual
/-- Constructor summaries may establish this predicate without a term walk. -/
def structural : Tm → Bool
  | .sym _ | .var _ => true
  | .tag => false
  | .expr xs => structuralList xs
def structuralList : List Tm → Bool
  | [] => true
  | x :: xs => structural x && structuralList xs
end

theorem structuralList_eq_all (xs : List Tm) : structuralList xs = xs.all structural := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [structuralList, ih]

theorem structural_tagFree {t : Tm} (h : structural t = true) : TagFree t := by
  induction t using Tm.induction with
  | sym s => exact .sym s
  | var v => exact .var v
  | tag => cases h
  | expr xs ih =>
    exact .expr xs fun x hx => ih x hx ((List.all_eq_true.mp (by simpa [structural, structuralList_eq_all] using h)) x hx)

/-- `none` requests the complete occurrence frontier. -/
def project (pattern : Tm) : Option Tm :=
  if structural pattern then some pattern
  else match pattern.closedElems with
    | none => none
    | some xs => if structural (.expr xs) then some (.expr xs) else none

theorem project_denote {pattern query : Tm} (h : project pattern = some query) :
    query.denote = pattern.denote := by
  unfold project at h
  split at h
  · cases h; rfl
  · split at h
    · cases h
    · rename_i xs hx
      split at h
      · rename_i hs
        cases h
        rw [(structural_tagFree hs).denote_expr]
        exact Tm.denoteList_closedElems hx
      · cases h

/-- A concrete index query retains exactly the original unifiers. -/
theorem project_unifies {pattern query : Tm} (h : project pattern = some query)
    (θ : ℕ → PT) (row : Tm) : Unifies θ query row ↔ Unifies θ pattern row := by
  unfold Unifies
  rw [project_denote h]

/-- The semantic requirement on candidates, before exact matching. -/
def Candidate (θ : ℕ → PT) (query : Option Tm) (row : Tm) : Prop :=
  match query with
  | none => True
  | some q => Unifies θ q row

theorem candidate_complete (pattern row : Tm) (θ : ℕ → PT)
    (h : Unifies θ pattern row) : Candidate θ (project pattern) row := by
  cases hp : project pattern with
  | none => trivial
  | some q => exact (project_unifies hp θ row).mpr h

/-- Filtering the candidate frontier and then unifying retains the exact
occurrence list, including duplicates and its original order. -/
theorem filter_occurrences (pattern : Tm) (θ : ℕ → PT) (rows : List Tm) :
    (rows.filter (fun row => by classical exact decide (Candidate θ (project pattern) row))).filter
        (fun row => by classical exact decide (Unifies θ pattern row)) =
      rows.filter (fun row => by classical exact decide (Unifies θ pattern row)) := by
  classical
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    by_cases h : Unifies θ pattern row
    · have hc := candidate_complete pattern row θ h
      simp [h, hc, ih]
    · by_cases hc : Candidate θ (project pattern) row <;>
        simp [h, hc, ih]

/-- A closed cell exposes its logical list length to the index. -/
example : project (.cell (.sym 1) (.expr [.var 0, .var 1])) =
    some (.expr [.sym 1, .var 0, .var 1]) := rfl

/-- A partial tail must not be mistaken for a rigid three-element list. -/
example : project (.cell (.sym 1) (.var 0)) = none := rfl

/-- A nested cell uses the complete frontier until the index supports it. -/
example : project (.expr [.sym 2, .cell (.sym 1) (.expr [])]) = none := rfl

/-- Structural equality of the physical representations can reject a real
match. This is a negative control for indexing the carrier unchanged. -/
example :
    Unifies PT.var (.cell (.sym 1) (.expr [.sym 2])) (.expr [.sym 1, .sym 2]) ∧
    (Tm.cell (.sym 1) (.expr [.sym 2])).subst Tm.var ≠
      (Tm.expr [.sym 1, .sym 2]).subst Tm.var := by
  constructor
  · exact ⟨_, _, rfl, rfl, rfl⟩
  · intro h
    simp [Tm.subst, Tm.substList] at h


/-- Enumerating match environments through a host and resuming the body for
each is the same occurrence-preserving bind as running the body per row.
The constant host result does not replace the environment in this protocol. -/
theorem host_match_bind {Row Env Answer : Type} (rows : List Row)
    (matchRow : Row → List Env) (body : Env → List Answer) :
    (rows.flatMap matchRow).flatMap body =
      rows.flatMap (fun row => (matchRow row).flatMap body) := by
  exact List.flatMap_assoc ..

/-- Replacing two environments by one successful Boolean loses answers. -/
example : ([1, 2] : List Nat).flatMap (fun n => [n + 10]) ≠
    [1].flatMap (fun n => [n + 10]) := by decide

end Mettapedia.Machines.MatchIndexProjection
