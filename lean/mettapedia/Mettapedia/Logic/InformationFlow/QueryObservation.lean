import Mettapedia.Logic.InformationFlow.Label
import Mettapedia.Logic.InformationFlow.ObservationalSecurity

/-!
# Labeled query results and their observations

Projection of independently labeled rows commutes with pure row maps and with
joins whose derivation label is the join of the source labels. It preserves
the complete ordered visible list, so counts of that list are safe as well.

A meet over alternative derivations has a different purpose: under the
conditions in `Label`, it describes existential visibility, not visibility of
every occurrence. Applying that meet to all occurrences exposes secret bag
multiplicity. Row filtering also cannot repair a public result whose presence
was controlled by a secret. A label for the whole query response must cover
the empty response and the query's control dependencies.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.InformationFlow.QueryObservation

universe u v w

local instance : SemilatticeInf Bool := Bool.instDistribLattice.toLattice.toSemilatticeInf
local instance : SemilatticeSup Bool := Bool.instDistribLattice.toLattice.toSemilatticeSup
local instance : OrderTop Bool := Bool.instBoundedOrder.toOrderTop

variable {L : Type u} {A : Type v} {B : Type w}

/-- Preserve the order and multiplicity of rows admitted at this clearance. -/
def visibleRows [Preorder L] [DecidableLE L] (clearance : L)
    (rows : List (L × A)) : List A :=
  rows.filterMap fun row => if row.1 ≤ clearance then some row.2 else none

@[simp] theorem visibleRows_nil [Preorder L] [DecidableLE L] (clearance : L) :
    visibleRows clearance ([] : List (L × A)) = [] := rfl

@[simp] theorem visibleRows_cons [Preorder L] [DecidableLE L]
    (clearance : L) (row : L × A) (rows : List (L × A)) :
    visibleRows clearance (row :: rows) =
      if row.1 ≤ clearance then row.2 :: visibleRows clearance rows
      else visibleRows clearance rows := by
  by_cases visible : row.1 ≤ clearance <;> simp [visibleRows, visible]

theorem visibleRows_append [Preorder L] [DecidableLE L]
    (clearance : L) (left right : List (L × A)) :
    visibleRows clearance (left ++ right) =
      visibleRows clearance left ++ visibleRows clearance right := by
  exact List.filterMap_append

/-- A pure value transformation retains each row's dependency label. -/
def mapRows (f : A → B) (rows : List (L × A)) : List (L × B) :=
  rows.map fun row => (row.1, f row.2)

theorem visibleRows_mapRows [Preorder L] [DecidableLE L]
    (clearance : L) (f : A → B) (rows : List (L × A)) :
    visibleRows clearance (mapRows f rows) =
      (visibleRows clearance rows).map f := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    simp only [mapRows, List.map_cons, visibleRows_cons]
    split <;> simp_all [mapRows]

/-- All ordered pairs of rows, with both sources recorded in the label. -/
def joinRows [SemilatticeSup L]
    (left : List (L × A)) (right : List (L × B)) : List (L × (A × B)) :=
  left.flatMap fun first =>
    right.map fun second => (first.1 ⊔ second.1, (first.2, second.2))

private theorem visibleRows_join_one [SemilatticeSup L] [DecidableLE L]
    (clearance : L) (first : L × A) (right : List (L × B)) :
    visibleRows clearance
        (right.map fun second => (first.1 ⊔ second.1, (first.2, second.2))) =
      if first.1 ≤ clearance then
        (visibleRows clearance right).map fun second => (first.2, second)
      else [] := by
  induction right with
  | nil => simp
  | cons second right ih =>
    simp only [List.map_cons, visibleRows_cons, sup_le_iff, ih]
    by_cases hfirst : first.1 ≤ clearance <;>
      by_cases hsecond : second.1 ≤ clearance <;>
      simp [hfirst, hsecond]

/-- The complete visible ordered bag of a labeled join is obtained by joining
the visible inputs. This is stronger than equality of existential support. -/
theorem visibleRows_joinRows [SemilatticeSup L] [DecidableLE L]
    (clearance : L) (left : List (L × A)) (right : List (L × B)) :
    visibleRows clearance (joinRows left right) =
      (visibleRows clearance left).flatMap fun first =>
        (visibleRows clearance right).map fun second => (first, second) := by
  induction left with
  | nil => rfl
  | cons first left ih =>
    change visibleRows clearance
      ((right.map fun second => (first.1 ⊔ second.1, (first.2, second.2))) ++
        joinRows left right) = _
    rw [visibleRows_append, visibleRows_join_one, ih, visibleRows_cons]
    split <;> simp_all

/-- A concrete two-run theorem for the join algorithm, not merely a law of
its annotation algebra. Equal visible input lists give equal complete visible
output lists, including their order, multiplicity, and emptiness. -/
theorem joinRows_noninterference [SemilatticeSup L] [DecidableLE L]
    (clearance : L) :
    ObservationalSecurity.Noninterference
      (fun left right : List (L × A) × List (L × B) =>
        visibleRows clearance left.1 = visibleRows clearance right.1 ∧
        visibleRows clearance left.2 = visibleRows clearance right.2)
      { observe := visibleRows clearance }
      (fun input => joinRows input.1 input.2) := by
  intro left right related
  change visibleRows clearance (joinRows left.1 left.2) =
    visibleRows clearance (joinRows right.1 right.2)
  rw [visibleRows_joinRows, visibleRows_joinRows, related.1, related.2]

/-- Every function of the complete visible join is a safe whole-query
observation. This includes counts, emptiness, and first-answer observations;
it does not license observing hidden occurrences before projection. -/
theorem joinRows_whole_query_noninterference
    [SemilatticeSup L] [DecidableLE L] {View : Type*}
    (clearance : L) (observe : List (A × B) → View) :
    ObservationalSecurity.Noninterference
      (fun left right : List (L × A) × List (L × B) =>
        visibleRows clearance left.1 = visibleRows clearance right.1 ∧
        visibleRows clearance left.2 = visibleRows clearance right.2)
      { observe := fun rows => observe (visibleRows clearance rows) }
      (fun input => joinRows input.1 input.2) := by
  exact ObservationalSecurity.noninterference_postcompose
    (joinRows_noninterference clearance) observe

/-- Query-result publication uses one label covering the entire response,
including whether its result list is empty. The caller must account for every
read and control dependency when establishing that label. -/
def publishQuery [Preorder L] [DecidableLE L]
    (clearance dependency : L) (answer : A) : Option A :=
  if dependency ≤ clearance then some answer else none

theorem publishQuery_of_not_le [Preorder L] [DecidableLE L]
    (clearance dependency : L) (hidden : ¬ dependency ≤ clearance)
    (answer : A) : publishQuery clearance dependency answer = none := by
  simp [publishQuery, hidden]

theorem publishQuery_of_le [Preorder L] [DecidableLE L]
    (clearance dependency : L) (visible : dependency ≤ clearance)
    (answer : A) : publishQuery clearance dependency answer = some answer := by
  simp [publishQuery, visible]

/-- A group of derivations for one value is labeled uniformly by the meet.
This is precisely the unsound step when all bag occurrences are then exposed. -/
def annotateWithAlternativeMeet (rows : List (Bool × Nat)) : List (Bool × Nat) :=
  rows.map fun row => (alternativeLabel (rows.map Prod.fst), row.2)

/-- One public derivation and an additional secret derivation have the same
visible input, but a shared meet annotation releases a different bag count. -/
theorem alternative_meet_leaks_multiplicity :
    let absent := [(false, 7)]
    let present := [(false, 7), (true, 7)]
    visibleRows false absent = visibleRows false present ∧
    alternativeLabel (absent.map Prod.fst) =
      alternativeLabel (present.map Prod.fst) ∧
    (visibleRows false (annotateWithAlternativeMeet absent)).length = 1 ∧
    (visibleRows false (annotateWithAlternativeMeet present)).length = 2 := by
  decide

/-- The result value is public, but whether it exists depends on a secret. -/
def secretGuardedPublicRow (secret : Bool) : List (Bool × Nat) :=
  if secret then [(false, 7)] else []

/-- Filtering returned rows cannot remove this implicit flow: there are no
secret-labeled returned rows to discard. The empty result is observable. -/
theorem row_filtering_does_not_hide_secret_existence :
    visibleRows false (secretGuardedPublicRow false) = [] ∧
    visibleRows false (secretGuardedPublicRow true) = [7] := by
  decide

/-- Accounting for the secret control dependency on the whole response hides
both the empty and nonempty results. -/
theorem whole_query_label_hides_secret_existence :
    publishQuery false true (visibleRows false (secretGuardedPublicRow false)) =
      publishQuery false true (visibleRows false (secretGuardedPublicRow true)) ∧
    publishQuery false true (visibleRows false (secretGuardedPublicRow true)) =
      none := by
  decide

/-- Labeling the whole response does not suppress an independently public
answer, and preserves its empty/nonempty distinction when that is public. -/
theorem whole_query_public_results_remain_observable :
    publishQuery false false ([] : List Nat) = some [] ∧
    publishQuery false false [7] = some [7] ∧
    publishQuery false false ([] : List Nat) ≠ publishQuery false false [7] := by
  decide

/-- Source-join labeling is the positive bag control: the secret occurrence
is withheld while the public occurrence is retained. -/
theorem join_preserves_public_bag_with_secret_alternative :
    visibleRows false (joinRows [(false, 7), (true, 7)] [(false, 2)]) = [(7, 2)] ∧
    visibleRows false (joinRows [(false, 7)] [(false, 2)]) = [(7, 2)] := by
  decide

end Mettapedia.Logic.InformationFlow.QueryObservation
