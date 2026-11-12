import Mettapedia.Languages.MeTTa.PeTTa.LibTransform
import Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaStoreSelection

/-!
# `collect`, `all` and `unique` over one pattern are requests with a predicate query

The earlier modules of this lane show that a transform whose rules read, take, check single
absences and make is a run of the first-order step. `collect`, `all` and `unique` say
something about every match of a pattern at once, which a rule instance of that step does
not: they need the observation "these are all the occurrences whose atom matches". The
ordered-store step has that observation (`PredicateQuery`, checked when a request is
admitted). This module states the library model's laws for these conjuncts, over one
pattern, as admitted requests of that step.

The store of the model is the list of the labels of distinct occurrences `rows`.

* `collect_take_query`: `(collect (take p) C)` is the removal request with its predicate
  query for "p matches the atom": the step admits it, the store the model leaves is the
  labels of the step's rows after it, and `C` is bound to the labels of the taken
  occurrences.
* `all_take_query`: `(all (take p))` leaves the same store by the same request; its
  answers are one instance set for each match.
* `unique_read_query`: `(unique (read p))` has its one branch exactly when the read
  request with its predicate query reads exactly one occurrence; the step admits that
  request and the store is left as it is.

Negative example: `Controls.unique_needs_one` (with two matching occurrences the request
with its predicate query reads two, and `unique` has no branch).

Not here: conditions over joint matches of several patterns; `collect` in read mode with a
pattern for the collection; these conjuncts inside a kernel with other conjuncts.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.LibTransformStep

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst matchAtom)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Interface
open Mettapedia.Languages.MeTTa.ContextualTransform
open PeTTaStoreSelection (atomFrames)
open LibTransform

variable {O : Type} [DecidableEq O] (label : O → Atom)

/-- "The pattern matches the atom", the predicate of the query. -/
def meets (p : Atom) (atom : Atom) : Bool := (matchAtom [] p atom).isSome

/-- The removal request with its predicate query for the matches of `p`. -/
abbrev takeMatches (p : Atom) (rows : List O) : OrderedStore.Publication Atom O :=
  StoreOperations.removeRequest (Tm := fun _ : PUnit.{1} => Atom) (a := PUnit.unit) label
    (meets p) rows

/-- The read request with its predicate query for the matches of `p`. -/
abbrev readMatches (p : Atom) (rows : List O) : OrderedStore.Publication Atom O :=
  StoreOperations.readRequest (Tm := fun _ : PUnit.{1} => Atom) (a := PUnit.unit) label
    (meets p) rows

omit [DecidableEq O] in
theorem filter_labels (p : Atom) (rows : List O) :
    (rows.map label).filter (fun atom => (matchAtom [] p atom).isSome) =
      (rows.filter fun occurrence => meets p (label occurrence)).map label := by
  simp [List.filter_map, Function.comp_def, meets]

/-- **`(collect (take p) C)` is one take with its predicate query.** The step admits the removal
request for the matches of `p`; the model's transform leaves the labels of the step's rows
after it, and answers the template with `C` bound to the labels of the taken occurrences. -/
theorem collect_take_query (rows : List O) (unique : rows.Nodup) (p template : Atom)
    (C : String) (knowledge : EquationStore Atom)
    (consistent : atomFrames.Solvable (a := PUnit.unit) knowledge) :
    ∃ admitted : (OrderedStore.step atomFrames PUnit.unit label).Admits
        (s := (knowledge, rows)) (takeMatches label p rows),
      (transform (collectTake p C) template (rows.map label)).drain =
        (instances template
            [(C, .expression ((takeMatches label p rows).selection.taken.map label))],
          ((OrderedStore.step atomFrames PUnit.unit label).result (takeMatches label p rows)
            admitted).2.map label) := by
  have admitted := (StoreOperations.remove_admits_exact atomFrames PUnit.unit label
    (meets p) knowledge rows).mpr ⟨unique, consistent⟩
  refine ⟨admitted, ?_⟩
  have left := StoreOperations.remove_all_correspondence atomFrames PUnit.unit label
    (meets p) knowledge rows admitted
  rw [transform_collect_take, filter_labels]
  refine Prod.ext rfl ?_
  have rowsLeft := congrArg Prod.fst left
  simpa [StoreAndDemand.StoreEffects.removeAll, meets] using rowsLeft

/-- **`(all (take p))` is the same take with its predicate query**: the store it leaves is the
labels of the step's rows after that request. -/
theorem all_take_query (rows : List O) (unique : rows.Nodup) (p template : Atom)
    (knowledge : EquationStore Atom)
    (consistent : atomFrames.Solvable (a := PUnit.unit) knowledge) :
    ∃ admitted : (OrderedStore.step atomFrames PUnit.unit label).Admits
        (s := (knowledge, rows)) (takeMatches label p rows),
      (transform (allTake p) template (rows.map label)).drain.2 =
        ((OrderedStore.step atomFrames PUnit.unit label).result (takeMatches label p rows)
          admitted).2.map label := by
  have admitted := (StoreOperations.remove_admits_exact atomFrames PUnit.unit label
    (meets p) knowledge rows).mpr ⟨unique, consistent⟩
  refine ⟨admitted, ?_⟩
  have left := StoreOperations.remove_all_correspondence atomFrames PUnit.unit label
    (meets p) knowledge rows admitted
  rw [transform_all_take]
  have rowsLeft := congrArg Prod.fst left
  simpa [StoreAndDemand.StoreEffects.removeAll, meets] using rowsLeft

/-- **`(unique (read p))` has its branch exactly when the read with its predicate
query is of one occurrence.** The step admits that read request in any case; the model's
`unique` has exactly one joint match exactly when that request reads exactly one
occurrence. -/
theorem unique_read_query (rows : List O) (unique : rows.Nodup) (p : Atom)
    (knowledge : EquationStore Atom)
    (consistent : atomFrames.Solvable (a := PUnit.unit) knowledge) :
    (OrderedStore.step atomFrames PUnit.unit label).Admits (s := (knowledge, rows))
        (readMatches label p rows) ∧
      ((∃ t, jointIn (rows.map label) [] [p] = [t]) ↔
        ∃ occurrence, (readMatches label p rows).selection.read = [occurrence]) := by
  refine ⟨(StoreOperations.read_admits_exact atomFrames PUnit.unit label (meets p)
    knowledge rows).mpr ⟨unique, consistent⟩, ?_⟩
  have count : (jointIn (rows.map label) [] [p]).length =
      (rows.filter fun occurrence => meets p (label occurrence)).length := by
    rw [jointIn_one, List.length_map, ← List.length_map (f := Prod.snd), matchesIn_snd,
      filter_labels, List.length_map]
  show _ ↔ ∃ occurrence,
    (rows.filter fun occurrence => meets p (label occurrence)) = [occurrence]
  rw [← List.length_eq_one_iff, ← List.length_eq_one_iff, count]

namespace Controls

/-- Negative: with two occurrences that match, the read with its predicate query is of
both, so `unique` has no branch. -/
theorem unique_needs_one :
    (readMatches (fun n : Nat => if n = 2 then Atom.symbol "other" else .symbol "x")
        (.var "any") [0, 1]).selection.read = [0, 1] ∧
      ¬ ∃ t, jointIn [Atom.symbol "x", .symbol "x"] [] [.var "any"] = [t] := by
  refine ⟨by decide, ?_⟩
  rintro ⟨t, one⟩
  have two : (jointIn [Atom.symbol "x", .symbol "x"] [] [.var "any"]).length = 2 := by decide
  rw [one] at two
  cases two

end Controls

end Mettapedia.Languages.MeTTa.PeTTa.LibTransformStep
