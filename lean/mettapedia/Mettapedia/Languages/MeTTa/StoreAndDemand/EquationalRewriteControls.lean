import Mettapedia.Languages.MeTTa.StoreAndDemand.EquationalRewritePublication
import Mettapedia.Languages.MeTTa.StoreAndDemand.EquationalMatchRewrite
import Mettapedia.GSLT.Equations.RecipeMatching

/-! # A compound equality with two legitimate bindings

`UnitRange =e (Range Float 0 1)` and
`UnitRange =e (Range Integer 0 1)` give the *same stored occurrence*
two represented shapes. Replacing it with a note mentioning the bound
type yields two different raw answers. Replacing it with a type-free note
converges. Repeated witnesses and repeated stored occurrences are tested
against the actual ordered publication adapter.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.StoreAndDemand.EquationalRewriteControls

open Mettapedia.GSLT.Equations.RecipeMatching
open Mettapedia.UniversalAlgebra
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaStoreSelection (atomFrames)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting (EquationStore)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.OrderedStore (publish)
open MatchRewritePublication EquationalRewritePublication

private inductive Head where
  | alias | float | integer | zero | one | range
  deriving DecidableEq

private def sig : Signature where
  Operation := Head
  arity
    | .range => 3
    | _ => 0

private abbrev Id := Fin 5

private def arguments (t : Id) : Fin 3 → Id :=
  fun i => if i.val = 0 then t else if i.val = 1 then 3 else 4

private def recipes (addInteger : Bool) : Catalogue sig Id where
  rows
    | .range => (0, arguments 1) :: (if addInteger then [(0, arguments 2)] else [])
    | .alias => [(0, Fin.elim0)]
    | .float => [(1, Fin.elim0)]
    | .integer => [(2, Fin.elim0)]
    | .zero => [(3, Fin.elim0)]
    | .one => [(4, Fin.elim0)]

private def pattern : Term sig := .op .range (fun i =>
  if i.val = 0 then .var 0 else if i.val = 1 then .op .zero Fin.elim0 else .op .one Fin.elim0)

private def storedTerm : Term sig := .op .alias Fin.elim0
private def floatType : Term sig := .op .float Fin.elim0
private def integerType : Term sig := .op .integer Fin.elim0

private def equations : EquationSystem sig := ⟨[
  (storedTerm, pattern.subst (fun _ => floatType)),
  (storedTerm, pattern.subst (fun _ => integerType))]⟩

/-- Both substitutions match the same stored value in the independent
equational theory. The indexed test below uses the finite recipes. -/
theorem both_bindings_are_equational :
    EquationalConsequence equations (pattern.subst (fun _ => floatType), storedTerm) ∧
    EquationalConsequence equations (pattern.subst (fun _ => integerType), storedTerm) := by
  constructor <;> apply EquationalConsequence.symm <;> apply EquationalConsequence.of_mem
  · change (storedTerm, pattern.subst (fun _ => floatType)) ∈ equations.equations
    simp [equations]
  · change (storedTerm, pattern.subst (fun _ => integerType)) ∈ equations.equations
    simp [equations]

private def bindings (addInteger : Bool) : List Id :=
  (List.finRange 5).filter fun t => decide ((0 : Id) ∈ (recipes addInteger).roots (fun _ => t) pattern)

theorem bindings_iff (addInteger : Bool) (t : Id) :
    t ∈ bindings addInteger ↔ (recipes addInteger).Matches (fun _ => t) pattern 0 := by
  simp [bindings, Catalogue.mem_roots_iff]

theorem bindings_before_and_after :
    bindings false = [1] ∧ bindings true = [1, 2] := by decide +kernel

private def stored : Atom := .symbol "UnitRange"
private def note : Atom := .symbol "IntervalAdmitted"
private def typed (t : Id) : Atom :=
  .expression [.symbol "Admitted", if t = 1 then .symbol "Float" else .symbol "Integer"]

private def label (o : Nat) : Atom := if o < 2 then stored else note

private def replace (addInteger exposeType : Bool) : Replacement := fun _ row =>
  if row = stored then some ((bindings addInteger).map fun t => if exposeType then typed t else note)
  else some []

/-- Adding an equation can make the old plan ambiguous, without
appending a row or losing the old match witness. -/
theorem growth_can_make_a_prepared_replacement_ambiguous :
    prepare label (coalesce (replace false true)) 0 [0] = .ok [(0, typed 1)] ∧
    prepare label (coalesce (replace true true)) 0 [0] = .error .ambiguous := by
  let first := bindings_before_and_after.1
  let second := bindings_before_and_after.2
  have distinct : typed 1 ≠ typed 2 := by decide +kernel
  constructor
  · simp [prepare, label, replace, coalesce, first]
  · simp [prepare, label, replace, coalesce, second, distinct]

/-- Two witnesses per row coalesce inside each fibre. The two raw row
occurrences remain two rewrites in the original order. -/
theorem consensus_keeps_both_occurrences :
    prepare label (coalesce (replace true false)) 0 [0, 1] = .ok [(0, note), (1, note)] := by
  simp [prepare, label, replace, coalesce, bindings_before_and_after.2]

/-- Both entries are published by the existing mixed take/make step.
The fresh results are never offered back to the matcher in this commit. -/
theorem consensus_is_one_ordered_publication :
    let items : List (Nat × Atom) := [(0, note), (1, note)]
    let request' := request items [2, 3]
    ∃ admitted : (step label (coalesce (replace true false)) [] 0).Admits
        (s := (([] : EquationStore Atom), [0, 1])) request',
      let after := (step label (coalesce (replace true false)) [] 0).result request' admitted
      after.2 = [2, 3] ∧ after.2.map label = [note, note] ∧ request'.selection.taken.length = 2 := by
  dsimp only
  have consistent : atomFrames.Solvable (a := PUnit.unit) ([] : EquationStore Atom) :=
    ⟨PUnit.unit, atomFrames.id PUnit.unit, fun _ member => nomatch member⟩
  obtain ⟨admitted, _, ordered, output, count⟩ := prepare_publication label
    (coalesce (replace true false)) [] (fresh := [2, 3]) consensus_keeps_both_occurrences
    (by simp) (by simp) (by simp) (by decide +kernel) (by rfl) consistent
  exact ⟨admitted, ordered, output, count⟩

private def integerOnly (addInteger : Bool) : Replacement := fun _ row =>
  if row = stored ∧ (2 : Id) ∈ bindings addInteger then some [note] else some []

/-- A new equation can reach a previously missed row without any data
append. An every cut must account for this absence observation too. -/
theorem equality_change_enables_an_old_miss :
    prepare label (coalesce (integerOnly false)) 0 [0] = .ok [] ∧
    prepare label (coalesce (integerOnly true)) 0 [0] = .ok [(0, note)] := by
  simp [integerOnly, label, prepare, coalesce, bindings_before_and_after.1, bindings_before_and_after.2]

theorem an_incomplete_fibre_is_not_a_miss :
    prepare label (coalesce (fun _ _ => none)) 0 [0] = .error .incomplete := by
  simp [prepare, coalesce]

private def warm : Atom := .symbol "Warm"
private def cold : Atom := .symbol "Cold"

private def aliasPresentation (a : Atom) : Atom := if a = cold then warm else a

/-- Reading both proposed outputs through an alias view can make them
agree for printing. Raw storage still distinguishes them, for example
when the alias is later retracted. Quotient agreement alone is not a
license to choose a raw replacement. -/
theorem print_agreement_is_not_raw_agreement :
    GSLT.Equations.OccurrenceChoices.resolve ([cold, warm].map aliasPresentation) =
        some (some warm) ∧
      GSLT.Equations.OccurrenceChoices.resolve [cold, warm] = none := by
  decide +kernel

/-- The empty output block is a *successful* take, as opposed to a
miss. Both have no new output rows, but the return count is different. -/
theorem a_delete_is_not_a_miss :
    (EquationalMatchRewrite.entries label [0] [some []]).length = 1 ∧
    (EquationalMatchRewrite.entries label [0] [none]).length = 0 := ⟨rfl, rfl⟩

/-- Single-pass and in-place are different observations. The existing
ordered publication keeps survivors in order, then appends its fresh
outputs. A positional text substitution would put 2 before survivor 1. -/
theorem ordered_publication_is_not_in_place :
    publish ([0, 1] : List Nat) (request [(0, note)] [2]).selection = [1, 2] ∧
    publish ([0, 1] : List Nat) (request [(0, note)] [2]).selection ≠ [2, 1] := by
  decide +kernel

end Mettapedia.Languages.MeTTa.StoreAndDemand.EquationalRewriteControls
