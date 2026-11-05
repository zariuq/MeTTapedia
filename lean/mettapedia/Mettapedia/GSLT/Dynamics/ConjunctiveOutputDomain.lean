import Mettapedia.GSLT.Dynamics.ConjunctiveBindingDomain
import Mathlib.Data.Fintype.BigOperators

/-!
# Source-derived finite output domains for conjunctive regions

Captured values, factor coordinates and head constants determine a finite
active domain. The existing binding join preserves it. Head instantiation
reads bound slots only; it does not invent a default for an unbound variable.
The output catalogue is a semantic enclosure, not a runtime grounding plan,
an answer bag, or a claim of globally minimal storage.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.ConjunctiveOutputDomain

open ConjunctiveRegionProvenance GenericJoinRegions ConjunctiveRowMatching ConjunctiveBindingDomain
open scoped BigOperators

variable {n : Nat} {Value Name Id : Type} [DecidableEq Value] [DecidableEq Name]

def tuples (domain : Finset Value) (arity : Nat) : Finset (List Value) :=
  (Fintype.piFinset fun _ : Fin arity => domain).image List.ofFn

theorem mem_tuples (domain : Finset Value) (arity : Nat) (values : List Value) :
    values ∈ tuples domain arity ↔ values.length = arity ∧ ∀ value ∈ values, value ∈ domain := by
  constructor
  · intro member
    obtain ⟨fields, inside, rfl⟩ := Finset.mem_image.mp member
    refine ⟨List.length_ofFn, ?_⟩
    intro value present
    obtain ⟨index, rfl⟩ := List.mem_ofFn.mp present
    exact Fintype.mem_piFinset.mp inside index
  · rintro ⟨rfl, inside⟩
    apply Finset.mem_image.mpr
    exact ⟨values.get, Fintype.mem_piFinset.mpr (fun index => inside _ (List.get_mem values index)), List.ofFn_get values⟩

theorem card_tuples (domain : Finset Value) (arity : Nat) : (tuples domain arity).card = domain.card ^ arity := by
  calc
    _ = (Fintype.piFinset fun _ : Fin arity => domain).card :=
      Finset.card_image_iff.mpr List.ofFn_injective.injOn
    _ = _ := Fintype.card_piFinset_const domain arity

def catalogue (domain : Finset Value) (shapes : Finset (Name × Nat)) : Finset (Name × List Value) :=
  shapes.biUnion fun shape => (tuples domain shape.2).image fun values => (shape.1, values)

theorem mem_catalogue (domain : Finset Value) (shapes : Finset (Name × Nat)) (name : Name) (values : List Value) :
    (name, values) ∈ catalogue domain shapes ↔
      (name, values.length) ∈ shapes ∧ ∀ value ∈ values, value ∈ domain := by
  constructor
  · intro member
    obtain ⟨⟨head, arity⟩, shape, found⟩ := Finset.mem_biUnion.mp member
    obtain ⟨fields, included, same⟩ := Finset.mem_image.mp found
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
    obtain ⟨length, inside⟩ := (mem_tuples domain arity fields).mp included
    exact ⟨by simpa only [length] using shape, inside⟩
  · rintro ⟨shape, inside⟩
    exact Finset.mem_biUnion.mpr ⟨(name, values.length), shape,
      Finset.mem_image.mpr ⟨values, (mem_tuples _ _ _).mpr ⟨rfl, inside⟩, rfl⟩⟩

theorem catalogue_card_le (domain : Finset Value) (shapes : Finset (Name × Nat)) :
    (catalogue domain shapes).card ≤ ∑ shape ∈ shapes, domain.card ^ shape.2 := by
  apply Finset.card_biUnion_le.trans
  apply Finset.sum_le_sum
  intro shape _
  exact Finset.card_image_le.trans (card_tuples domain shape.2).le

theorem catalogue_card (domain : Finset Value) (shapes : Finset (Name × Nat)) :
    (catalogue domain shapes).card = ∑ shape ∈ shapes, domain.card ^ shape.2 := by
  have selectedShape (shape : Name × Nat) (fact : Name × List Value)
      (member : fact ∈ (tuples domain shape.2).image (fun values => (shape.1, values))) :
      shape = (fact.1, fact.2.length) := by
    obtain ⟨values, inside, rfl⟩ := Finset.mem_image.mp member
    exact Prod.ext rfl ((mem_tuples domain shape.2 values).mp inside).1.symm
  have separate : (shapes : Set (Name × Nat)).PairwiseDisjoint
      (fun shape => (tuples domain shape.2).image fun values => (shape.1, values)) := by
    intro first _ second _ distinct
    apply Finset.disjoint_left.mpr
    intro fact inFirst inSecond
    exact distinct ((selectedShape first fact inFirst).trans (selectedShape second fact inSecond).symm)
  calc
    _ = ∑ shape ∈ shapes, ((tuples domain shape.2).image fun values => (shape.1, values)).card :=
      Finset.card_biUnion separate
    _ = _ := by
      apply Finset.sum_congr rfl
      intro shape _
      rw [Finset.card_image_iff.mpr (fun first _ second _ same => (Prod.mk.inj same).2)]
      exact card_tuples domain shape.2

/-- Validation tests the shape and coordinates, without enumerating the
Cartesian catalogue. A native index may refine these finite membership tests. -/
def contains (domain : Finset Value) (shapes : Finset (Name × Nat)) (fact : Name × List Value) : Bool :=
  decide ((fact.1, fact.2.length) ∈ shapes) && fact.2.all (fun value => decide (value ∈ domain))

theorem contains_iff (domain : Finset Value) (shapes : Finset (Name × Nat)) (fact : Name × List Value) :
    contains domain shapes fact = true ↔ fact ∈ catalogue domain shapes := by
  rw [mem_catalogue]
  simp [contains]

def instantiate (environment : Environment n Value) : List (Cell (Fin n) Value) → Option (List Value)
  | [] => some []
  | .constant value :: rest => (instantiate environment rest).map (value :: ·)
  | .variable name :: rest => do
      let value ← environment name
      let values ← instantiate environment rest
      return value :: values

omit [DecidableEq Value] in
theorem instantiate_iff (environment : Environment n Value) (cells : List (Cell (Fin n) Value)) (values : List Value) :
    instantiate environment cells = some values ↔ List.Forall₂ (holds environment) cells values := by
  induction cells generalizing values with
  | nil => cases values <;> simp [instantiate]
  | cons cell cells ih =>
      cases cell with
      | constant value =>
          cases values <;> simp [instantiate, List.forall₂_cons, holds, ← ih, and_comm]
      | «variable» name =>
          cases found : environment name with
          | none => cases values <;> simp [instantiate, found, List.forall₂_cons, holds]
          | some value =>
              cases rest : instantiate environment cells <;>
                cases values <;> simp [instantiate, found, rest, List.forall₂_cons, holds, ← ih]

omit [DecidableEq Value] in
theorem instantiate_total (environment : Environment n Value)
    (total : ∀ name, ∃ value, environment name = some value) (cells : List (Cell (Fin n) Value)) :
    ∃ values, instantiate environment cells = some values := by
  induction cells with
  | nil => exact ⟨[], rfl⟩
  | cons cell cells ih =>
      obtain ⟨values, found⟩ := ih
      cases cell with
      | constant value => exact ⟨value :: values, by simp [instantiate, found]⟩
      | «variable» name =>
          obtain ⟨value, read⟩ := total name
          exact ⟨value :: values, by simp [instantiate, found, read]⟩

omit [DecidableEq Value] in
theorem instantiate_domain (domain : Finset Value) (environment : Environment n Value)
    (initial : InDomain domain environment) (cells : List (Cell (Fin n) Value)) (values : List Value)
    (constants : ∀ value, Cell.constant value ∈ cells → value ∈ domain)
    (rendered : instantiate environment cells = some values) : ∀ value ∈ values, value ∈ domain := by
  have matched := (instantiate_iff environment cells values).mp rendered
  clear rendered
  revert constants
  induction matched with
  | nil => simp
  | @cons cell value cells values held _ ih =>
      intro constants item member
      rcases List.mem_cons.mp member with same | member
      · subst item
        cases cell with
        | constant literal =>
            change literal = value at held
            subst value
            exact constants literal List.mem_cons_self
        | «variable» name => exact initial name value held
      · exact ih (fun value present => constants value (List.mem_cons_of_mem _ present)) item member

abbrev Head (Name Value : Type) (n : Nat) := Name × List (Cell (Fin n) Value)

def constants (cells : List (Cell (Fin n) Value)) : List Value := cells.filterMap fun cell => match cell with
  | .constant value => some value
  | .variable _ => none

def activeDomain (before : Environment n Value) (factors : List (Factor (Fin n) Value Id))
    (heads : List (Head Name Value n)) : Finset Value :=
  inputDomain before factors ∪ (heads.flatMap fun head => constants head.2).toFinset

def shapes (heads : List (Head Name Value n)) : Finset (Name × Nat) :=
  (heads.map fun head => (head.1, head.2.length)).toFinset

omit [DecidableEq Name] in
theorem activeDomain_captures (before : Environment n Value) (factors : List (Factor (Fin n) Value Id))
    (heads : List (Head Name Value n)) : InDomain (activeDomain before factors heads) before := by
  intro name value found
  exact Finset.mem_union_left _ (inputDomain_captures before factors name value found)

omit [DecidableEq Name] in
theorem activeDomain_rows (before : Environment n Value) (factors : List (Factor (Fin n) Value Id))
    (heads : List (Head Name Value n)) : RowsInDomain (activeDomain before factors heads) factors := by
  intro factor present row stored column
  exact Finset.mem_union_left _ (inputDomain_rows before factors factor present row stored column)

omit [DecidableEq Name] in
theorem activeDomain_constant (before : Environment n Value) (factors : List (Factor (Fin n) Value Id))
    (heads : List (Head Name Value n)) (head : Head Name Value n) (present : head ∈ heads)
    (value : Value) (literal : Cell.constant value ∈ head.2) : value ∈ activeDomain before factors heads := by
  apply Finset.mem_union_right
  apply List.mem_toFinset.mpr
  exact List.mem_flatMap.mpr ⟨head, present, List.mem_filterMap.mpr ⟨.constant value, literal, rfl⟩⟩

/-- A fixed global domain can be reused when every current query row and
captured value stays in it. Head constants are checked independently. -/
theorem run_head_in_catalogue (domain : Finset Value) (shapes : Finset (Name × Nat))
    (before : Environment n Value) (factors : List (Factor (Fin n) Value Id))
    (head : Head Name Value n) (shape : (head.1, head.2.length) ∈ shapes)
    (initial : InDomain domain before) (rows : RowsInDomain domain factors)
    (constants : ∀ value, Cell.constant value ∈ head.2 → value ∈ domain)
    (covered : Covered before factors) (answer : Environment n Value × List Id)
    (produced : answer ∈ ConjunctiveBindingJoin.run before factors) :
    ∃ values, instantiate answer.1 head.2 = some values ∧
      (head.1, values) ∈ catalogue domain shapes := by
  obtain ⟨values, rendered⟩ := instantiate_total answer.1 (covered_results_total before factors covered answer produced) head.2
  have bounded := run_domain domain before factors initial rows answer produced
  have inside := instantiate_domain _ answer.1 bounded head.2 values constants rendered
  have length := ((instantiate_iff answer.1 head.2 values).mp rendered).length_eq
  refine ⟨values, rendered, (mem_catalogue _ _ _ _).mpr ⟨?_, inside⟩⟩
  rw [← length]
  exact shape

/-- The query and authored heads determine their own enclosure. No final
answer enumeration or asserted output-domain theorem is an input. -/
theorem run_head_bounded (before : Environment n Value) (factors : List (Factor (Fin n) Value Id))
    (heads : List (Head Name Value n)) (head : Head Name Value n) (present : head ∈ heads)
    (covered : Covered before factors) (answer : Environment n Value × List Id)
    (produced : answer ∈ ConjunctiveBindingJoin.run before factors) :
    ∃ values, instantiate answer.1 head.2 = some values ∧
      (head.1, values) ∈ catalogue (activeDomain before factors heads) (shapes heads) :=
  run_head_in_catalogue _ _ before factors head
    (List.mem_toFinset.mpr (List.mem_map.mpr ⟨head, present, rfl⟩))
    (activeDomain_captures before factors heads) (activeDomain_rows before factors heads)
    (activeDomain_constant before factors heads head present) covered answer produced

end Mettapedia.GSLT.Dynamics.ConjunctiveOutputDomain
