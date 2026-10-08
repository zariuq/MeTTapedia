import Mettapedia.SetTheory.CarveOuts.WellFoundedBubble

/-!
# The hyperset values of two finite graphs

* **The ordinal three as a graph.** On the nodes `0, 1, 2` with an edge from `a` to `b`
  whenever `b < a` (edges `1 → 0`, `2 → 0`, `2 → 1`), every node is well-founded and the
  hyperset decoration sends the nodes to the ordinals `0`, `1`, `2`; at the point `2` it is
  `{∅, {∅}}` (`decorate_ordTwo_two`). The value is obtained from the `ZFSet` decoration through
  the agreement of Foundation and Aczel on well-founded graphs (`decorate_eq_ofZFSet`).
* **The nest.** The node `blank` decorates to `∅` (`decorate_nest_blank`); the node `point`
  decorates to a hyperset `x` with `x = {∅, x}` (`decorate_nest_point`), the only such
  hyperset (`eq_decorate_nest_point`). It is not well-founded (`not_wf_decorate_nest_point`),
  and it is neither `∅` nor the Quine atom (`decorate_nest_point_ne_empty`,
  `decorate_nest_point_ne_quineAtom`).
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.CarveOuts

open Mettapedia.SetTheory.AntiFoundation
open Mettapedia.TypeTheory.MaterialSets
open Mettapedia.TypeTheory.MaterialSets.Hypersets

/-! ## The ordinal three -/

/-- An edge from `a` to `b` exactly when `b < a`. -/
def ordTwoEdge : Fin 3 → Fin 3 → Prop :=
  fun a b => b < a

/-- The `ZFSet` decoration: the ordinals `0`, `1`, `2`. -/
def ordTwoZF : Fin 3 → ZFSet.{0}
  | 0 => ∅
  | 1 => {∅}
  | 2 => {∅, {∅}}

theorem ordTwo_acc (a : Fin 3) : Acc (flip ordTwoEdge) a :=
  wellFounded_lt.apply a

theorem ordTwoZF_decorates : Decorates ordTwoEdge (fun x y : ZFSet.{0} => x ∈ y) ordTwoZF := by
  intro a z
  show z ∈ ordTwoZF a ↔ ∃ b, b < a ∧ z = ordTwoZF b
  match a with
  | 0 =>
    constructor
    · intro h
      exact absurd h (ZFSet.notMem_empty z)
    · rintro ⟨b, hb, _⟩
      exact absurd hb (Fin.not_lt_zero b)
  | 1 =>
    show z ∈ ({∅} : ZFSet.{0}) ↔ _
    rw [ZFSet.mem_singleton]
    constructor
    · rintro rfl
      exact ⟨0, by decide, rfl⟩
    · rintro ⟨b, hb, rfl⟩
      match b with
      | 0 => rfl
      | 1 => exact absurd hb (by decide)
      | 2 => exact absurd hb (by decide)
  | 2 =>
    show z ∈ ({∅, {∅}} : ZFSet.{0}) ↔ _
    rw [ZFSet.mem_insert_iff, ZFSet.mem_singleton]
    constructor
    · rintro (rfl | rfl)
      · exact ⟨0, by decide, rfl⟩
      · exact ⟨1, by decide, rfl⟩
    · rintro ⟨b, hb, rfl⟩
      match b with
      | 0 => exact Or.inl rfl
      | 1 => exact Or.inr rfl
      | 2 => exact absurd hb (by decide)

/-- The hyperset of each node is the `ZFSet` ordinal, read as a hyperset. -/
theorem decorate_ordTwo (a : Fin 3) :
    HSet.decorate ordTwoEdge a = HSet.ofZFSet (ordTwoZF a) :=
  (decorate_eq_ofZFSet ordTwoZF_decorates (ordTwo_acc a)).symm

/-- **The point of the three-node graph decorates to `{∅, {∅}}`.** -/
theorem decorate_ordTwo_two :
    HSet.decorate ordTwoEdge 2 = ({∅, {∅}} : HSet.{0}) := by
  rw [decorate_ordTwo]
  show HSet.ofZFSet {∅, {∅}} = _
  rw [HSet.ofZFSet_pair, HSet.ofZFSet_singleton, HSet.ofZFSet_empty]

theorem wf_decorate_ordTwo (a : Fin 3) : (HSet.decorate ordTwoEdge a).WF :=
  HSet.wf_decorate_iff.mpr (ordTwo_acc a)

/-! ## The nest -/

theorem decorate_nest_blank : HSet.decorate nestEdge Nest.blank = (∅ : HSet.{0}) := by
  rw [HSet.eq_empty_iff]
  intro z hz
  obtain ⟨b, hb, _⟩ := HSet.mem_decorate.mp hz
  exact hb

/-- **The nest decorates to `x = {∅, x}`.** -/
theorem decorate_nest_point :
    HSet.decorate nestEdge Nest.point =
      ({∅, HSet.decorate nestEdge Nest.point} : HSet.{0}) := by
  apply HSet.ext
  intro z
  rw [HSet.mem_decorate, HSet.mem_insert_iff, HSet.mem_singleton]
  constructor
  · rintro ⟨b, _, rfl⟩
    cases b
    · exact Or.inl decorate_nest_blank
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨Nest.blank, trivial, decorate_nest_blank⟩
    · exact ⟨Nest.point, trivial, rfl⟩

/-- The nest is the only hyperset `x` with `x = {∅, x}`. -/
theorem eq_decorate_nest_point {y : HSet.{0}} (h : y = {∅, y}) :
    y = HSet.decorate nestEdge Nest.point := by
  let d : Nest → HSet.{0} := fun n => match n with
    | .blank => ∅
    | .point => y
  have hd : HSet.IsDecoration nestEdge d := by
    intro a z
    cases a
    · constructor
      · intro hz
        exact absurd hz (HSet.notMem_empty z)
      · rintro ⟨b, hb, _⟩
        exact hb.elim
    · show z ∈ y ↔ _
      rw [h, HSet.mem_insert_iff, HSet.mem_singleton]
      constructor
      · rintro (rfl | rfl)
        · exact ⟨Nest.blank, trivial, rfl⟩
        · exact ⟨Nest.point, trivial, rfl⟩
      · rintro ⟨b, _, rfl⟩
        cases b
        · exact Or.inl rfl
        · exact Or.inr rfl
  exact congrFun hd.eq_decorate Nest.point

theorem not_wf_decorate_nest_point : ¬ (HSet.decorate nestEdge Nest.point).WF :=
  HSet.not_wf_of_mem_self (HSet.decorate_mem_decorate (r := nestEdge) (a := Nest.point)
    (b := Nest.point) trivial)

theorem decorate_nest_point_ne_empty : HSet.decorate nestEdge Nest.point ≠ (∅ : HSet.{0}) :=
  fun h => HSet.notMem_empty _
    (h ▸ HSet.decorate_mem_decorate (r := nestEdge) (a := Nest.point) (b := Nest.point) trivial)

theorem decorate_nest_point_ne_quineAtom :
    HSet.decorate nestEdge Nest.point ≠ HSet.quineAtom.{0} := by
  intro h
  have hmem : (∅ : HSet.{0}) ∈ HSet.decorate nestEdge Nest.point := by
    rw [decorate_nest_point, HSet.mem_insert_iff]
    exact Or.inl rfl
  rw [h, HSet.mem_quineAtom] at hmem
  exact HSet.empty_ne_quineAtom hmem

end Mettapedia.SetTheory.CarveOuts
