import Mettapedia.Machines.CMemory.Examples
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# Fractional permissions for shared reading

Boyland's fractional permissions ("Checking Interference with Fractional
Permissions", SAS 2003): a permission on one cell is an amount in `(0, 1]`
together with the content it sees.  Two shares are separate when their amounts
add up to at most `1` and they see the same content.  The amount `1` is the
whole permission: it may write and free.  Any positive amount may read.

`Frac C` is a separation algebra and a `CellPermission`, so the block heap
`Heap (Frac (Option V))`, the seven primitives, their locality and the frame
rule all apply to it unchanged: they were proved once for every cell
permission algebra.

## Examples

* **Positive.**  A whole points-to splits into two halves
  (`pointsTo_eq_halves`), and a half is enough to load (`load_half`).
* **Negative.**  A half is not enough to store (`store_half_undefined`); a half
  and the whole are not separate (`half_not_separate_whole`); two halves that
  see different contents are not separate (`halves_disagree_not_separate`).
-/

set_option autoImplicit false

namespace Mettapedia.Machines.CMemory

open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open scoped Mettapedia.GSLT.SeparationAlgebra
open CellPermission

universe v

/-- **Fractional permissions** on one cell: no share, or a share of a positive
amount that sees a content. -/
inductive Frac (C : Type v) where
  | none
  | share (amount : ℚ) (positive : 0 < amount) (content : C)

namespace Frac

variable {C : Type v}

instance : Zero (Frac C) := ⟨.none⟩

/-- Shares add their amounts. -/
def add : Frac C → Frac C → Frac C
  | .none, y => y
  | .share a positive c, .none => .share a positive c
  | .share a positiveA c, .share b positiveB _ => .share (a + b) (add_pos positiveA positiveB) c

instance : Add (Frac C) := ⟨add⟩

/-- Two shares are separate when they add up to at most the whole and see the
same content. -/
def Separate : Frac C → Frac C → Prop
  | .share a _ c, .share b _ d => a + b ≤ 1 ∧ c = d
  | _, _ => True

theorem share_eq {a b : ℚ} {positiveA : 0 < a} {positiveB : 0 < b} {c d : C}
    (amounts : a = b) (contents : c = d) :
    Frac.share a positiveA c = Frac.share b positiveB d := by
  subst amounts
  subst contents
  rfl

theorem share_add_share (a b : ℚ) (positiveA : 0 < a) (positiveB : 0 < b) (c d : C) :
    Frac.share a positiveA c + Frac.share b positiveB d =
      Frac.share (a + b) (add_pos positiveA positiveB) c := rfl

instance instSepAlgebra : SepAlgebra (Frac C) where
  Separate := Separate
  separate_zero x := by cases x <;> trivial
  separate_symm := by
    rintro (_ | ⟨a, _, c⟩) (_ | ⟨b, _, d⟩) separate <;> try trivial
    exact ⟨by rw [add_comm]; exact separate.1, separate.2.symm⟩
  add_zero x := by cases x <;> rfl
  add_comm := by
    rintro (_ | ⟨a, _, c⟩) (_ | ⟨b, _, d⟩) separate <;> try rfl
    exact share_eq (add_comm a b) separate.2
  add_assoc := by
    rintro (_ | ⟨a, _, c⟩) (_ | ⟨b, _, d⟩) (_ | ⟨e, _, f⟩) - - - <;> try rfl
    exact share_eq (add_assoc a b e) rfl
  separate_of_separate_add := by
    rintro (_ | ⟨a, _, c⟩) (_ | ⟨b, positiveB, d⟩) (_ | ⟨e, positiveE, f⟩) separate - <;>
      try trivial
    obtain ⟨sum, same⟩ := separate
    exact ⟨by change a + (b + e) ≤ 1 at sum; linarith, same⟩
  separate_add_of_separate_add := by
    rintro (_ | ⟨a, _, c⟩) (_ | ⟨b, _, d⟩) (_ | ⟨e, _, f⟩) separate separateParts <;>
      try trivial
    obtain ⟨sum, same⟩ := separate
    exact ⟨by change a + (b + e) ≤ 1 at sum; linarith,
      same.trans separateParts.2⟩

/-- Half of the whole permission. -/
def half (c : C) : Frac C := .share (1 / 2) (by norm_num) c

instance instCellPermission : CellPermission (Frac C) C where
  read x := match x with
    | .none => Option.none
    | .share _ _ c => some c
  whole c := .share 1 one_pos c
  read_whole _ := rfl
  read_zero := rfl
  read_add := by
    rintro (_ | ⟨a, _, c⟩) (_ | ⟨b, _, d⟩) e - read
    · cases read
    · cases read
    · exact read
    · exact read
  eq_zero_of_whole_separate := by
    rintro c (_ | ⟨b, positive, d⟩) separate
    · rfl
    · have := separate.1
      linarith
  eq_zero_of_add_eq_zero := by
    rintro (_ | ⟨a, _, c⟩) (_ | ⟨b, _, d⟩) - sum
    · rfl
    · rfl
    · cases sum
    · cases sum

theorem whole_eq (c : C) : (whole c : Frac C) = .share 1 one_pos c := rfl

/-- **The whole permission splits into two halves**, which are separate. -/
theorem whole_eq_half_add_half (c : C) :
    half c ## half c ∧ (whole c : Frac C) = half c + half c := by
  refine ⟨⟨by norm_num, rfl⟩, ?_⟩
  rw [whole_eq, half, share_add_share]
  exact share_eq (by norm_num) rfl

theorem read_half (c : C) : read (half c) = some c := rfl

theorem half_ne_whole (c c' : C) : half c ≠ whole c' := by
  rw [whole_eq, half]
  intro same
  injection same with amounts
  norm_num at amounts

end Frac

/-! ## Shared reading on the fractional heap -/

section Shared

variable {V : Type}

open Frac

/-- **Positive control**: a whole points-to is two half points-to facts. -/
theorem pointsTo_eq_halves (p : Ptr) (v : V) :
    PointsTo (L := Frac (Option V)) p v =
      (PointsToPerm p (half (some v)) ∗ PointsToPerm p (half (some v))) := by
  funext σ
  apply propext
  obtain ⟨separate, sum⟩ := whole_eq_half_add_half (some v)
  have cells : segment p.offset [half (some v)] ## segment p.offset [half (some v)] ∧
      segment p.offset [half (some v)] + segment p.offset [half (some v)] =
        segment p.offset [(whole (some v) : Frac (Option V))] := by
    simp only [segment_singleton]
    constructor
    · intro i
      by_cases same : i = p.offset
      · subst i
        simpa only [Function.update_self] using separate
      · simp only [Function.update_of_ne same]
        exact SepAlgebra.separate_zero _
    · funext i
      by_cases same : i = p.offset
      · subst i
        simp only [Pi.add_apply, Function.update_self, sum]
      · simp only [Pi.add_apply, Function.update_of_ne same]
        exact SepAlgebra.add_zero _
  have left : PointsToPerm (L := Frac (Option V)) p (half (some v)) =
      fun σ => σ = atBlock p.block (.empty, segment p.offset [half (some v)]) := rfl
  rw [left, sepConj_atBlock_iff]
  simp only [PointsTo, Cells, List.map_cons, List.map_nil]
  constructor
  · rintro rfl
    exact ⟨⟨Or.inl rfl, cells.1⟩, by rw [← cells.2]; rfl⟩
  · rintro ⟨-, rfl⟩
    rw [← cells.2]
    rfl

theorem cell_of_pointsToPerm {p : Ptr} {x : Frac (Option V)} {σ : Heap (Frac (Option V))}
    (holds : PointsToPerm p x σ) : (σ p.block).2 p.offset = x := by
  subst holds
  simpa using segment_at (L := Frac (Option V)) p.offset [x] (k := 0) (by simp)

/-- **Positive control**: half a permission is enough to load. -/
theorem load_half (p : Ptr) (v : V) :
    CTriple (L := Frac (Option V)) (PointsToPerm p (half (some v))) (CProg.load p)
      (fun r σ => r = v ∧ PointsToPerm p (half (some v)) σ) :=
  load_rule fun σ holds => by rw [cell_of_pointsToPerm holds]; rfl

/-- **Negative control**: half a permission is not enough to store. -/
theorem store_half_undefined (p : Ptr) (v w : V) (σ : Heap (Frac (Option V)))
    (holds : PointsToPerm p (half (some v)) σ) :
    ¬ (CProg.store p w).Safe act σ := by
  rintro ⟨⟨c, whole_at⟩, -⟩
  rw [cell_of_pointsToPerm holds] at whole_at
  exact half_ne_whole _ _ whole_at

/-- **Negative control**: a half and the whole together exceed the whole. -/
theorem half_not_separate_whole (c c' : Option V) :
    ¬ (half c ## (whole c' : Frac (Option V))) := by
  rintro ⟨sum, -⟩
  norm_num at sum

/-- **Negative control**: two halves that see different contents are not
separate. -/
theorem halves_disagree_not_separate (c c' : Option V) (different : c ≠ c') :
    ¬ (half c ## half c') :=
  fun ⟨_, same⟩ => different same

end Shared

end Mettapedia.Machines.CMemory
