import Mettapedia.OSLF.Syntax.BindingScopePullback
import Mettapedia.OSLF.Syntax.BindingContextRows
import Mathlib.Data.Finset.Sort
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Computing variable pullbacks from finite context maps

The candidates are pairs of finite declaration positions with the same ambient
position. Each ambient position determines its declared sort, so this finite
computation needs no equality decision on the sort carrier. Sorting the
compatible index pairs gives a duplicate-free declaration table.

The constructed table supplies the complete variable pullback, including
recovery and its inverse laws. The binding-term pullback laws therefore apply
to arbitrary finite parameter maps, rather than only a supplied example.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.ScopePullback.Finite

open ContextPositions

variable {S : Signature} {L R Γ : Ctx S}
  (left : Ren S L Γ) (right : Ren S R Γ)

abbrev Pair := { slots : Fin L.length × Fin R.length //
  CommonABT.index (left _ (ofSlot L slots.1)) = CommonABT.index (right _ (ofSlot R slots.2)) }

instance : Fintype (Pair left right) := inferInstanceAs (Fintype (Subtype _))

def rank (pair : Pair left right) : Fin (L.length * R.length) := finProdFinEquiv pair.val

theorem rank_injective : Function.Injective (rank left right) :=
  fun _ _ same => Subtype.ext (finProdFinEquiv.injective same)

abbrev precedes (first second : Pair left right) : Prop := rank left right first ≤ rank left right second

instance : DecidableRel (precedes left right) := fun _ _ => inferInstance
instance : IsTrans (Pair left right) (precedes left right) := ⟨fun _ _ _ first second => le_trans first second⟩
instance : Std.Antisymm (precedes left right) :=
  ⟨fun _ _ first second => rank_injective left right (le_antisymm first second)⟩
instance : Std.Total (precedes left right) := ⟨fun _ _ => le_total _ _⟩

def rows : List (Pair left right) := Finset.univ.sort (precedes left right)

theorem rows_distinct : (rows left right).Nodup := Finset.sort_nodup _ _

theorem pair_mem (pair : Pair left right) : pair ∈ rows left right := by simp [rows]

abbrev sortOf (pair : Pair left right) : S.Srt := L.get pair.val.1

def leftValue (pair : Pair left right) : Var L (sortOf left right pair) := ofSlot L pair.val.1

theorem pair_sort (pair : Pair left right) : L.get pair.val.1 = R.get pair.val.2 :=
  sort_eq_of_equal_index (left _ (ofSlot L pair.val.1)) (right _ (ofSlot R pair.val.2)) pair.property

def rightValue (pair : Pair left right) : Var R (sortOf left right pair) :=
  castSort (pair_sort left right pair).symm (ofSlot R pair.val.2)

theorem left_index (pair : Pair left right) : CommonABT.index (leftValue left right pair) = pair.val.1.val :=
  index_ofSlot L pair.val.1

theorem right_index (pair : Pair left right) : CommonABT.index (rightValue left right pair) = pair.val.2.val := by
  exact (index_castSort (S := S) (pair_sort left right pair).symm (ofSlot R pair.val.2)).trans
    (index_ofSlot R pair.val.2)

theorem ambient_values_agree (pair : Pair left right) :
    left _ (leftValue left right pair) = right _ (rightValue left right pair) := by
  apply CommonABT.index_injective (S := S)
  change CommonABT.index (left _ (ofSlot L pair.val.1)) =
    CommonABT.index (right _ (castSort (pair_sort left right pair).symm (ofSlot R pair.val.2)))
  rw [map_castSort (S := S) right (pair_sort left right pair).symm (ofSlot R pair.val.2), index_castSort]
  exact pair.property

abbrev fromVariables {sort : S.Srt} (first : Var L sort) (second : Var R sort)
    (same : left sort first = right sort second) : Pair left right :=
  ⟨(toSlot first, toSlot second), (map_index_ofSlot left first).trans
    ((congrArg (CommonABT.index (S := S)) same).trans (map_index_ofSlot right second).symm)⟩

abbrev context : Ctx S := ContextRows.context (sortOf left right) (rows left right)

def toLeft : Ren S (context left right) L :=
  ContextRows.project (sortOf left right) (rows left right) (leftValue left right)

def toRight : Ren S (context left right) R :=
  ContextRows.project (sortOf left right) (rows left right) (rightValue left right)

theorem commutes (sort : S.Srt) (position : Var (context left right) sort) :
    left sort (toLeft left right sort position) = right sort (toRight left right sort position) := by
  let row := ContextRows.rowAt (sortOf left right) (rows left right) position
  let recorded := ContextRows.rowSort (sortOf left right) (rows left right) position
  change left sort (castSort recorded (leftValue left right row)) =
    right sort (castSort recorded (rightValue left right row))
  rw [map_castSort (S := S) left recorded, map_castSort (S := S) right recorded]
  exact congrArg (castSort recorded) (ambient_values_agree left right row)

def recover (sort : S.Srt) (first : Var L sort) (second : Var R sort)
    (same : left sort first = right sort second) : Var (context left right) sort :=
  castSort (slot_sort first)
    (ContextRows.select (sortOf left right) (rows left right) (fromVariables left right first second same)
      (pair_mem left right _))

theorem recover_left (sort : S.Srt) (first : Var L sort) (second : Var R sort)
    (same : left sort first = right sort second) :
    toLeft left right sort (recover left right sort first second same) = first := by
  let pair := fromVariables left right first second same
  have selected := ContextRows.project_select (sortOf left right) (rows left right) (leftValue left right)
    pair (pair_mem left right pair)
  have lifted := map_castSort_heq (S := S) (toLeft left right) (slot_sort first)
    (ContextRows.select (sortOf left right) (rows left right) pair (pair_mem left right pair))
  exact eq_of_heq (lifted.trans (selected.heq.trans (ofSlot_toSlot_heq first)))

theorem recover_right (sort : S.Srt) (first : Var L sort) (second : Var R sort)
    (same : left sort first = right sort second) :
    toRight left right sort (recover left right sort first second same) = second := by
  let pair := fromVariables left right first second same
  have selected := ContextRows.project_select (sortOf left right) (rows left right) (rightValue left right)
    pair (pair_mem left right pair)
  have lifted := map_castSort_heq (S := S) (toRight left right) (slot_sort first)
    (ContextRows.select (sortOf left right) (rows left right) pair (pair_mem left right pair))
  have original : HEq (rightValue left right pair) second :=
    (castSort_heq _ _).trans (ofSlot_toSlot_heq second)
  exact eq_of_heq (lifted.trans (selected.heq.trans original))

theorem from_projected {sort : S.Srt} (position : Var (context left right) sort)
    (same : left sort (toLeft left right sort position) = right sort (toRight left right sort position)) :
    fromVariables left right (toLeft left right sort position) (toRight left right sort position) same =
      ContextRows.rowAt (sortOf left right) (rows left right) position := by
  apply Subtype.ext
  apply Prod.ext
  · apply Fin.ext
    change CommonABT.index (toLeft left right sort position) = _
    rw [toLeft, ContextRows.index_project]
    exact left_index left right _
  · apply Fin.ext
    change CommonABT.index (toRight left right sort position) = _
    rw [toRight, ContextRows.index_project]
    exact right_index left right _

theorem recover_pair (sort : S.Srt) (position : Var (context left right) sort)
    (same : left sort (toLeft left right sort position) = right sort (toRight left right sort position)) :
    recover left right sort (toLeft left right sort position) (toRight left right sort position) same = position := by
  apply CommonABT.index_injective (S := S)
  have indexRecovered := index_castSort (S := S) (slot_sort (toLeft left right sort position))
    (ContextRows.select (sortOf left right) (rows left right)
      (fromVariables left right (toLeft left right sort position) (toRight left right sort position) same)
      (pair_mem left right _))
  change CommonABT.index (castSort _ _) = _
  rw [indexRecovered, ContextRows.index_select, from_projected]
  have restored := ContextRows.index_select_rowAt (sortOf left right) (rows left right)
    (rows_distinct left right) position
  simpa only [ContextRows.index_select] using restored

/-- A computable pullback of arbitrary finite typed context maps. -/
def build : Mettapedia.OSLF.Binding.ScopePullback left right where
  context := context left right
  toLeft := toLeft left right
  toRight := toRight left right
  commutes := commutes left right
  recover := recover left right
  recover_left := recover_left left right
  recover_right := recover_right left right
  recover_pair := fun sort position => recover_pair left right sort position (commutes left right sort position)

end Mettapedia.OSLF.Binding.ScopePullback.Finite
