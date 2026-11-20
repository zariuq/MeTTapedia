import Mathlib.Data.List.TakeDrop

/-!
# Sized append views for exact registered replay caches

This representation is used by proof construction. Each leaf retains its
actual Array and a checked size; branch indices retain subtree sizes without
traversing theorem payloads. The balanced builder preserves the exact Array,
its order, duplicate entries and physical addresses. Its lookup work counts
tree descents, with one Array lookup at a leaf; it is not a machine-time or
allocation model for the native receiver.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.ReplayCacheViews

universe u
variable {α : Type u}

structure Block (α : Type u) where
  values : Array α
  count : Nat
  sized : values.size = count

def Block.ofArray (values : Array α) : Block α := ⟨values, values.size, rfl⟩

inductive View (α : Type u) : Nat → Type u
  | leaf (block : Block α) : View α block.count
  | append {leftSize rightSize : Nat} (left : View α leftSize) (right : View α rightSize) :
      View α (leftSize + rightSize)

namespace View

def values : {size : Nat} → View α size → Array α
  | _, .leaf block => block.values
  | _, .append left right => values left ++ values right

@[simp] theorem values_size {size : Nat} (view : View α size) : view.values.size = size := by
  induction view with
  | leaf block => exact block.sized
  | append _ _ left right => simp only [values, Array.size_append, left, right]

def height : {size : Nat} → View α size → Nat
  | _, .leaf _ => 1
  | _, .append left right => max left.height right.height + 1

def read? : {size : Nat} → View α size → Nat → Option α
  | _, .leaf block, index => block.values[index]?
  | _, @View.append _ leftSize _ left right, index =>
      if index < leftSize then left.read? index else right.read? (index - leftSize)

def readWork : {size : Nat} → View α size → Nat → Nat
  | _, .leaf _, _ => 1
  | _, @View.append _ leftSize _ left right, index =>
      (if index < leftSize then left.readWork index else right.readWork (index - leftSize)) + 1

theorem read_values {size : Nat} (view : View α size) (index : Nat) :
    view.read? index = view.values[index]? := by
  induction view generalizing index with
  | leaf _ => rfl
  | @append leftSize rightSize left right leftIH rightIH =>
      simp only [read?, values, Array.getElem?_append, values_size]
      split
      · exact leftIH index
      · exact rightIH (index - leftSize)

theorem readWork_le_height {size : Nat} (view : View α size) (index : Nat) :
    view.readWork index ≤ view.height := by
  induction view generalizing index with
  | leaf _ => exact Nat.le_refl _
  | @append leftSize rightSize left right leftIH rightIH =>
      simp only [readWork, height]
      split
      · exact Nat.add_le_add_right (Nat.le_trans (leftIH index) (Nat.le_max_left _ _)) 1
      · exact Nat.add_le_add_right (Nat.le_trans (rightIH (index - leftSize)) (Nat.le_max_right _ _)) 1

/-- Proof generators may reassociate append nodes using this equality;
no theorem payload is traversed and no address is permuted. -/
theorem reassociate {firstSize secondSize thirdSize : Nat}
    (first : View α firstSize) (second : View α secondSize) (third : View α thirdSize) :
    (View.append (View.append first second) third).values =
      (View.append first (View.append second third)).values :=
  Array.append_assoc

def select? {size : Nat} (view : View α size) : List Nat → Option (List α)
  | [] => some []
  | index :: later => do
      let value ← view.read? index
      let values ← view.select? later
      return value :: values

def selectionWork {size : Nat} (view : View α size) (indices : List Nat) : Nat :=
  (indices.map (fun index => view.readWork index)).sum

theorem selectionWork_le {size : Nat} (view : View α size) (indices : List Nat) :
    view.selectionWork indices ≤ indices.length * view.height := by
  induction indices with
  | nil =>
      simpa only [selectionWork, List.map_nil, List.sum_nil, List.length_nil, Nat.zero_mul] using
        (Nat.le_refl 0)
  | cons index later ih =>
      change view.readWork index + view.selectionWork later ≤ (later.length + 1) * view.height
      have one := view.readWork_le_height index
      rw [Nat.add_mul, Nat.one_mul]
      omega

end View

abbrev Packed (α : Type u) := Sigma (View α)

def blockValues (blocks : List (Block α)) : Array α :=
  blocks.foldr (fun block rest => block.values ++ rest) #[]

theorem blockValues_append (first second : List (Block α)) :
    blockValues (first ++ second) = blockValues first ++ blockValues second := by
  induction first with
  | nil => simp [blockValues]
  | cons block rest ih =>
      simp only [List.cons_append, blockValues, List.foldr_cons] at ih ⊢
      rw [ih, Array.append_assoc]

def build (blocks : List (Block α)) : Packed α :=
  match blocks with
  | [] => ⟨0, .leaf ⟨#[], 0, rfl⟩⟩
  | [block] => ⟨block.count, .leaf block⟩
  | first :: second :: rest =>
      let all := first :: second :: rest
      let middle := all.length / 2
      let left := build (all.take middle)
      let right := build (all.drop middle)
      ⟨left.1 + right.1, .append left.2 right.2⟩
termination_by blocks.length
decreasing_by all_goals simp_wf; all_goals omega

theorem build_values (blocks : List (Block α)) : (build blocks).2.values = blockValues blocks := by
  match blocks with
  | [] => rw [build]; rfl
  | [block] =>
      rw [build]
      simp only [View.values, blockValues, List.foldr_cons, List.foldr_nil, Array.append_empty]
  | first :: second :: rest =>
      rw [build]
      change (build ((first :: second :: rest).take ((first :: second :: rest).length / 2))).2.values ++
        (build ((first :: second :: rest).drop ((first :: second :: rest).length / 2))).2.values = _
      rw [build_values, build_values, ← blockValues_append, List.take_append_drop]
termination_by blocks.length
decreasing_by all_goals simp_wf; all_goals omega

theorem build_size (blocks : List (Block α)) : (build blocks).1 = (blockValues blocks).size := by
  rw [← build_values, View.values_size]

theorem build_height_le (level : Nat) (blocks : List (Block α))
    (bounded : blocks.length ≤ 2 ^ level) : (build blocks).2.height ≤ level + 1 := by
  induction level generalizing blocks with
  | zero =>
      cases blocks with
      | nil => rw [build]; exact Nat.le_refl _
      | cons first rest =>
          cases rest with
          | nil => rw [build]; exact Nat.le_refl _
          | cons _ _ => simp at bounded
  | succ level ih =>
      cases blocks with
      | nil => rw [build]; change 1 ≤ level + 1 + 1; omega
      | cons first rest =>
          cases rest with
          | nil => rw [build]; change 1 ≤ level + 1 + 1; omega
          | cons second rest =>
              let all := first :: second :: rest
              have total : all.length ≤ 2 * 2 ^ level := by
                simpa only [all, Nat.pow_succ, Nat.mul_comm] using bounded
              have leftBound : (all.take (all.length / 2)).length ≤ 2 ^ level := by
                rw [List.length_take]
                omega
              have rightBound : (all.drop (all.length / 2)).length ≤ 2 ^ level := by
                rw [List.length_drop]
                omega
              have left := ih (all.take (all.length / 2)) leftBound
              have right := ih (all.drop (all.length / 2)) rightBound
              rw [build]
              change max (build (all.take (all.length / 2))).2.height
                (build (all.drop (all.length / 2))).2.height + 1 ≤ _
              have both := Nat.max_le.mpr ⟨left, right⟩
              omega

theorem build_read (blocks : List (Block α)) (index : Nat) :
    (build blocks).2.read? index = (blockValues blocks)[index]? := by
  rw [View.read_values, build_values]

theorem build_readWork_le (level : Nat) (blocks : List (Block α))
    (bounded : blocks.length ≤ 2 ^ level) (index : Nat) :
    (build blocks).2.readWork index ≤ level + 1 :=
  Nat.le_trans (View.readWork_le_height _ _) (build_height_le level blocks bounded)

/-- Rebalancing after append retains the exact cache extension used by the
registered checker, including multi-output declaration blocks. -/
theorem build_append_values (blocks : List (Block α)) (next : Block α) :
    (build (blocks ++ [next])).2.values = (build blocks).2.values ++ next.values := by
  rw [build_values, blockValues_append, build_values]
  simp only [blockValues, List.foldr_cons, List.foldr_nil, Array.append_empty]

namespace Controls

def blocks : List (Block Nat) :=
  [Block.ofArray #[7, 7], Block.ofArray #[], Block.ofArray #[11], Block.ofArray #[13, 17]]

theorem actual_order_and_duplicates : (build blocks).2.values = #[7, 7, 11, 13, 17] := by
  rw [build_values]
  decide

theorem actual_physical_addresses :
    (build blocks).2.read? 0 = some 7 ∧ (build blocks).2.read? 1 = some 7 ∧
      (build blocks).2.read? 3 = some 13 ∧ (build blocks).2.read? 5 = none := by
  simp only [build_read]
  decide

theorem actual_bounded_descents :
    (build blocks).2.readWork 3 = 3 ∧ (build blocks).2.height = 3 := by decide +kernel

theorem appended_two_outputs :
    (build (blocks ++ [Block.ofArray #[19, 23]])).2.read? 5 = some 19 ∧
      (build (blocks ++ [Block.ofArray #[19, 23]])).2.read? 6 = some 23 := by
  simp only [build_read]
  decide

theorem reversing_blocks_changes_addresses :
    (build blocks.reverse).2.read? 0 ≠ (build blocks).2.read? 0 := by
  simp only [build_read]
  decide

end Controls

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.ReplayCacheViews

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.ReplayCacheViews.build_values
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.ReplayCacheViews.build_height_le
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.ReplayCacheViews.build_read
