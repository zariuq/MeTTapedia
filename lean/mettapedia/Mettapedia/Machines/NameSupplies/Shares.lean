import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic

/-!
# Shares of the unit interval: the identities of interval tree clocks

An interval tree clock (Almeida, Baquero and Fonte, *Interval Tree Clocks*, OPODIS 2008) gives each
live participant an *identity*: a share of the unit interval, written as a tree whose leaves own
none or all of their part.  Forking a participant splits its share into two disjoint halves; joining
two participants takes the union of their shares.  So shares of live participants stay disjoint,
and a share split and joined again comes back to itself.

A point of the interval is an infinite binary sequence (`ℕ → Bool`), and a node sends a point to
its left or right half by its first bit.

* `owns_join`: a join owns exactly the points of either share.
* `owns_split`, `split_disjoint`: the two halves of a split own exactly the points of the share,
  and no point twice.
* `Normal`: no node has two empty or two full halves.  Joins and splits keep shares normal, a
  normal share owns a point exactly when it is not `none` (`normal_nonempty_iff`), and the halves of
  a nonempty normal share are nonempty (`split_normal`).
* `join_split`: joining the two halves of a normal share gives the share back.
* `piece`: the share of component `i` of `k` components, by repeated splitting: pieces are parts of
  the share (`piece_owns`), pairwise disjoint (`pieces_disjoint`), normal and nonempty
  (`piece_normal`).
* `size`: the number of nodes; shares of bounded size are finitely many (`finite_size_le`).
-/

set_option autoImplicit false

namespace Mettapedia.Machines.NameSupplies

/-- A share of the unit interval: none of it, all of it, or a share of each half. -/
inductive Share where
  | none
  | all
  | node (left right : Share)
  deriving DecidableEq, Repr

namespace Share

/-- A point after its first bit. -/
def tail (point : ℕ → Bool) : ℕ → Bool := fun n => point (n + 1)

/-- The point with first bit `bit`, then `point`. -/
def push (bit : Bool) (point : ℕ → Bool) : ℕ → Bool
  | 0 => bit
  | n + 1 => point n

@[simp] theorem push_zero (bit : Bool) (point : ℕ → Bool) : push bit point 0 = bit := rfl

@[simp] theorem tail_push (bit : Bool) (point : ℕ → Bool) : tail (push bit point) = point := rfl

/-- The points a share owns. -/
def Owns : Share → (ℕ → Bool) → Prop
  | none, _ => False
  | all, _ => True
  | node left right, point => cond (point 0) (right.Owns (tail point)) (left.Owns (tail point))

/-- Two shares overlap when some point is owned by both. -/
def Overlap (first second : Share) : Prop := ∃ point, first.Owns point ∧ second.Owns point

theorem Overlap.symm {first second : Share} (overlap : Overlap first second) :
    Overlap second first :=
  let ⟨point, inFirst, inSecond⟩ := overlap
  ⟨point, inSecond, inFirst⟩

theorem overlap_comm (first second : Share) : Overlap first second ↔ Overlap second first :=
  ⟨Overlap.symm, Overlap.symm⟩

/-- A node, collapsing two empty halves to `none` and two full halves to `all`. -/
def node' : Share → Share → Share
  | none, none => none
  | all, all => all
  | left, right => node left right

theorem owns_node' (left right : Share) (point : ℕ → Bool) :
    (node' left right).Owns point ↔ (node left right).Owns point := by
  cases left <;> cases right <;> cases point 0 <;> simp [node', Owns, *]

/-- **Join**: the union of two shares. -/
def join : Share → Share → Share
  | none, second => second
  | first, none => first
  | all, _ => all
  | _, all => all
  | node left right, node left' right' => node' (join left left') (join right right')

@[simp] theorem join_none (share : Share) : join share none = share := by
  cases share <;> rfl

@[simp] theorem all_join (share : Share) : join all share = all := by
  cases share <;> rfl

/-- **A join owns exactly the points of either share.** -/
theorem owns_join (first second : Share) (point : ℕ → Bool) :
    (join first second).Owns point ↔ first.Owns point ∨ second.Owns point := by
  induction first generalizing second point with
  | none => simp [join, Owns]
  | all => cases second <;> simp [join, Owns]
  | node left right ihLeft ihRight =>
      cases second with
      | none => simp [join, Owns]
      | all => simp [join, Owns]
      | node left' right' =>
          rw [join, owns_node']
          cases bit : point 0 <;> simp [Owns, bit, ihLeft, ihRight]

theorem overlap_join (first second other : Share) :
    Overlap (join first second) other ↔ Overlap first other ∨ Overlap second other := by
  simp only [Overlap, owns_join]
  constructor
  · rintro ⟨point, inFirst | inSecond, inOther⟩
    · exact Or.inl ⟨point, inFirst, inOther⟩
    · exact Or.inr ⟨point, inSecond, inOther⟩
  · rintro (⟨point, inFirst, inOther⟩ | ⟨point, inSecond, inOther⟩)
    · exact ⟨point, Or.inl inFirst, inOther⟩
    · exact ⟨point, Or.inr inSecond, inOther⟩

/-- **Split** a share into two halves. -/
def split : Share → Share × Share
  | none => (none, none)
  | all => (node all none, node none all)
  | node none right => (node none (split right).1, node none (split right).2)
  | node left none => (node (split left).1 none, node (split left).2 none)
  | node left right => (node left none, node none right)

/-- **The halves of a split own exactly the points of the share.** -/
theorem owns_split (share : Share) (point : ℕ → Bool) :
    (split share).1.Owns point ∨ (split share).2.Owns point ↔ share.Owns point := by
  induction share generalizing point with
  | none => simp [split, Owns]
  | all => cases bit : point 0 <;> simp [split, Owns, bit]
  | node left right ihLeft ihRight =>
      cases left <;> cases right <;> cases bit : point 0 <;>
        simp_all [split, Owns]

/-- **No point is in both halves of a split.** -/
theorem split_disjoint (share : Share) : ¬ Overlap (split share).1 (split share).2 := by
  rintro ⟨point, inFirst, inSecond⟩
  induction share generalizing point with
  | none => simp [split, Owns] at inFirst
  | all => cases bit : point 0 <;> simp_all [split, Owns]
  | node left right ihLeft ihRight =>
      cases left <;> cases right <;> cases bit : point 0 <;> simp_all [split, Owns]

theorem owns_of_split_fst {share : Share} {point : ℕ → Bool}
    (inHalf : (split share).1.Owns point) : share.Owns point :=
  (owns_split share point).mp (Or.inl inHalf)

theorem owns_of_split_snd {share : Share} {point : ℕ → Bool}
    (inHalf : (split share).2.Owns point) : share.Owns point :=
  (owns_split share point).mp (Or.inr inHalf)

/-! ## Normal shares -/

/-- No node has two empty halves or two full halves. -/
def Normal : Share → Prop
  | none => True
  | all => True
  | node left right =>
      left.Normal ∧ right.Normal ∧ ¬ (left = none ∧ right = none) ∧ ¬ (left = all ∧ right = all)

theorem normal_node' {left right : Share} (normalLeft : left.Normal) (normalRight : right.Normal) :
    (node' left right).Normal := by
  cases left <;> cases right <;> simp_all [node', Normal]

/-- **Joins keep shares normal.** -/
theorem normal_join {first second : Share} (normalFirst : first.Normal)
    (normalSecond : second.Normal) : (join first second).Normal := by
  induction first generalizing second with
  | none => exact normalSecond
  | all => cases second <;> simp [join, Normal]
  | node left right ihLeft ihRight =>
      cases second with
      | none => exact normalFirst
      | all => simp [join, Normal]
      | node left' right' =>
          exact normal_node' (ihLeft normalFirst.1 normalSecond.1)
            (ihRight normalFirst.2.1 normalSecond.2.1)

/-- **A normal share owns a point exactly when it is not `none`.** -/
theorem normal_nonempty_iff {share : Share} (normal : share.Normal) :
    share ≠ none ↔ ∃ point, share.Owns point := by
  induction share with
  | none => simp [Owns]
  | all => exact ⟨fun _ => ⟨fun _ => false, trivial⟩, fun _ => nofun⟩
  | node left right ihLeft ihRight =>
      refine ⟨fun _ => ?_, fun _ => nofun⟩
      obtain ⟨normalLeft, normalRight, notBothNone, -⟩ := normal
      by_cases leftNone : left = none
      · have rightNonempty := (ihRight normalRight).mp fun same => notBothNone ⟨leftNone, same⟩
        obtain ⟨point, inRight⟩ := rightNonempty
        exact ⟨push true point, by simpa [Owns] using inRight⟩
      · obtain ⟨point, inLeft⟩ := (ihLeft normalLeft).mp leftNone
        exact ⟨push false point, by simpa [Owns] using inLeft⟩

/-- A nonempty normal share overlaps itself. -/
theorem overlap_self {share : Share} (normal : share.Normal) (nonempty : share ≠ none) :
    Overlap share share :=
  let ⟨point, owned⟩ := (normal_nonempty_iff normal).mp nonempty
  ⟨point, owned, owned⟩

theorem join_ne_none {first second : Share} (normalFirst : first.Normal)
    (nonempty : first ≠ none) : join first second ≠ none := by
  intro empty
  obtain ⟨point, owned⟩ := (normal_nonempty_iff normalFirst).mp nonempty
  have := (owns_join first second point).mpr (Or.inl owned)
  rw [empty] at this
  exact this

/-- **The halves of a nonempty normal share are nonempty and normal.** -/
theorem split_normal {share : Share} (normal : share.Normal) (nonempty : share ≠ none) :
    (split share).1.Normal ∧ (split share).2.Normal ∧
      (split share).1 ≠ none ∧ (split share).2 ≠ none := by
  induction share with
  | none => exact absurd rfl nonempty
  | all => simp [split, Normal]
  | node left right ihLeft ihRight =>
      obtain ⟨normalLeft, normalRight, notBothNone, notBothAll⟩ := normal
      cases left with
      | none =>
          have rightNonempty : right ≠ none := fun same => notBothNone ⟨rfl, same⟩
          obtain ⟨n₁, n₂, e₁, e₂⟩ := ihRight normalRight rightNonempty
          simp [split, Normal, n₁, n₂, e₁, e₂]
      | all =>
          cases right with
          | none => simp [split, Normal]
          | all => exact absurd ⟨rfl, rfl⟩ notBothAll
          | node l r => simp_all [split, Normal]
      | node l r =>
          cases right with
          | none =>
              obtain ⟨n₁, n₂, e₁, e₂⟩ := ihLeft normalLeft nofun
              simp [split, Normal, n₁, n₂, e₁, e₂]
          | all => simp_all [split, Normal]
          | node l' r' => simp_all [split, Normal]

/-- **Joining the two halves of a normal share gives the share back.** -/
theorem join_split {share : Share} (normal : share.Normal) :
    join (split share).1 (split share).2 = share := by
  induction share with
  | none => rfl
  | all => rfl
  | node left right ihLeft ihRight =>
      obtain ⟨normalLeft, normalRight, notBothNone, notBothAll⟩ := normal
      cases left with
      | none =>
          rw [show split (node none right) =
              (node none (split right).1, node none (split right).2) from by cases right <;> rfl]
          simp only [join, ihRight normalRight]
          cases right with
          | none => exact absurd ⟨rfl, rfl⟩ notBothNone
          | all => rfl
          | node l r => rfl
      | all =>
          cases right with
          | none => rfl
          | all => exact absurd ⟨rfl, rfl⟩ notBothAll
          | node l r => rfl
      | node l r =>
          cases right with
          | none =>
              simp only [split, join, ihLeft normalLeft]
              rfl
          | all => rfl
          | node l' r' => rfl

/-! ## Pieces of a share -/

/-- The share of component `i` of a parallel composition of `k` components: the first takes the
left half, the others share the right half, and a single component takes the whole share. -/
def piece : Share → ℕ → ℕ → Share
  | share, 0, _ => share
  | share, 1, _ => share
  | share, _ + 2, 0 => (split share).1
  | share, k + 2, i + 1 => piece (split share).2 (k + 1) i

/-- **A piece is a part of the share.** -/
theorem piece_owns {share : Share} {k i : ℕ} {point : ℕ → Bool}
    (inPiece : (piece share k i).Owns point) : share.Owns point := by
  induction k generalizing share i with
  | zero => exact inPiece
  | succ k ih =>
      cases k with
      | zero => exact inPiece
      | succ k =>
          cases i with
          | zero => exact owns_of_split_fst inPiece
          | succ i => exact owns_of_split_snd (ih inPiece)

theorem overlap_of_piece {share other : Share} {k i : ℕ}
    (overlap : Overlap (piece share k i) other) : Overlap share other :=
  let ⟨point, inPiece, inOther⟩ := overlap
  ⟨point, piece_owns inPiece, inOther⟩

/-- **Pieces of a share are normal and nonempty.** -/
theorem piece_normal {share : Share} (normal : share.Normal) (nonempty : share ≠ none) (k i : ℕ) :
    (piece share k i).Normal ∧ piece share k i ≠ none := by
  induction k generalizing share i with
  | zero => exact ⟨normal, nonempty⟩
  | succ k ih =>
      cases k with
      | zero => exact ⟨normal, nonempty⟩
      | succ k =>
          obtain ⟨n₁, n₂, e₁, e₂⟩ := split_normal normal nonempty
          cases i with
          | zero => exact ⟨n₁, e₁⟩
          | succ i => exact ih n₂ e₂ i

/-- **Distinct pieces are disjoint.** -/
theorem pieces_disjoint (share : Share) {k i j : ℕ} (iBelow : i < k) (jBelow : j < k)
    (distinct : i ≠ j) : ¬ Overlap (piece share k i) (piece share k j) := by
  induction k generalizing share i j with
  | zero => omega
  | succ k ih =>
      cases k with
      | zero => omega
      | succ k =>
          cases i with
          | zero =>
              cases j with
              | zero => exact absurd rfl distinct
              | succ j =>
                  rintro ⟨point, inFirst, inSecond⟩
                  exact split_disjoint share ⟨point, inFirst, piece_owns inSecond⟩
          | succ i =>
              cases j with
              | zero =>
                  rintro ⟨point, inFirst, inSecond⟩
                  exact split_disjoint share ⟨point, inSecond, piece_owns inFirst⟩
              | succ j =>
                  exact ih (split share).2 (by omega) (by omega) (by omega)

/-! ## Size -/

/-- The number of nodes of a share. -/
def size : Share → ℕ
  | none => 1
  | all => 1
  | node left right => left.size + right.size + 1

theorem size_pos (share : Share) : 0 < share.size := by
  cases share <;> simp [size]

/-- The shares of at most `n` nodes. -/
def upTo : ℕ → Finset Share
  | 0 => ∅
  | n + 1 => {none, all} ∪ ((upTo n) ×ˢ (upTo n)).image fun halves => node halves.1 halves.2

theorem mem_upTo {n : ℕ} {share : Share} (small : share.size ≤ n) : share ∈ upTo n := by
  induction n generalizing share with
  | zero => exact absurd small (Nat.not_le.mpr (size_pos share))
  | succ n ih =>
      cases share with
      | none => simp [upTo]
      | all => simp [upTo]
      | node left right =>
          have leftSmall : left.size ≤ n := by
            have := size_pos right
            simp only [size] at small
            omega
          have rightSmall : right.size ≤ n := by
            have := size_pos left
            simp only [size] at small
            omega
          simp only [upTo, Finset.mem_union, Finset.mem_image, Finset.mem_product]
          exact Or.inr ⟨(left, right), ⟨ih leftSmall, ih rightSmall⟩, rfl⟩

/-- **Shares of bounded size are finitely many.** -/
theorem finite_size_le (bound : ℕ) : {share : Share | share.size ≤ bound}.Finite :=
  (upTo bound).finite_toSet.subset fun _ small => mem_upTo small

/-! ## Depth and dyadic intervals -/

/-- The depth of a share: the number of halvings along its longest path. -/
def depth : Share → ℕ
  | none => 0
  | all => 0
  | node left right => max left.depth right.depth + 1

theorem split_node_none (right : Share) :
    split (node none right) = (node none (split right).1, node none (split right).2) := rfl

theorem split_node_left {left : Share} (nonempty : left ≠ none) :
    split (node left none) = (node (split left).1 none, node (split left).2 none) := by
  cases left with
  | none => exact absurd rfl nonempty
  | all => rfl
  | node l r => rfl

/-- **A split goes at most one level deeper.** -/
theorem depth_split_le (share : Share) :
    (split share).1.depth ≤ share.depth + 1 ∧ (split share).2.depth ≤ share.depth + 1 := by
  induction share with
  | none => exact ⟨Nat.zero_le _, Nat.zero_le _⟩
  | all => exact ⟨le_refl _, le_refl _⟩
  | node left right ihLeft ihRight =>
      cases left with
      | none =>
          rw [split_node_none]
          simp only [depth]
          omega
      | all =>
          cases right with
          | none => simp [split, depth]
          | all => simp [split, depth]
          | node l r => simp only [split, depth]; omega
      | node l r =>
          cases right with
          | none =>
              rw [split_node_left (show Share.node l r ≠ none from nofun)]
              simp only [depth] at ihLeft ⊢
              omega
          | all => simp only [split, depth]; omega
          | node l' r' => simp only [split, depth]; omega

/-- The dyadic interval at a path of halvings: `false` takes the left half, `true` the right. -/
def interval : List Bool → Share
  | [] => all
  | false :: path => node (interval path) none
  | true :: path => node none (interval path)

@[simp] theorem interval_nil : interval [] = all := rfl

theorem interval_ne_none (path : List Bool) : interval path ≠ none := by
  cases path with
  | nil => nofun
  | cons bit path => cases bit <;> nofun

theorem interval_normal (path : List Bool) : (interval path).Normal := by
  induction path with
  | nil => trivial
  | cons bit path ih =>
      cases bit
      · exact ⟨ih, trivial, fun both => interval_ne_none path both.1, fun both => by cases both.2⟩
      · exact ⟨trivial, ih, fun both => interval_ne_none path both.2, fun both => by cases both.1⟩

@[simp] theorem depth_interval (path : List Bool) : (interval path).depth = path.length := by
  induction path with
  | nil => rfl
  | cons bit path ih => cases bit <;> simp [interval, depth, ih]

@[simp] theorem size_interval (path : List Bool) : (interval path).size = 2 * path.length + 1 := by
  induction path with
  | nil => rfl
  | cons bit path ih => cases bit <;> simp [interval, size, ih] <;> omega

/-- **Halving a dyadic interval gives the intervals one level down.** -/
theorem split_interval (path : List Bool) :
    split (interval path) = (interval (path ++ [false]), interval (path ++ [true])) := by
  induction path with
  | nil => rfl
  | cons bit path ih =>
      cases bit
      · rw [interval, split_node_left (interval_ne_none path), ih]
        rfl
      · rw [interval, split_node_none, ih]
        rfl

end Share

end Mettapedia.Machines.NameSupplies
