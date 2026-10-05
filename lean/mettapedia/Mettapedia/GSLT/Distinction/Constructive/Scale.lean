import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Logic.Function.Iterate
import Mathlib.Algebra.Order.Ring.Int

/-!
# Constructive value scales

The classical behavioural metric reads formulas into the real numbers and
takes suprema over arbitrary sets.  The constructive layer reads them into a
**value scale**: a linearly ordered additive commutative group `V` with a unit
`one > 0` and a **discount**, an additive map that is nonnegative and
contracting on nonnegative values.  Order on `V` is decidable as part of the
linear order, so comparisons, maxima and minima are computed.

* Finite suprema and infima over lists (`listSup`, `listInf`) and the
  **Hausdorff value** of a distance between two finite lists
  (`hausdorff`).  The key estimate `abs_listSup_sub_listSup_le_hausdorff`
  bounds the difference of two finite suprema by the Hausdorff value; it is the
  diamond case of every adequacy proof in this layer.
* `Scale`, with derived laws of the discount (`discount_sub`, `discount_mono`,
  `abs_discount`), `Scale.clamp` (nonexpansive, `abs_clamp_sub_clamp_le`) and
  the geometric tail of iterated discounts (`Scale.tail`).
* `Scale.integers`: the integers with a positive unit and the identity
  discount, that is rational values with a fixed denominator and discount one.
  Its order and group laws use no choice principle.

Everything here is generic in `V` and avoids `Classical.choice`.  This is not
cosmetic: in the current toolchain the field and order laws of Mathlib's `ℚ`
(even `Rat.add_comm`) depend on `Classical.choice`, while those of `ℤ` and the
generic ordered-group lemmas used below do not.  The few generic lemmas whose
library proofs are classical (`abs_nonpos_iff`, `abs_min_sub_min_le_max`,
`abs_max_sub_max_le_max`, `map_sub` for bundled maps) are reproved here.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Distinction.Constructive

universe uV uA uB

variable {α : Type uA} {β : Type uB}

/-! ## Finite infima over lists -/

section Order

variable {V : Type uV} [LinearOrder V]

/-- The smallest value of `f` on a list, `top` on the empty list. -/
def listInf (top : V) (f : α → V) : List α → V
  | [] => top
  | head :: rest => min (f head) (listInf top f rest)

@[simp] theorem listInf_nil (top : V) (f : α → V) : listInf top f [] = top := rfl

@[simp] theorem listInf_cons (top : V) (f : α → V) (head : α) (rest : List α) :
    listInf top f (head :: rest) = min (f head) (listInf top f rest) := rfl

theorem listInf_le (top : V) (f : α → V) : ∀ {list : List α} {element : α}, element ∈ list →
    listInf top f list ≤ f element
  | [], _, member => absurd member List.not_mem_nil
  | _ :: _, _, member => by
      rcases List.mem_cons.mp member with rfl | member
      · exact min_le_left _ _
      · exact (min_le_right _ _).trans (listInf_le top f member)

theorem listInf_le_top (top : V) (f : α → V) : ∀ list : List α, listInf top f list ≤ top
  | [] => le_rfl
  | _ :: rest => (min_le_right _ _).trans (listInf_le_top top f rest)

theorem le_listInf (top : V) (f : α → V) {bound : V} (le_top : bound ≤ top) :
    ∀ {list : List α}, (∀ element ∈ list, bound ≤ f element) → bound ≤ listInf top f list
  | [], _ => le_top
  | head :: _, each =>
      le_min (each head List.mem_cons_self)
        (le_listInf top f le_top fun element member => each element (List.mem_cons_of_mem _ member))

/-- On a nonempty list of values below `top` the infimum is attained. -/
theorem exists_eq_listInf (top : V) (f : α → V) :
    ∀ {list : List α}, list ≠ [] → (∀ element ∈ list, f element ≤ top) →
      ∃ element ∈ list, listInf top f list = f element
  | [], nonempty, _ => absurd rfl nonempty
  | [head], _, below => ⟨head, List.mem_cons_self, by
      rw [listInf_cons, listInf_nil]
      exact min_eq_left (below head List.mem_cons_self)⟩
  | head :: second :: rest, _, below => by
      obtain ⟨element, member, attained⟩ :=
        exists_eq_listInf top f (list := second :: rest) (List.cons_ne_nil _ _)
          (fun element member => below element (List.mem_cons_of_mem _ member))
      rw [listInf_cons]
      rcases min_choice (f head) (listInf top f (second :: rest)) with same | same
      · exact ⟨head, List.mem_cons_self, same⟩
      · exact ⟨element, List.mem_cons_of_mem _ member, same.trans attained⟩

end Order

/-! ## Finite suprema over lists and the Hausdorff value -/

section ZeroOrder

variable {V : Type uV} [Zero V] [LinearOrder V]

/-- The largest value of `f` on a list, `0` on the empty list. -/
def listSup (f : α → V) : List α → V
  | [] => 0
  | head :: rest => max (f head) (listSup f rest)

@[simp] theorem listSup_nil (f : α → V) : listSup f [] = 0 := rfl

@[simp] theorem listSup_cons (f : α → V) (head : α) (rest : List α) :
    listSup f (head :: rest) = max (f head) (listSup f rest) := rfl

theorem listSup_nonneg (f : α → V) : ∀ list : List α, 0 ≤ listSup f list
  | [] => le_rfl
  | _ :: rest => (listSup_nonneg f rest).trans (le_max_right _ _)

theorem le_listSup (f : α → V) : ∀ {list : List α} {element : α}, element ∈ list →
    f element ≤ listSup f list
  | [], _, member => absurd member List.not_mem_nil
  | _ :: _, _, member => by
      rcases List.mem_cons.mp member with rfl | member
      · exact le_max_left _ _
      · exact (le_listSup f member).trans (le_max_right _ _)

theorem listSup_le (f : α → V) {bound : V} (nonneg : 0 ≤ bound) :
    ∀ {list : List α}, (∀ element ∈ list, f element ≤ bound) → listSup f list ≤ bound
  | [], _ => nonneg
  | head :: _, each =>
      max_le (each head List.mem_cons_self)
        (listSup_le f nonneg fun element member => each element (List.mem_cons_of_mem _ member))

theorem listSup_le_listSup_cons (f : α → V) (head : α) (rest : List α) :
    listSup f rest ≤ listSup f (head :: rest) := le_max_right _ _

/-- On a nonempty list of nonnegative values the supremum is attained. -/
theorem exists_eq_listSup (f : α → V) :
    ∀ {list : List α}, list ≠ [] → (∀ element ∈ list, 0 ≤ f element) →
      ∃ element ∈ list, listSup f list = f element
  | [], nonempty, _ => absurd rfl nonempty
  | [head], _, nonneg => ⟨head, List.mem_cons_self, by
      rw [listSup_cons, listSup_nil]
      exact max_eq_left (nonneg head List.mem_cons_self)⟩
  | head :: second :: rest, _, nonneg => by
      obtain ⟨element, member, attained⟩ :=
        exists_eq_listSup f (list := second :: rest) (List.cons_ne_nil _ _)
          (fun element member => nonneg element (List.mem_cons_of_mem _ member))
      rw [listSup_cons]
      rcases max_choice (f head) (listSup f (second :: rest)) with same | same
      · exact ⟨head, List.mem_cons_self, same⟩
      · exact ⟨element, List.mem_cons_of_mem _ member, same.trans attained⟩

theorem listSup_le_listSup (f : α → V) (g : β → V) {first : List α} {second : List β}
    (matched : ∀ element ∈ first, ∃ other ∈ second, f element ≤ g other) :
    listSup f first ≤ listSup g second :=
  listSup_le f (listSup_nonneg g second) fun element member => by
    obtain ⟨other, otherMember, le⟩ := matched element member
    exact le.trans (le_listSup g otherMember)

theorem listSup_congr {f g : α → V} : ∀ {list : List α}, (∀ element ∈ list, f element = g element) →
    listSup f list = listSup g list
  | [], _ => rfl
  | head :: _, same => by
      rw [listSup_cons, listSup_cons, same head List.mem_cons_self,
        listSup_congr fun element member => same element (List.mem_cons_of_mem _ member)]

/-- The **Hausdorff value** of a distance between two lists: the larger of the
two directed values `sup_a inf_b d a b` and `sup_b inf_a d a b`, with infima
over an empty list at `top`.  It is `0` for two empty lists and `top` when
exactly one is empty. -/
def hausdorff (top : V) (distance : α → β → V) (first : List α) (second : List β) : V :=
  max (listSup (fun element => listInf top (distance element) second) first)
    (listSup (fun other => listInf top (fun element => distance element other) first) second)

theorem hausdorff_nonneg (top : V) (distance : α → β → V) (first : List α) (second : List β) :
    0 ≤ hausdorff top distance first second :=
  (listSup_nonneg _ _).trans (le_max_left _ _)

theorem hausdorff_le_top {top : V} (topNonneg : 0 ≤ top) (distance : α → β → V)
    (first : List α) (second : List β) : hausdorff top distance first second ≤ top :=
  max_le (listSup_le _ topNonneg fun _ _ => listInf_le_top _ _ _)
    (listSup_le _ topNonneg fun _ _ => listInf_le_top _ _ _)

theorem hausdorff_nil_nil (top : V) (distance : α → β → V) :
    hausdorff top distance [] [] = 0 := by
  rw [hausdorff, listSup_nil, listSup_nil, max_self]

/-- At Hausdorff value at most `0`, every element of the first list has a
partner in the second list at distance `0`. -/
theorem exists_zero_of_hausdorff_le_zero {top : V} (topPos : 0 < top) {distance : α → β → V}
    {first : List α} {second : List β}
    (nonneg : ∀ element ∈ first, ∀ other ∈ second, 0 ≤ distance element other)
    (belowTop : ∀ element ∈ first, ∀ other ∈ second, distance element other ≤ top)
    (zero : hausdorff top distance first second ≤ 0) {element : α} (member : element ∈ first) :
    ∃ other ∈ second, distance element other = 0 := by
  have small : listInf top (distance element) second ≤ 0 :=
    ((le_listSup (fun element => listInf top (distance element) second) member).trans
      (le_max_left _ _)).trans zero
  cases second with
  | nil => exact absurd (lt_of_lt_of_le topPos small) (lt_irrefl 0)
  | cons head rest =>
      obtain ⟨other, otherMember, attained⟩ :=
        exists_eq_listInf top (distance element) (List.cons_ne_nil head rest)
          (belowTop element member)
      exact ⟨other, otherMember,
        le_antisymm (attained ▸ small) (nonneg element member other otherMember)⟩

/-- The symmetric partner lemma for the second list. -/
theorem exists_zero_of_hausdorff_le_zero' {top : V} (topPos : 0 < top) {distance : α → β → V}
    {first : List α} {second : List β}
    (nonneg : ∀ element ∈ first, ∀ other ∈ second, 0 ≤ distance element other)
    (belowTop : ∀ element ∈ first, ∀ other ∈ second, distance element other ≤ top)
    (zero : hausdorff top distance first second ≤ 0) {other : β} (member : other ∈ second) :
    ∃ element ∈ first, distance element other = 0 := by
  have small : listInf top (fun element => distance element other) first ≤ 0 :=
    ((le_listSup (fun other => listInf top (fun element => distance element other) first)
      member).trans (le_max_right _ _)).trans zero
  cases first with
  | nil => exact absurd (lt_of_lt_of_le topPos small) (lt_irrefl 0)
  | cons head rest =>
      obtain ⟨element, elementMember, attained⟩ :=
        exists_eq_listInf top (fun element => distance element other) (List.cons_ne_nil head rest)
          (fun element elementMember => belowTop element elementMember other member)
      exact ⟨element, elementMember,
        le_antisymm (attained ▸ small) (nonneg element elementMember other member)⟩

end ZeroOrder

section Group

variable {V : Type uV} [AddCommGroup V] [LinearOrder V] [IsOrderedAddMonoid V]

/-! ## Order lemmas proved without choice -/

theorem eq_of_abs_sub_nonpos {a b : V} (bound : |a - b| ≤ 0) : a = b := by
  have upper : a - b ≤ 0 := (le_abs_self _).trans bound
  have lower : 0 ≤ a - b := by
    have negBound : -0 ≤ -|a - b| := neg_le_neg bound
    rw [neg_zero] at negBound
    exact negBound.trans (neg_abs_le (a - b))
  exact sub_eq_zero.mp (le_antisymm upper lower)

theorem abs_min_sub_min_le (a b c d : V) : |min a b - min c d| ≤ max |a - c| |b - d| := by
  rw [abs_sub_le_iff]
  constructor
  · rcases min_choice c d with same | same <;> rw [same]
    · exact (sub_le_sub_right (min_le_left a b) c).trans
        ((le_abs_self _).trans (le_max_left _ _))
    · exact (sub_le_sub_right (min_le_right a b) d).trans
        ((le_abs_self _).trans (le_max_right _ _))
  · rcases min_choice a b with same | same <;> rw [same]
    · refine (sub_le_sub_right (min_le_left c d) a).trans ?_
      rw [abs_sub_comm a c]
      exact (le_abs_self _).trans (le_max_left _ _)
    · refine (sub_le_sub_right (min_le_right c d) b).trans ?_
      rw [abs_sub_comm b d]
      exact (le_abs_self _).trans (le_max_right _ _)

theorem abs_max_sub_max_le (a b c d : V) : |max a b - max c d| ≤ max |a - c| |b - d| := by
  rw [abs_sub_le_iff]
  constructor
  · rcases max_choice a b with same | same <;> rw [same]
    · exact (sub_le_sub_left (le_max_left c d) a).trans
        ((le_abs_self _).trans (le_max_left _ _))
    · exact (sub_le_sub_left (le_max_right c d) b).trans
        ((le_abs_self _).trans (le_max_right _ _))
  · rcases max_choice c d with same | same <;> rw [same]
    · refine (sub_le_sub_left (le_max_left a b) c).trans ?_
      rw [abs_sub_comm a c]
      exact (le_abs_self _).trans (le_max_left _ _)
    · refine (sub_le_sub_left (le_max_right a b) d).trans ?_
      rw [abs_sub_comm b d]
      exact (le_abs_self _).trans (le_max_right _ _)

/-- `max` with a fixed left argument does not increase a slack. -/
theorem max_le_max_add {base first second slack : V} (slackNonneg : 0 ≤ slack)
    (le : first ≤ second + slack) : max base first ≤ max base second + slack :=
  max_le ((le_max_left base second).trans (le_add_of_nonneg_right slackNonneg))
    (le.trans (add_le_add (le_max_right base second) le_rfl))

/-! ## Suprema with slack -/

/-- A supremum transferred along a matching with slack. -/
theorem listSup_le_listSup_add (f : α → V) (g : β → V) {first : List α} {second : List β}
    {slack : V} (slackNonneg : 0 ≤ slack)
    (matched : ∀ element ∈ first, ∃ other ∈ second, f element ≤ g other + slack) :
    listSup f first ≤ listSup g second + slack :=
  listSup_le f (add_nonneg (listSup_nonneg g second) slackNonneg) fun element member => by
    obtain ⟨other, otherMember, close⟩ := matched element member
    exact close.trans (add_le_add (le_listSup g otherMember) le_rfl)

theorem listSup_le_listSup_add_of_le {f g : α → V} {slack : V} (slackNonneg : 0 ≤ slack)
    {list : List α} (each : ∀ element ∈ list, f element ≤ g element + slack) :
    listSup f list ≤ listSup g list + slack :=
  listSup_le_listSup_add f g slackNonneg fun element member => ⟨element, member, each element member⟩

theorem listInf_le_listInf_add (top : V) {f g : α → V} {slack : V} (slackNonneg : 0 ≤ slack) :
    ∀ {list : List α}, (∀ element ∈ list, f element ≤ g element + slack) →
      listInf top f list ≤ listInf top g list + slack
  | [], _ => le_add_of_nonneg_right slackNonneg
  | head :: _, each => by
      rw [listInf_cons, listInf_cons, ← min_add_add_right]
      exact min_le_min (each head List.mem_cons_self)
        (listInf_le_listInf_add top slackNonneg fun element member =>
          each element (List.mem_cons_of_mem _ member))

/-! ## The finite Hausdorff estimate -/

/-- One direction of the **finite Hausdorff estimate**: every value of `f` is
within its own infimum distance of the supremum of `g`. -/
theorem le_listSup_add_listInf {top : V} {f : α → V} {g : β → V} {distance : α → β → V}
    {element : α} (belowTop : f element ≤ top) :
    ∀ {second : List β}, (∀ other ∈ second, f element ≤ g other + distance element other) →
      f element ≤ listSup g second + listInf top (distance element) second
  | [], _ => by rw [listSup_nil, listInf_nil, zero_add]; exact belowTop
  | head :: rest, close => by
      rw [listInf_cons]
      rcases min_choice (distance element head) (listInf top (distance element) rest) with
        same | same <;> rw [same]
      · exact (close head List.mem_cons_self).trans
          (add_le_add (le_listSup g List.mem_cons_self) le_rfl)
      · exact (le_listSup_add_listInf belowTop fun other member =>
          close other (List.mem_cons_of_mem _ member)).trans
          (add_le_add (listSup_le_listSup_cons g head rest) le_rfl)

/-- **The finite Hausdorff estimate**: two suprema of functions that are close
along a distance differ by at most the Hausdorff value of that distance. -/
theorem abs_listSup_sub_listSup_le_hausdorff {top : V} {f : α → V} {g : β → V}
    {distance : α → β → V} {first : List α} {second : List β}
    (fBelow : ∀ element ∈ first, f element ≤ top) (gBelow : ∀ other ∈ second, g other ≤ top)
    (forward : ∀ element ∈ first, ∀ other ∈ second, f element ≤ g other + distance element other)
    (backward : ∀ element ∈ first, ∀ other ∈ second, g other ≤ f element + distance element other) :
    |listSup f first - listSup g second| ≤ hausdorff top distance first second := by
  rw [abs_sub_le_iff, sub_le_iff_le_add', sub_le_iff_le_add']
  constructor
  · refine listSup_le f (add_nonneg (listSup_nonneg _ _) (hausdorff_nonneg _ _ _ _))
      fun element member => ?_
    refine (le_listSup_add_listInf (fBelow element member) (forward element member)).trans
      (add_le_add le_rfl ?_)
    exact (le_listSup (fun element => listInf top (distance element) second) member).trans
      (le_max_left _ _)
  · refine listSup_le g (add_nonneg (listSup_nonneg _ _) (hausdorff_nonneg _ _ _ _))
      fun other member => ?_
    refine (le_listSup_add_listInf (distance := fun other element => distance element other)
      (gBelow other member) fun element elementMember =>
        backward element elementMember other member).trans (add_le_add le_rfl ?_)
    exact (le_listSup (fun other => listInf top (fun element => distance element other) first)
      member).trans (le_max_right _ _)

/-- The Hausdorff value is nonexpansive in the distance. -/
theorem hausdorff_le_hausdorff_add {top : V} {distance distance' : α → β → V}
    {first : List α} {second : List β} {slack : V} (slackNonneg : 0 ≤ slack)
    (close : ∀ element ∈ first, ∀ other ∈ second,
      distance' element other ≤ distance element other + slack) :
    hausdorff top distance' first second ≤ hausdorff top distance first second + slack := by
  unfold hausdorff
  refine max_le ?_ ?_
  · exact (listSup_le_listSup_add_of_le slackNonneg fun element member =>
      listInf_le_listInf_add top slackNonneg fun other otherMember =>
        close element member other otherMember).trans
      (add_le_add (le_max_left _ _) le_rfl)
  · exact (listSup_le_listSup_add_of_le slackNonneg fun other member =>
      listInf_le_listInf_add top slackNonneg fun element elementMember =>
        close element elementMember other member).trans
      (add_le_add (le_max_right _ _) le_rfl)

/-! ## Value scales -/

/-- A **value scale**: a positive unit and a discount that is additive,
nonnegative and contracting on nonnegative values. -/
structure Scale (V : Type uV) [AddCommGroup V] [LinearOrder V] [IsOrderedAddMonoid V] where
  /-- The value of truth. -/
  one : V
  one_pos : 0 < one
  /-- The weight of one step into the future. -/
  discount : V → V
  discount_add : ∀ first second, discount (first + second) = discount first + discount second
  discount_nonneg : ∀ {value : V}, 0 ≤ value → 0 ≤ discount value
  discount_le : ∀ {value : V}, 0 ≤ value → discount value ≤ value

namespace Scale

variable (K : Scale V)

theorem zero_le_one : 0 ≤ K.one := le_of_lt K.one_pos

theorem discount_zero : K.discount 0 = 0 := by
  have doubled := K.discount_add 0 0
  rw [add_zero] at doubled
  exact (add_left_cancel (doubled.symm.trans (add_zero _).symm))

theorem discount_neg (value : V) : K.discount (-value) = -K.discount value := by
  have sum := K.discount_add (-value) value
  rw [neg_add_cancel, K.discount_zero] at sum
  exact eq_neg_of_add_eq_zero_left sum.symm

theorem discount_sub (first second : V) :
    K.discount (first - second) = K.discount first - K.discount second := by
  rw [sub_eq_add_neg, K.discount_add, K.discount_neg, ← sub_eq_add_neg]

theorem discount_mono {first second : V} (le : first ≤ second) :
    K.discount first ≤ K.discount second := by
  have nonneg := K.discount_nonneg (sub_nonneg.mpr le)
  rw [K.discount_sub] at nonneg
  exact sub_nonneg.mp nonneg

theorem abs_discount (value : V) : |K.discount value| = K.discount |value| := by
  rcases le_total 0 value with nonneg | nonpos
  · rw [abs_of_nonneg (K.discount_nonneg nonneg), abs_of_nonneg nonneg]
  · have image : K.discount value ≤ 0 := by
      have := K.discount_mono nonpos
      rwa [K.discount_zero] at this
    rw [abs_of_nonpos image, abs_of_nonpos nonpos, K.discount_neg]

theorem discount_le_one : K.discount K.one ≤ K.one := K.discount_le K.zero_le_one

/-- Iterated discounts of nonnegative values stay nonnegative. -/
theorem iterate_discount_nonneg (steps : ℕ) {value : V} (nonneg : 0 ≤ value) :
    0 ≤ K.discount^[steps] value := by
  induction steps with
  | zero => exact nonneg
  | succ steps inductionHypothesis =>
      rw [Function.iterate_succ_apply']
      exact K.discount_nonneg inductionHypothesis

/-- The scale is **positive** when the discount keeps positive values positive. -/
def Positive : Prop := ∀ {value : V}, 0 < value → 0 < K.discount value

theorem eq_zero_of_discount_le_zero {K : Scale V} (positive : K.Positive) {value : V}
    (nonneg : 0 ≤ value) (le : K.discount value ≤ 0) : value = 0 := by
  rcases lt_or_ge 0 value with pos | nonpos
  · exact absurd le (not_le_of_gt (positive pos))
  · exact le_antisymm nonpos nonneg

/-- Clamp a value to `[0, one]`. -/
def clamp (value : V) : V := max 0 (min K.one value)

theorem clamp_nonneg (value : V) : 0 ≤ K.clamp value := le_max_left _ _

theorem clamp_le_one (value : V) : K.clamp value ≤ K.one :=
  max_le K.zero_le_one (min_le_left _ _)

theorem clamp_of_mem {value : V} (nonneg : 0 ≤ value) (le_one : value ≤ K.one) :
    K.clamp value = value := by
  unfold clamp
  rw [min_eq_right le_one, max_eq_right nonneg]

theorem clamp_mono {first second : V} (le : first ≤ second) : K.clamp first ≤ K.clamp second :=
  max_le_max le_rfl (min_le_min le_rfl le)

theorem abs_clamp_sub_clamp_le (first second : V) :
    |K.clamp first - K.clamp second| ≤ |first - second| := by
  unfold clamp
  refine (abs_max_sub_max_le _ _ _ _).trans (max_le ?_ ?_)
  · rw [sub_self, abs_zero]
    exact abs_nonneg _
  · refine (abs_min_sub_min_le _ _ _ _).trans (max_le ?_ le_rfl)
    rw [sub_self, abs_zero]
    exact abs_nonneg _

/-- The **geometric tail**: the sum of the iterated discounts of `one` from
step `start` for `length` steps. -/
def tail (start : ℕ) : ℕ → V
  | 0 => 0
  | length + 1 => tail start length + K.discount^[start + length] K.one

theorem tail_nonneg (start length : ℕ) : 0 ≤ K.tail start length := by
  induction length with
  | zero => exact le_rfl
  | succ length inductionHypothesis =>
      exact add_nonneg inductionHypothesis (K.iterate_discount_nonneg _ K.zero_le_one)

end Scale

end Group

/-! ## The integer scale -/

/-- **The integer scale**: the integers with a positive unit and the identity
discount.  A value `k` reads as the rational `k / unit`; the discount is one. -/
def Scale.integers (unit : ℤ) (positive : 0 < unit) : Scale ℤ where
  one := unit
  one_pos := positive
  discount := id
  discount_add _ _ := rfl
  discount_nonneg nonneg := nonneg
  discount_le _ := le_rfl

theorem Scale.integers_positive (unit : ℤ) (positive : 0 < unit) :
    (Scale.integers unit positive).Positive := fun positive' => positive'

end Mettapedia.GSLT.Distinction.Constructive
