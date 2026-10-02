import Mettapedia.Algorithms.DerivationPrefix
import Mathlib.Data.List.Pairwise
import Mathlib.Data.List.Nodup

/-!
# Lazy combination of bounded child caches

The product selector admits one zero rank and only its coordinate neighbors.
Child caches are ordered, distinct lists constructed by earlier selectors.
The implementation never enumerates the full Cartesian product and spends
at most k rank expansions on a request for k parent candidates.

Its global prefix theorem is against independent child source predicates.
The child-cache truncation law supplies the omitted-parent dominance proof.
-/

set_option autoImplicit false

namespace Mettapedia.Algorithms.LazyProductPrefixes

open DerivationPrefix

variable {Left Right : Type}

structure Cache (Value : Type) (cost : Value → Nat) where
  values : List Value
  distinct : values.Nodup
  ordered : values.Pairwise (fun first second => cost first ≤ cost second)

def axis {Value : Type} (cost : Value → Nat) (cache : Cache Value cost)
    (positive : 0 < cache.values.length) : LazyCartesianRanks.Axis where
  count := cache.values.length
  positive := positive
  weight index := cost (cache.values.get index)
  ordered := by
    intro first second order
    rcases Fin.eq_or_lt_of_le order with same | before
    · subst second; exact le_rfl
    · exact cache.ordered.rel_get_of_lt before

def axes (leftCost : Left → Nat) (rightCost : Right → Nat)
    (left : Cache Left leftCost) (right : Cache Right rightCost)
    (leftPositive : 0 < left.values.length) (rightPositive : 0 < right.values.length) :=
  [axis leftCost left leftPositive, axis rightCost right rightPositive]

def decode (leftCost : Left → Nat) (rightCost : Right → Nat)
    (left : Cache Left leftCost) (right : Cache Right rightCost)
    (leftPositive : 0 < left.values.length) (rightPositive : 0 < right.values.length)
    (point : LazyCartesianRanks.Point (axes leftCost rightCost left right
      leftPositive rightPositive)) : Left × Right :=
  (left.values.get point.1, right.values.get point.2.1)

theorem decode_injective (leftCost : Left → Nat) (rightCost : Right → Nat)
    (left : Cache Left leftCost) (right : Cache Right rightCost)
    (leftPositive : 0 < left.values.length) (rightPositive : 0 < right.values.length) :
    Function.Injective (decode leftCost rightCost left right leftPositive rightPositive) := by
  intro first second same
  rcases first with ⟨firstL, firstR, ⟨⟩⟩
  rcases second with ⟨secondL, secondR, ⟨⟩⟩
  have sameL := left.distinct.injective_get (congrArg Prod.fst same)
  have sameR := right.distinct.injective_get (congrArg Prod.snd same)
  change firstL = secondL at sameL
  change firstR = secondR at sameR
  subst secondL; subst secondR; rfl

theorem decode_cost (leftCost : Left → Nat) (rightCost : Right → Nat)
    (left : Cache Left leftCost) (right : Cache Right rightCost)
    (leftPositive : 0 < left.values.length) (rightPositive : 0 < right.values.length)
    (point : LazyCartesianRanks.Point (axes leftCost rightCost left right
      leftPositive rightPositive)) :
    pairCost leftCost rightCost (decode leftCost rightCost left right
      leftPositive rightPositive point) =
      LazyCartesianRanks.cost (axes leftCost rightCost left right
        leftPositive rightPositive) point := by
  rcases point with ⟨first, second, ⟨⟩⟩
  simp only [decode, pairCost, axes, axis, LazyCartesianRanks.cost, Nat.add_zero]

theorem decode_image (leftCost : Left → Nat) (rightCost : Right → Nat)
    (left : Cache Left leftCost) (right : Cache Right rightCost)
    (leftPositive : 0 < left.values.length) (rightPositive : 0 < right.values.length)
    (pair : Left × Right) :
    (∃ point, decode leftCost rightCost left right leftPositive rightPositive point = pair) ↔
      pair ∈ product left.values right.values := by
  constructor
  · rintro ⟨point, same⟩
    subst pair
    exact (mem_product _ _ _).mpr ⟨List.get_mem _ _, List.get_mem _ _⟩
  · intro present
    have members := (mem_product _ _ _).mp present
    obtain ⟨first, firstEq⟩ := List.mem_iff_get.mp members.1
    obtain ⟨second, secondEq⟩ := List.mem_iff_get.mp members.2
    exact ⟨(first, second, ()), Prod.ext firstEq secondEq⟩

def selected (requested : Nat) (leftCost : Left → Nat) (rightCost : Right → Nat)
    (left : Cache Left leftCost) (right : Cache Right rightCost) : List (Left × Right) :=
  if leftPositive : 0 < left.values.length then
    if rightPositive : 0 < right.values.length then
      ((LazyCartesianRanks.extract (axes leftCost rightCost left right
        leftPositive rightPositive) requested requested).1.published).map
        (decode leftCost rightCost left right leftPositive rightPositive)
    else []
  else []

theorem selected_retained_correct (requested : Nat)
    (leftCost : Left → Nat) (rightCost : Right → Nat)
    (left : Cache Left leftCost) (right : Cache Right rightCost) :
    Correct requested (pairCost leftCost rightCost)
      (fun pair => pair ∈ product left.values right.values)
      (selected requested leftCost rightCost left right) := by
  classical
  unfold selected
  split
  next leftPositive =>
    split
    next rightPositive =>
      let coordinateAxes := axes leftCost rightCost left right leftPositive rightPositive
      have rankCorrect := graph_prefix_correct (LazyCartesianRanks.graph coordinateAxes)
        (LazyCartesianRanks.neighbors_monotone coordinateAxes) [LazyCartesianRanks.zero coordinateAxes]
        (LazyCartesianRanks.every_point_reachable coordinateAxes) requested
      have mapped := map_correct requested (LazyCartesianRanks.cost coordinateAxes)
        (pairCost leftCost rightCost) (fun _ => True) _ rankCorrect
        (decode leftCost rightCost left right leftPositive rightPositive)
        (decode_injective leftCost rightCost left right leftPositive rightPositive)
        (decode_cost leftCost rightCost left right leftPositive rightPositive)
      have sourceEq : (fun pair => ∃ point, True ∧
          decode leftCost rightCost left right leftPositive rightPositive point = pair) =
          (fun pair => pair ∈ product left.values right.values) := by
        funext pair
        apply propext
        simpa using decode_image leftCost rightCost left right leftPositive rightPositive pair
      rw [sourceEq] at mapped
      exact mapped
    next rightEmpty =>
      apply empty_correct
      intro pair present
      have member := (mem_product _ _ _).mp present
      have empty : right.values = [] := List.eq_nil_of_length_eq_zero (by omega)
      simpa [empty] using member.2
  next leftEmpty =>
    apply empty_correct
    intro pair present
    have member := (mem_product _ _ _).mp present
    have empty : left.values = [] := List.eq_nil_of_length_eq_zero (by omega)
    simpa [empty] using member.1

/-- A lazy product of child k-prefixes is a globally correct parent
k-prefix. It retains tied derivation identities and never computes the
independent exhaustive source before selection. -/
theorem selected_source_correct (requested : Nat)
    (leftCost : Left → Nat) (rightCost : Right → Nat)
    (leftSource : Left → Prop) (rightSource : Right → Prop)
    (left : Cache Left leftCost) (right : Cache Right rightCost)
    (leftCorrect : Correct requested leftCost leftSource left.values)
    (rightCorrect : Correct requested rightCost rightSource right.values) :
    Correct requested (pairCost leftCost rightCost)
      (fun pair => leftSource pair.1 ∧ rightSource pair.2)
      (selected requested leftCost rightCost left right) := by
  classical
  have retained := selected_retained_correct requested leftCost rightCost left right
  apply extend_by_dominance requested (pairCost leftCost rightCost)
    (fun pair => leftSource pair.1 ∧ rightSource pair.2)
    (fun pair => pair ∈ product left.values right.values) _ retained
  · intro pair present
    have members := (mem_product _ _ _).mp present
    exact ⟨leftCorrect.sound _ members.1, rightCorrect.sound _ members.2⟩
  · intro pair allowed absent
    by_cases positive : 0 < requested
    · obtain ⟨witnesses, distinct, full, included, cheap⟩ :=
        product_dominates requested positive leftCost rightCost leftSource rightSource
          left.values right.values leftCorrect rightCorrect pair allowed absent
      exact ⟨witnesses, distinct, full, included, cheap⟩
    · have zero : requested = 0 := by omega
      exact ⟨[], List.nodup_nil, by simp [zero], by simp, by simp⟩

def combined (requested : Nat) (leftCost : Left → Nat) (rightCost : Right → Nat)
    (left : Cache Left leftCost) (right : Cache Right rightCost) :
    Cache (Left × Right) (pairCost leftCost rightCost) where
  values := selected requested leftCost rightCost left right
  distinct := (selected_retained_correct requested leftCost rightCost left right).distinct
  ordered := (selected_retained_correct requested leftCost rightCost left right).ordered

namespace Controls

def child : Cache Nat id :=
  ⟨[0, 1], by decide, by decide⟩

example : (selected 3 id id child child).map (pairCost id id) = [0, 1, 1] := by decide
example : (selected 3 id id child child).length = 3 := by decide
example : (selected 7 id id child child).length = 4 := by decide

end Controls

end Mettapedia.Algorithms.LazyProductPrefixes
