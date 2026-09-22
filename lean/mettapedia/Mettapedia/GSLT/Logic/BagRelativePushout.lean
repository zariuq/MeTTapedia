import Mettapedia.GSLT.Logic.RedexRelativeCongruence
import Mathlib.Data.Multiset.UnionInter
import Mathlib.Algebra.Order.Sub.Unbundled.Basic

/-!
# The context monoid of a parallel calculus has relative pushouts

A process calculus whose composition is parallel has a very concrete category of
contexts: a context is the bag of processes placed beside the hole, composition
is bag union, and the whole thing is the one-object category on the free
commutative monoid of bags.

That category has relative pushouts, for every span and every bound, and the
construction is the one the arithmetic suggests: the part two bounds share is
their bag intersection, and cutting it away is least.  So every reaction a
parallel calculus can perform has a least label for its redex, and by
`RedexRelativeCongruence.ipoBisimilar_comp` the induced bisimilarity is a
congruence for every context.

Nothing here is about any particular calculus; what a calculus supplies is the
reaction rules, and the bags they are written over.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.BagRelativePushout

open CategoryTheory
open Mettapedia.GSLT.RelativePushout
open Mettapedia.GSLT.RedexRelativeCongruence

universe u

variable {α : Type u} [DecidableEq α]

/-- The context monoid: bags of components, composing by union. -/
abbrev Bag (α : Type u) [DecidableEq α] : Type u := Multiplicative (Multiset α)

/-- Its single object. -/
abbrev Obj (α : Type u) [DecidableEq α] : SingleObj (Bag α) := SingleObj.star _

/-- A bag, as an arrow of that category. -/
def bag (m : Multiset α) : Obj α ⟶ Obj α := Multiplicative.ofAdd m

@[simp]
theorem bag_comp (m n : Multiset α) : bag m ≫ bag n = bag (m + n) :=
  congrArg Multiplicative.ofAdd (add_comm n m)

theorem bag_id : bag (0 : Multiset α) = 𝟙 (Obj α) := rfl

theorem bag_injective {m n : Multiset α} (equal : bag m = bag n) : m = n :=
  congrArg Multiplicative.toAdd equal

theorem bag_surjective (arrow : Obj α ⟶ Obj α) : ∃ m : Multiset α, arrow = bag m :=
  ⟨Multiplicative.toAdd arrow, rfl⟩

/-! ## The relative pushout -/

/-- **The candidate that cuts away what two bounds share.**  The shared part of
two bags is their intersection; removing it is the reduction a relative pushout
performs. -/
def cutCandidate (f g p r : Multiset α) (w : f + p = g + r) :
    Candidate (bag f) (bag g) (bag p) (bag r) where
  apex := Obj α
  inl := bag (p - p ∩ r)
  inr := bag (r - p ∩ r)
  down := bag (p ∩ r)
  comm := by
    rw [bag_comp, bag_comp]
    refine congrArg bag (add_right_cancel (b := p ∩ r) ?_)
    rw [add_assoc, add_assoc, tsub_add_cancel_of_le Multiset.inter_le_left,
      tsub_add_cancel_of_le Multiset.inter_le_right]
    exact w
  fac_left := by
    rw [bag_comp, tsub_add_cancel_of_le Multiset.inter_le_left]
  fac_right := by
    rw [bag_comp, tsub_add_cancel_of_le Multiset.inter_le_right]

/-- **Every span of bags has relative pushouts.**  So a parallel calculus has a
least label for every reaction it can perform. -/
theorem hasRelativePushouts (f g : Multiset α) :
    HasRelativePushouts (bag f) (bag g) := by
  intro apex h i w
  obtain ⟨p, hEq⟩ := bag_surjective h
  obtain ⟨r, iEq⟩ := bag_surjective i
  rw [hEq, iEq] at w ⊢
  rw [bag_comp, bag_comp] at w
  have wCoords : f + p = g + r := bag_injective w
  refine ⟨cutCandidate f g p r wCoords, ?_⟩
  intro candidate
  obtain ⟨u, inlEq⟩ := bag_surjective candidate.inl
  obtain ⟨x, inrEq⟩ := bag_surjective candidate.inr
  obtain ⟨m, downEq⟩ := bag_surjective candidate.down
  have leftFac := candidate.fac_left
  have rightFac := candidate.fac_right
  rw [inlEq, downEq, bag_comp] at leftFac
  rw [inrEq, downEq, bag_comp] at rightFac
  have leftCoords : u + m = p := bag_injective leftFac
  have rightCoords : x + m = r := bag_injective rightFac
  have mLeP : m ≤ p := by
    rw [← leftCoords]
    exact Multiset.le_iff_exists_add.mpr ⟨u, add_comm u m⟩
  have mLeR : m ≤ r := by
    rw [← rightCoords]
    exact Multiset.le_iff_exists_add.mpr ⟨x, add_comm x m⟩
  have mLeK : m ≤ p ∩ r := Multiset.le_inter mLeP mLeR
  have uIs : p - m = u := by rw [← leftCoords, add_tsub_cancel_right]
  have xIs : r - m = x := by rw [← rightCoords, add_tsub_cancel_right]
  refine ⟨bag (p ∩ r - m), ⟨?_, ?_, ?_⟩, ?_⟩
  · show bag (p - p ∩ r) ≫ bag (p ∩ r - m) = candidate.inl
    rw [bag_comp, tsub_add_tsub_cancel Multiset.inter_le_left mLeK, uIs, inlEq]
  · show bag (r - p ∩ r) ≫ bag (p ∩ r - m) = candidate.inr
    rw [bag_comp, tsub_add_tsub_cancel Multiset.inter_le_right mLeK, xIs, inrEq]
  · show bag (p ∩ r - m) ≫ candidate.down = bag (p ∩ r)
    rw [downEq, bag_comp, tsub_add_cancel_of_le mLeK]
  · rintro mediator ⟨mediatesLeft, -, -⟩
    obtain ⟨e, mediatorEq⟩ := bag_surjective mediator
    have restated : bag (p - p ∩ r) ≫ bag e = bag u := by
      rw [← mediatorEq, ← inlEq]
      exact mediatesLeft
    rw [bag_comp] at restated
    have coords : p - p ∩ r + e = u := bag_injective restated
    have target : p - p ∩ r + (p ∩ r - m) = u := by
      rw [tsub_add_tsub_cancel Multiset.inter_le_left mLeK, uIs]
    rw [mediatorEq]
    exact congrArg bag (add_left_cancel (coords.trans target.symm))

/-- **A bound whose legs share nothing is least.**  The criterion, in the form a
concrete calculus uses it. -/
theorem isIdemPushout_bag (f g p r : Multiset α)
    (w : bag f ≫ bag p = bag g ≫ bag r) (shared : p ∩ r = 0) :
    IsIdemPushout (bag f) (bag g) (bag p) (bag r) w := by
  intro candidate
  obtain ⟨u, inlEq⟩ := bag_surjective candidate.inl
  obtain ⟨x, inrEq⟩ := bag_surjective candidate.inr
  obtain ⟨m, downEq⟩ := bag_surjective candidate.down
  have leftFac := candidate.fac_left
  have rightFac := candidate.fac_right
  rw [inlEq, downEq, bag_comp] at leftFac
  rw [inrEq, downEq, bag_comp] at rightFac
  have leftCoords : u + m = p := bag_injective leftFac
  have rightCoords : x + m = r := bag_injective rightFac
  have mLeP : m ≤ p := by
    rw [← leftCoords]
    exact Multiset.le_iff_exists_add.mpr ⟨u, add_comm u m⟩
  have mLeR : m ≤ r := by
    rw [← rightCoords]
    exact Multiset.le_iff_exists_add.mpr ⟨x, add_comm x m⟩
  have mZero : m = 0 :=
    le_antisymm (shared ▸ Multiset.le_inter mLeP mLeR) (Multiset.zero_le m)
  have uIs : u = p := by rw [← leftCoords, mZero, add_zero]
  have xIs : x = r := by rw [← rightCoords, mZero, add_zero]
  refine ⟨bag 0, ⟨?_, ?_, ?_⟩, ?_⟩
  · show bag p ≫ bag 0 = candidate.inl
    rw [bag_comp, add_zero, inlEq, uIs]
  · show bag r ≫ bag 0 = candidate.inr
    rw [bag_comp, add_zero, inrEq, xIs]
  · show bag 0 ≫ candidate.down = bag 0
    rw [downEq, bag_comp, zero_add, mZero]
  · rintro mediator ⟨mediatesLeft, -, -⟩
    obtain ⟨e, mediatorEq⟩ := bag_surjective mediator
    have restated : bag p ≫ bag e = bag u := by
      rw [← mediatorEq, ← inlEq]
      exact mediatesLeft
    rw [bag_comp] at restated
    have coords : p + e = u := bag_injective restated
    rw [mediatorEq]
    refine congrArg bag ?_
    have : p + e = p + 0 := by rw [coords, uIs, add_zero]
    exact add_left_cancel this

/-- **In the bag context category a bound is least exactly when its two legs
share nothing.**  The converse half is `BagRelativePushout.isIdemPushout_bag`;
this half cuts the shared part away with `BagRelativePushout.cutCandidate`. -/
theorem isIdemPushout_bag_iff {α : Type*} [DecidableEq α] (f g p r : Multiset α)
    (w : bag f ≫ bag p = bag g ≫ bag r) :
    IsIdemPushout (bag f) (bag g) (bag p) (bag r) w ↔ p ∩ r = 0 := by
  refine ⟨fun ipo => ?_, isIdemPushout_bag f g p r w⟩
  have coordinates : f + p = g + r := by
    rw [bag_comp, bag_comp] at w
    exact bag_injective w
  obtain ⟨mediator, ⟨mediatesLeft, -, -⟩, -⟩ :=
    ipo (BagRelativePushout.cutCandidate f g p r coordinates)
  obtain ⟨extra, mediatorEq⟩ := bag_surjective mediator
  have restated : bag p ≫ bag extra = bag (p - p ∩ r) := by
    rw [← mediatorEq]
    exact mediatesLeft
  rw [bag_comp] at restated
  have cut : p + extra = p - p ∩ r := bag_injective restated
  have total : p + (extra + p ∩ r) = p + 0 := by
    rw [add_zero, ← add_assoc, cut, tsub_add_cancel_of_le Multiset.inter_le_left]
  -- `extra + p ∩ r = 0` forces the shared part to be empty, by cardinality.
  have vanishes : extra + p ∩ r = 0 := add_left_cancel total
  have counted := congrArg Multiset.card vanishes
  simp only [Multiset.card_add, Multiset.card_zero] at counted
  exact Multiset.card_eq_zero.mp (by omega)

/-- **And therefore the congruence.**  Bisimilarity of the labelled transitions
a bag calculus induces is preserved by every context. -/
theorem congruence (rules : ReactionRule (Obj α) → Prop)
    {left right : Obj α ⟶ Obj α} (bisim : IPOBisimilar rules left right)
    (context : Obj α ⟶ Obj α) :
    IPOBisimilar rules (left ≫ context) (right ≫ context) := by
  refine ipoBisimilar_comp (fun _ agent rule _ => ?_) bisim context
  obtain ⟨agentBag, agentEq⟩ := bag_surjective agent
  obtain ⟨redexBag, redexEq⟩ := bag_surjective rule.redex
  rw [agentEq, redexEq]
  exact hasRelativePushouts agentBag redexBag

end Mettapedia.GSLT.BagRelativePushout
