import Mettapedia.CategoryTheory.GroundMonoidActionCategory
import Mettapedia.GSLT.Logic.RedexRelativeCongruence
import Mathlib.Data.Multiset.UnionInter
import Mathlib.Algebra.Order.Sub.Unbundled.Basic

/-!
# Complete relative pushouts for grounded multiset contexts

Closed agents and contexts have distinct endpoints. Intersection removes the
common outer context, and every competing candidate factors uniquely by its
remaining common multiset. The origin cannot be a competing context apex.
All origin-based spans have RPOs, including identity-origin spans; IPOs of
closed agents are exactly bounds with disjoint label and reaction context.
-/

set_option autoImplicit false

namespace Mettapedia.CategoryTheory.GroundMultiset

open _root_.CategoryTheory
open Mettapedia.GSLT.RelativePushout
open Mettapedia.GSLT.RedexRelativeCongruence
open GroundMonoidAction

universe u

variable {Payload : Type u}

instance multisetAction : MulAction (Multiplicative (Multiset Payload)) (Multiset Payload) where
  smul context value := context.toAdd + value
  one_smul value := zero_add value
  mul_smul first second value := add_assoc first.toAdd second.toAdd value

abbrev Category (Payload : Type u) := Object (Multiplicative (Multiset Payload)) (Multiset Payload)

def closed (value : Multiset Payload) : (.origin : Category Payload) ⟶ .interface := valueArrow value

def parallel (context : Multiset Payload) : (.interface : Category Payload) ⟶ .interface :=
  contextArrow (Multiplicative.ofAdd context)

@[simp] theorem closed_parallel (value context : Multiset Payload) :
    closed value ≫ parallel context = closed (value + context) :=
  congrArg Arrow.value (add_comm context value)

@[simp] theorem parallel_comp (first second : Multiset Payload) :
    parallel first ≫ parallel second = parallel (first + second) :=
  congrArg Arrow.context (congrArg Multiplicative.ofAdd (add_comm second first))

@[simp] theorem parallel_zero : parallel (0 : Multiset Payload) = 𝟙 (.interface : Category Payload) := rfl

theorem closed_injective : Function.Injective (closed (Payload := Payload)) := by
  intro first second same
  exact Arrow.value.inj same

theorem parallel_injective : Function.Injective (parallel (Payload := Payload)) := by
  intro first second same
  exact congrArg Multiplicative.toAdd (Arrow.context.inj same)

variable [DecidableEq Payload]

def cutCandidate (source redex label reaction : Multiset Payload)
    (square : source + label = redex + reaction) :
    Candidate (closed source) (closed redex) (parallel label) (parallel reaction) where
  apex := .interface
  inl := parallel (label - label ∩ reaction)
  inr := parallel (reaction - label ∩ reaction)
  down := parallel (label ∩ reaction)
  comm := by
    rw [closed_parallel, closed_parallel]
    refine congrArg closed (add_right_cancel (b := label ∩ reaction) ?_)
    rw [add_assoc, add_assoc, tsub_add_cancel_of_le Multiset.inter_le_left,
      tsub_add_cancel_of_le Multiset.inter_le_right]
    exact square
  fac_left := by rw [parallel_comp, tsub_add_cancel_of_le Multiset.inter_le_left]
  fac_right := by rw [parallel_comp, tsub_add_cancel_of_le Multiset.inter_le_right]

theorem cutCandidate_universal (source redex label reaction : Multiset Payload)
    (square : source + label = redex + reaction) :
    IsRelativePushout (cutCandidate source redex label reaction square) := by
  rintro ⟨apex, left, right, down, _, leftFac, rightFac⟩
  cases apex with
  | origin => cases left
  | interface =>
    cases left with
    | context left =>
      cases right with
      | context right =>
        cases down with
        | context down =>
          change parallel left.toAdd ≫ parallel down.toAdd = parallel label at leftFac
          change parallel right.toAdd ≫ parallel down.toAdd = parallel reaction at rightFac
          rw [parallel_comp] at leftFac rightFac
          have first : left.toAdd + down.toAdd = label := parallel_injective leftFac
          have second : right.toAdd + down.toAdd = reaction := parallel_injective rightFac
          have downLeLabel : down.toAdd ≤ label := by
            rw [← first]
            exact Multiset.le_iff_exists_add.mpr ⟨left.toAdd, add_comm _ _⟩
          have downLeReaction : down.toAdd ≤ reaction := by
            rw [← second]
            exact Multiset.le_iff_exists_add.mpr ⟨right.toAdd, add_comm _ _⟩
          have downLeCommon : down.toAdd ≤ label ∩ reaction := Multiset.le_inter downLeLabel downLeReaction
          have firstRest : label - down.toAdd = left.toAdd := by rw [← first, add_tsub_cancel_right]
          have secondRest : reaction - down.toAdd = right.toAdd := by rw [← second, add_tsub_cancel_right]
          refine ⟨parallel (label ∩ reaction - down.toAdd), ⟨?_, ?_, ?_⟩, ?_⟩
          · change parallel (label - label ∩ reaction) ≫ parallel (label ∩ reaction - down.toAdd) = parallel left.toAdd
            rw [parallel_comp, tsub_add_tsub_cancel Multiset.inter_le_left downLeCommon, firstRest]
          · change parallel (reaction - label ∩ reaction) ≫ parallel (label ∩ reaction - down.toAdd) = parallel right.toAdd
            rw [parallel_comp, tsub_add_tsub_cancel Multiset.inter_le_right downLeCommon, secondRest]
          · change parallel (label ∩ reaction - down.toAdd) ≫ parallel down.toAdd = parallel (label ∩ reaction)
            rw [parallel_comp, tsub_add_cancel_of_le downLeCommon]
          · rintro mediator ⟨leftLaw, _, _⟩
            cases mediator with
            | context extra =>
              change parallel (label - label ∩ reaction) ≫ parallel extra.toAdd = parallel left.toAdd at leftLaw
              rw [parallel_comp] at leftLaw
              have actual := parallel_injective leftLaw
              have canonical : label - label ∩ reaction + (label ∩ reaction - down.toAdd) = left.toAdd := by
                rw [tsub_add_tsub_cancel Multiset.inter_le_left downLeCommon, firstRest]
              change parallel extra.toAdd = parallel (label ∩ reaction - down.toAdd)
              exact congrArg parallel (add_left_cancel (actual.trans canonical.symm))

theorem closed_hasRelativePushouts (source redex : Multiset Payload) :
    HasRelativePushouts (closed source) (closed redex) := by
  intro target label reaction square
  cases label with
  | context label =>
    cases reaction with
    | context reaction =>
      change closed source ≫ parallel label.toAdd = closed redex ≫ parallel reaction.toAdd at square
      rw [closed_parallel, closed_parallel] at square
      have coordinates := closed_injective square
      exact ⟨cutCandidate source redex label.toAdd reaction.toAdd coordinates,
        cutCandidate_universal source redex label.toAdd reaction.toAdd coordinates⟩

omit [DecidableEq Payload] in
theorem identity_left_hasRelativePushouts {C : Type*} [_root_.CategoryTheory.Category C]
    {source target : C} (arrow : source ⟶ target) : HasRelativePushouts (𝟙 source) arrow := by
  intro bound left right square
  let candidate : Candidate (𝟙 source) arrow left right :=
    { apex := target, inl := arrow, inr := 𝟙 target, down := right,
      comm := by simp,
      fac_left := by simpa using square.symm,
      fac_right := by simp }
  refine ⟨candidate, fun other => ⟨other.inr, ⟨?_, ?_, ?_⟩, ?_⟩⟩
  · simpa [candidate] using other.comm.symm
  · simp [candidate]
  · exact other.fac_right
  · intro mediator laws
    simpa [candidate] using laws.2.1

omit [DecidableEq Payload] in
theorem identity_right_hasRelativePushouts {C : Type*} [_root_.CategoryTheory.Category C]
    {source target : C} (arrow : source ⟶ target) : HasRelativePushouts arrow (𝟙 source) := by
  intro bound left right square
  let candidate : Candidate arrow (𝟙 source) left right :=
    { apex := target, inl := 𝟙 target, inr := arrow, down := left,
      comm := by simp,
      fac_left := by simp,
      fac_right := by simpa using square }
  refine ⟨candidate, fun other => ⟨other.inl, ⟨?_, ?_, ?_⟩, ?_⟩⟩
  · simp [candidate]
  · simpa [candidate] using other.comm
  · exact other.fac_left
  · intro mediator laws
    simpa [candidate] using laws.1

/-- Condition 20.1 for every actual origin-based span of this grounded
parallel context category, with no restriction on the rule carrier. -/
theorem redex_relativePushouts {first second : Category Payload}
    (agent : (.origin : Category Payload) ⟶ first) (redex : (.origin : Category Payload) ⟶ second) :
    HasRelativePushouts agent redex := by
  cases agent with
  | identity => exact identity_left_hasRelativePushouts redex
  | value source =>
    cases redex with
    | identity => exact identity_right_hasRelativePushouts (closed source)
    | value redex => exact closed_hasRelativePushouts source redex

theorem closed_ipo_iff (source redex label reaction : Multiset Payload)
    (square : closed source ≫ parallel label = closed redex ≫ parallel reaction) :
    IsIdemPushout (closed source) (closed redex) (parallel label) (parallel reaction) square ↔
      label ∩ reaction = 0 := by
  have coordinates : source + label = redex + reaction := by
    rw [closed_parallel, closed_parallel] at square
    exact closed_injective square
  constructor
  · intro least
    obtain ⟨mediator, ⟨leftLaw, _, _⟩, _⟩ := least (cutCandidate source redex label reaction coordinates)
    cases mediator with
    | context extra =>
      change parallel label ≫ parallel extra.toAdd = parallel (label - label ∩ reaction) at leftLaw
      rw [parallel_comp] at leftLaw
      have cut := parallel_injective leftLaw
      have zero : extra.toAdd + label ∩ reaction = 0 := by
        apply add_left_cancel (a := label)
        rw [← add_assoc, cut, tsub_add_cancel_of_le Multiset.inter_le_left, add_zero]
      have counted := congrArg Multiset.card zero
      simp only [Multiset.card_add, Multiset.card_zero] at counted
      exact Multiset.card_eq_zero.mp (by omega)
  · intro shared
    have universal := cutCandidate_universal source redex label reaction coordinates
    have same : cutCandidate source redex label reaction coordinates =
        Candidate.self (closed source) (closed redex) (parallel label) (parallel reaction) square := by
      simp only [cutCandidate, Candidate.self, shared, tsub_zero, parallel_zero]
    rw [same] at universal
    exact universal

/-- Condition 20.2 at every actual context and interface. -/
theorem bisimulation_congruence (rules : ReactionRule (.origin : Category Payload) → Prop)
    {source target : Category Payload}
    {left right : (.origin : Category Payload) ⟶ source}
    (related : IPOBisimilar rules left right) (context : source ⟶ target) :
    IPOBisimilar rules (left ≫ context) (right ≫ context) :=
  ipoBisimilar_comp (fun _ agent rule _ => redex_relativePushouts agent rule.redex) related context

end Mettapedia.CategoryTheory.GroundMultiset
