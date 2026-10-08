import Mettapedia.CategoryTheory.GroundPathCategory
import Mettapedia.GSLT.Logic.RelativePushout
import Mathlib.Data.Nat.Find

/-!
# Relative pushouts of actual closed-value/context bounds

Two descents factoring the same path are comparable by suffix length. Among
the actual commuting candidates of a closed-value bound there is therefore a
maximal descent, bounded by the supplied context length. Path cancellation
earns all three mediating equations and uniqueness. This proof does not cancel
the action on closed values or assume that two hole positions have different
ground readouts.
-/

set_option autoImplicit false

namespace Mettapedia.CategoryTheory.GroundPath

open _root_.CategoryTheory
open Mettapedia.GSLT.RelativePushout

universe u v w

variable {V : Type u} [Quiver.{v} V]

/-- Suffixes of a single path are comparable, including different interfaces. -/
theorem suffix_factor {source first second target : V}
    (firstPrefix : Quiver.Path source first) (long : Quiver.Path first target)
    (secondPrefix : Quiver.Path source second) (short : Quiver.Path second target)
    (same : firstPrefix.comp long = secondPrefix.comp short)
    (ordered : short.length ≤ long.length) :
    ∃ middle : Quiver.Path first second, middle.comp short = long := by
  induction short generalizing first with
  | nil => exact ⟨long, rfl⟩
  | @cons middle target previous frame inductionHypothesis =>
    cases long with
    | nil => simp only [Quiver.Path.length_cons, Quiver.Path.length_nil] at ordered; omega
    | @cons otherMiddle _ otherPrevious otherFrame =>
      simp only [Quiver.Path.comp_cons, Quiver.Path.cons.injEq] at same
      obtain rfl := same.1
      have shorter : previous.length ≤ otherPrevious.length := by
        simpa only [Quiver.Path.length_cons, Nat.add_le_add_iff_right] using ordered
      obtain ⟨factor, factors⟩ := inductionHypothesis firstPrefix otherPrevious
        same.2.1.eq shorter
      refine ⟨factor, ?_⟩
      rw [Quiver.Path.comp_cons, factors, same.2.2.eq]

variable (action : Action.{u,v,w} V)
variable {first second target : V}

/-- A candidate expressed in actual paths and actual closed-value readouts. -/
structure PathCandidate (firstValue : action.Value first) (secondValue : action.Value second)
    (left : Quiver.Path first target) (right : Quiver.Path second target) where
  apex : V
  inl : Quiver.Path first apex
  inr : Quiver.Path second apex
  down : Quiver.Path apex target
  comm : action.path inl firstValue = action.path inr secondValue
  fac_left : inl.comp down = left
  fac_right : inr.comp down = right

namespace PathCandidate

variable {action}
variable {firstValue : action.Value first} {secondValue : action.Value second}
variable {left : Quiver.Path first target} {right : Quiver.Path second target}

def self (commutes : action.path left firstValue = action.path right secondValue) :
    PathCandidate action firstValue secondValue left right where
  apex := target
  inl := left
  inr := right
  down := .nil
  comm := commutes
  fac_left := rfl
  fac_right := rfl

theorem descent_bounded (candidate : PathCandidate action firstValue secondValue left right) :
    candidate.down.length ≤ left.length := by
  have counted := congrArg Quiver.Path.length candidate.fac_left
  rw [Quiver.Path.length_comp] at counted
  omega

/-- The maximum is taken over genuinely commuting candidates, not merely all
common suffixes whose action might identify unequal inner values. -/
theorem maximal_descent (commutes : action.path left firstValue = action.path right secondValue) :
    ∃ candidate : PathCandidate action firstValue secondValue left right,
      ∀ other : PathCandidate action firstValue secondValue left right,
        other.down.length ≤ candidate.down.length := by
  classical
  let attained : Nat → Prop := fun length =>
    ∃ candidate : PathCandidate action firstValue secondValue left right,
      candidate.down.length = length
  have zero : attained 0 := ⟨self commutes, rfl⟩
  obtain ⟨candidate, counted⟩ := Nat.findGreatest_spec
    (P := attained) (Nat.zero_le left.length) zero
  refine ⟨candidate, fun other => ?_⟩
  rw [counted]
  exact Nat.le_findGreatest other.descent_bounded ⟨other, rfl⟩

def Mediates (candidate other : PathCandidate action firstValue secondValue left right)
    (factor : Quiver.Path candidate.apex other.apex) : Prop :=
  candidate.inl.comp factor = other.inl ∧ candidate.inr.comp factor = other.inr ∧
    factor.comp other.down = candidate.down

/-- Complete factorization and uniqueness follow from actual suffix factoring
and path cancellation; no injectivity of the value action is used. -/
theorem maximal_is_universal
    (candidate : PathCandidate action firstValue secondValue left right)
    (maximal : ∀ other : PathCandidate action firstValue secondValue left right,
      other.down.length ≤ candidate.down.length)
    (other : PathCandidate action firstValue secondValue left right) :
    ∃! factor : Quiver.Path candidate.apex other.apex, Mediates candidate other factor := by
  obtain ⟨factor, descent⟩ := suffix_factor candidate.inl candidate.down other.inl other.down
    (candidate.fac_left.trans other.fac_left.symm) (maximal other)
  refine ⟨factor, ⟨?_, ?_, descent⟩, ?_⟩
  · apply other.down.comp_injective_left
    change (candidate.inl.comp factor).comp other.down = other.inl.comp other.down
    rw [Quiver.Path.comp_assoc, descent, candidate.fac_left, other.fac_left]
  · apply other.down.comp_injective_left
    change (candidate.inr.comp factor).comp other.down = other.inr.comp other.down
    rw [Quiver.Path.comp_assoc, descent, candidate.fac_right, other.fac_right]
  · intro alternative compatible
    exact other.down.comp_injective_left (compatible.2.2.trans descent.symm)

def categorical (candidate : PathCandidate action firstValue secondValue left right) :
    Candidate (valueArrow action firstValue) (valueArrow action secondValue)
      (contextArrow action left) (contextArrow action right) where
  apex := .interface candidate.apex
  inl := .context candidate.inl
  inr := .context candidate.inr
  down := .context candidate.down
  comm := congrArg Arrow.value candidate.comm
  fac_left := congrArg Arrow.context candidate.fac_left
  fac_right := congrArg Arrow.context candidate.fac_right

theorem descent_right_bounded (candidate : PathCandidate action firstValue secondValue left right) :
    candidate.down.length ≤ right.length := by
  have counted := congrArg Quiver.Path.length candidate.fac_right
  rw [Quiver.Path.length_comp] at counted
  omega

theorem categorical_isRelativePushout
    (candidate : PathCandidate action firstValue secondValue left right)
    (maximal : ∀ other : PathCandidate action firstValue secondValue left right,
      other.down.length ≤ candidate.down.length) : IsRelativePushout candidate.categorical := by
  intro other
  rcases other with ⟨otherApex, otherInl, otherInr, otherDescent, otherComm, otherFacLeft, otherFacRight⟩
  cases otherApex with
  | origin => cases otherInl
  | interface otherApex =>
    cases otherInl with
    | context otherLeft =>
      cases otherInr with
      | context otherRight =>
        cases otherDescent with
        | context otherDown =>
          let pathOther : PathCandidate action firstValue secondValue left right := {
            apex := otherApex, inl := otherLeft, inr := otherRight, down := otherDown,
            comm := Arrow.value.inj otherComm,
            fac_left := Arrow.context.inj otherFacLeft,
            fac_right := Arrow.context.inj otherFacRight }
          obtain ⟨factor, ⟨leftFactors, rightFactors, descent⟩, unique⟩ :=
            PathCandidate.maximal_is_universal candidate maximal pathOther
          refine ⟨Arrow.context factor,
            ⟨congrArg Arrow.context leftFactors, congrArg Arrow.context rightFactors,
              congrArg Arrow.context descent⟩, ?_⟩
          intro alternative compatible
          cases alternative with
          | context alternativePath =>
            apply congrArg Arrow.context
            exact unique alternativePath
              ⟨Arrow.context.inj compatible.1, Arrow.context.inj compatible.2.1,
                Arrow.context.inj compatible.2.2⟩

end PathCandidate

/-- Every bound on two closed values has an actual relative pushout in the
ground/context category. Its construction retains all sorted interfaces. -/
theorem ground_hasRelativePushouts {first second : V}
    (firstValue : action.Value first) (secondValue : action.Value second) :
    HasRelativePushouts (valueArrow action firstValue) (valueArrow action secondValue) := by
  intro apex left right commutes
  cases apex with
  | origin => cases left
  | interface target =>
    cases left with
    | context leftPath =>
      cases right with
      | context rightPath =>
        have groundCommutes : action.path leftPath firstValue = action.path rightPath secondValue :=
          Arrow.value.inj commutes
        obtain ⟨candidate, maximal⟩ := PathCandidate.maximal_descent groundCommutes
        refine ⟨candidate.categorical, ?_⟩
        exact PathCandidate.categorical_isRelativePushout candidate maximal

/-- A bound with the actual identity reaction context is an idem pushout.
The proof checks every candidate; a context that can be removed from an
identity path has zero length and cannot remove a retained probe frame. -/
theorem ground_identityReactionIPO {source target : V}
    (supplied : action.Value source) (redex : action.Value target)
    (label : Quiver.Path source target)
    (square : valueArrow action supplied ≫ contextArrow action label =
      valueArrow action redex ≫ 𝟙 (.interface target : Object action)) :
    IsIdemPushout (valueArrow action supplied) (valueArrow action redex)
      (contextArrow action label) (𝟙 (.interface target : Object action)) square := by
  have commutes : action.path label supplied = action.path (.nil : Quiver.Path target target) redex :=
    Arrow.value.inj square
  let candidate : PathCandidate action supplied redex label (.nil : Quiver.Path target target) :=
    PathCandidate.self commutes
  have universal := PathCandidate.categorical_isRelativePushout candidate
    (fun other => other.descent_right_bounded)
  exact universal

/-- An IPO excludes every genuinely commuting candidate with a nonempty
context descent. This is the converse minimality test used by probe labels. -/
theorem ipo_no_context_descent {first second target : V}
    (firstValue : action.Value first) (secondValue : action.Value second)
    (left : Quiver.Path first target) (right : Quiver.Path second target)
    (square : valueArrow action firstValue ≫ contextArrow action left =
      valueArrow action secondValue ≫ contextArrow action right)
    (ipo : IsIdemPushout (valueArrow action firstValue) (valueArrow action secondValue)
      (contextArrow action left) (contextArrow action right) square)
    (candidate : PathCandidate action firstValue secondValue left right) :
    candidate.down.length = 0 := by
  obtain ⟨section_, splits⟩ := ipo.down_splits candidate.categorical
  cases section_ with
  | context suppliedPath =>
    have paths := Arrow.context.inj splits
    have counted := congrArg Quiver.Path.length paths
    simp only [Quiver.Path.length_comp, Quiver.Path.length_nil] at counted
    omega

end Mettapedia.CategoryTheory.GroundPath
