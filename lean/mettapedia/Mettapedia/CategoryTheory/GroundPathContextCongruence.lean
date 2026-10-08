import Mettapedia.CategoryTheory.GroundPathRelativePushout
import Mettapedia.GSLT.Logic.RedexRelativeCongruence

/-!
# Earned contextual congruence for closed-value path categories

Origin-identity spans have explicit universal candidates, and all other closed
spans have the actual path RPO. The shared IPO replay theorem therefore earns
literal-label bisimulation congruence for every typed path context and every
chosen rule set. Behavioral comparison of labels is a separate question.
-/

set_option autoImplicit false

namespace Mettapedia.CategoryTheory.GroundPath

open _root_.CategoryTheory
open Mettapedia.GSLT.RelativePushout
open Mettapedia.GSLT.RedexRelativeCongruence

universe u v w

theorem identity_left_hasRPO {C : Type u} [Category.{v} C] {first second : C}
    (arrow : first ⟶ second) : HasRelativePushouts (𝟙 first) arrow := by
  intro target left right square
  let selected : Candidate (𝟙 first) arrow left right :=
    { apex := second
      inl := arrow
      inr := 𝟙 second
      down := right
      comm := by simp
      fac_left := by simpa only [Category.id_comp] using square.symm
      fac_right := Category.id_comp right }
  refine ⟨selected, ?_⟩
  intro other
  refine ⟨other.inr, ?_, ?_⟩
  · exact ⟨by simpa only [selected, Category.id_comp] using other.comm.symm,
      Category.id_comp _, other.fac_right⟩
  · intro mediator equations
    simpa only [selected, Category.id_comp] using equations.2.1

theorem identity_right_hasRPO {C : Type u} [Category.{v} C] {first second : C}
    (arrow : first ⟶ second) : HasRelativePushouts arrow (𝟙 first) := by
  intro target left right square
  let selected : Candidate arrow (𝟙 first) left right :=
    { apex := second
      inl := 𝟙 second
      inr := arrow
      down := left
      comm := by simp
      fac_left := Category.id_comp left
      fac_right := by simpa only [Category.id_comp] using square }
  refine ⟨selected, ?_⟩
  intro other
  refine ⟨other.inl, ?_, ?_⟩
  · exact ⟨Category.id_comp _, by simpa only [selected, Category.id_comp] using other.comm,
      other.fac_left⟩
  · intro mediator equations
    simpa only [selected, Category.id_comp] using equations.1

variable {V : Type u} [Quiver.{v} V] (action : Action.{u,v,w} V)

theorem origin_hasRelativePushouts {first second : Object action}
    (left : (.origin : Object action) ⟶ first) (right : (.origin : Object action) ⟶ second) :
    HasRelativePushouts left right := by
  cases left with
  | identity => exact identity_left_hasRPO right
  | value firstValue =>
    cases right with
    | identity => exact identity_right_hasRPO (valueArrow action firstValue)
    | value secondValue => exact ground_hasRelativePushouts action firstValue secondValue

theorem context_bisimulation_congruence
    (rules : ReactionRule (.origin : Object action) → Prop) {first second : Object action}
    (left right : (.origin : Object action) ⟶ first)
    (related : IPOBisimilar rules left right) (context : first ⟶ second) :
    IPOBisimilar rules (left ≫ context) (right ≫ context) :=
  ipoBisimilar_comp (fun _ agent rule _ => origin_hasRelativePushouts action agent rule.redex)
    related context

end Mettapedia.CategoryTheory.GroundPath
