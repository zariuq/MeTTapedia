import Mettapedia.CategoryTheory.MixedResidueFactorization
import Mettapedia.CategoryTheory.MixedResidueGroundCategory
import Mettapedia.CategoryTheory.GroundMultisetRelativePushout

/-!
# Complete relative pushouts for grounded mixed contexts

The independently constructed greatest outer factor and local frame/residue
cancellation earn its closed-value commuting square. Every categorical
candidate then factors uniquely through it. Origin-identity spans are included.
Literal-label IPO bisimulation consequently respects every actual mixed
context; payload labels identified by a further behavioral relation are a
separate condition.
-/

set_option autoImplicit false

namespace Mettapedia.CategoryTheory.MixedResidue

open _root_.CategoryTheory
open Mettapedia.GSLT.RelativePushout
open Mettapedia.GSLT.RedexRelativeCongruence

universe u v w z

variable {Vertex : Type u} [Quiver.{v} Vertex] {Payload : Vertex → Type w}
variable [∀ sort, DecidableEq (Payload sort)]
variable [∀ target : Vertex, DecidableEq (Σ middle : Vertex, middle ⟶ target)]
variable (action : Action.{u,v,w,z} Payload) (qualified : action.Cancellative)

def commonCandidate {first second target : Vertex}
    (firstValue : action.Value first) (secondValue : action.Value second)
    (left : Context Payload first target) (right : Context Payload second target)
    (square : action.read left firstValue = action.read right secondValue) :
    Candidate (valueArrow action firstValue) (valueArrow action secondValue)
      (contextArrow action left) (contextArrow action right) where
  apex := .interface (commonFactor left right).apex
  inl := .context (commonFactor left right).inl
  inr := .context (commonFactor left right).inr
  down := .context (commonFactor left right).down
  comm := by
    apply congrArg Arrow.value
    apply action.read_injective qualified (commonFactor left right).down
    rw [← action.read_comp, ← action.read_comp, (commonFactor left right).fac_left,
      (commonFactor left right).fac_right]
    exact square
  fac_left := congrArg Arrow.context (commonFactor left right).fac_left
  fac_right := congrArg Arrow.context (commonFactor left right).fac_right

theorem commonCandidate_universal {first second target : Vertex}
    (firstValue : action.Value first) (secondValue : action.Value second)
    (left : Context Payload first target) (right : Context Payload second target)
    (square : action.read left firstValue = action.read right secondValue) :
    IsRelativePushout (commonCandidate action qualified firstValue secondValue left right square) := by
  rintro ⟨otherApex, otherLeft, otherRight, otherDown, _, leftFactors, rightFactors⟩
  cases otherApex with
  | origin => cases otherLeft
  | interface otherApex =>
    cases otherLeft with
    | context otherLeft =>
      cases otherRight with
      | context otherRight =>
        cases otherDown with
        | context otherDown =>
          let other : Factorization left right := {
            apex := otherApex, inl := otherLeft, inr := otherRight, down := otherDown,
            fac_left := Arrow.context.inj leftFactors,
            fac_right := Arrow.context.inj rightFactors }
          obtain ⟨mediator, ⟨leftLaw, rightLaw, downLaw⟩, unique⟩ :=
            Factorization.commonFactor_universal other
          refine ⟨Arrow.context mediator,
            ⟨congrArg Arrow.context leftLaw, congrArg Arrow.context rightLaw,
              congrArg Arrow.context downLaw⟩, ?_⟩
          intro alternative laws
          cases alternative with
          | context alternative =>
            apply congrArg Arrow.context
            exact unique alternative ⟨Arrow.context.inj laws.1, Arrow.context.inj laws.2.1,
              Arrow.context.inj laws.2.2⟩

include qualified

theorem closed_hasRelativePushouts {first second : Vertex}
    (firstValue : action.Value first) (secondValue : action.Value second) :
    HasRelativePushouts (valueArrow action firstValue) (valueArrow action secondValue) := by
  intro target left right square
  cases target with
  | origin => cases left
  | interface target =>
    cases left with
    | context left =>
      cases right with
      | context right =>
        have readSquare := Arrow.value.inj square
        exact ⟨commonCandidate action qualified firstValue secondValue left right readSquare,
          commonCandidate_universal action qualified firstValue secondValue left right readSquare⟩

/-- All actual origin-based spans satisfy the relative-pushout condition. -/
theorem redex_relativePushouts {first second : Object action}
    (agent : (.origin : Object action) ⟶ first) (redex : (.origin : Object action) ⟶ second) :
    HasRelativePushouts agent redex := by
  cases agent with
  | identity => exact GroundMultiset.identity_left_hasRelativePushouts redex
  | value supplied =>
    cases redex with
    | identity => exact GroundMultiset.identity_right_hasRelativePushouts (valueArrow action supplied)
    | value redex => exact closed_hasRelativePushouts action qualified supplied redex

theorem bisimulation_congruence (rules : ReactionRule (.origin : Object action) → Prop)
    {source target : Object action}
    {left right : (.origin : Object action) ⟶ source}
    (related : IPOBisimilar rules left right) (context : source ⟶ target) :
    IPOBisimilar rules (left ≫ context) (right ≫ context) :=
  ipoBisimilar_comp (fun _ agent rule _ => redex_relativePushouts action qualified agent rule.redex)
    related context

end Mettapedia.CategoryTheory.MixedResidue
