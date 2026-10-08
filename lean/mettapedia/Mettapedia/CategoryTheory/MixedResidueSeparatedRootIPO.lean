import Mettapedia.CategoryTheory.MixedResidueRelativePushout

/-!
# Relative minimality of distinct outer context shapes

A zero-residue constructor frame and a parallel context have no common
outer frame or residue. Their independently constructed common factor is
the complete bound itself, so every actual commuting closed-value square
with these two contexts is an IPO. This includes an empty input placed
beside a nonempty constructor term; no faithful ground action is used.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.CategoryTheory.MixedResidue

open _root_.CategoryTheory
open Mettapedia.GSLT.RelativePushout

universe u v w z

variable {Vertex : Type u} [Quiver.{v} Vertex] {Payload : Vertex → Type w}
variable [∀ sort, DecidableEq (Payload sort)]
variable [∀ target : Vertex, DecidableEq (Σ middle : Vertex, middle ⟶ target)]

theorem frame_parallel_isIdemPushout
    (action : Action.{u,v,w,z} Payload)
    {source middle target : Vertex}
    (first : action.Value source) (second : action.Value target)
    (edge : middle ⟶ target) (inner : Context Payload source middle)
    (residue : Multiset (Payload target))
    (square : action.read (.frame 0 edge inner) first =
      action.read (.parallel residue) second) :
    IsIdemPushout (valueArrow action first) (valueArrow action second)
      (contextArrow action (.frame 0 edge inner))
      (contextArrow action (.parallel residue)) (congrArg Arrow.value square) := by
  have factorRead : commonFactor (.frame 0 edge inner) (.parallel residue) =
      Factorization.parallel (.frame 0 edge inner) (.parallel residue) := by
    rw [commonFactor.eq_def]
  intro candidate
  rcases candidate with ⟨apex, left, right, down, _comm, leftFactors, rightFactors⟩
  cases apex with
  | origin => cases left
  | interface apex =>
    cases left with
    | context left =>
      cases right with
      | context right =>
        cases down with
        | context down =>
          let other : Factorization (.frame 0 edge inner) (.parallel residue) := {
            apex := apex, inl := left, inr := right, down := down,
            fac_left := Arrow.context.inj leftFactors,
            fac_right := Arrow.context.inj rightFactors }
          have universal := Factorization.commonFactor_universal other
          rw [factorRead] at universal
          simp only [Factorization.Mediates, Factorization.parallel, Context.outerBag,
            Multiset.zero_inter, Context.subtractOuter, tsub_zero] at universal
          obtain ⟨mediator, ⟨leftLaw, rightLaw, downLaw⟩, unique⟩ := universal
          refine ⟨Arrow.context mediator, ⟨congrArg Arrow.context leftLaw,
            congrArg Arrow.context rightLaw, congrArg Arrow.context downLaw⟩, ?_⟩
          intro alternative laws
          cases alternative with
          | context alternative =>
            apply congrArg Arrow.context
            exact unique alternative ⟨Arrow.context.inj laws.1,
              Arrow.context.inj laws.2.1, Arrow.context.inj laws.2.2⟩

end Mettapedia.CategoryTheory.MixedResidue
