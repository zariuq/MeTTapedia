import Mettapedia.OSLF.Framework.SortedCommutativeContextReactiveSystem

/-!
# Earned monicity and complete probe squares

Fixed post-context cancellation comes from actual normal-form composition,
and cancellation on closed arrows comes from the independently earned local
free-frame and residue actions. Thus every raw quotient arrow is monic. A
probe square with identity reaction context is consequently an actual IPO:
every competitor factors uniquely through its complete supplied right leg.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.SortedCommutative

open _root_.CategoryTheory
open Mettapedia.GSLT.RelativePushout

universe u v

variable {signature : Mettapedia.OSLF.SortedConstructors.Signature.{u,v}}
variable {Parallel : signature.Srt → Prop}

instance rawArrow_mono {source target : RawObject signature Parallel} (arrow : source ⟶ target) : Mono arrow where
  right_cancellation := by
    intro incoming first second same
    cases arrow with
    | identity => cases first; cases second; rfl
    | value supplied => cases first; cases second; rfl
    | context suppliedContext =>
      cases first with
      | value before =>
        cases second with
        | value after =>
          have values := RawArrow.value.inj same
          have readings := (ContextClass.normalize_filling suppliedContext before).trans
            (values.trans (ContextClass.normalize_filling suppliedContext after).symm)
          exact congrArg RawArrow.value
            ((mixedAction signature Parallel).read_injective (mixedCancellative signature Parallel)
              (normalizeContext suppliedContext) readings)
      | context before =>
        cases second with
        | context after =>
          have contexts := RawArrow.context.inj same
          have normalized := (ContextClass.normalize_comp before suppliedContext).symm.trans
            ((congrArg normalizeContext contexts).trans (ContextClass.normalize_comp after suppliedContext))
          exact congrArg RawArrow.context ((contextEquiv _ _).injective
            (Mettapedia.CategoryTheory.MixedResidue.Context.comp_cancel_post
              (normalizeContext suppliedContext) normalized))

theorem raw_right_identity_isIPO {root source target : RawObject signature Parallel}
    {agent : root ⟶ source} {redex : root ⟶ target} (label : source ⟶ target)
    (square : agent ≫ label = redex) :
    IsIdemPushout agent redex label (𝟙 target) (square.trans (Category.comp_id redex).symm) := by
  intro candidate
  refine ⟨candidate.inr, ?_, ?_⟩
  · refine ⟨?_, Category.id_comp _, candidate.fac_right⟩
    change label ≫ candidate.inr = candidate.inl
    apply (cancel_mono candidate.down).mp
    rw [Category.assoc, candidate.fac_right, Category.comp_id, candidate.fac_left]
  · intro other laws
    exact (cancel_mono candidate.down).mp (laws.2.2.trans candidate.fac_right.symm)

end Mettapedia.OSLF.SortedCommutative
