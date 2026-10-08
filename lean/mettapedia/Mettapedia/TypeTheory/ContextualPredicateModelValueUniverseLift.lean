import Mettapedia.TypeTheory.ContextualPredicateModelUniverseLift
import Mettapedia.TypeTheory.ContextualTelescopeUniverseLift
import Mettapedia.TypeTheory.ContextualSumUniverseLift

/-!
# Complete dependent values through contextual carrier lifts

Application, dependent pairing, second projection and full-motive sum
elimination retain both their original family and complete supplied section.
The comparison uses the earned self-extension and sum-packing readouts.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualPredicateModelUniverseLift

open Mettapedia.GSLT.Core.ContextualLadder
open ContextualPredicateModel ContextualModelTelescopes ContextualCwfUniverseLift
open ContextualSumComprehension
open ContextualProductComparison (selfExtend)

universe c s t m p uc vs wt ms
variable {C : CwfWithTerminal.{c,s,t,m}}

theorem lift_application_value (localModel : LocalModel.{c,s,t,m,p} C) {Γ : C.toCwf.Ctx}
    (A : C.toCwf.Ty Γ) (B : C.toCwf.Ty (C.toCwf.ext Γ A))
    (f : C.toCwf.Tm Γ (localModel.products.pi A B)) (a : C.toCwf.Tm Γ A) :
    (⟨(Raised.{c, s, t, m, uc, vs, wt, ms} C.toCwf).tySub (ULift.up B) (selfExtend (Raised.{c, s, t, m, uc, vs, wt, ms} C.toCwf) (ULift.up a)),
      (liftProducts localModel.products).app (ULift.up f) (ULift.up a)⟩ :
      Value (Raised.{c, s, t, m, uc, vs, wt, ms} C.toCwf) (ULift.up Γ)) =
      liftValue (⟨C.toCwf.tySub B (selfExtend C.toCwf a), localModel.products.app f a⟩ :
        Value C.toCwf Γ) := by
  apply liftedValue_eq
  · exact congrArg (C.toCwf.tySub B) (selfExtend_readout (ULift.up a))
  · exact products_app_readout localModel.products (ULift.up f) (ULift.up a)

theorem lift_second_value (localModel : LocalModel.{c,s,t,m,p} C) {Γ : C.toCwf.Ctx}
    (A : C.toCwf.Ty Γ) (B : C.toCwf.Ty (C.toCwf.ext Γ A))
    (p : C.toCwf.Tm Γ (localModel.sums.operations.sigma A B)) :
    (⟨(Raised.{c, s, t, m, uc, vs, wt, ms} C.toCwf).tySub (ULift.up B)
        (selfExtend (Raised.{c, s, t, m, uc, vs, wt, ms} C.toCwf)
          ((liftStableSums localModel.sums).operations.fst (ULift.up p))),
      (liftStableSums localModel.sums).operations.snd (ULift.up p)⟩ :
      Value (Raised.{c, s, t, m, uc, vs, wt, ms} C.toCwf) (ULift.up Γ)) =
      liftValue (⟨C.toCwf.tySub B (selfExtend C.toCwf (localModel.sums.operations.fst p)),
        localModel.sums.operations.snd p⟩ : Value C.toCwf Γ) := by
  apply liftedValue_eq
  · exact congrArg (C.toCwf.tySub B) (selfExtend_readout (ULift.up (localModel.sums.operations.fst p)))
  · exact sums_snd_readout localModel.sums.operations (ULift.up p)

theorem lift_pair_value (localModel : LocalModel.{c,s,t,m,p} C) {Γ : C.toCwf.Ctx}
    (A : C.toCwf.Ty Γ) (B : C.toCwf.Ty (C.toCwf.ext Γ A)) (a : C.toCwf.Tm Γ A)
    (b : C.toCwf.Tm Γ (C.toCwf.tySub B (selfExtend C.toCwf a)))
    (b' : (Raised.{c, s, t, m, uc, vs, wt, ms} C.toCwf).Tm (ULift.up Γ)
      ((Raised.{c, s, t, m, uc, vs, wt, ms} C.toCwf).tySub (ULift.up B) (selfExtend (Raised.{c, s, t, m, uc, vs, wt, ms} C.toCwf) (ULift.up a))))
    (bodies : HEq b'.down b) :
    (⟨ULift.up (localModel.sums.operations.sigma A B),
      (liftStableSums localModel.sums).operations.pair (ULift.up a) b'⟩ :
      Value (Raised.{c, s, t, m, uc, vs, wt, ms} C.toCwf) (ULift.up Γ)) =
      liftValue (⟨localModel.sums.operations.sigma A B, localModel.sums.operations.pair a b⟩ :
        Value C.toCwf Γ) := by
  apply liftedValue_eq
  · rfl
  · have second : cast (congrArg (C.toCwf.Tm Γ)
        (congrArg (C.toCwf.tySub B) (selfExtend_readout (ULift.up a)))) b'.down = b :=
      eq_of_heq ((cast_heq _ _).trans bodies)
    change HEq (localModel.sums.operations.pair a _) (localModel.sums.operations.pair a b)
    exact heq_of_eq (congrArg (localModel.sums.operations.pair a) second)

theorem lift_elimination_value (localModel : LocalModel.{c,s,t,m,p} C) {Γ : C.toCwf.Ctx}
    (A : C.toCwf.Ty Γ) (B : C.toCwf.Ty (C.toCwf.ext Γ A))
    (M : C.toCwf.Ty (sumContext localModel.sums A B))
    (body : C.toCwf.Tm (tupleContext A B) (C.toCwf.tySub M (pack localModel.sums A B)))
    (body' : (Raised.{c, s, t, m, uc, vs, wt, ms} C.toCwf).Tm
      (tupleContext (ULift.up A) (ULift.up B))
      ((Raised.{c, s, t, m, uc, vs, wt, ms} C.toCwf).tySub (ULift.up M) (pack (liftStableSums localModel.sums) (ULift.up A) (ULift.up B))))
    (bodies : HEq body'.down body) (p : C.toCwf.Tm Γ (localModel.sums.operations.sigma A B)) :
    (⟨(Raised.{c, s, t, m, uc, vs, wt, ms} C.toCwf).tySub (ULift.up M) (selfExtend (Raised.{c, s, t, m, uc, vs, wt, ms} C.toCwf) (ULift.up p)),
      (Raised.{c, s, t, m, uc, vs, wt, ms} C.toCwf).tmSub
        (eliminate (liftStableSums localModel.sums) (ULift.up A) (ULift.up B) (ULift.up M) body')
        (selfExtend (Raised.{c, s, t, m, uc, vs, wt, ms} C.toCwf) (ULift.up p))⟩ :
      Value (Raised.{c, s, t, m, uc, vs, wt, ms} C.toCwf) (ULift.up Γ)) =
      liftValue (⟨C.toCwf.tySub M (selfExtend C.toCwf p),
        C.toCwf.tmSub (eliminate localModel.sums A B M body) (selfExtend C.toCwf p)⟩ :
          Value C.toCwf Γ) := by
  apply liftedValue_eq
  · exact congrArg (C.toCwf.tySub M) (selfExtend_readout (ULift.up p))
  · have transported : cast (congrArg (C.toCwf.Tm (tupleContext A B))
        (congrArg (C.toCwf.tySub M) (pack_down localModel.sums (ULift.up A) (ULift.up B))))
        body'.down = body := eq_of_heq ((cast_heq _ _).trans bodies)
    have resultSection := elimination_down localModel.sums (ULift.up A) (ULift.up B) (ULift.up M) body'
    have completeSection := resultSection.trans
      (congrArg (eliminate localModel.sums A B M) transported)
    change HEq (C.toCwf.tmSub
      (eliminate (liftStableSums localModel.sums) (ULift.up A) (ULift.up B) (ULift.up M) body').down
      (selfExtend (Raised.{c, s, t, m, uc, vs, wt, ms} C.toCwf) (ULift.up p)).down) _
    exact (heq_of_eq (congrArg
      (fun sectionValue => C.toCwf.tmSub sectionValue
        (selfExtend (Raised.{c, s, t, m, uc, vs, wt, ms} C.toCwf) (ULift.up p)).down) completeSection)).trans
          (term_action_eq _ (selfExtend_readout (ULift.up p)))

end Mettapedia.TypeTheory.ContextualPredicateModelUniverseLift
