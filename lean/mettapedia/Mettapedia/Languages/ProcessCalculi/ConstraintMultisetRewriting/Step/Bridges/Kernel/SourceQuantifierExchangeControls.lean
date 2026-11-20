import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.SourceQuantifierExchange

/-! Universal exchange can be used under a choice context. Exchanging ordinary
function arguments has a different meaning and is not a certificate rule. -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.SourceQuantifierExchange.Controls

open Mettapedia.Logic Mettapedia.Languages.OpenTheory Mettapedia.Languages.HOLLight
open ReferenceBooleanSemantics

universe w

def firstProjection : HOL.ClosedTerm Symbol (.arr .prop (.arr .prop .prop)) :=
  .lam (.lam (.var (.vs .vz)))

def secondProjection : HOL.ClosedTerm Symbol (.arr .prop (.arr .prop .prop)) :=
  .lam (.lam (.var .vz))

theorem bare_function_exchange_changes_meaning (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) :
    model.denote firstProjection (fun index => nomatch index) ≠
      model.denote secondProjection (fun index => nomatch index) := by
  intro same
  have unequal := congrFun (congrFun same (ULift.up True)) (ULift.up False)
  have impossible : True = False := congrArg ULift.down unequal
  exact impossible.mp True.intro

theorem bare_function_exchange_has_no_certificate (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol)
    (meanings : Meanings model) : ¬ Nonempty (Certificate firstProjection secondProjection) := by
  rintro ⟨certificate⟩
  exact bare_function_exchange_changes_meaning model
    (certificate.denotes model meanings (fun index => nomatch index))

/-- This is the contextual shape needed when a recursive definition chooses
a function satisfying universally quantified equations. The choice term is
retained verbatim; its value or evaluation is never assumed. -/
def exchange_under_choice {context : HOL.Ctx AtomicTy}
    {first second selected : HOL.Ty AtomicTy}
    (choose : HOL.Term Symbol context (.arr (.arr selected .prop) selected))
    (predicate : HOL.Formula Symbol (second :: first :: selected :: context)) :
    Certificate
      (.app choose (.lam (universal (universal predicate))))
      (.app choose (.lam (universal (universal (HOL.rename exchange predicate))))) :=
  .app (.refl choose) (.lam (.universalExchange predicate))

theorem exchange_under_choice_denotes (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol)
    (meanings : Meanings model) {context : HOL.Ctx AtomicTy}
    {first second selected : HOL.Ty AtomicTy}
    (choose : HOL.Term Symbol context (.arr (.arr selected .prop) selected))
    (predicate : HOL.Formula Symbol (second :: first :: selected :: context))
    (valuation : model.Valuation context) :
    model.denote (.app choose (.lam (universal (universal predicate)))) valuation =
      model.denote (.app choose (.lam (universal (universal (HOL.rename exchange predicate))))) valuation :=
  (exchange_under_choice choose predicate).denotes model meanings valuation

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.SourceQuantifierExchange.Controls
