import Mettapedia.OSLF.Syntax.RhoCommunicationSchema

/-!
# The Chapter 6 communication schema at arbitrary closed channel and payload

The source's only Chapter 6 reduction substitutes the quotation of the
payload into a continuation open under one name. This file checks the rule
uniformly for every closed channel, payload, and scoped continuation, while
keeping the source's ACU congruence separate from raw syntax.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoSchema.Chapter6

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.RhoSchema

def output (channel : Term sig [] Srt.nm)
    (payload : Term sig [] Srt.pr) : Term sig [] Srt.pr :=
  .op Op.out (.cons channel (.cons payload .nil))

def input (channel : Term sig [] Srt.nm)
    (continuation : Term sig [Srt.nm] Srt.pr) : Term sig [] Srt.pr :=
  .op Op.inp (.cons channel (.cons continuation .nil))

def quote (payload : Term sig [] Srt.pr) : Term sig [] Srt.nm :=
  .op Op.quo (.cons payload .nil)

private def closeRule (channel : Term sig [] Srt.nm)
    (payload : Term sig [] Srt.pr) : Sub sig G []
  | _, .zero => channel
  | _, .succ .zero => payload

private def supplyContinuation
    (continuation : Term sig [Srt.nm] Srt.pr) :
    (i : Fin metas.length) → Term sig (metas.get i).1 (metas.get i).2
  | ⟨0, _⟩ => continuation

private theorem supplyContinuation_zero
    (continuation : Term sig [Srt.nm] Srt.pr) :
    supplyContinuation continuation (0 : Fin metas.length) = continuation := by
  rfl

private def commInstanceFor (channel : Term sig [] Srt.nm)
    (payload : Term sig [] Srt.pr)
    (continuation : Term sig [Srt.nm] Srt.pr) :
    RuleInstance metas comm where
  body := supplyContinuation continuation
  close := closeRule channel payload

theorem instantiated_source
    (channel : Term sig [] Srt.nm) (payload : Term sig [] Srt.pr)
    (continuation : Term sig [Srt.nm] Srt.pr) :
    bind (closeRule channel payload)
      (instantiate (supplyContinuation continuation) comm.lhs) =
        parT (output channel payload) (input channel continuation) := by
  have hsub :
      (fun s v => bind (liftSub (closeRule channel payload) [Srt.nm])
        (argsToSub (Args.cons (Term.var Var.zero) Args.nil) s v)) =
      (fun s v => (Term.var v : Term sig [Srt.nm] s)) := by
    funext s v
    cases v with
    | zero => rfl
    | succ v => cases v
  simp [comm, commLhs, output, input,
    parT, instantiate, instantiateArgs, bind, bindArgs, bind_comp,
    liftSub]
  rw [supplyContinuation_zero continuation]
  simp only [hsub, bind_id]
  simp [closeRule]

theorem instantiated_target
    (channel : Term sig [] Srt.nm) (payload : Term sig [] Srt.pr)
    (continuation : Term sig [Srt.nm] Srt.pr) :
    bind (closeRule channel payload)
      (instantiate (supplyContinuation continuation) comm.rhs) =
        inst continuation (quote payload) := by
  have hsub :
      (fun s v => bind (closeRule channel payload)
        (argsToSub
          (Args.cons
            (Term.op Op.quo
              (Args.cons (Term.var (Var.succ Var.zero)) Args.nil))
            Args.nil) s v)) =
      extend (quote payload) := by
    funext s v
    cases v with
    | zero => rfl
    | succ v => cases v
  simp [comm, commRhs, cont, instantiate, instantiateArgs,
    quote, inst, bind_comp, hsub]
  rw [supplyContinuation_zero continuation]

/-- The book's source-order COMM, uniformly in its three inputs. -/
theorem source_order_comm
    (channel : Term sig [] Srt.nm) (payload : Term sig [] Srt.pr)
    (continuation : Term sig [Srt.nm] Srt.pr) :
    rho.StepModE (parT (input channel continuation) (output channel payload))
      (inst continuation (quote payload)) := by
  apply Presentation.stepModE_resp_left
    (par_comm (input channel continuation) (output channel payload))
  apply Presentation.stepModE_of_rule (i := ⟨0, by decide⟩)
  exact stepModE_of_step (E := rhoE)
    (by
      rw [← instantiated_source channel payload continuation,
        ← instantiated_target channel payload continuation]
      exact step_of_rootStep comm
        (rootStep_of_instance comm (commInstanceFor channel payload continuation)))

/-- The same uniform rule is observable in the extensional GSLT obtained
from the Chapter 6 presentation. -/
theorem source_order_comm_extensional
    (channel : Term sig [] Srt.nm) (payload : Term sig [] Srt.pr)
    (continuation : Term sig [Srt.nm] Srt.pr) :
    (rho.toUnpositioned.toExtensionalGSLTAt Srt.pr).Step
      (parT (input channel continuation) (output channel payload))
      (inst continuation (quote payload)) :=
  (rho.stepModE_iff_toUnpositioned).mp
    (source_order_comm channel payload continuation)

/-- The one-rule presentation cannot communicate from the null process as
a raw root firing; this preserves the operational distinction from equations. -/
theorem nil_has_no_root_communication (target : Term sig [] Srt.pr) :
    ¬ RootStep comm nilP target :=
  nil_does_not_step target

end Mettapedia.OSLF.Binding.RhoSchema.Chapter6
