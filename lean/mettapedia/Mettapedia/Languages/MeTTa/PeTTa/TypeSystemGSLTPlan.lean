import Mettapedia.Languages.MeTTa.PeTTa.TypeSystemGSLTDecision

/-!
# The typed decision plan (specialization IR, stage 1)

Specialization compiles the PROVED decision semantics — never the
transitional runtime realization — into an instruction form a generic
executor can run at native cost.  This module is the first stage: the
plan IR, the compiler from the decision semantics' staged structure, the
plan interpreter, and the correspondence theorem `Plan.exec = decide`.
Because both sides are total Lean functions over the same mirror algebra,
the correspondence is an EQUALITY, not a simulation argument: whatever
the serialized pack's executor is later proved to implement, it inherits
the decision soundness theorems through this equation.

Stage boundaries, stated exactly: the plan here is the instruction form
of the FIXED guard system's decision function (the closed rule set is
what compile-time specialization exploits); the generic compiler from an
arbitrary validated presentation to a plan, the byte-level pack with its
decode theorem, and the C executor are the next stages of the arc.
-/

namespace Mettapedia.Languages.MeTTa.PeTTa.TypeSystemGSLTPlan

open Mettapedia.Languages.MeTTa.PeTTa.TypeSystemGSLTDecision

/-- The decision plan: a staged instruction tree.  Each node is one
decision the specialized executor takes; the operand stack discipline of
the eventual pack serializes exactly this shape. -/
inductive Plan where
  /-- Dispatch on boundness: unbound values take the boundness branch. -/
  | checkBound (unbound bound : Plan)
  /-- Boundness verdict for the committed/base case. -/
  | boundnessVerdict
  /-- Run the mismatch search; on a checked certificate, refute; on
  exhaustion, report incomplete; otherwise continue. -/
  | searchRefute (next : Plan)
  /-- Run the has-type search; on a checked certificate, establish; on
  exhaustion, report incomplete; otherwise undetermined. -/
  | searchEstablish

/-- The plan interpreter: a small-step executor over the mirror algebra.
The eventual generic C executor implements THIS function against the
serialized pack. -/
def Plan.exec (plan : Plan) (fuel : Nat) (env : Env)
    (value : Option Val) (formal : Ty) (mode : Mode) : Verdict :=
  match plan with
  | .checkBound unbound bound =>
      match value with
      | none => unbound.exec fuel env none formal mode
      | some _ => bound.exec fuel env value formal mode
  | .boundnessVerdict =>
      if mode.committed && formal.isBase then .refuted .unbound
      else .undetermined
  | .searchRefute next =>
      match value with
      | none => next.exec fuel env none formal mode
      | some v =>
          match searchMismatch fuel env v formal with
          | .yes cert =>
              if cert.check env v formal then .refuted (.mismatch cert)
              else .incomplete
          | .out => .incomplete
          | .no => next.exec fuel env value formal mode
  | .searchEstablish =>
      match value with
      | none => .undetermined
      | some v =>
          match searchHasType fuel env v formal with
          | .yes cert =>
              if cert.check env v formal then .established cert
              else .incomplete
          | .out => .incomplete
          | .no => .undetermined

/-- The compiled plan of the guard system's decision function. -/
def guardPlan : Plan :=
  .checkBound .boundnessVerdict (.searchRefute .searchEstablish)

/-- Correspondence: executing the compiled plan IS the decision function.
Every decision soundness theorem transfers through this equation to
whatever implements the plan. -/
theorem guardPlan_exec_eq_decide
    (fuel : Nat) (env : Env) (value : Option Val) (formal : Ty)
    (mode : Mode) :
    guardPlan.exec fuel env value formal mode =
      decide fuel env value formal mode := by
  cases value with
  | none => rfl
  | some v =>
      simp only [guardPlan, Plan.exec, TypeSystemGSLTDecision.decide]
      cases searchMismatch fuel env v formal <;> rfl

/-- Corollaries: the plan inherits the decision soundness theorems. -/
theorem guardPlan_refuted_mismatch_sound
    {fuel env v formal mode cert}
    (h : guardPlan.exec fuel env (some v) formal mode =
         .refuted (.mismatch cert)) :
    Mismatch env v formal :=
  decide_refuted_mismatch_sound
    (by rw [← guardPlan_exec_eq_decide]; exact h)

theorem guardPlan_established_sound {fuel env v formal mode cert}
    (h : guardPlan.exec fuel env (some v) formal mode =
         .established cert) :
    HasType env v formal :=
  decide_established_sound
    (by rw [← guardPlan_exec_eq_decide]; exact h)

end Mettapedia.Languages.MeTTa.PeTTa.TypeSystemGSLTPlan
