import Mettapedia.OSLF.Syntax.PatternAsBindingSignature
import Mettapedia.OSLF.Syntax.StepRelationCaptureWitness

/-!
# The repair computes the reduct that neither applier does

The defect witness retains the old raw capturing result and a target-depth-only
lifting result that shifts too far. The rule-aware engine now computes the
correct result on that example. This module independently represents the same
dependency using declared metavariable arguments.

Adjoining the rule's metavariables to the signature supplies exactly that datum,
and supplies it in the type.  A metavariable matched `k` binders deep is
declared with arity `k`, so its body is a term in a context of `k` variables and
every occurrence of it must be applied to `k` arguments naming which variables it
may depend on.  Instantiation then weakens by whatever the occurrence's position
requires, because its defined substitution explicitly lifts under binders.
Scope indices alone do not uniquely determine that lift.

This module carries that out on the defect's own rule and shows the result is
the correct reduct.
-/

namespace Mettapedia.OSLF.Binding

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Binding.PatternPresentation
open Mettapedia.OSLF.Binding.StepCapture

set_option autoImplicit false

namespace PatternRepair

/-- One metavariable, declared to depend on one variable -- the binder the rule's
left-hand side matched it under. -/
abbrev metas : List (MetaArity patSig) := [([PatSrt.pat], PatSrt.pat)]

abbrev schemaSig : Signature := withMetas patSig metas

/-- `lambda y. lambda y. X[y]`, where the argument records that `X` may depend on
the *outer* binder -- the one it was matched under -- and not on the inner one
the rule introduces. -/
def rhsSchema : Term schemaSig [] PatSrt.pat :=
  Term.op (S := schemaSig) (Sum.inl (PatOp.lamOp (some "y")))
    (.cons
      (Term.op (S := schemaSig) (Sum.inl (PatOp.lamOp (some "y")))
        (.cons
          (Term.op (S := schemaSig) (Sum.inr (MetaOp.mk ⟨0, by decide⟩))
            (.cons (Term.var (Var.succ Var.zero)) .nil))
          .nil))
      .nil)

/-- The matched value, in the scope it was matched in: one variable available,
which is the binder it sat under. -/
def bodyX : Term patSig [PatSrt.pat] PatSrt.pat :=
  Term.op (S := patSig) (PatOp.lamOp (some "q"))
    (.cons (Term.var (Var.succ Var.zero)) .nil)

def bodyFor : (i : Fin metas.length) →
    Term patSig (metas.get i).1 (metas.get i).2
  | ⟨0, _⟩ => bodyX

/-- The declared metavariable body lives in a one-variable scope, the schema
supplies the enclosing variable explicitly, and instantiation uses lifted
substitution to compute the correct reduct. -/
theorem repair_computes_correct :
    erase (instantiate bodyFor rhsSchema) = progCorrect := rfl

/-- **And neither applier does.**  The three results side by side. -/
theorem repair_is_the_only_correct_one :
    erase (instantiate bodyFor rhsSchema) = progCorrect
      ∧ progActual ≠ progCorrect
      ∧ Pattern.lambda (some "y") (.lambda (some "y") (.lambda (some "q") (.bvar 3)))
          ≠ progCorrect :=
  ⟨repair_computes_correct, neither_applier_is_correct.1, neither_applier_is_correct.2⟩

/-- The matched value really does use the binder it was matched under, so this
is not a case where every weakening happens to agree. -/
theorem body_uses_its_scope :
    erase bodyX = .lambda (some "q") (.bvar 1) := rfl

/-- **Negative control: the arity is load-bearing.**  Declaring the metavariable
with no arguments -- which is what treating it as an operator constant amounts
to -- forces its body to be closed, so the value that was matched under a binder
is not even expressible.  The repair is not a different traversal; it is a
different type. -/
theorem closed_arity_cannot_hold_the_value :
    ∀ t : Term patSig [] PatSrt.pat, erase t ≠ .lambda (some "q") (.bvar 1) := by
  intro t h
  have hc := erase_closed t
  rw [h] at hc
  exact absurd hc (by decide +kernel)

end PatternRepair

end Mettapedia.OSLF.Binding
