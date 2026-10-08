import Mettapedia.OSLF.Framework.InstrumentTreeDecision
import Mettapedia.GSLT.Causality.FundedAssayCompletion

/-!
# Funded structural tests with complete received trees

Complementary guards run the independently defined Boolean evaluator.
Their certificates refer to structural satisfaction, including its genuine
dependent constructor arguments. The declared purse price is the complete
traversal account of that procedure. Actual maximal executions retain the
received tree and authored origin, and their certificate is earned from
the firing rather than a predicted outcome.

This is an operational resource-calculus consumer. A lowering of these
structural tests to an instrumented process runtime is a separate comparison.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.InstrumentObservations

open Mettapedia.GSLT.Causality ResourceInteraction OccurrenceHistory ComplementaryAssay

universe u v

variable {Symbols : Type u} {arity : Symbols → Nat} [DecidableEq Symbols]
variable {Origins : Type v} [DecidableEq Origins]

def TestCertificate (formula : Formula Symbols arity) (branch : Verdict)
    (tree : Tree Symbols arity) : Prop :=
  match branch with
  | .confirm => Satisfies formula tree
  | .refute => ¬ Satisfies formula tree

omit [DecidableEq Origins] in
theorem test_firing_certificate (formula : Formula Symbols arity)
    {branch : Verdict} (firing : Firing Origins (evaluate formula) branch) :
    TestCertificate formula branch firing.value := by
  cases branch with
  | confirm => exact (evaluate_iff formula firing.value).1 firing.guard
  | refute => exact (evaluate_false_iff formula firing.value).1 firing.guard

theorem maximal_structural_test_verdict (formula : Formula Symbols arity)
    (session : Nat) (origin : Origins) (tree : Tree Symbols arity) (budget : Nat)
    (affordable : traversalWork formula tree ≤ budget)
    {target : Multiset (Resource (Tree Symbols arity) Origins ⊕ Unit)}
    (path : OccurrencePath (paid (evaluate formula) (traversalWork formula)).presentation
      (marking (ready session origin tree) (purse budget)) target)
    (maximal : Maximal (evaluate formula) (traversalWork formula) target) :
    outputs (leftPart target) = { (session, verdictOf (evaluate formula tree), origin, tree) } ∧
      TestCertificate formula (verdictOf (evaluate formula tree)) tree ∧
      ((paid (evaluate formula) (traversalWork formula)).pathEntries path).length = 1 := by
  obtain ⟨readout, count⟩ := maximal_affordable_verdict
    (evaluate formula) (traversalWork formula) session origin tree budget affordable path maximal
  exact ⟨readout, test_firing_certificate formula
    (selected (evaluate formula) session origin tree), count⟩

omit [DecidableEq Origins] in
theorem structural_test_purse_conservation (formula : Formula Symbols arity)
    (session : Nat) (origin : Origins) (tree : Tree Symbols arity) (budget : Nat)
    (affordable : traversalWork formula tree ≤ budget) :
    budget =
      (rightPart (completed (evaluate formula) (traversalWork formula) session origin tree budget)).card +
        traversalWork formula tree :=
  paidRun_conserved _ _ _ _ _ _ affordable

theorem complete_structural_readout (formula : Formula Symbols arity)
    (session : Nat) (origin : Origins) (tree : Tree Symbols arity) (budget : Nat) :
    observed (evaluate formula) (traversalWork formula) session origin (some tree) budget =
      if traversalWork formula tree ≤ budget then
        { (session, verdictOf (evaluate formula tree), origin, tree) } else 0 :=
  observed_some _ _ _ _ _ _

end Mettapedia.OSLF.Framework.InstrumentObservations
