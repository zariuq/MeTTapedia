import Mettapedia.OSLF.Framework.InstrumentTestExecution
import Mettapedia.OSLF.Framework.StructuralFundedAssays

/-!
# Funded assays priced by their computed structural inspection

The test and its price are the two readouts of the complete structural
inspection. Actual firings earn positive or negative satisfaction evidence.
Maximal affordable executions produce the corresponding retained verdict,
and the purse account agrees with the independently defined traversal.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.InstrumentObservations

open Mettapedia.GSLT.Causality ResourceInteraction OccurrenceHistory ComplementaryAssay

universe u v

variable {Symbols : Type u} {arity : Symbols → Nat} [DecidableEq Symbols]
variable {Origins : Type v} [DecidableEq Origins]

omit [DecidableEq Origins] in
theorem inspection_answer_comparison (formula : Formula Symbols arity) :
    (fun tree => (inspect formula tree).1) = evaluate formula :=
  funext (fun tree => congrArg Prod.fst (inspect_readout formula tree))

omit [DecidableEq Origins] in
theorem inspection_price_comparison (formula : Formula Symbols arity) :
    (fun tree => (inspect formula tree).2) = traversalWork formula :=
  funext (inspect_work formula)

omit [DecidableEq Origins] in
theorem inspection_firing_certificate (formula : Formula Symbols arity)
    {branch : Verdict} (firing : Firing Origins (fun tree => (inspect formula tree).1) branch) :
    TestCertificate formula branch firing.value := by
  cases branch with
  | confirm => exact (inspect_answer_iff formula firing.value).1 firing.guard
  | refute => exact (inspect_refutation_iff formula firing.value).1 firing.guard

theorem maximal_paid_inspection (formula : Formula Symbols arity)
    (session : Nat) (origin : Origins) (tree : Tree Symbols arity) (budget : Nat)
    (affordable : (inspect formula tree).2 ≤ budget)
    {target : Multiset (Resource (Tree Symbols arity) Origins ⊕ Unit)}
    (path : OccurrencePath
      (paid (fun value => (inspect formula value).1) (fun value => (inspect formula value).2)).presentation
      (marking (ready session origin tree) (purse budget)) target)
    (maximal : Maximal (fun value => (inspect formula value).1)
      (fun value => (inspect formula value).2) target) :
    outputs (leftPart target) = { (session, verdictOf (inspect formula tree).1, origin, tree) } ∧
      TestCertificate formula (verdictOf (inspect formula tree).1) tree ∧
      ((paid (fun value => (inspect formula value).1)
        (fun value => (inspect formula value).2)).pathEntries path).length = 1 := by
  obtain ⟨readout, count⟩ := maximal_affordable_verdict
    (fun value => (inspect formula value).1) (fun value => (inspect formula value).2)
    session origin tree budget affordable path maximal
  exact ⟨readout, inspection_firing_certificate formula
    (selected (fun value => (inspect formula value).1) session origin tree), count⟩

theorem inspection_observed_comparison (formula : Formula Symbols arity)
    (session : Nat) (origin : Origins) (arrival : Option (Tree Symbols arity)) (budget : Nat) :
    observed (fun tree => (inspect formula tree).1) (fun tree => (inspect formula tree).2)
      session origin arrival budget =
        observed (evaluate formula) (traversalWork formula) session origin arrival budget := by
  rw [inspection_answer_comparison, inspection_price_comparison]

omit [DecidableEq Origins] in
theorem inspection_fee_conserved (formula : Formula Symbols arity)
    (session : Nat) (origin : Origins) (tree : Tree Symbols arity) (budget : Nat)
    (affordable : (inspect formula tree).2 ≤ budget) :
    budget =
      (rightPart (completed (fun value => (inspect formula value).1)
        (fun value => (inspect formula value).2) session origin tree budget)).card +
          traversalWork formula tree := by
  rw [← inspect_work formula tree]
  exact paidRun_conserved _ _ _ _ _ _ affordable

end Mettapedia.OSLF.Framework.InstrumentObservations
