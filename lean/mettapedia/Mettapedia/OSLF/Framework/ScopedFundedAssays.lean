import Mettapedia.OSLF.Syntax.ParallelScopeDecision
import Mettapedia.GSLT.Causality.FundedAssayCompletion

/-!
# Funded assays for actual quotient scope membership

The guard runs the independently computed composite-scope decision on an
actual authored equation class. Its complete firing retains the received
class, session and origin. The guard certificate proves either the original
existential composite membership or its negation. A maximal affordable
execution earns the complete verdict readout and its actual occurrence count.

The testing price is a supplied schedule. The separate classifier-query
account does not by itself price the two raw scope predicates.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.ParallelFragment

open Mettapedia.Algebra.SupportSeparatedDecomposition
open Mettapedia.GSLT.Causality ResourceInteraction OccurrenceHistory ComplementaryAssay

universe v

instance parallelClassDecidableEq : DecidableEq ParallelClass :=
  inventoryQ_injective.decidableEq

variable {Origins : Type v} [DecidableEq Origins]
variable {classify : Fin 3 → Bool}
variable {left right : Term psig [] PSrt.proc → Prop}
variable [DecidablePred left] [DecidablePred right]

theorem decideCompositeQ_false_iff
    (leftInvariant : ScopeInvariant left) (rightInvariant : ScopeInvariant right)
    (leftSupported : LeftSupported classify (inventoryScope left))
    (rightSupported : RightSupported classify (inventoryScope right))
    (value : ParallelClass) :
    decideCompositeQ classify left right value = false ↔
      ¬ CompositeScopeQ left right leftInvariant rightInvariant value := by
  rw [← decideCompositeQ_iff leftInvariant rightInvariant leftSupported rightSupported value]
  cases decideCompositeQ classify left right value <;> decide

/-- The specification remains the independently defined quotient predicate. -/
def ScopeCertificate (leftInvariant : ScopeInvariant left)
    (rightInvariant : ScopeInvariant right) (branch : Verdict) (value : ParallelClass) : Prop :=
  match branch with
  | .confirm => CompositeScopeQ left right leftInvariant rightInvariant value
  | .refute => ¬ CompositeScopeQ left right leftInvariant rightInvariant value

omit [DecidableEq Origins] in
theorem scope_firing_certificate
    (leftInvariant : ScopeInvariant left) (rightInvariant : ScopeInvariant right)
    (leftSupported : LeftSupported classify (inventoryScope left))
    (rightSupported : RightSupported classify (inventoryScope right))
    {branch : Verdict} (firing : Firing Origins (decideCompositeQ classify left right) branch) :
    ScopeCertificate leftInvariant rightInvariant branch firing.value := by
  cases branch with
  | confirm =>
    exact (decideCompositeQ_iff leftInvariant rightInvariant leftSupported rightSupported _).1
      firing.guard
  | refute =>
    exact (decideCompositeQ_false_iff leftInvariant rightInvariant leftSupported rightSupported _).1
      firing.guard

theorem maximal_scope_verdict
    (leftInvariant : ScopeInvariant left) (rightInvariant : ScopeInvariant right)
    (leftSupported : LeftSupported classify (inventoryScope left))
    (rightSupported : RightSupported classify (inventoryScope right))
    (cost : ParallelClass → Nat) (session : Nat) (origin : Origins)
    (value : ParallelClass) (budget : Nat) (affordable : cost value ≤ budget)
    {target : Multiset (Resource ParallelClass Origins ⊕ Unit)}
    (path : OccurrencePath (paid (decideCompositeQ classify left right) cost).presentation
      (marking (ready session origin value) (purse budget)) target)
    (maximal : Maximal (decideCompositeQ classify left right) cost target) :
    outputs (leftPart target) =
        { (session, verdictOf (decideCompositeQ classify left right value), origin, value) } ∧
      ScopeCertificate leftInvariant rightInvariant
        (verdictOf (decideCompositeQ classify left right value)) value ∧
      ((paid (decideCompositeQ classify left right) cost).pathEntries path).length = 1 := by
  obtain ⟨readout, count⟩ := maximal_affordable_verdict
    (decideCompositeQ classify left right) cost session origin value budget affordable path maximal
  exact ⟨readout, scope_firing_certificate leftInvariant rightInvariant leftSupported rightSupported
    (selected (decideCompositeQ classify left right) session origin value), count⟩

theorem computed_scope_readout (cost : ParallelClass → Nat)
    (session : Nat) (origin : Origins) (value : ParallelClass) (budget : Nat) :
    observed (decideCompositeQ classify left right) cost session origin (some value) budget =
      if cost value ≤ budget then
        { (session, verdictOf (decideCompositeQ classify left right value), origin, value) } else 0 :=
  observed_some _ _ _ _ _ _

end Mettapedia.OSLF.Binding.ParallelFragment
