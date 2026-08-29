import Mettapedia.GSLT.Core.ObservationScopeCompletion

/-!
# Residual disposition after an observation stops

Finishing an observation scope does not decide what happened to the unobserved
execution frontier.  A caller may retain an admitted residual, deliberately
contract its local search after satisfying a finite demand, or establish that
no residual exists because execution was inspected closed.

These are evidence-bearing alternatives, not Boolean labels.  In particular,
observation contraction is local to the owned search scope: it neither proves
execution closure nor grants state-commit, external-effect, or permanent
space-pruning authority.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Core.ObservationResidualDisposition

open Mettapedia.GSLT.Core.OpenTotalityObservation
open Mettapedia.GSLT.Core.ObservationScopeCompletion

universe uOccurrence uResidual uRevision uCoverage uBound uReceipt uFault
universe uContractionReceipt

/-! ## Three lawful dispositions -/

/-- What an observation owner did with the residual after its scope became
complete.  The contraction receipt is authored by the caller; this layer does
not choose a default or reinterpret contraction as semantic pruning. -/
inductive ResidualDisposition
    {Occurrence : Type uOccurrence}
    {Residual : Type uResidual} {Revision : Type uRevision}
    {Coverage : Type uCoverage} {Bound : Type uBound}
    {Receipt : Type uReceipt} {Fault : Type uFault}
    {CaptureAdmitted : Residual → Revision → Prop}
    (scope : ScopedObservation Occurrence Residual Revision Coverage Bound
      Receipt Fault CaptureAdmitted)
    (ContractionReceipt : Type uContractionReceipt) where
  /-- Retain the exact captured residual after the scope finishes. -/
  | retained
      (complete : scope.ScopeComplete)
      (captured : CapturedResidual CaptureAdmitted
        scope.observation.completion)
      (present : scope.observation.resumable = some captured)
  /-- Deliberately stop the owned search after finite demand satisfaction.
  No resumable residual is exported. -/
  | contracted
      (satisfied : scope.DemandSatisfied)
      (receipt : ContractionReceipt)
      (notExported : scope.observation.resumable = none)
  /-- Closure proves that no residual can exist. -/
  | closedNoResidual
      (closed : scope.ExecutionClosed)

namespace ResidualDisposition

variable
    {Occurrence : Type uOccurrence}
    {Residual : Type uResidual} {Revision : Type uRevision}
    {Coverage : Type uCoverage} {Bound : Type uBound}
    {Receipt : Type uReceipt} {Fault : Type uFault}
    {CaptureAdmitted : Residual → Revision → Prop}
    {scope : ScopedObservation Occurrence Residual Revision Coverage Bound
      Receipt Fault CaptureAdmitted}
    {ContractionReceipt : Type uContractionReceipt}

/-- Every disposition is available only after the observation scope itself
has completed, while preserving the reason for completion. -/
theorem scopeComplete
    (disposition : ResidualDisposition scope ContractionReceipt) :
    scope.ScopeComplete := by
  cases disposition with
  | retained complete _ _ => exact complete
  | contracted satisfied _ _ => exact Or.inl satisfied
  | closedNoResidual closed => exact Or.inr closed

/-- A closed disposition cannot hide a captured residual. -/
theorem no_residual_of_closed
    (closed : scope.ExecutionClosed) :
    scope.observation.resumable = none :=
  scope.no_residual_of_executionClosed closed

/-- Constructor classifiers are useful to runtime refinements without
collapsing the payloads carried by the constructors. -/
def IsRetained : ResidualDisposition scope ContractionReceipt → Prop
  | .retained _ _ _ => True
  | _ => False

def IsContracted : ResidualDisposition scope ContractionReceipt → Prop
  | .contracted _ _ _ => True
  | _ => False

def IsClosed : ResidualDisposition scope ContractionReceipt → Prop
  | .closedNoResidual _ => True
  | _ => False

theorem demandSatisfied_of_isContracted
    (disposition : ResidualDisposition scope ContractionReceipt)
    (contracted : disposition.IsContracted) :
    scope.DemandSatisfied := by
  cases disposition with
  | retained => simp [IsContracted] at contracted
  | contracted satisfied => exact satisfied
  | closedNoResidual => simp [IsContracted] at contracted

theorem executionClosed_of_isClosed
    (disposition : ResidualDisposition scope ContractionReceipt)
    (closed : disposition.IsClosed) :
    scope.ExecutionClosed := by
  cases disposition with
  | retained => simp [IsClosed] at closed
  | contracted => simp [IsClosed] at closed
  | closedNoResidual executionClosed => exact executionClosed

/-- A retained captured residual is incompatible with inspected closure. -/
theorem not_executionClosed_of_isRetained
    (disposition : ResidualDisposition scope ContractionReceipt)
    (retained : disposition.IsRetained) :
    ¬ scope.ExecutionClosed := by
  cases disposition with
  | retained _ captured present =>
      intro closed
      have absent := scope.no_residual_of_executionClosed closed
      rw [present] at absent
      cases absent
  | contracted => simp [IsRetained] at retained
  | closedNoResidual => simp [IsRetained] at retained

/-- A whole-bag observation cannot deliberately contract merely from a finite
answer count.  It must reach the closed disposition. -/
theorem completeBag_not_isContracted
    (disposition : ResidualDisposition scope ContractionReceipt)
    (demand : scope.demand = .completeBag) :
    ¬ disposition.IsContracted := by
  intro contracted
  have satisfied := disposition.demandSatisfied_of_isContracted contracted
  have impossible : ¬ scope.DemandSatisfied := by
    simp [ScopedObservation.DemandSatisfied, CountSatisfied, demand]
  exact impossible satisfied

/-- Retention, contraction, and closure remain constructor-distinct. -/
theorem retained_not_contracted
    (disposition : ResidualDisposition scope ContractionReceipt) :
    disposition.IsRetained → ¬ disposition.IsContracted := by
  cases disposition <;> simp [IsRetained, IsContracted]

theorem contracted_not_closed
    (disposition : ResidualDisposition scope ContractionReceipt) :
    disposition.IsContracted → ¬ disposition.IsClosed := by
  cases disposition <;> simp [IsContracted, IsClosed]

theorem retained_not_closed
    (disposition : ResidualDisposition scope ContractionReceipt) :
    disposition.IsRetained → ¬ disposition.IsClosed := by
  cases disposition <;> simp [IsRetained, IsClosed]

end ResidualDisposition

/-! ## Positive and negative controls -/

namespace Canary

open Mettapedia.GSLT.Core.ObservationScopeCompletion.Canary
open Mettapedia.GSLT.Dynamics.SpaceExecutionClosureBoundary

/-- The same one-tick run as the retained canary, observed without exporting
its exact live residual. -/
def firstUncapturedAfterOne : TickScope where
  demand := .first
  observation := Tick.tickDriver.observeBoundedRun [()] .start () 1

theorem first_uncaptured_satisfies_demand :
    firstUncapturedAfterOne.DemandSatisfied := by
  change 1 ≤ 1
  omega

theorem first_uncaptured_is_not_execution_closed :
    ¬ firstUncapturedAfterOne.ExecutionClosed := by
  rintro ⟨coverage, equality⟩
  cases equality

theorem first_uncaptured_exports_no_residual :
    firstUncapturedAfterOne.observation.resumable = none :=
  rfl

def firstContracted : ResidualDisposition firstUncapturedAfterOne Unit :=
  .contracted first_uncaptured_satisfies_demand ()
    first_uncaptured_exports_no_residual

theorem first_contracted_is_contracted :
    firstContracted.IsContracted :=
  trivial

theorem first_contraction_does_not_prove_closure :
    firstContracted.IsContracted ∧
      ¬ firstUncapturedAfterOne.ExecutionClosed :=
  ⟨first_contracted_is_contracted,
    first_uncaptured_is_not_execution_closed⟩

/-- The existing captured first-result observation inhabits the retained
constructor without reconstructing or replacing its captured payload. -/
theorem first_retained_exists :
    ∃ disposition : ResidualDisposition firstCapturedAfterOne Unit,
      disposition.IsRetained := by
  cases present : firstCapturedAfterOne.observation.resumable with
  | none =>
      have exactResidual := first_after_one_retains_exact_residual
      simp [Observation.resume?, present] at exactResidual
  | some captured =>
      refine ⟨.retained
        first_scope_completes_before_execution_closes.1
        captured present, ?_⟩
      trivial

def closedDisposition :
    ResidualDisposition closedEmptyFirst Unit :=
  .closedNoResidual closed_empty_first_is_execution_closed

theorem closed_disposition_is_closed :
    closedDisposition.IsClosed :=
  trivial

/-- Negative whole-bag control: no inhabitant of the disposition envelope for
the live one-tick bag can be classified as an authorized contraction. -/
theorem complete_bag_disposition_cannot_contract
    (disposition : ResidualDisposition completeBagAfterOne Unit) :
    ¬ disposition.IsContracted :=
  disposition.completeBag_not_isContracted rfl

/-- One compact proof object records the implementation-facing boundary. -/
structure SeparationCrown : Prop where
  retainedFirst :
    ∃ disposition : ResidualDisposition firstCapturedAfterOne Unit,
      disposition.IsRetained
  contractedFirst : firstContracted.IsContracted
  contractionNotClosure :
    ¬ firstUncapturedAfterOne.ExecutionClosed
  closedSource : closedDisposition.IsClosed
  completeBagCannotContract :
    ∀ disposition : ResidualDisposition completeBagAfterOne Unit,
      ¬ disposition.IsContracted

theorem separationCrown : SeparationCrown where
  retainedFirst := first_retained_exists
  contractedFirst := first_contracted_is_contracted
  contractionNotClosure := first_uncaptured_is_not_execution_closed
  closedSource := closed_disposition_is_closed
  completeBagCannotContract := complete_bag_disposition_cannot_contract

end Canary

#print axioms ResidualDisposition.scopeComplete
#print axioms ResidualDisposition.no_residual_of_closed
#print axioms ResidualDisposition.not_executionClosed_of_isRetained
#print axioms ResidualDisposition.completeBag_not_isContracted
#print axioms ResidualDisposition.retained_not_contracted
#print axioms ResidualDisposition.contracted_not_closed
#print axioms Canary.first_contraction_does_not_prove_closure
#print axioms Canary.first_retained_exists
#print axioms Canary.complete_bag_disposition_cannot_contract
#print axioms Canary.separationCrown

end Mettapedia.GSLT.Core.ObservationResidualDisposition
