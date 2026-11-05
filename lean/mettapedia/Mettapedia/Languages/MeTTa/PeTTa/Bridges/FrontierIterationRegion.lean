import Mettapedia.Languages.MeTTa.PeTTa.Bridges.FrontierIterationSource
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.PureCallPortfolio

/-!
# Completed frontier-driver regions

The source driver and phase semantics are supplied as checked evidence.
Private phase allowance is not evaluator fuel. Exhaustion restores the exact
entrance and selects reference execution, and exact-page observation declines.
This functional attempt does not license rollback of native published effects.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.FrontierIterationRegion

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.GSLT.Dynamics ObservationQualified
open Eval SpaceSemantics EffectfulQuerySource FrontierIterationSource
open DeclarativeSpec (Runs)

def entry (driver : String) (names : Names) : Atom :=
  .expression [.symbol driver, .var names.frontier, .var names.counter]

theorem source_meaning {program : Program} {driver : String} {names : Names} {phase : Atom}
    (certificate : Certificate program driver names phase) (worker : Body)
    (law : ∀ bindings before after next, worker bindings before = some (after, next) →
      PureReturns program bindings before phase after (.expression next))
    (fuel : Nat) (frontier : List Atom) (count : Nat) (before after : Effects.State) (result : Nat)
    (completed : iterate worker names fuel frontier count before = some (after, result)) :
    PureCallPortfolio.sourceMeaning program (callee names frontier count) (entry driver names) before =
      {PureCallPortfolio.complete after (number result)} := by
  have returned := FrontierIterationSource.call_returns certificate worker law fuel frontier count before after result completed
  ext observed
  change Runs program {state := before, control := .evaluate (callee names frontier count) (entry driver names)}
    (.complete observed.state observed.answers observed.input observed.output) ↔ _
  rw [pure_returns_derivation_iff program (callee names frontier count) before after (entry driver names) (number result) returned]
  cases observed
  simp [PureCallPortfolio.complete, PureCallPortfolio.Completed.mk.injEq]

def region {Regime : Type} {program : Program} {driver : String} {names : Names} {phase : Atom}
    (regime : Regime) (certificate : Certificate program driver names phase) (worker : Body)
    (law : ∀ bindings before after next, worker bindings before = some (after, next) →
      PureReturns program bindings before phase after (.expression next))
    (fuel : Nat) (frontier : List Atom) (count : Nat) :
    CertifiedRegion (PureCallPortfolio.boundary program (callee names frontier count) (entry driver names)) Regime where
  regime := regime
  Artifact := PureCallPortfolio.Completed
  attempt before := match iterate worker names fuel frontier count before with
    | none => .declined before
    | some receipt => .committed (PureCallPortfolio.complete receipt.1 (number receipt.2))
  decode observed := {observed}
  restores before restored declined := by
    dsimp only at declined
    split at declined
    · exact (PartialRegionPlan.Attempt.declined.inj declined).symm
    · cases declined
  exact before observed committed := by
    split at committed
    · cases committed
    next receipt completed =>
      cases PartialRegionPlan.Attempt.committed.inj committed
      exact (source_meaning certificate worker law fuel frontier count before receipt.1 receipt.2 completed).symm

def admission {Regime : Type} {program : Program} {driver : String} {names : Names} {phase : Atom}
    (observation : PureCallExtraction.Observation) (regime : Regime)
    (certificate : Certificate program driver names phase) (worker : Body)
    (law : ∀ bindings before after next, worker bindings before = some (after, next) →
      PureReturns program bindings before phase after (.expression next))
    (fuel : Nat) (frontier : List Atom) (count : Nat) :
    Option (CertifiedRegion (PureCallPortfolio.boundary program (callee names frontier count) (entry driver names)) Regime) :=
  match observation with
  | .exactPage => none
  | .completedResult => some (region regime certificate worker law fuel frontier count)

theorem execute_exact {Regime : Type} {program : Program} {driver : String} {names : Names} {phase : Atom}
    (regime : Regime) (certificate : Certificate program driver names phase) (worker : Body)
    (law : ∀ bindings before after next, worker bindings before = some (after, next) →
      PureReturns program bindings before phase after (.expression next))
    (fuel : Nat) (frontier : List Atom) (count : Nat) (before : Effects.State) :
    (region regime certificate worker law fuel frontier count).execute before =
      PureCallPortfolio.sourceMeaning program (callee names frontier count) (entry driver names) before :=
  congrFun (region regime certificate worker law fuel frontier count).execute_eq_reference before

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.FrontierIterationRegion
