import Mettapedia.Languages.MeTTa.PeTTa.Bridges.PagedFoldAdmission
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.FoldAlgebraPortfolio

/-!
# Algebraic workers against the executable source-fold oracle

The reference observes completed runs of the retained driver that executes
actual PeTTa callback steps. Accepted algebraic workers have both directions
of correspondence with those runs. Source debit, callback-prefix and exact
page observers receive no final-value-only candidate.

Unknown source callbacks are not licensed to run through the restricted
driver: admission retains the original request for its ordinary reference.
The native host dispatcher and physical implementation are separate adapters.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.PagedFoldPortfolio

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.GSLT.Dynamics ObservationQualified
open SpaceSemantics FoldSourceBoundary FoldAlgebraPortfolio

structure Completed where
  world : Effects.State
  value : Atom

def sourceMeaning (program : Program) (caller : Subst) (code : Code) (items : List Atom) (initial : Atom)
    (world : Effects.State) : Set Completed :=
  {answer | ∃ fuel, (PagedFold.run program (code.callback caller) fuel
    ⟨.ready world items initial, [], 0, 0⟩).1.phase = .done answer.world answer.value}

def boundary (program : Program) (caller : Subst) (code : Code) (items : List Atom) (initial : Atom) :
    Boundary Effects.State (Set Completed) (Set Completed) where
  source := sourceMeaning program caller code items initial
  summarize := id
  future := {Question := Set Completed → Bool, Answer _ := Bool, read question answers := question answers}
  sufficient _ _ same question := congrArg question same

theorem source_singleton {program : Program} {caller : Subst} {code : Code} {items : List Atom} {initial : Atom}
    (driver : FoldRegionEntry.Driver program caller code items initial) (world : Effects.State) :
    sourceMeaning program caller code items initial world = {⟨world, driver.result⟩} := by
  ext answer
  constructor
  · rintro ⟨fuel, completed⟩
    let request : PagedFoldAdmission.Request := ⟨program, code.callback caller, world, items, initial⟩
    let session : PagedFoldAdmission.Session :=
      ⟨request, (PagedFold.run program (code.callback caller) fuel request.start).1,
        ⟨driver.result, driver.returns world⟩, ⟨fuel, rfl⟩⟩
    have source := PagedFoldAdmission.completed_page_is_source_value session answer.world answer.value completed
    have value := FoldSource.evaluates_unique source.2 (driver.returns world)
    cases answer
    simp only [Set.mem_singleton_iff, Completed.mk.injEq]
    exact ⟨source.1, value⟩
  · intro member
    have same : answer = ⟨world, driver.result⟩ := member
    subst answer
    obtain ⟨ticks, values, _, complete⟩ := PagedFold.completes_evaluation (driver.returns world)
    exact ⟨ticks + 2 * items.length + 1, congrArg (fun page : PagedFold.State × Nat => page.1.phase) complete⟩

def region {program : Program} {caller : Subst} {code : Code} {items : List Atom} {initial : Atom}
    (driver : FoldRegionEntry.Driver program caller code items initial) (regime : Regime) :
    CertifiedRegion (boundary program caller code items initial) Regime where
  regime := regime
  Artifact := Completed
  attempt world := .committed ⟨world, driver.result⟩
  decode answer := {answer}
  restores _ _ impossible := by cases impossible
  exact world _ committed := by cases committed; exact (source_singleton driver world).symm

inductive Observer | completedValue | callbackPrefixes | sourceDebit | sourcePages
  deriving DecidableEq

def gather (observer : Observer) (budget : Nat) (program : Program) (caller : Subst) (code : Code)
    (items : List Atom) (initial : Atom) (estimate : Regime → Effects.State → Estimate) :
    List (Candidate (boundary program caller code items initial) Regime) :=
  match observer with
  | .completedValue =>
      (FoldAlgebraPortfolio.drivers budget program caller code items initial).map fun (ordinal, regime, driver) =>
        ⟨region driver regime, estimate regime, ordinal⟩
  | .callbackPrefixes | .sourceDebit | .sourcePages => []

theorem final_worker_does_not_claim_source_debit (budget : Nat) (program : Program) (caller : Subst) (code : Code)
    (items : List Atom) (initial : Atom) (estimate : Regime → Effects.State → Estimate) :
    gather .sourceDebit budget program caller code items initial estimate = [] := rfl

theorem selected_worker_agrees_with_executable_source (budget : Nat) (program : Program) (caller : Subst) (code : Code)
    (items : List Atom) (initial : Atom) (estimate : Regime → Effects.State → Estimate) (world : Effects.State) :
    RegionPortfolio.execute world (gather .completedValue budget program caller code items initial estimate) =
      sourceMeaning program caller code items initial world := RegionPortfolio.execute_exact _ _

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.PagedFoldPortfolio
