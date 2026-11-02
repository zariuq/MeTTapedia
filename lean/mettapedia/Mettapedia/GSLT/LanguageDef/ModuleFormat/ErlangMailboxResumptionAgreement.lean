import Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangMailboxRunnerAgreement

/-! Whole-machine mailbox resumption retains the original source path.
The public actor adapter resumes this machine, rather than replaying a
trace-only entry or restarting a pending mailbox operation. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangMailbox.Execution.Runner

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Machines.ResumableSearchRunner (Machine Reached)
open Model

abbrev search := Complete.Normalized.search plan [] (.base "ErMailboxConfig") .canonical

theorem advance_source_path {source : Pattern} {machine : Complete.Classes.Machine plan}
    (reached : Reached search machine) (origin : Path base source machine.state)
    (canonical : CanonicalBags.canon machine.state = machine.state) (typed : Sorted machine.state)
    (ticks quantum : Nat) :
    Path base source (Machine.advance search ticks quantum machine).state ∧
      CanonicalBags.canon (Machine.advance search ticks quantum machine).state =
        (Machine.advance search ticks quantum machine).state ∧
      Sorted (Machine.advance search ticks quantum machine).state := by
  have path := Mettapedia.Machines.ResumableSearchRunner.advance_reaches
    (Complete.Normalized.search_lawful plan [] (.base "ErMailboxConfig") .canonical)
    (Reduces := Complete.Normalized.NormalizedStep plan [] (.base "ErMailboxConfig") .canonical)
    (fun valid => ⟨_, GeneralOccurrenceSemantics.Receipt.semantic_step plan [] (.base "ErMailboxConfig") valid, rfl⟩)
    quantum ticks reached
  obtain ⟨actual, fixed, sorted⟩ := normalized_path_readback canonical typed path
  exact ⟨origin.trans actual, fixed, sorted⟩

theorem advance_done_value {source answer : Pattern} (settles : Settles base source answer)
    {machine : Complete.Classes.Machine plan} (reached : Reached search machine)
    (origin : Path base source machine.state)
    (canonical : CanonicalBags.canon machine.state = machine.state) (typed : Sorted machine.state)
    (ticks quantum : Nat) (done : (Machine.advance search ticks quantum machine).phase = .done) :
    (Machine.advance search ticks quantum machine).state = answer := by
  obtain ⟨path, _, sorted⟩ := advance_source_path reached origin canonical typed ticks quantum
  have further := Mettapedia.Machines.ResumableSearchRunner.advance_reached
    (Complete.Normalized.search_lawful plan [] (.base "ErMailboxConfig") .canonical) ticks quantum reached
  have noStep := Complete.Normalized.done_no_step plan [] (.base "ErMailboxConfig") equations_checked further done
  exact settles.exact _ path (fun target step => noStep target ((step_iff_reference sorted).mpr step))

theorem resume_exact (machine : Complete.Classes.Machine plan) (first extra quantum : Nat) :
    Machine.advance search extra quantum (Machine.advance search first quantum machine) =
      Machine.advance search (first + extra) quantum machine :=
  (Machine.advance_add search first extra quantum machine).symm

end Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangMailbox.Execution.Runner
