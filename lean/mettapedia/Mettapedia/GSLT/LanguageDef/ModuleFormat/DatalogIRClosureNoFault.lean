import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRCanonicalProvider
import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRReceiptKeys

/-! Prepared positive runs cannot encounter an internal receipt/provider
fault. Every published key decodes, successful commits retain canonical facts,
and those facts pass the same provider checker used by the runtime. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.ClosureMachine

open Mettapedia.Languages.Datalog
open Mettapedia.OSLF.MeTTaIL Syntax

theorem commit_total (program : Program) (seeds : List GroundFact) (prepared : Executable.Prepared)
    (accepted : Executable.prepare program seeds = .ok prepared)
    (scope : GeneralPremise.Static.checkLanguage (GeneralPlanEnvironment.environment (Executable.plan prepared prepared.seedFacts)) = true)
    (snapshot : List Pattern) (batch : List GeneralOccurrenceSemantics.Receipt)
    (valid : ∀ receipt ∈ batch, receipt.Valid (Executable.plan prepared snapshot) [] (.base "DlStatement") (Executable.request prepared.vocabulary))
    (facts : List Pattern) (before : List Key) : ∃ outputs after, commit? prepared snapshot batch facts before = some (outputs,after) := by
  induction batch generalizing facts before with
  | nil => exact ⟨facts,before,by simp only [commit?]⟩
  | cons receipt batch ih =>
    obtain ⟨key,read⟩ := ReceiptKeys.total program seeds prepared accepted snapshot scope receipt (valid receipt List.mem_cons_self)
    obtain ⟨outputs,after,rest⟩ := ih (fun other member => valid other (List.mem_cons_of_mem _ member))
      (insert facts receipt.target) (insert before key)
    refine ⟨outputs,after,?_⟩
    simpa only [commit?,read,Option.bind_eq_bind,Option.bind_some] using rest

theorem begin_noFault (program : Program) (seeds : List GroundFact) (prepared : Executable.Prepared)
    (accepted : Executable.prepare program seeds = .ok prepared) : (begin prepared).fault = none := by
  have checked := canonical_closed program seeds prepared accepted _ (begin_canonical program seeds prepared accepted)
  change closed prepared prepared.seedFacts.eraseDups = true at checked
  simp only [begin,checked,if_true]

theorem tick_noFault (program : Program) (seeds : List GroundFact) (prepared : Executable.Prepared)
    (accepted : Executable.prepare program seeds = .ok prepared)
    (scope : GeneralPremise.Static.checkLanguage (GeneralPlanEnvironment.environment (Executable.plan prepared prepared.seedFacts)) = true)
    (machine : Machine prepared) (reached : SearchReached prepared machine)
    (canonical : CanonicalFacts prepared machine.facts) (healthy : machine.fault = none) (quantum : Nat) :
    (tick prepared machine quantum).fault = none := by
  obtain ⟨work,read⟩ := reached healthy
  have resumed : (search prepared machine.facts).resume machine.run quantum =
      (search prepared machine.facts).run (Executable.request prepared.vocabulary) (work + quantum) := by
    rw [read]
    exact (Complete.Normalized.search_lawful (Executable.plan prepared machine.facts) [] (.base "DlStatement") .standard).resume_run _ _ _
  have valid : ∀ receipt ∈ (search prepared machine.facts).publication ((search prepared machine.facts).resume machine.run quantum),
      receipt.Valid (Executable.plan prepared machine.facts) [] (.base "DlStatement") (Executable.request prepared.vocabulary) := by
    rw [resumed]
    exact (Complete.Normalized.search_lawful (Executable.plan prepared machine.facts) [] (.base "DlStatement") .standard).sound _ (work + quantum)
  obtain ⟨facts,keys,committed⟩ := commit_total program seeds prepared accepted scope machine.facts _ valid machine.facts machine.keys
  have nextCanonical := commit_canonical program seeds prepared accepted scope machine.facts _ valid machine.facts machine.keys facts keys canonical committed
  have nextClosed := canonical_closed program seeds prepared accepted facts nextCanonical
  unfold tick
  split
  · exact healthy
  · dsimp only
    split
    · exact healthy
    · simp only [committed,nextClosed,if_true]
      split
      · exact healthy
      · rfl

theorem advance_noFault (program : Program) (seeds : List GroundFact) (prepared : Executable.Prepared)
    (accepted : Executable.prepare program seeds = .ok prepared)
    (scope : GeneralPremise.Static.checkLanguage (GeneralPlanEnvironment.environment (Executable.plan prepared prepared.seedFacts)) = true)
    (machine : Machine prepared) (reached : SearchReached prepared machine) (canonical : CanonicalFacts prepared machine.facts)
    (healthy : machine.fault = none) (ticks quantum : Nat) : (advance prepared ticks quantum machine).fault = none := by
  induction ticks generalizing machine with
  | zero => exact healthy
  | succ ticks ih =>
    exact ih _ (tick_searchReached prepared machine reached quantum) (tick_canonical program seeds prepared accepted scope machine reached canonical quantum)
      (tick_noFault program seeds prepared accepted scope machine reached canonical healthy quantum)

theorem run_noFault (program : Program) (seeds : List GroundFact) (prepared : Executable.Prepared)
    (accepted : Executable.prepare program seeds = .ok prepared)
    (scope : GeneralPremise.Static.checkLanguage (GeneralPlanEnvironment.environment (Executable.plan prepared prepared.seedFacts)) = true)
    (ticks quantum : Nat) : (advance prepared ticks quantum (begin prepared)).fault = none :=
  advance_noFault program seeds prepared accepted scope (begin prepared) (begin_searchReached prepared)
    (begin_canonical program seeds prepared accepted) (begin_noFault program seeds prepared accepted) ticks quantum

#print axioms commit_total
#print axioms run_noFault

end Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.ClosureMachine
