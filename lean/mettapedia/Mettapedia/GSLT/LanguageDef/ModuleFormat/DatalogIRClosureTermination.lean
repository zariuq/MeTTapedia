import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRClosureBounds
import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRSnapshotTermination
import Mettapedia.OSLF.MeTTaIL.Complete.Settled
import Mathlib.Data.Finset.Max

/-! Finite source facts force reachable snapshots to stabilize. While a
stable snapshot remains pending, its actual retained search accumulates work;
completed searches remain complete under further resumption. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.ClosureMachine

open Mettapedia.Languages.Datalog
open Mettapedia.OSLF.MeTTaIL Syntax

theorem facts_eventually_constant (program : Program) (seeds : List GroundFact) (prepared : Executable.Prepared)
    (accepted : Executable.prepare program seeds = .ok prepared)
    (scope : GeneralPremise.Static.checkLanguage (GeneralPlanEnvironment.environment (Executable.plan prepared prepared.seedFacts)) = true)
    (quantum : Nat) : ∃ start, ∀ extra,
      (advance prepared (start + extra) quantum (begin prepared)).facts = (advance prepared start quantum (begin prepared)).facts := by
  classical
  let bound := (physicalFactUniverse program seeds prepared).card
  let lengths := (Finset.range (bound + 1)).filter fun length =>
    ∃ ticks, (advance prepared ticks quantum (begin prepared)).facts.length = length
  have member (ticks : Nat) : (advance prepared ticks quantum (begin prepared)).facts.length ∈ lengths :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (run_fact_length_bound program seeds prepared accepted scope ticks quantum)),ticks,rfl⟩
  have inhabited : lengths.Nonempty := ⟨_,member 0⟩
  have maximum := Finset.max'_mem lengths inhabited
  obtain ⟨start,atMaximum⟩ := (Finset.mem_filter.mp maximum).2
  refine ⟨start,?_⟩
  intro extra
  have ordered := advance_fact_order prepared (advance prepared start quantum (begin prepared)) (run_fact_order prepared start quantum).2 extra quantum
  rw [← advance_add] at ordered
  have upper := Finset.le_max' lengths _ (member (start + extra))
  rw [← atMaximum] at upper
  exact (ordered.1.sublist.eq_of_length_le upper).symm

theorem pending_tick_work (program : Program) (seeds : List GroundFact) (prepared : Executable.Prepared)
    (accepted : Executable.prepare program seeds = .ok prepared)
    (scope : GeneralPremise.Static.checkLanguage (GeneralPlanEnvironment.environment (Executable.plan prepared prepared.seedFacts)) = true)
    (machine : Machine prepared) (canonical : CanonicalFacts prepared machine.facts) (healthy : machine.fault = none)
    (work quantum : Nat) (read : machine.run = (search prepared machine.facts).run (Executable.request prepared.vocabulary) work)
    (pending : machine.complete = false) (nextPending : (tick prepared machine quantum).complete = false)
    (unchanged : (tick prepared machine quantum).facts = machine.facts) :
    ((search prepared machine.facts).status ((search prepared machine.facts).resume machine.run quantum) != .complete) = true ∧
    (tick prepared machine quantum).run =
      (search prepared (tick prepared machine quantum).facts).run (Executable.request prepared.vocabulary) (work + quantum) := by
  have reached : SearchReached prepared machine := by intro _; exact ⟨work,read⟩
  have nextHealthy := tick_noFault program seeds prepared accepted scope machine reached canonical healthy quantum
  have searchPending : ((search prepared machine.facts).status ((search prepared machine.facts).resume machine.run quantum) != .complete) = true := by
    by_contra failed
    have completed : ((search prepared machine.facts).status ((search prepared machine.facts).resume machine.run quantum) != .complete) = false :=
      Bool.eq_false_iff.mpr failed
    cases committed : commit? prepared machine.facts
        ((search prepared machine.facts).publication ((search prepared machine.facts).resume machine.run quantum)) machine.facts machine.keys with
    | none => simp [tick,pending,healthy,completed,committed] at nextHealthy
    | some result =>
      rcases result with ⟨facts,keys⟩
      by_cases same : facts = machine.facts
      · simp [tick,pending,healthy,completed,committed,same] at nextPending
      · by_cases checked : closed prepared facts = true
        · simp [tick,pending,healthy,completed,committed,same,checked] at unchanged
        · simp [tick,pending,healthy,completed,committed,same,checked] at nextHealthy
  have resumed : (search prepared machine.facts).resume machine.run quantum =
      (search prepared machine.facts).run (Executable.request prepared.vocabulary) (work + quantum) := by
    rw [read]
    exact (Complete.Normalized.search_lawful (Executable.plan prepared machine.facts) [] (.base "DlStatement") .standard).resume_run _ _ _
  refine ⟨searchPending,?_⟩
  have shape : tick prepared machine quantum =
      {machine with run := (search prepared machine.facts).resume machine.run quantum} := by
    simp only [tick,pending,healthy,Option.isSome_none,Bool.false_or,Bool.false_eq_true,if_false,searchPending,if_true]
  rw [shape]
  exact resumed

theorem search_complete_later (prepared : Executable.Prepared) (facts : List Pattern) (first extra : Nat)
    (done : (search prepared facts).status ((search prepared facts).run (Executable.request prepared.vocabulary) first) = .complete) :
    (search prepared facts).status ((search prepared facts).run (Executable.request prepared.vocabulary) (first + extra)) = .complete := by
  have resumed : (search prepared facts).resume ((search prepared facts).run (Executable.request prepared.vocabulary) first) extra =
      (search prepared facts).run (Executable.request prepared.vocabulary) (first + extra) :=
    (Complete.Normalized.search_lawful (Executable.plan prepared facts) [] (.base "DlStatement") .standard).resume_run _ first extra
  rw [← resumed]
  exact (Complete.Settled.normalized_stable (Executable.plan prepared facts) [] (.base "DlStatement") .standard _ extra done).2

theorem advance_succ_right (prepared : Executable.Prepared) (ticks quantum : Nat) (machine : Machine prepared) :
    advance prepared (ticks + 1) quantum machine = tick prepared (advance prepared ticks quantum machine) quantum := by
  rw [advance_add]
  rfl

theorem run_eventually_complete (program : Program) (seeds : List GroundFact) (prepared : Executable.Prepared)
    (accepted : Executable.prepare program seeds = .ok prepared)
    (scope : GeneralPremise.Static.checkLanguage (GeneralPlanEnvironment.environment (Executable.plan prepared prepared.seedFacts)) = true)
    (quantum : Nat) (positive : 0 < quantum) :
    ∃ ticks, (advance prepared ticks quantum (begin prepared)).complete = true := by
  by_contra noFinish
  have pending (ticks : Nat) : (advance prepared ticks quantum (begin prepared)).complete = false :=
    Bool.eq_false_iff.mpr (fun done => noFinish ⟨ticks,done⟩)
  obtain ⟨start,constant⟩ := facts_eventually_constant program seeds prepared accepted scope quantum
  obtain ⟨work,read⟩ := (advance_searchReached prepared (begin prepared) (begin_searchReached prepared) start quantum)
    (run_noFault program seeds prepared accepted scope start quantum)
  have reading : ∀ extra,
      (advance prepared (start + extra) quantum (begin prepared)).run =
        (search prepared (advance prepared (start + extra) quantum (begin prepared)).facts).run
          (Executable.request prepared.vocabulary) (work + extra * quantum) := by
    intro extra
    induction extra with
    | zero => simpa only [Nat.add_zero,Nat.zero_mul] using read
    | succ extra ih =>
      have after : advance prepared (start + (extra + 1)) quantum (begin prepared) =
          tick prepared (advance prepared (start + extra) quantum (begin prepared)) quantum := by
        rw [← Nat.add_assoc,advance_succ_right]
      have unchanged : (tick prepared (advance prepared (start + extra) quantum (begin prepared)) quantum).facts =
          (advance prepared (start + extra) quantum (begin prepared)).facts := by
        rw [← after,constant (extra + 1),constant extra]
      have step := pending_tick_work program seeds prepared accepted scope (advance prepared (start + extra) quantum (begin prepared))
        (run_canonical program seeds prepared accepted scope (start + extra) quantum)
        (run_noFault program seeds prepared accepted scope (start + extra) quantum) (work + extra * quantum) quantum ih (pending _)
        (by rw [← after]; exact pending _) unchanged
      rw [← after] at step
      simpa only [Nat.add_mul,Nat.one_mul,Nat.add_assoc] using step.2
  obtain ⟨limit,done⟩ := SnapshotTermination.search_finishes program seeds prepared accepted
    (advance prepared start quantum (begin prepared)).facts scope
  let targetWork := work + limit * quantum + quantum
  have enough : limit ≤ targetWork := by
    have product : limit ≤ limit * quantum := by
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left limit (show 1 ≤ quantum from positive)
    omega
  have fixedDone := search_complete_later prepared (advance prepared start quantum (begin prepared)).facts limit (targetWork - limit) done
  have currentDone : (search prepared (advance prepared (start + limit) quantum (begin prepared)).facts).status
      ((search prepared (advance prepared (start + limit) quantum (begin prepared)).facts).run
        (Executable.request prepared.vocabulary) targetWork) = .complete := by
    rw [constant limit]
    simpa only [Nat.add_sub_of_le enough] using fixedDone
  have after : advance prepared (start + (limit + 1)) quantum (begin prepared) =
      tick prepared (advance prepared (start + limit) quantum (begin prepared)) quantum := by
    rw [← Nat.add_assoc,advance_succ_right]
  have unchanged : (tick prepared (advance prepared (start + limit) quantum (begin prepared)) quantum).facts =
      (advance prepared (start + limit) quantum (begin prepared)).facts := by
    rw [← after,constant (limit + 1),constant limit]
  have step := pending_tick_work program seeds prepared accepted scope (advance prepared (start + limit) quantum (begin prepared))
    (run_canonical program seeds prepared accepted scope (start + limit) quantum)
    (run_noFault program seeds prepared accepted scope (start + limit) quantum) (work + limit * quantum) quantum (reading limit) (pending _)
    (by rw [← after]; exact pending _) unchanged
  have resumed : (search prepared (advance prepared (start + limit) quantum (begin prepared)).facts).resume
      (advance prepared (start + limit) quantum (begin prepared)).run quantum =
        (search prepared (advance prepared (start + limit) quantum (begin prepared)).facts).run
          (Executable.request prepared.vocabulary) targetWork := by
    rw [reading limit]
    exact (Complete.Normalized.search_lawful (Executable.plan prepared _) [] (.base "DlStatement") .standard).resume_run _ _ _
  have impossible := step.1
  rw [resumed,currentDone] at impossible
  simp at impossible

#print axioms facts_eventually_constant
#print axioms pending_tick_work
#print axioms search_complete_later
#print axioms run_eventually_complete

end Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.ClosureMachine
