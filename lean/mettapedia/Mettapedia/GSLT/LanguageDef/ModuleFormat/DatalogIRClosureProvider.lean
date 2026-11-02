import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRClosureProgress
import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRSourcePlan

/-! Healthy reachable frames carry a checked provider snapshot. Replacing
the immutable provider preserves the actual shared plan's admission, and
resumed runs retain every encoded seed fact. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.ClosureMachine

open Mettapedia.Languages.Datalog
open Mettapedia.OSLF.MeTTaIL Syntax

def HealthyProvider (prepared : Executable.Prepared) (machine : Machine prepared) : Prop :=
  machine.fault = none → closed prepared machine.facts = true

theorem begin_healthyProvider (prepared : Executable.Prepared) : HealthyProvider prepared (begin prepared) := by
  intro healthy
  cases checked : closed prepared prepared.seedFacts.eraseDups with
  | false => simp [begin,checked] at healthy
  | true => exact checked

theorem tick_healthyProvider (prepared : Executable.Prepared) (machine : Machine prepared)
    (previous : HealthyProvider prepared machine) (quantum : Nat) : HealthyProvider prepared (tick prepared machine quantum) := by
  unfold tick
  split
  · exact previous
  · dsimp only
    split
    · exact previous
    · try dsimp only
      split
      · intro impossible; cases impossible
      · try dsimp only
        split
        · exact previous
        · split
          · rename_i checked
            intro _
            exact checked
          · intro impossible; cases impossible

theorem advance_healthyProvider (prepared : Executable.Prepared) (machine : Machine prepared)
    (previous : HealthyProvider prepared machine) (ticks quantum : Nat) :
    HealthyProvider prepared (advance prepared ticks quantum machine) := by
  induction ticks generalizing machine with
  | zero => exact previous
  | succ ticks ih => exact ih _ (tick_healthyProvider prepared machine previous quantum)

theorem run_healthyProvider (prepared : Executable.Prepared) (ticks quantum : Nat) :
    HealthyProvider prepared (advance prepared ticks quantum (begin prepared)) :=
  advance_healthyProvider prepared (begin prepared) (begin_healthyProvider prepared) ticks quantum

theorem run_admitted (prepared : Executable.Prepared)
    (initial : (Executable.plan prepared prepared.seedFacts.eraseDups).complete = true) (ticks quantum : Nat)
    (healthy : (advance prepared ticks quantum (begin prepared)).fault = none) :
    (Executable.plan prepared (advance prepared ticks quantum (begin prepared)).facts).complete = true :=
  Executable.snapshot_admission_transport prepared prepared.seedFacts.eraseDups _ initial
    (run_healthyProvider prepared ticks quantum healthy)

theorem run_seed_fact (program : Program) (seeds : List GroundFact) (prepared : Executable.Prepared)
    (accepted : Executable.prepare program seeds = .ok prepared) (ticks quantum : Nat)
    (fact : GroundFact) (member : fact ∈ seeds) :
    ∃ code ∈ (advance prepared ticks quantum (begin prepared)).facts,
      Executable.fact? prepared.vocabulary fact = some code := by
  obtain ⟨core,values,_,encoded,rfl⟩ := PlanReading.prepared_payload program seeds prepared accepted
  obtain ⟨code,present,formed⟩ := SourceQueries.encoded_member core.vocabulary seeds values
    (CompilationFlow.mapM_relation _ _ _ encoded) fact member
  refine ⟨code,advance_facts_monotone _ _ ticks quantum code ?_,formed⟩
  exact List.mem_eraseDups.mpr (List.mem_eraseDups.mpr present)

#print axioms run_healthyProvider
#print axioms run_admitted
#print axioms run_seed_fact

end Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.ClosureMachine
