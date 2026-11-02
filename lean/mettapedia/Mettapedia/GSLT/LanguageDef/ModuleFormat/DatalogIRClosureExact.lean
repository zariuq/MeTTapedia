import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRClosureCanonical
import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRSearchCoverage

/-! Completed actual closure-model runs compute exactly the independent
least positive source semantics. Canonical snapshots, seed preservation,
admission transport and stable-publication evidence are derived from the run.
Finite completion and the textual frontend remain separate contracts. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.ClosureMachine

open Mettapedia.Languages.Datalog
open Mettapedia.OSLF.MeTTaIL Syntax

theorem run_facts_exact (program : Program) (seeds : List GroundFact) (prepared : Executable.Prepared)
    (accepted : Executable.prepare program seeds = .ok prepared)
    (initial : (Executable.plan prepared prepared.seedFacts.eraseDups).complete = true)
    (scope : GeneralPremise.Static.checkLanguage (GeneralPlanEnvironment.environment (Executable.plan prepared prepared.seedFacts)) = true)
    (ticks quantum : Nat) (finished : (advance prepared ticks quantum (begin prepared)).complete = true)
    (fact : GroundFact) :
    fact ∈ ((advance prepared ticks quantum (begin prepared)).facts.filterMap (Executable.decodeFact? prepared)) ↔
      Closure.Derives Executable.policy program seeds fact := by
  let machine := advance prepared ticks quantum (begin prepared)
  let facts := machine.facts.filterMap (Executable.decodeFact? prepared)
  obtain ⟨healthy,work,done,before,committed⟩ := run_settlementEvidence prepared ticks quantum finished
  have admitted := run_admitted prepared initial ticks quantum healthy
  have encoded := canonical_decoding prepared machine.facts (run_canonical program seeds prepared accepted scope ticks quantum)
  have closed : Closure.FactsComplete Executable.policy program ⟨facts,[]⟩ := by
    intro key conclusion produced
    have authorized := (Closure.mem_firings_iff Executable.policy program facts key conclusion).mp produced
    exact SearchCoverage.stable_commit_closed program seeds prepared accepted facts machine.facts encoded admitted scope work done
      before machine.keys committed ⟨key,conclusion,[]⟩ authorized
  have seeded : ∀ seed ∈ seeds, seed ∈ facts := by
    intro seed member
    obtain ⟨code,present,formed⟩ := run_seed_fact program seeds prepared accepted ticks quantum seed member
    exact List.mem_filterMap.mpr ⟨code,present,Executable.decodeFact?_roundtrip prepared seed code formed⟩
  constructor
  · intro member
    obtain ⟨code,present,decoded⟩ := List.mem_filterMap.mp member
    obtain ⟨actual,read,derived⟩ := run_factsSound program seeds prepared accepted scope ticks quantum code present
    have same : actual = fact := Option.some.inj (read.symm.trans decoded)
    exact same ▸ derived
  · intro derived
    exact Closure.derives_in_closed Executable.policy program seeds ⟨facts,[]⟩ seeded closed derived

#print axioms run_facts_exact

end Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.ClosureMachine
