import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRReceiptCanonical
import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRClosureProvider

/-! Every reachable closure snapshot has the canonical encoder's physical
representation. Decoding that actual snapshot therefore yields an aligned
source fact list, rather than an assumed representation witness. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.ClosureMachine

open Mettapedia.Languages.Datalog
open Mettapedia.OSLF.MeTTaIL Syntax

def CanonicalFacts (prepared : Executable.Prepared) (codes : List Pattern) : Prop :=
  ∀ code ∈ codes, ∃ fact : GroundFact, Executable.fact? prepared.vocabulary fact = some code

private theorem encoded_canonical (pools : Join.Pools) (facts : List GroundFact) (codes : List Pattern)
    (encoded : List.Forall₂ (fun fact code => Executable.fact? pools fact = some code) facts codes) :
    ∀ code ∈ codes, ∃ fact : GroundFact, Executable.fact? pools fact = some code := by
  induction encoded with
  | nil => intro _ member; cases member
  | @cons fact code facts codes formed rest ih =>
    intro other member
    rcases List.mem_cons.mp member with rfl | later
    · exact ⟨fact,formed⟩
    · exact ih other later

theorem canonical_decoding (prepared : Executable.Prepared) (codes : List Pattern)
    (canonical : CanonicalFacts prepared codes) :
    List.Forall₂ (fun fact code => Executable.fact? prepared.vocabulary fact = some code)
      (codes.filterMap (Executable.decodeFact? prepared)) codes := by
  induction codes with
  | nil => exact .nil
  | cons code codes ih =>
    obtain ⟨fact,encoded⟩ := canonical code List.mem_cons_self
    have decoded := Executable.decodeFact?_roundtrip prepared fact code encoded
    rw [List.filterMap_cons,decoded]
    exact .cons encoded (ih (fun other member => canonical other (List.mem_cons_of_mem _ member)))

theorem begin_canonical (program : Program) (seeds : List GroundFact) (prepared : Executable.Prepared)
    (accepted : Executable.prepare program seeds = .ok prepared) : CanonicalFacts prepared (begin prepared).facts := by
  obtain ⟨core,values,_,read,rfl⟩ := PlanReading.prepared_payload program seeds prepared accepted
  have encoded := encoded_canonical core.vocabulary seeds values (CompilationFlow.mapM_relation _ _ _ read)
  intro code member
  exact encoded code (List.mem_eraseDups.mp (List.mem_eraseDups.mp member))

theorem commit_canonical (program : Program) (seeds : List GroundFact) (prepared : Executable.Prepared)
    (accepted : Executable.prepare program seeds = .ok prepared)
    (scope : GeneralPremise.Static.checkLanguage (GeneralPlanEnvironment.environment (Executable.plan prepared prepared.seedFacts)) = true)
    (snapshot : List Pattern) (batch : List GeneralOccurrenceSemantics.Receipt)
    (valid : ∀ receipt ∈ batch, receipt.Valid (Executable.plan prepared snapshot) [] (.base "DlStatement") (Executable.request prepared.vocabulary))
    (facts : List Pattern) (before : List Key) (outputs : List Pattern) (after : List Key)
    (previous : CanonicalFacts prepared facts)
    (committed : commit? prepared snapshot batch facts before = some (outputs,after)) : CanonicalFacts prepared outputs := by
  have membership := (Conservation.commit_observations prepared snapshot batch facts before outputs after committed).1
  intro code member
  rcases (membership code).mp member with old | emitted
  · exact previous code old
  · obtain ⟨receipt,present,rfl⟩ := List.mem_map.mp emitted
    exact ReceiptCanonical.target program seeds prepared accepted snapshot scope receipt (valid receipt present)

theorem tick_canonical (program : Program) (seeds : List GroundFact) (prepared : Executable.Prepared)
    (accepted : Executable.prepare program seeds = .ok prepared)
    (scope : GeneralPremise.Static.checkLanguage (GeneralPlanEnvironment.environment (Executable.plan prepared prepared.seedFacts)) = true)
    (machine : Machine prepared) (reached : SearchReached prepared machine)
    (previous : CanonicalFacts prepared machine.facts) (quantum : Nat) : CanonicalFacts prepared (tick prepared machine quantum).facts := by
  unfold tick
  split
  · exact previous
  · rename_i active
    have noFault : machine.fault = none := by
      cases found : machine.fault with
      | none => rfl
      | some fault => simp [found] at active
    obtain ⟨work,read⟩ := reached noFault
    have resumed : (search prepared machine.facts).resume machine.run quantum =
        (search prepared machine.facts).run (Executable.request prepared.vocabulary) (work + quantum) := by
      rw [read]
      exact (Complete.Normalized.search_lawful (Executable.plan prepared machine.facts) [] (.base "DlStatement") .standard).resume_run _ _ _
    have valid : ∀ receipt ∈ (search prepared machine.facts).publication ((search prepared machine.facts).resume machine.run quantum),
        receipt.Valid (Executable.plan prepared machine.facts) [] (.base "DlStatement") (Executable.request prepared.vocabulary) := by
      rw [resumed]
      exact (Complete.Normalized.search_lawful (Executable.plan prepared machine.facts) [] (.base "DlStatement") .standard).sound _ (work + quantum)
    dsimp only
    split
    · exact previous
    · try dsimp only
      split
      · exact previous
      · rename_i facts keys committed
        have result := commit_canonical program seeds prepared accepted scope machine.facts _ valid machine.facts machine.keys facts keys previous committed
        try dsimp only
        split
        · exact previous
        · split
          · exact result
          · exact previous

theorem advance_canonical (program : Program) (seeds : List GroundFact) (prepared : Executable.Prepared)
    (accepted : Executable.prepare program seeds = .ok prepared)
    (scope : GeneralPremise.Static.checkLanguage (GeneralPlanEnvironment.environment (Executable.plan prepared prepared.seedFacts)) = true)
    (machine : Machine prepared) (reached : SearchReached prepared machine) (previous : CanonicalFacts prepared machine.facts)
    (ticks quantum : Nat) : CanonicalFacts prepared (advance prepared ticks quantum machine).facts := by
  induction ticks generalizing machine with
  | zero => exact previous
  | succ ticks ih =>
    exact ih _ (tick_searchReached prepared machine reached quantum) (tick_canonical program seeds prepared accepted scope machine reached previous quantum)

theorem run_canonical (program : Program) (seeds : List GroundFact) (prepared : Executable.Prepared)
    (accepted : Executable.prepare program seeds = .ok prepared)
    (scope : GeneralPremise.Static.checkLanguage (GeneralPlanEnvironment.environment (Executable.plan prepared prepared.seedFacts)) = true)
    (ticks quantum : Nat) : CanonicalFacts prepared (advance prepared ticks quantum (begin prepared)).facts :=
  advance_canonical program seeds prepared accepted scope (begin prepared) (begin_searchReached prepared)
    (begin_canonical program seeds prepared accepted) ticks quantum

#print axioms canonical_decoding
#print axioms commit_canonical
#print axioms run_canonical

end Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.ClosureMachine
