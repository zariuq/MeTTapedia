import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRCommitSoundness
import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRClosureReachability

/-! Every finite native-model prefix contains only decodable, independently
derivable Datalog facts. The invariant includes pending and faulted states;
it does not assert search exhaustion or source-firing coverage. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.ClosureMachine

open Mettapedia.Languages.Datalog
open Mettapedia.OSLF.MeTTaIL Syntax

private instance : LawfulBEq Pattern where
  rfl := by intro value; change decide (value = value) = true; simp
  eq_of_beq := by intro first second same; change decide (first = second) = true at same; exact of_decide_eq_true same

private theorem traversed_member {α β : Type} (encode : α → Option β) (inputs : List α) (outputs : List β)
    (encoded : inputs.mapM encode = some outputs) (output : β) (member : output ∈ outputs) :
    ∃ input ∈ inputs, encode input = some output := by
  induction inputs generalizing outputs with
  | nil =>
    have empty : outputs = [] := by simpa using encoded.symm
    subst outputs
    cases member
  | cons input inputs ih =>
    cases first : encode input with
    | none => simp [List.mapM_cons,first] at encoded
    | some value =>
      cases later : inputs.mapM encode with
      | none => simp [List.mapM_cons,first,later] at encoded
      | some rest =>
        have same : value :: rest = outputs := by simpa [List.mapM_cons,first,later] using encoded
        subst outputs
        rcases List.mem_cons.mp member with rfl | member
        · exact ⟨input,List.mem_cons_self,first⟩
        · obtain ⟨source,present,read⟩ := ih rest later member
          exact ⟨source,List.mem_cons_of_mem _ present,read⟩

def FactsSound (prepared : Executable.Prepared) (program : Program) (seeds : List GroundFact)
    (values : List Pattern) : Prop := ∀ value ∈ values, ∃ fact,
      Executable.decodeFact? prepared value = some fact ∧ Closure.Derives Executable.policy program seeds fact

theorem begin_factsSound (program : Program) (seeds : List GroundFact) (prepared : Executable.Prepared)
    (accepted : Executable.prepare program seeds = .ok prepared) :
    FactsSound prepared program seeds (begin prepared).facts := by
  obtain ⟨core,encoded,_,read,same⟩ := PlanReading.prepared_payload program seeds prepared accepted
  subst prepared
  intro value member
  have present : value ∈ encoded := List.mem_eraseDups.mp (List.mem_eraseDups.mp member)
  obtain ⟨fact,atSource,formed⟩ := traversed_member (Executable.fact? core.vocabulary) seeds encoded read value present
  exact ⟨fact,Executable.decodeFact?_roundtrip _ fact value formed,.seed atSource⟩

theorem tick_factsSound (program : Program) (seeds : List GroundFact) (prepared : Executable.Prepared)
    (accepted : Executable.prepare program seeds = .ok prepared)
    (checked : GeneralPremise.Static.checkLanguage (GeneralPlanEnvironment.environment (Executable.plan prepared prepared.seedFacts)) = true)
    (machine : Machine prepared) (reached : SearchReached prepared machine)
    (sound : FactsSound prepared program seeds machine.facts) (quantum : Nat) :
    FactsSound prepared program seeds (tick prepared machine quantum).facts := by
  unfold tick
  split
  · exact sound
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
    let facts := machine.facts.filterMap (Executable.decodeFact? prepared)
    have represented : ∀ value ∈ machine.facts, ∃ fact ∈ facts, Executable.decodeFact? prepared value = some fact := by
      intro value member
      obtain ⟨fact,decoded,_⟩ := sound value member
      exact ⟨fact,List.mem_filterMap.mpr ⟨value,member,decoded⟩,decoded⟩
    have derived : ∀ fact ∈ facts, Closure.Derives Executable.policy program seeds fact := by
      intro fact member
      obtain ⟨value,present,decoded⟩ := List.mem_filterMap.mp member
      obtain ⟨actual,read,derived⟩ := sound value present
      have same : actual = fact := Option.some.inj (read.symm.trans decoded)
      exact same ▸ derived
    dsimp only
    split
    · exact sound
    · try dsimp only
      split
      · exact sound
      · rename_i resultFacts resultKeys committed
        have resultSound : FactsSound prepared program seeds resultFacts :=
          CommitSoundness.source_facts program seeds seeds prepared accepted machine.facts facts represented derived checked _ valid
            machine.keys resultFacts resultKeys committed
        try dsimp only
        split
        · exact sound
        · split
          · exact resultSound
          · exact sound

theorem advance_factsSound (program : Program) (seeds : List GroundFact) (prepared : Executable.Prepared)
    (accepted : Executable.prepare program seeds = .ok prepared)
    (checked : GeneralPremise.Static.checkLanguage (GeneralPlanEnvironment.environment (Executable.plan prepared prepared.seedFacts)) = true)
    (machine : Machine prepared) (reached : SearchReached prepared machine)
    (sound : FactsSound prepared program seeds machine.facts) (ticks quantum : Nat) :
    FactsSound prepared program seeds (advance prepared ticks quantum machine).facts := by
  induction ticks generalizing machine with
  | zero => exact sound
  | succ ticks ih =>
    exact ih _ (tick_searchReached prepared machine reached quantum)
      (tick_factsSound program seeds prepared accepted checked machine reached sound quantum)

theorem run_factsSound (program : Program) (seeds : List GroundFact) (prepared : Executable.Prepared)
    (accepted : Executable.prepare program seeds = .ok prepared)
    (checked : GeneralPremise.Static.checkLanguage (GeneralPlanEnvironment.environment (Executable.plan prepared prepared.seedFacts)) = true)
    (ticks quantum : Nat) : FactsSound prepared program seeds (advance prepared ticks quantum (begin prepared)).facts :=
  advance_factsSound program seeds prepared accepted checked (begin prepared) (begin_searchReached prepared)
    (begin_factsSound program seeds prepared accepted) ticks quantum

#print axioms begin_factsSound
#print axioms tick_factsSound
#print axioms advance_factsSound
#print axioms run_factsSound

end Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.ClosureMachine
