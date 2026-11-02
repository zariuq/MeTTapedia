import Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangMailboxModelAgreement
import Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangMailboxCanonical
import Mettapedia.OSLF.MeTTaIL.Complete.Normalized
import Mettapedia.OSLF.MeTTaIL.Complete.Explore

/-! Readback of every finite shared-runner prefix and every completed
mailbox answer. The canonical commit mode is the emitted kernel's actual
mode. A finite budget remains pending unless the runner proves completion. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangMailbox.Execution.Runner

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Machines.ResumableSearchRunner (Machine)
open Model

abbrev base := ContextualStep.engineBasePremises Engine.RelationEnv.empty

theorem commit_fixed {source : Pattern} (canonical : CanonicalBags.canon source = source) :
    Complete.Normalized.commit plan .canonical source = source := by
  have laws : Complete.Normalized.laws plan = [] := by cbv
  have extrusions : Complete.Normalized.extrusions plan = [] := by cbv
  rw [Complete.Normalized.commit, Complete.Normalized.standard, laws, extrusions,
    CollectionLaws.standardForm_nil, canonical]

theorem normalized_readback {source target : Pattern}
    (canonical : CanonicalBags.canon source = source)
    (step : Complete.Normalized.NormalizedStep plan [] (.base "ErMailboxConfig") .canonical source target) :
    ContextualStep.Step base language source target ∧
      CanonicalBags.canon target = target ∧ Sorted target := by
  obtain ⟨reached, step, committed⟩ := step
  obtain ⟨actual, typed⟩ := step_readback step
  have fixed := step_preserves_canonical base canonical actual
  rw [commit_fixed fixed] at committed
  subst target
  exact ⟨actual, fixed, typed⟩

theorem normalized_path_readback {source target : Pattern}
    (canonical : CanonicalBags.canon source = source) (typed : Sorted source)
    (path : Relation.ReflTransGen
      (Complete.Normalized.NormalizedStep plan [] (.base "ErMailboxConfig") .canonical) source target) :
    Path base source target ∧ CanonicalBags.canon target = target ∧ Sorted target := by
  induction path with
  | refl => exact ⟨.refl, canonical, typed⟩
  | tail _ step ih =>
      obtain ⟨actual, fixed, sorted⟩ := normalized_readback ih.2.1 step
      exact ⟨ih.1.tail actual, fixed, sorted⟩

def run (source : Pattern) (ticks quantum : Nat) : Complete.Classes.Machine plan :=
  Machine.advance (Complete.Normalized.search plan [] (.base "ErMailboxConfig") .canonical) ticks quantum
    (Machine.begin (Complete.Normalized.search plan [] (.base "ErMailboxConfig") .canonical)
      (Complete.Normalized.commit plan .canonical source))

theorem run_source_path (source : Pattern) (ticks quantum : Nat)
    (canonical : CanonicalBags.canon source = source) (typed : Sorted source) :
    Path base source (run source ticks quantum).state ∧
      CanonicalBags.canon (run source ticks quantum).state = (run source ticks quantum).state ∧
      Sorted (run source ticks quantum).state := by
  have path := Mettapedia.Machines.ResumableSearchRunner.advance_reaches
    (Complete.Normalized.search_lawful plan [] (.base "ErMailboxConfig") .canonical)
    (Reduces := Complete.Normalized.NormalizedStep plan [] (.base "ErMailboxConfig") .canonical)
    (fun valid => ⟨_, GeneralOccurrenceSemantics.Receipt.semantic_step plan [] (.base "ErMailboxConfig") valid, rfl⟩)
    quantum ticks
    (Mettapedia.Machines.ResumableSearchRunner.begin_reached
      (Complete.Normalized.commit plan .canonical source))
  change Relation.ReflTransGen
    (Complete.Normalized.NormalizedStep plan [] (.base "ErMailboxConfig") .canonical)
    (Complete.Normalized.commit plan .canonical source) (run source ticks quantum).state at path
  rw [commit_fixed canonical] at path
  exact normalized_path_readback canonical typed path

theorem equations_checked : Complete.Predecessors.equationsChecked plan = true := by cbv

theorem descent_checked : StructuralDescent.checkEnvironment environment = true := by cbv

theorem search_settles (source : Pattern) :
    ∃ work, Complete.Classes.complete plan
      (Complete.Classes.runAt plan [] (.base "ErMailboxConfig") source work) = true :=
  Complete.Classes.equationFree_eventually_complete plan [] (.base "ErMailboxConfig") source
    equations_empty descent_checked

theorem source_step_discovered {source target : Pattern} (typed : Sorted source)
    (step : ContextualStep.Step base language source target) :
    ∃ work receipt, receipt ∈ (Complete.Classes.runAt plan [] (.base "ErMailboxConfig") source work).log ∧
      receipt.target = target := by
  obtain ⟨work, receipt, member, after⟩ := Complete.Classes.complete_in_limit plan [] (.base "ErMailboxConfig")
    source equations_checked ((step_iff_reference typed).mpr step)
  exact ⟨work, receipt, member, Complete.Classes.equivalent_eq_of_no_equations plan [] (.base "ErMailboxConfig")
    equations_empty after⟩

theorem source_path_explored {source target : Pattern}
    (canonical : CanonicalBags.canon source = source) (typed : Sorted source)
    (path : Path base source target) :
    Complete.Explore.Explored
      (S := Complete.Normalized.search plan [] (.base "ErMailboxConfig") .canonical) source target ∧
      CanonicalBags.canon target = target ∧ Sorted target := by
  induction path with
  | refl => exact ⟨Complete.Explore.explored_source _, canonical, typed⟩
  | @tail middle target _ step ih =>
      have semantic := (step_iff_reference ih.2.2).mpr step
      obtain ⟨_, targetTyped⟩ := step_readback semantic
      have fixed := step_preserves_canonical base ih.2.1 step
      obtain ⟨work, receipt, member, endpoint⟩ := source_step_discovered ih.2.2 step
      have published : receipt ∈
          (Complete.Normalized.search plan [] (.base "ErMailboxConfig") .canonical).publication
            ((Complete.Normalized.search plan [] (.base "ErMailboxConfig") .canonical).run middle work) := member
      have found := Complete.Explore.explored_target
        (Complete.Normalized.search_lawful plan [] (.base "ErMailboxConfig") .canonical) ih.1 published
      change Complete.Explore.Explored
        (S := Complete.Normalized.search plan [] (.base "ErMailboxConfig") .canonical)
        source (Complete.Normalized.commit plan .canonical receipt.target) at found
      rw [endpoint, commit_fixed fixed] at found
      exact ⟨found, fixed, targetTyped⟩

theorem done_value {source answer : Pattern} (settles : Settles base source answer)
    (canonical : CanonicalBags.canon source = source) (typed : Sorted source)
    (ticks quantum : Nat) (done : (run source ticks quantum).phase = .done) :
    (run source ticks quantum).state = answer := by
  obtain ⟨path, _, sorted⟩ := run_source_path source ticks quantum canonical typed
  have reached := Mettapedia.Machines.ResumableSearchRunner.run_reached
    (Complete.Normalized.search_lawful plan [] (.base "ErMailboxConfig") .canonical)
    (Complete.Normalized.commit plan .canonical source) ticks quantum
  have noStep := Complete.Normalized.done_no_step plan [] (.base "ErMailboxConfig") equations_checked reached done
  exact settles.exact _ path (fun target step => noStep target ((step_iff_reference sorted).mpr step))

end Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangMailbox.Execution.Runner
