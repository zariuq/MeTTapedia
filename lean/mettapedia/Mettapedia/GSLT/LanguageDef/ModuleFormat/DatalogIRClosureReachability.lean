import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRClosureMachine

/-! Every live epoch runs an actual prefix of the shared search. Resumption
retains that prefix, and a new fact snapshot starts a new search at zero. -/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.ClosureMachine

open Mettapedia.OSLF.MeTTaIL Syntax

def SearchReached (prepared : Executable.Prepared) (machine : Machine prepared) : Prop :=
  machine.fault = none → ∃ work,
    machine.run = (search prepared machine.facts).run (Executable.request prepared.vocabulary) work

theorem begin_searchReached (prepared : Executable.Prepared) : SearchReached prepared (begin prepared) := by
  intro _
  exact ⟨0,rfl⟩

theorem tick_searchReached (prepared : Executable.Prepared) (machine : Machine prepared)
    (reached : SearchReached prepared machine) (quantum : Nat) : SearchReached prepared (tick prepared machine quantum) := by
  unfold tick
  split
  · exact reached
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
    dsimp only
    split
    · intro _
      exact ⟨work + quantum,resumed⟩
    · try dsimp only
      split
      · intro impossible
        cases impossible
      · try dsimp only
        split
        · intro _
          exact ⟨work + quantum,resumed⟩
        · split
          · intro _
            exact ⟨0,rfl⟩
          · intro impossible
            cases impossible

theorem advance_searchReached (prepared : Executable.Prepared) (machine : Machine prepared)
    (reached : SearchReached prepared machine) (ticks quantum : Nat) :
    SearchReached prepared (advance prepared ticks quantum machine) := by
  induction ticks generalizing machine with
  | zero => exact reached
  | succ ticks ih => exact ih _ (tick_searchReached prepared machine reached quantum)

theorem publication_valid (prepared : Executable.Prepared) (machine : Machine prepared)
    (reached : SearchReached prepared machine) (noFault : machine.fault = none) :
    ∀ receipt ∈ (search prepared machine.facts).publication machine.run,
      receipt.Valid (Executable.plan prepared machine.facts) [] (.base "DlStatement")
        (Executable.request prepared.vocabulary) := by
  obtain ⟨work,read⟩ := reached noFault
  rw [read]
  exact (Complete.Normalized.search_lawful (Executable.plan prepared machine.facts) [] (.base "DlStatement") .standard).sound _ work

#print axioms begin_searchReached
#print axioms tick_searchReached
#print axioms advance_searchReached
#print axioms publication_valid

end Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.ClosureMachine
