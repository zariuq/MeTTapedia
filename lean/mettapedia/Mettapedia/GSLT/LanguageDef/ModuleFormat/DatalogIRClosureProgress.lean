import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRClosureSoundness

/-! Reachable closure frames preserve old facts and retain concrete
settlement evidence. A completed frame records a drained shared search and
successful commit of that publication without changing its fact snapshot. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.ClosureMachine

open Mettapedia.OSLF.MeTTaIL Syntax

theorem tick_facts_monotone (prepared : Executable.Prepared) (machine : Machine prepared) (quantum : Nat) :
    ∀ fact ∈ machine.facts, fact ∈ (tick prepared machine quantum).facts := by
  unfold tick
  split
  · exact fun _ member => member
  · dsimp only
    split
    · exact fun _ member => member
    · try dsimp only
      split
      · exact fun _ member => member
      · rename_i facts keys committed
        have preserves : ∀ fact ∈ machine.facts, fact ∈ facts := by
          intro fact member
          exact ((Conservation.commit_observations prepared machine.facts _ machine.facts machine.keys facts keys committed).1 fact).mpr (Or.inl member)
        try dsimp only
        split
        · exact fun _ member => member
        · split
          · exact preserves
          · exact fun _ member => member

theorem advance_facts_monotone (prepared : Executable.Prepared) (machine : Machine prepared) (ticks quantum : Nat) :
    ∀ fact ∈ machine.facts, fact ∈ (advance prepared ticks quantum machine).facts := by
  induction ticks generalizing machine with
  | zero => exact fun _ member => member
  | succ ticks ih =>
    intro fact member
    exact ih _ fact (tick_facts_monotone prepared machine quantum fact member)

def SettlementEvidence (prepared : Executable.Prepared) (machine : Machine prepared) : Prop :=
  machine.complete = true → machine.fault = none ∧ ∃ work,
    (search prepared machine.facts).status ((search prepared machine.facts).run (Executable.request prepared.vocabulary) work) = .complete ∧
    ∃ before, commit? prepared machine.facts
      ((search prepared machine.facts).publication ((search prepared machine.facts).run (Executable.request prepared.vocabulary) work))
      machine.facts before = some (machine.facts,machine.keys)

theorem begin_settlementEvidence (prepared : Executable.Prepared) : SettlementEvidence prepared (begin prepared) := by
  intro impossible
  cases impossible

theorem tick_settlementEvidence (prepared : Executable.Prepared) (machine : Machine prepared)
    (reached : SearchReached prepared machine) (previous : SettlementEvidence prepared machine) (quantum : Nat) :
    SettlementEvidence prepared (tick prepared machine quantum) := by
  unfold tick
  split
  · exact previous
  · rename_i active
    have noFault : machine.fault = none := by
      cases found : machine.fault with
      | none => rfl
      | some fault => simp [found] at active
    have notComplete : machine.complete = false := by simpa [noFault] using active
    obtain ⟨work,read⟩ := reached noFault
    have resumed : (search prepared machine.facts).resume machine.run quantum =
        (search prepared machine.facts).run (Executable.request prepared.vocabulary) (work + quantum) := by
      rw [read]
      exact (Complete.Normalized.search_lawful (Executable.plan prepared machine.facts) [] (.base "DlStatement") .standard).resume_run _ _ _
    dsimp only
    split
    · intro impossible
      simp only [notComplete,Bool.false_eq_true] at impossible
    · rename_i finished
      have done : (search prepared machine.facts).status ((search prepared machine.facts).run (Executable.request prepared.vocabulary) (work + quantum)) = .complete := by
        simpa [resumed] using finished
      try dsimp only
      split
      · intro impossible
        simp only [notComplete,Bool.false_eq_true] at impossible
      · rename_i facts keys committed
        try dsimp only
        split
        · rename_i same
          subst facts
          intro _
          exact ⟨noFault,work + quantum,done,machine.keys,by simpa only [resumed] using committed⟩
        · split
          · intro impossible; cases impossible
          · intro impossible
            simp only [notComplete,Bool.false_eq_true] at impossible

theorem advance_settlementEvidence (prepared : Executable.Prepared) (machine : Machine prepared)
    (reached : SearchReached prepared machine) (previous : SettlementEvidence prepared machine) (ticks quantum : Nat) :
    SettlementEvidence prepared (advance prepared ticks quantum machine) := by
  induction ticks generalizing machine with
  | zero => exact previous
  | succ ticks ih =>
    exact ih _ (tick_searchReached prepared machine reached quantum)
      (tick_settlementEvidence prepared machine reached previous quantum)

theorem run_settlementEvidence (prepared : Executable.Prepared) (ticks quantum : Nat) :
    SettlementEvidence prepared (advance prepared ticks quantum (begin prepared)) :=
  advance_settlementEvidence prepared (begin prepared) (begin_searchReached prepared) (begin_settlementEvidence prepared) ticks quantum

#print axioms tick_facts_monotone
#print axioms advance_facts_monotone
#print axioms run_settlementEvidence

end Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.ClosureMachine
