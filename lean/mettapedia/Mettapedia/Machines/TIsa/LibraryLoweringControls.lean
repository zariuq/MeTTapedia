import Mettapedia.Machines.TIsa.LibraryLowering

/-!
Two ordinary bag additions implement one independently specified bulk add.
The controls distinguish exact completed-call behavior from prefix atomicity
and reject a replacement which silently reports refusal.
-/

set_option autoImplicit false
namespace Mettapedia.Machines.TIsa.LibraryLowering.Controls
open Mettapedia.GSLT.Logic.AbstractSeparationLogic

abbrev Bag := Multiset Nat
abbrev Operation := Nat × Nat

def expected (operation : Operation) (before : Bag) : Bag :=
  ({operation.1,operation.2} : Multiset Nat) + before

def high (operation : Operation) : Action Bag Bool where
  Safe := fun _ => True
  Step := fun before reply after => reply = true ∧ after = expected operation before

def low (atom : Nat) : Action Bag Unit :=
  Mettapedia.GSLT.Logic.AbstractSeparationLogic.Controls.addAct atom

def implementation (operation : Operation) : Prog Nat (fun _ => Unit) Bool :=
  .call operation.1 (fun _ => .call operation.2 (fun _ => .ret true))

theorem implementation_runs (operation : Operation) (before after : Bag) (reply : Bool) :
    (implementation operation).Runs low before reply after ↔
      reply = true ∧ after = expected operation before := by
  cases reply <;>
    simp [implementation,Prog.Runs,low,
      Mettapedia.GSLT.Logic.AbstractSeparationLogic.Controls.addAct,expected,Multiset.cons_swap,eq_comm]

theorem correct : Correct high low Eq implementation where
  defined := by
    intro operation source target represented
    subst target
    simp [high,implementation,Prog.Safe,low,
      Mettapedia.GSLT.Logic.AbstractSeparationLogic.Controls.addAct]
  complete := by
    intro operation source target reply following represented step
    subst target
    exact ⟨following,(implementation_runs operation source following reply).mpr step,rfl⟩
  sound := by
    intro operation source target reply after represented run
    subst target
    exact ⟨after,(implementation_runs operation source after reply).mp run,rfl⟩

def client : Prog Operation (fun _ => Bool) Bool :=
  .call (1,2) (fun _ => .call (3,4) (fun _ => .ret true))

theorem client_run : client.Runs high 0 true ({1,2,3,4} : Bag) := by
  simp [client,Prog.Runs,high,expected]
  decide

theorem client_lowered : (expand implementation client).Runs low 0 true ({1,2,3,4} : Bag) := by
  obtain ⟨after,run,same⟩ := correct.realizes client 0 ({1,2,3,4} : Bag) 0 true rfl client_run
  simpa only [←same] using run

theorem client_reflects (reply : Bool) (after : Bag)
    (run : (expand implementation client).Runs low 0 reply after) :
    reply = true ∧ after = ({1,2,3,4} : Bag) := by
  obtain ⟨following,sourceRun,same⟩ := correct.reflects client 0 0 after reply rfl run
  rw [←same]
  obtain ⟨_firstReply,middle,first,_secondReply,final,second,done⟩ := sourceRun
  refine ⟨done.1.symm,?_⟩
  rw [←done.2,second.2,first.2]
  decide

theorem source_frame (operation : Operation) (before frame : Bag) :
    expected operation (before + frame) = expected operation before + frame := by
  simp [expected]

def refusing (_ : Operation) : Prog Nat (fun _ => Unit) Bool := .ret false

theorem spurious_refusal_rejected : ¬ Correct high low Eq refusing := by
  intro claimed
  have run : (refusing (1,2)).Runs low (0 : Bag) false 0 := ⟨rfl,rfl⟩
  obtain ⟨following,step,_same⟩ := claimed.sound (1,2) 0 0 false 0 rfl run
  exact Bool.noConfusion step.1

theorem visible_prefix_is_not_atomic :
    (low 1).Step (0 : Bag) () ({1} : Bag) ∧
      ({1} : Bag) ≠ 0 ∧ ¬ (high (1,2)).Step 0 true ({1} : Bag) := by
  refine ⟨rfl,by decide,?_⟩
  intro step
  have size := congrArg Multiset.card step.2
  simp [expected] at size

#print axioms correct
#print axioms client_lowered
#print axioms client_reflects
#print axioms source_frame
#print axioms spurious_refusal_rejected
#print axioms visible_prefix_is_not_atomic
end Mettapedia.Machines.TIsa.LibraryLowering.Controls
