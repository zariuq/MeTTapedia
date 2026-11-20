import Mettapedia.Machines.TIsa.NativeRefinement

/-!
# Derived operation libraries over the existing program semantics

A library implements each operation by an existing `Prog`. Expansion is a
compiler over that syntax, not a second interpreter. Component contracts
retain both directions of outcomes and exact definedness through a state
representation. These laws compose through arbitrary client programs.

The native transfer reuses the established machine boundary. It does not
infer atomicity, frames, resource erasure or concrete native certificates
from program expansion; those remain obligations of the selected interface.
-/

set_option autoImplicit false
namespace Mettapedia.Machines.TIsa.LibraryLowering
open Mettapedia.GSLT.Logic.AbstractSeparationLogic

universe uHigh uLow uReply uSource uTarget uMachine
variable {HighOp : Type uHigh} {LowOp : Type uLow}
variable {HighReply : HighOp → Type uReply} {LowReply : LowOp → Type uReply}
variable {Source : Type uSource} {Target : Type uTarget} {Result : Type uReply}

abbrev Library := (operation : HighOp) → Prog LowOp LowReply (HighReply operation)

def expand (library : Library (HighOp := HighOp) (HighReply := HighReply) (LowReply := LowReply)) :
    Prog HighOp HighReply Result → Prog LowOp LowReply Result
  | .ret value => .ret value
  | .call operation next => (library operation).bind (fun reply => expand library (next reply))

theorem expand_bind (library : Library (HighOp := HighOp) (HighReply := HighReply) (LowReply := LowReply))
    {Other : Type uReply} (program : Prog HighOp HighReply Result) (next : Result → Prog HighOp HighReply Other) :
    expand library (program.bind next) = (expand library program).bind (fun value => expand library (next value)) := by
  induction program with
  | ret value => rfl
  | call operation later ih => simp only [Prog.call_bind,expand,ih,Prog.bind_assoc]

structure Correct (high : (operation : HighOp) → Action Source (HighReply operation))
    (low : (operation : LowOp) → Action Target (LowReply operation))
    (related : Source → Target → Prop) (library : Library (HighOp := HighOp) (HighReply := HighReply) (LowReply := LowReply)) : Prop where
  defined : ∀ operation source target, related source target →
    ((high operation).Safe source ↔ (library operation).Safe low target)
  complete : ∀ operation source target reply following, related source target →
    (high operation).Step source reply following →
    ∃ after, (library operation).Runs low target reply after ∧ related following after
  sound : ∀ operation source target reply after, related source target →
    (library operation).Runs low target reply after →
    ∃ following, (high operation).Step source reply following ∧ related following after

variable {high : (operation : HighOp) → Action Source (HighReply operation)}
variable {low : (operation : LowOp) → Action Target (LowReply operation)}
variable {related : Source → Target → Prop} {library : Library (HighOp := HighOp) (HighReply := HighReply) (LowReply := LowReply)}

theorem Correct.realizes (correct : Correct high low related library) (program : Prog HighOp HighReply Result)
    (source following : Source) (target : Target) (value : Result) (represented : related source target)
    (run : program.Runs high source value following) :
    ∃ after, (expand library program).Runs low target value after ∧ related following after := by
  induction program generalizing source target with
  | ret answer =>
    obtain ⟨rfl,rfl⟩ := run
    exact ⟨target,⟨rfl,rfl⟩,represented⟩
  | call operation next ih =>
    obtain ⟨reply,middle,first,later⟩ := run
    obtain ⟨middleTarget,executed,middleRelated⟩ := correct.complete operation source target reply middle represented first
    obtain ⟨after,rest,finalRelated⟩ := ih reply middle middleTarget middleRelated later
    exact ⟨after,(Prog.runs_bind low (library operation) (fun reply => expand library (next reply)) target value after).mpr
      ⟨reply,middleTarget,executed,rest⟩,finalRelated⟩

theorem Correct.reflects (correct : Correct high low related library) (program : Prog HighOp HighReply Result)
    (source : Source) (target after : Target) (value : Result) (represented : related source target)
    (run : (expand library program).Runs low target value after) :
    ∃ following, program.Runs high source value following ∧ related following after := by
  induction program generalizing source target with
  | ret answer =>
    obtain ⟨rfl,rfl⟩ := run
    exact ⟨source,⟨rfl,rfl⟩,represented⟩
  | call operation next ih =>
    obtain ⟨reply,middleTarget,first,later⟩ :=
      (Prog.runs_bind low (library operation) (fun reply => expand library (next reply)) target value after).mp run
    obtain ⟨middle,step,middleRelated⟩ := correct.sound operation source target reply middleTarget represented first
    obtain ⟨following,rest,finalRelated⟩ := ih reply middle middleTarget middleRelated later
    exact ⟨following,⟨reply,middle,step,rest⟩,finalRelated⟩

theorem Correct.safe_iff (correct : Correct high low related library) (program : Prog HighOp HighReply Result)
    (source : Source) (target : Target) (represented : related source target) :
    program.Safe high source ↔ (expand library program).Safe low target := by
  induction program generalizing source target with
  | ret value => exact Iff.rfl
  | call operation next ih =>
    change (high operation).Safe source ∧ (∀ reply middle, (high operation).Step source reply middle → (next reply).Safe high middle) ↔ _
    rw [expand,Prog.safe_bind]
    constructor
    · rintro ⟨defined,continuation⟩
      refine ⟨(correct.defined operation source target represented).mp defined,?_⟩
      intro reply middleTarget step
      obtain ⟨middle,first,middleRelated⟩ := correct.sound operation source target reply middleTarget represented step
      exact (ih reply middle middleTarget middleRelated).mp (continuation reply middle first)
    · rintro ⟨defined,continuation⟩
      refine ⟨(correct.defined operation source target represented).mpr defined,?_⟩
      intro reply middle step
      obtain ⟨middleTarget,first,middleRelated⟩ := correct.complete operation source target reply middle represented step
      exact (ih reply middle middleTarget middleRelated).mpr (continuation reply middleTarget first)

theorem Correct.observed_iff (correct : Correct high low related library) (program : Prog HighOp HighReply Result)
    {View : Type uMachine} (sourceView : Source → View) (targetView : Target → View)
    (agree : ∀ source target, related source target → sourceView source = targetView target)
    (source : Source) (target : Target) (represented : related source target) (value : Result) (view : View) :
    (∃ following, program.Runs high source value following ∧ sourceView following = view) ↔
    ∃ after, (expand library program).Runs low target value after ∧ targetView after = view := by
  constructor
  · rintro ⟨following,run,observed⟩
    obtain ⟨after,executed,finalRelated⟩ := correct.realizes program source following target value represented run
    exact ⟨after,executed,(agree following after finalRelated).symm.trans observed⟩
  · rintro ⟨after,run,observed⟩
    obtain ⟨following,executed,finalRelated⟩ := correct.reflects program source target after value represented run
    exact ⟨following,executed,(agree following after finalRelated).trans observed⟩

theorem Correct.native_realizes (correct : Correct high low related library)
    {MachineState : Type uMachine} (machine : NativeRefinement.Machine MachineState)
    (representation : Prog LowOp LowReply Result → Target → MachineState → Prop)
    (observation : Result → Target → MachineState → Prop)
    (boundary : NativeRefinement.Boundary low machine representation observation)
    (program : Prog HighOp HighReply Result) (source following : Source) (target : Target)
    (native : MachineState) (value : Result) (represented : related source target)
    (entry : representation (expand library program) target native) (safe : program.Safe high source)
    (run : program.Runs high source value following) :
    ∃ afterTarget count afterNative, related following afterTarget ∧
      machine.executes count native afterNative ∧ machine.frame native afterNative ∧ observation value afterTarget afterNative := by
  obtain ⟨afterTarget,executed,finalRelated⟩ := correct.realizes program source following target value represented run
  obtain ⟨count,afterNative,nativeRun,frame,observed⟩ := boundary.realizes (expand library program)
    target afterTarget native value ((correct.safe_iff program source target represented).mp safe) entry executed
  exact ⟨afterTarget,count,afterNative,finalRelated,nativeRun,frame,observed⟩

section Composition
universe uMiddle uMiddleState
variable {MiddleOp : Type uMiddle} {MiddleReply : MiddleOp → Type uReply} {Middle : Type uMiddleState}

def compose (upper : (operation : HighOp) → Prog MiddleOp MiddleReply (HighReply operation))
    (lower : (operation : MiddleOp) → Prog LowOp LowReply (MiddleReply operation))
    (operation : HighOp) : Prog LowOp LowReply (HighReply operation) := expand lower (upper operation)

theorem expand_compose (upper : (operation : HighOp) → Prog MiddleOp MiddleReply (HighReply operation))
    (lower : (operation : MiddleOp) → Prog LowOp LowReply (MiddleReply operation))
    (program : Prog HighOp HighReply Result) :
    expand lower (expand upper program) = expand (compose upper lower) program := by
  induction program with
  | ret value => rfl
  | call operation next ih => simp only [expand,expand_bind,ih,compose]

theorem Correct.compose
    {middle : (operation : MiddleOp) → Action Middle (MiddleReply operation)}
    {upper : (operation : HighOp) → Prog MiddleOp MiddleReply (HighReply operation)}
    {lower : (operation : MiddleOp) → Prog LowOp LowReply (MiddleReply operation)}
    {first : Source → Middle → Prop} {second : Middle → Target → Prop}
    (upperCorrect : Correct high middle first upper) (lowerCorrect : Correct middle low second lower) :
    Correct high low (fun source target => ∃ state, first source state ∧ second state target) (compose upper lower) where
  defined := by
    rintro operation source target ⟨state,represented,realized⟩
    exact (upperCorrect.defined operation source state represented).trans
      (lowerCorrect.safe_iff (upper operation) state target realized)
  complete := by
    rintro operation source target reply following ⟨state,represented,realized⟩ step
    obtain ⟨middleAfter,run,firstRelated⟩ := upperCorrect.complete operation source state reply following represented step
    obtain ⟨after,executed,secondRelated⟩ := lowerCorrect.realizes (upper operation) state middleAfter target reply realized run
    exact ⟨after,executed,middleAfter,firstRelated,secondRelated⟩
  sound := by
    rintro operation source target reply after ⟨state,represented,realized⟩ run
    obtain ⟨middleAfter,executed,secondRelated⟩ := lowerCorrect.reflects (upper operation) state target after reply realized run
    obtain ⟨following,step,firstRelated⟩ := upperCorrect.sound operation source state reply middleAfter represented executed
    exact ⟨following,step,middleAfter,firstRelated,secondRelated⟩
end Composition

#print axioms expand_compose
#print axioms Correct.compose
#print axioms Correct.realizes
#print axioms Correct.reflects
#print axioms Correct.safe_iff
#print axioms Correct.observed_iff
#print axioms Correct.native_realizes
end Mettapedia.Machines.TIsa.LibraryLowering
