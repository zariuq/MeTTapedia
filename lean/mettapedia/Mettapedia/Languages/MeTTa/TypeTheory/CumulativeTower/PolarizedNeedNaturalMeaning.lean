import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.PolarizedNeedNaturalContinuation
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.PolarizedNeedNaturalMachineLaws

/-!
# Independent meaning of first-class owned-machine controls

Source evaluation and consumer evaluation meet at an intermediate answer and
world. The source rules themselves contain no consumer or machine-path premise.
This proof-layer interpretation retains the entire heap and receipt world,
including the effects of applying a function after retrieving it from a cache.

Protocol stacks interpret ownership finalization and resumption independently
of execution. They do not assert that an initial program already has a source
derivation; that information must be reconstructed from a completed path.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
namespace PolarizedNeedNaturalSemantics
namespace Reflection

open PrimeNeedReference PolarizedNeedMachine

variable {Head Operation Effect StableFault NativeFault : Type} {m : Nat}

def EvalMeaning
    (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)
    (closure : Closure Head Operation Effect m) (kont : Kont Head Operation Effect m)
    (world : NeedWorld Head Operation Effect StableFault NativeFault m)
    (outcome : Outcome Head Operation Effect StableFault NativeFault m)
    (final : NeedWorld Head Operation Effect StableFault NativeFault m) : Prop :=
  ∃ raw selected, Nonempty (Eval primitive closure world raw selected) ∧
    Nonempty (KontEval primitive kont raw selected outcome final)

def ResumeMeaning
    (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)
    (resume : Resume Head Operation Effect m)
    (input : Outcome Head Operation Effect StableFault NativeFault m)
    (world : NeedWorld Head Operation Effect StableFault NativeFault m)
    (outcome : Outcome Head Operation Effect StableFault NativeFault m)
    (final : NeedWorld Head Operation Effect StableFault NativeFault m) : Prop :=
  match resume, input with
  | .finish kont, input => Nonempty (KontEval primitive kont input world outcome final)
  | .bindNative body kont, .value (.returned (.native value)) =>
      EvalMeaning primitive (body.open value) kont world outcome final
  | .bindSigma body kont, .value (.returned (.native value)) =>
      EvalMeaning primitive (body.open value) (.pair value kont) world outcome final
  | .bindValue body kont, .value (.returned value) =>
      EvalMeaning primitive (body.open value) kont world outcome final
  | .bindNative _ _, .value _ | .bindSigma _ _, .value _ =>
      outcome = .retryableFault (.domain .expectedNativeValue) ∧ world = final
  | .bindValue _ _, .value _ =>
      outcome = .retryableFault (.domain .expectedReturnedValue) ∧ world = final
  | .bindNative _ _, .stableFault fault | .bindValue _ _, .stableFault fault
      | .bindSigma _ _, .stableFault fault => outcome = .stableFault fault ∧ world = final
  | .bindNative _ _, .retryableFault reason | .bindValue _ _, .retryableFault reason
      | .bindSigma _ _, .retryableFault reason => outcome = .retryableFault reason ∧ world = final
  | .bindNeed _ _, _ =>
      outcome = .retryableFault (.domain .allocationResumeDemanded) ∧ world = final

def LocalMeaning
    (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)
    (state : Local Head Operation Effect StableFault NativeFault m)
    (world : NeedWorld Head Operation Effect StableFault NativeFault m)
    (outcome : Outcome Head Operation Effect StableFault NativeFault m)
    (final : NeedWorld Head Operation Effect StableFault NativeFault m) : Prop :=
  match state with
  | .evaluate closure kont => EvalMeaning primitive closure kont world outcome final
  | .demand cell resume =>
      ∃ input selected, Nonempty (Force primitive cell world input selected) ∧
        ResumeMeaning primitive resume input selected outcome final
  | .complete result => result = outcome ∧ world = final

def StackMeaning
    (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault) :
    List (Frame (Resume Head Operation Effect m)) →
      Outcome Head Operation Effect StableFault NativeFault m →
      NeedWorld Head Operation Effect StableFault NativeFault m →
      Outcome Head Operation Effect StableFault NativeFault m →
      NeedWorld Head Operation Effect StableFault NativeFault m → Prop
  | [], input, world, outcome, final => input = outcome ∧ world = final
  | .commit cell owner :: rest, input, world, outcome, final =>
      StackMeaning primitive rest (finalize world cell owner input).1
        (finalize world cell owner input).2 outcome final
  | .resume token :: rest, input, world, outcome, final =>
      ∃ result selected, ResumeMeaning primitive token input world result selected ∧
        StackMeaning primitive rest result selected outcome final

def ControlMeaning
    (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)
    (control : NeedControl Head Operation Effect StableFault NativeFault m)
    (world : NeedWorld Head Operation Effect StableFault NativeFault m)
    (outcome : Outcome Head Operation Effect StableFault NativeFault m)
    (final : NeedWorld Head Operation Effect StableFault NativeFault m) : Prop :=
  match control with
  | .run state stack =>
      ∃ result selected, LocalMeaning primitive state world result selected ∧
        StackMeaning primitive stack result selected outcome final
  | .force cell stack =>
      ∃ result selected, Nonempty (Force primitive cell world result selected) ∧
        StackMeaning primitive stack result selected outcome final
  | .returned result stack => StackMeaning primitive stack result world outcome final
  | .halted result => result = outcome ∧ world = final

theorem eval_done_meaning
    {primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault}
    {closure : Closure Head Operation Effect m}
    {world final : NeedWorld Head Operation Effect StableFault NativeFault m}
    {outcome : Outcome Head Operation Effect StableFault NativeFault m} :
    EvalMeaning primitive closure .done world outcome final ↔
      Nonempty (Eval primitive closure world outcome final) := by
  constructor
  · rintro ⟨raw, selected, evaluated, ⟨consumed⟩⟩
    obtain ⟨rfl, rfl⟩ := consumed.done_exact
    exact evaluated
  · intro evaluated
    exact ⟨outcome, final, evaluated, ⟨.done outcome final⟩⟩

theorem deliver_meaning
    (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)
    (input : Outcome Head Operation Effect StableFault NativeFault m)
    (kont : Kont Head Operation Effect m)
    (world : NeedWorld Head Operation Effect StableFault NativeFault m)
    (outcome : Outcome Head Operation Effect StableFault NativeFault m)
    (final : NeedWorld Head Operation Effect StableFault NativeFault m) :
    LocalMeaning primitive (deliver input kont) world outcome final ↔
      Nonempty (KontEval primitive kont input world outcome final) := by
  induction kont generalizing input with
  | done => simp only [deliver, LocalMeaning, KontEval.done_iff, eq_comm]
  | pair first rest ih =>
      rw [KontEval.pair_iff]
      cases input with
      | value answer =>
          cases answer with
          | returned value =>
              cases value with
              | native second => exact ih (.value (.returned (.native (.pair first second))))
              | thunk _ _ _ _ =>
                  simp only [deliver, pairOutcome, LocalMeaning, KontEval.retry_iff, eq_comm]
              | packNative _ _ =>
                  simp only [deliver, pairOutcome, LocalMeaning, KontEval.retry_iff, eq_comm]
          | nativeFunction body =>
              simp only [deliver, pairOutcome, LocalMeaning, KontEval.retry_iff, eq_comm]
          | valueFunction body =>
              simp only [deliver, pairOutcome, LocalMeaning, KontEval.retry_iff, eq_comm]
      | stableFault fault =>
          simp only [deliver, pairOutcome, LocalMeaning, KontEval.stable_iff, eq_comm]
      | retryableFault reason =>
          simp only [deliver, pairOutcome, LocalMeaning, KontEval.retry_iff, eq_comm]
  | nativeApply argument rest =>
      cases input with
      | value answer =>
          cases answer with
          | returned value =>
              constructor
              · rintro ⟨rfl, rfl⟩
                exact ⟨.nativeMismatch argument rest (.returned value) world (by
                  intro body impossible
                  cases impossible)⟩
              · rintro ⟨evaluation⟩
                cases evaluation
                exact ⟨rfl, rfl⟩
          | nativeFunction body =>
              constructor
              · rintro ⟨raw, selected, ⟨evaluated⟩, ⟨consumed⟩⟩
                exact ⟨.nativeApply argument body evaluated consumed⟩
              · rintro ⟨evaluation⟩
                cases evaluation with
                | nativeApply _ _ evaluated consumed => exact ⟨_, _, ⟨evaluated⟩, ⟨consumed⟩⟩
                | nativeMismatch _ _ _ _ wrong => exact False.elim (wrong body rfl)
          | valueFunction body =>
              constructor
              · rintro ⟨rfl, rfl⟩
                exact ⟨.nativeMismatch argument rest (.valueFunction body) world (by
                  intro nativeBody impossible
                  cases impossible)⟩
              · rintro ⟨evaluation⟩
                cases evaluation
                exact ⟨rfl, rfl⟩
      | stableFault fault => simp only [deliver, LocalMeaning, KontEval.stable_iff, eq_comm]
      | retryableFault reason => simp only [deliver, LocalMeaning, KontEval.retry_iff, eq_comm]
  | valueApply argument rest =>
      cases input with
      | value answer =>
          cases answer with
          | returned value =>
              constructor
              · rintro ⟨rfl, rfl⟩
                exact ⟨.valueMismatch argument rest (.returned value) world (by
                  intro body impossible
                  cases impossible)⟩
              · rintro ⟨evaluation⟩
                cases evaluation
                exact ⟨rfl, rfl⟩
          | nativeFunction body =>
              constructor
              · rintro ⟨rfl, rfl⟩
                exact ⟨.valueMismatch argument rest (.nativeFunction body) world (by
                  intro valueBody impossible
                  cases impossible)⟩
              · rintro ⟨evaluation⟩
                cases evaluation
                exact ⟨rfl, rfl⟩
          | valueFunction body =>
              constructor
              · rintro ⟨raw, selected, ⟨evaluated⟩, ⟨consumed⟩⟩
                exact ⟨.valueApply argument body evaluated consumed⟩
              · rintro ⟨evaluation⟩
                cases evaluation with
                | valueApply _ _ evaluated consumed => exact ⟨_, _, ⟨evaluated⟩, ⟨consumed⟩⟩
                | valueMismatch _ _ _ _ wrong => exact False.elim (wrong body rfl)
      | stableFault fault => simp only [deliver, LocalMeaning, KontEval.stable_iff, eq_comm]
      | retryableFault reason => simp only [deliver, LocalMeaning, KontEval.retry_iff, eq_comm]

theorem afterDemand_meaning
    (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)
    (resume : Resume Head Operation Effect m)
    (input : Outcome Head Operation Effect StableFault NativeFault m)
    (world : NeedWorld Head Operation Effect StableFault NativeFault m)
    (outcome : Outcome Head Operation Effect StableFault NativeFault m)
    (final : NeedWorld Head Operation Effect StableFault NativeFault m) :
    LocalMeaning primitive (afterDemand resume input) world outcome final ↔
      ResumeMeaning primitive resume input world outcome final := by
  cases resume with
  | finish kont => exact deliver_meaning primitive input kont world outcome final
  | bindNative body kont =>
      cases input with
      | value answer =>
          cases answer with
          | returned value => cases value <;> simp only [afterDemand, LocalMeaning, ResumeMeaning, eq_comm]
          | nativeFunction body => simp only [afterDemand, LocalMeaning, ResumeMeaning, eq_comm]
          | valueFunction body => simp only [afterDemand, LocalMeaning, ResumeMeaning, eq_comm]
      | stableFault fault => simp only [afterDemand, LocalMeaning, ResumeMeaning, eq_comm]
      | retryableFault reason => simp only [afterDemand, LocalMeaning, ResumeMeaning, eq_comm]
  | bindSigma body kont =>
      cases input with
      | value answer =>
          cases answer with
          | returned value => cases value <;> simp only [afterDemand, LocalMeaning, ResumeMeaning, eq_comm]
          | nativeFunction body => simp only [afterDemand, LocalMeaning, ResumeMeaning, eq_comm]
          | valueFunction body => simp only [afterDemand, LocalMeaning, ResumeMeaning, eq_comm]
      | stableFault fault => simp only [afterDemand, LocalMeaning, ResumeMeaning, eq_comm]
      | retryableFault reason => simp only [afterDemand, LocalMeaning, ResumeMeaning, eq_comm]
  | bindValue body kont =>
      cases input with
      | value answer => cases answer <;> simp only [afterDemand, LocalMeaning, ResumeMeaning, eq_comm]
      | stableFault fault => simp only [afterDemand, LocalMeaning, ResumeMeaning, eq_comm]
      | retryableFault reason => simp only [afterDemand, LocalMeaning, ResumeMeaning, eq_comm]
  | bindNeed body kont =>
      cases input <;> simp only [afterDemand, LocalMeaning, ResumeMeaning, eq_comm]

#print axioms eval_done_meaning
#print axioms deliver_meaning
#print axioms afterDemand_meaning

end Reflection
end PolarizedNeedNaturalSemantics
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
