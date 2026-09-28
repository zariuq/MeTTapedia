import Mettapedia.GSLT.LanguageDef.DefunctionalizedEquationBodies

/-!
# Execution that moves between a compiled and an interpreted tier

`DefunctionalizedEquationBodies` compiles slot-addressed equation bodies to a
first-order machine whose return frames are resume sites with captured slots.
A general interpreter runs the same programs with host continuations (the
source lowering of `CompiledContinuationAnswerProducer`).  A runtime mixes
them: some activations run compiled, others interpreted; a compiled task may
be deoptimized into the interpreter at any point, including after answers
have been published and with return frames pending; a task may re-enter the
compiled tier when its interpreted control is known to be the lowering of
compiled code.

Here one machine carries both representations, task by task and frame by
frame:

* controls and frames are sums of the compiled and interpreted forms;
* a *policy* chooses, per activation, which tier runs it;
* `deopt` moves a task, with its pending frames, to the interpreter;
  `reenter` moves an interpreted task back to compiled code when its body is
  the lowering of that code;
* decoding sends every state to the source lowering.

`balance_mixedStep` shows every step conserves the delivered answers followed
by the source denotation of the whole residual frontier, for every policy.
Transfers do not change the decoded state (`decode_deopt`, `decode_reenter`),
so `mixed_prefix` holds for every interleaving of steps and transfers: the
delivered answers are always a prefix of the source denotation, and
`mixed_completed` gives the whole denotation once the frontier is exhausted.
No schedule of switches can drop, replay or invent an answer.

This is the model-level contract the native prepared/search transfer realizes.
Transfer by ownership corresponds to moving a first-order frame unchanged
between tiers (`inl` frames keep their identity under `deopt` only after
decoding; a native runtime may keep them first-order and resume them in the
compiled tier later, which `reenter` licenses at task granularity).  It is not
a verified translation of CeTTa's C.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.MixedTierExecution

open CompiledContinuationAnswerProducer
open Mettapedia.Machines.SharedContinuation
open DefunctionalizedEquationBodies

variable {Term Store Rel Op : Type}
variable (L : TemplateLanguage Term) (S : StoreAlgebra Term Store Op)
variable [Inhabited Term] [DecidableEq Rel]

abbrev HBody (Term Store Rel : Type) := Body (Call Term Store Rel) (Answer Term Store)
abbrev HFrame (Term Store Rel : Type) := Answer Term Store → HBody Term Store Rel

/-- A task's control runs compiled (`inl`) or interpreted (`inr`). -/
abbrev MControl (L : TemplateLanguage Term) (Rel Op Store : Type) :=
  Control L Rel Op Store ⊕ HBody Term Store Rel

/-- A pending return is a first-order resume frame or a host continuation. -/
abbrev MFrame (L : TemplateLanguage Term) (Rel Op Store : Type) :=
  ReturnFrame L Rel Op ⊕ HFrame Term Store Rel

/-- The interpreter's view of a body: the source machine's own inspection. -/
def hostInstruction : HBody Term Store Rel →
    Instruction (Call Term Store Rel) (MFrame L Rel Op Store) (Answer Term Store)
  | .answer a => .ret a
  | .fail => .fail
  | .call c k => .call c (.inr k)
  | .tail c => .tail c

def liftInstruction :
    Instruction (Call Term Store Rel) (ReturnFrame L Rel Op) (Answer Term Store) →
      Instruction (Call Term Store Rel) (MFrame L Rel Op Store) (Answer Term Store)
  | .ret a => .ret a
  | .fail => .fail
  | .call c f => .call c (.inl f)
  | .tail c => .tail c

/-- Start an activation in the tier the policy selects. -/
def placeActivation (policy : Activation L Rel Op Store → Bool)
    (a : Activation L Rel Op Store) : MControl L Rel Op Store :=
  if policy a then .inl ⟨a.slots, a.code, a.frame, a.store⟩
  else .inr (decodeControl L S ⟨a.slots, a.code, a.frame, a.store⟩)

/-- The mixed machine.  A compiled frame resumes compiled code; a host frame
resumes host code. -/
def mixed (P : EqProgram L Rel Op) (policy : Activation L Rel Op Store → Bool) :
    Program Unit (MControl L Rel Op Store) (Call Term Store Rel)
      (MFrame L Rel Op Store) (Answer Term Store) where
  inspect
    | .inl c => liftInstruction L (inspectCode L S c.frame c.store c.code)
    | .inr b => hostInstruction L b
  branches _ c := (activate L S P c).map fun a => ((), placeActivation L S policy a)
  resume _ f a :=
    match f with
    | .inl f => ((), .inl (resumeControl L S f a))
    | .inr k => ((), .inr (k a))

/-! ### Decoding to the source lowering -/

def decodeM : MControl L Rel Op Store → HBody Term Store Rel
  | .inl c => decodeControl L S c
  | .inr b => b

def decodeMFrame : MFrame L Rel Op Store → HFrame Term Store Rel
  | .inl f => decodeFrame L S f
  | .inr k => k

def decodeMTask (t : Task Unit (MControl L Rel Op Store) (MFrame L Rel Op Store)) :
    Task Unit (HBody Term Store Rel) (HFrame Term Store Rel) :=
  ⟨(), decodeM L S t.control, t.returns.map (decodeMFrame L S)⟩

def decodeMState
    (s : State Unit (MControl L Rel Op Store) (MFrame L Rel Op Store) (Answer Term Store)) :
    ContinuationArenaBridge.Reference (Call Term Store Rel) (Answer Term Store) :=
  ⟨s.frontier.map (decodeMTask L S), s.emitted⟩

open ContinuationArenaBridge in
omit [DecidableEq Rel] in
/-- Running a compiled control and then decoding agrees with decoding and then
inspecting: the compiled part of a mixed task conserves the balance exactly as
the compiled machine does. -/
theorem decode_inl_instruction {k : Nat} (code : Code L Rel Op k) (frame : Fin k → Term) (σ : Store) :
    decodeM L S (.inl ⟨k, code, frame, σ⟩) =
      match liftInstruction L (inspectCode L S frame σ code) with
      | .ret a => .answer a
      | .fail => .fail
      | .call c f => .call c (decodeMFrame L S f)
      | .tail c => .call c .answer := by
  simp only [decodeM]
  rw [decode_inspect]
  cases inspectCode L S frame σ code <;> rfl

open ContinuationArenaBridge in
/-- Every step of the mixed machine conserves the delivered answers followed by
the source denotation of the residual frontier, whatever tier each task and
frame is in and whatever the placement policy. -/
theorem balance_mixedStep (P : EqProgram L Rel Op) (policy : Activation L Rel Op Store → Bool)
    (denotation : Denotation (sourceMachine L S P))
    (s : State Unit (MControl L Rel Op Store) (MFrame L Rel Op Store) (Answer Term Store)) :
    balance denotation.value (decodeMState L S (step (mixed L S P policy) s)) =
      balance denotation.value (decodeMState L S s) := by
  have placed : ∀ c : Call Term Store Rel,
      (activate L S P c).map (fun a => decodeM L S (placeActivation L S policy a)) =
        (sourceMachine L S P).branches c := by
    intro c
    simp only [sourceMachine]
    apply List.map_congr_left
    intro a _
    unfold placeActivation
    split <;> rfl
  rcases s with ⟨frontier, emitted⟩
  cases frontier with
  | nil => rfl
  | cons task rest =>
      rcases task with ⟨context, control, returns⟩
      cases control with
      | inl control =>
          rcases control with ⟨k, code, frame, σ⟩
          have hdec := decode_inspect L S code frame σ
          cases instr : inspectCode L S frame σ code with
          | ret a =>
              have hb : decodeControl L S ⟨k, code, frame, σ⟩ = .answer a := by
                rw [hdec, instr]; rfl
              cases returns with
              | nil =>
                  simp [step, mixed, instr, liftInstruction, decodeMState, decodeMTask, balance,
                    residuals, frontierValue, decodeM, hb, Body.answers, pendingAnswers,
                    List.append_assoc]
              | cons f pending =>
                  cases f with
                  | inl f =>
                      simp [step, mixed, instr, liftInstruction, decodeMState, decodeMTask, balance,
                        residuals, frontierValue, decodeM, hb, Body.answers, pendingAnswers,
                        decodeMFrame, decodeFrame]
                  | inr k' =>
                      simp [step, mixed, instr, liftInstruction, decodeMState, decodeMTask, balance,
                        residuals, frontierValue, decodeM, hb, Body.answers, pendingAnswers,
                        decodeMFrame]
          | fail =>
              have hb : decodeControl L S ⟨k, code, frame, σ⟩ = .fail := by
                rw [hdec, instr]; rfl
              simp [step, mixed, instr, liftInstruction, decodeMState, decodeMTask, balance,
                residuals, frontierValue, decodeM, hb, Body.answers]
          | call c f =>
              have hb : decodeControl L S ⟨k, code, frame, σ⟩ = .call c (decodeFrame L S f) := by
                rw [hdec, instr]; rfl
              simp only [step, mixed, instr, liftInstruction, decodeMState, decodeMTask, balance,
                residuals, List.map_cons, List.map_append, List.map_map, Function.comp_def,
                decodeM, hb]
              rw [frontierValue_append, frontierValue_map_run]
              simp only [frontierValue, Body.answers, denotation.unfold c, List.flatMap_assoc]
              rw [← placed c, List.flatMap_map]
              simp [pendingAnswers, decodeMFrame, decodeM]
          | tail c =>
              have hb : decodeControl L S ⟨k, code, frame, σ⟩ = .call c .answer := by
                rw [hdec, instr]; rfl
              simp only [step, mixed, instr, liftInstruction, decodeMState, decodeMTask, balance,
                residuals, List.map_cons, List.map_append, List.map_map, Function.comp_def,
                decodeM, hb]
              rw [frontierValue_append, frontierValue_map_run]
              simp only [frontierValue, Body.answers, denotation.unfold c, List.flatMap_assoc]
              rw [← placed c, List.flatMap_map]
              simp [decodeM]
      | inr b =>
          cases b with
          | answer a =>
              cases returns with
              | nil =>
                  simp [step, mixed, hostInstruction, decodeMState, decodeMTask, balance, residuals,
                    frontierValue, decodeM, Body.answers, pendingAnswers, List.append_assoc]
              | cons f pending =>
                  cases f with
                  | inl f =>
                      simp [step, mixed, hostInstruction, decodeMState, decodeMTask, balance,
                        residuals, frontierValue, decodeM, Body.answers, pendingAnswers,
                        decodeMFrame, decodeFrame]
                  | inr k' =>
                      simp [step, mixed, hostInstruction, decodeMState, decodeMTask, balance,
                        residuals, frontierValue, decodeM, Body.answers, pendingAnswers, decodeMFrame]
          | fail =>
              simp [step, mixed, hostInstruction, decodeMState, decodeMTask, balance, residuals,
                frontierValue, decodeM, Body.answers]
          | call c k' =>
              simp only [step, mixed, hostInstruction, decodeMState, decodeMTask, balance,
                residuals, List.map_cons, List.map_append, List.map_map, Function.comp_def]
              rw [frontierValue_append, frontierValue_map_run]
              simp only [frontierValue, decodeM, Body.answers, denotation.unfold c,
                List.flatMap_assoc]
              rw [← placed c, List.flatMap_map]
              simp [pendingAnswers, decodeMFrame]
              rfl
          | tail c =>
              simp only [step, mixed, hostInstruction, decodeMState, decodeMTask, balance,
                residuals, List.map_cons, List.map_append, List.map_map, Function.comp_def]
              rw [frontierValue_append, frontierValue_map_run]
              simp only [frontierValue, decodeM, Body.answers, denotation.unfold c,
                List.flatMap_assoc]
              rw [← placed c, List.flatMap_map]
              rfl

/-! ### Transfers between tiers -/

abbrev MState (L : TemplateLanguage Term) (Rel Op Store : Type) :=
  State Unit (MControl L Rel Op Store) (MFrame L Rel Op Store) (Answer Term Store)

abbrev MTask (L : TemplateLanguage Term) (Rel Op Store : Type) :=
  Task Unit (MControl L Rel Op Store) (MFrame L Rel Op Store)

/-- Deoptimize a task: its control and every pending frame move to the
interpreter, as the continuations the lowering would have built. -/
def deoptTask (t : MTask L Rel Op Store) : MTask L Rel Op Store :=
  ⟨(), .inr (decodeM L S t.control), t.returns.map fun f => .inr (decodeMFrame L S f)⟩

omit [DecidableEq Rel] in
theorem decode_deopt (t : MTask L Rel Op Store) :
    decodeMTask L S (deoptTask L S t) = decodeMTask L S t := by
  simp [deoptTask, decodeMTask, decodeM, decodeMFrame, List.map_map, Function.comp_def]

/-- Re-enter the compiled tier: an interpreted control is replaced by compiled
code whose lowering it is.  The pending frames keep their tiers. -/
def reenterTask (t : MTask L Rel Op Store) (c : Control L Rel Op Store) : MTask L Rel Op Store :=
  ⟨(), .inl c, t.returns⟩

omit [DecidableEq Rel] in
theorem decode_reenter (t : MTask L Rel Op Store) (c : Control L Rel Op Store)
    (lowering : decodeM L S t.control = decodeControl L S c) :
    decodeMTask L S (reenterTask L t c) = decodeMTask L S t := by
  simp only [reenterTask, decodeMTask, decodeM] at lowering ⊢
  rw [lowering]

/-- Rewrite the task at one frontier position. -/
def transferAt (i : Nat) (f : MTask L Rel Op Store → MTask L Rel Op Store)
    (s : MState L Rel Op Store) : MState L Rel Op Store :=
  ⟨s.frontier.mapIdx fun j t => if j = i then f t else t, s.emitted⟩

/-- A transfer changes representation only: the decoded state is unchanged. -/
def DecodePreserving (T : MState L Rel Op Store → MState L Rel Op Store) : Prop :=
  ∀ s, decodeMState L S (T s) = decodeMState L S s

omit [DecidableEq Rel] in
theorem transferAt_preserving (i : Nat) (f : MTask L Rel Op Store → MTask L Rel Op Store)
    (hf : ∀ t, decodeMTask L S (f t) = decodeMTask L S t) :
    DecodePreserving L S (transferAt L i f) := by
  intro s
  simp only [transferAt, decodeMState, State.mk.injEq, and_true]
  apply List.ext_getElem (by simp)
  intro j h₁ h₂
  simp only [List.getElem_map, List.getElem_mapIdx]
  split <;> simp [hf]

omit [DecidableEq Rel] in
/-- Deoptimizing any task preserves the decoded state. -/
theorem deoptAt_preserving (i : Nat) :
    DecodePreserving L S (transferAt L i (deoptTask (Rel := Rel) L S)) :=
  transferAt_preserving L S i _ (decode_deopt L S)

/-- A schedule operation: a mixed step, or a representation-only transfer. -/
def Admissible (P : EqProgram L Rel Op) (policy : Activation L Rel Op Store → Bool)
    (T : MState L Rel Op Store → MState L Rel Op Store) : Prop :=
  T = step (mixed L S P policy) ∨ DecodePreserving L S T

def runOps (ops : List (MState L Rel Op Store → MState L Rel Op Store))
    (s : MState L Rel Op Store) : MState L Rel Op Store :=
  ops.foldl (fun state T => T state) s

open ContinuationArenaBridge in
theorem balance_runOps (P : EqProgram L Rel Op) (policy : Activation L Rel Op Store → Bool)
    (denotation : Denotation (sourceMachine L S P))
    (ops : List (MState L Rel Op Store → MState L Rel Op Store))
    (admissible : ∀ T ∈ ops, Admissible L S P policy T) (s : MState L Rel Op Store) :
    balance denotation.value (decodeMState L S (runOps L ops s)) =
      balance denotation.value (decodeMState L S s) := by
  induction ops generalizing s with
  | nil => rfl
  | cons T rest ih =>
      simp only [runOps, List.foldl_cons] at ih ⊢
      rw [ih (fun T' mem => admissible T' (by simp [mem]))]
      rcases admissible T (by simp) with rfl | preserving
      · exact balance_mixedStep L S P policy denotation s
      · rw [preserving s]

/-- The initial state of a query under a placement policy. -/
def initialM (P : EqProgram L Rel Op) (policy : Activation L Rel Op Store → Bool)
    (c : Call Term Store Rel) : MState L Rel Op Store :=
  ⟨(activate L S P c).map fun a => ⟨(), placeActivation L S policy a, []⟩, []⟩

open ContinuationArenaBridge in
theorem balance_initialM (P : EqProgram L Rel Op) (policy : Activation L Rel Op Store → Bool)
    (denotation : Denotation (sourceMachine L S P)) (c : Call Term Store Rel) :
    balance denotation.value (decodeMState L S (initialM L S P policy c)) = denotation.value c := by
  have placed : (activate L S P c).map (fun a => decodeM L S (placeActivation L S policy a)) =
      (sourceMachine L S P).branches c := by
    simp only [sourceMachine]
    apply List.map_congr_left
    intro a _
    unfold placeActivation
    split <;> rfl
  simp only [initialM, decodeMState, decodeMTask, balance, residuals, List.map_map,
    Function.comp_def, List.map_nil, List.nil_append]
  rw [frontierValue_map_run, denotation.unfold c, ← placed, List.flatMap_map]
  simp [pendingAnswers]

/-- Under every placement policy and every schedule of steps and
representation-only transfers (deoptimization, re-entry), the delivered
answers are at every point a prefix of the source denotation, in order and with
multiplicity. -/
theorem mixed_prefix (P : EqProgram L Rel Op) (policy : Activation L Rel Op Store → Bool)
    (denotation : Denotation (sourceMachine L S P)) (c : Call Term Store Rel)
    (ops : List (MState L Rel Op Store → MState L Rel Op Store))
    (admissible : ∀ T ∈ ops, Admissible L S P policy T) :
    (runOps L ops (initialM L S P policy c)).emitted.map Prod.snd <+: denotation.value c := by
  have conserved := balance_runOps L S P policy denotation ops admissible (initialM L S P policy c)
  rw [balance_initialM] at conserved
  simp only [ContinuationArenaBridge.balance, decodeMState] at conserved
  exact ⟨_, conserved⟩

/-- Once such a schedule exhausts the frontier, exactly the source denotation
has been delivered. -/
theorem mixed_completed (P : EqProgram L Rel Op) (policy : Activation L Rel Op Store → Bool)
    (denotation : Denotation (sourceMachine L S P)) (c : Call Term Store Rel)
    (ops : List (MState L Rel Op Store → MState L Rel Op Store))
    (admissible : ∀ T ∈ ops, Admissible L S P policy T)
    (exhausted : (runOps L ops (initialM L S P policy c)).frontier = []) :
    (runOps L ops (initialM L S P policy c)).emitted.map Prod.snd = denotation.value c := by
  have conserved := balance_runOps L S P policy denotation ops admissible (initialM L S P policy c)
  rw [balance_initialM] at conserved
  simpa [ContinuationArenaBridge.balance, decodeMState, exhausted, ContinuationArenaBridge.residuals,
    frontierValue] using conserved

end Mettapedia.GSLT.LanguageDef.MixedTierExecution
