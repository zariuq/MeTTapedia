import Mettapedia.GSLT.LanguageDef.DefunctionalizedEquationBodies
import Mettapedia.GSLT.LanguageDef.DestinationPassingControls
import Mettapedia.GSLT.LanguageDef.HostCallMachine

/-!
# Outlining a control body into a local relation

A compiler may put a value-position body in a local code table and replace
its execution with a call. Its parameters must retain the identities of the
logical references the body reads. They are not copies of the references'
current values. The existing slot-addressed body calculus already represents
references and stores separately, including unbound references.

This module adds an executable local-call instruction to the existing shared
continuation machine. A local table entry contains code, never a captured
runtime environment. Each call carries just the referenced support slots;
entering the call reconstructs its activation. The code runs on the ordinary
equation machine and returns through its ordinary return frames.

`outline_steps` compares actual finite machine runs. The extra local-call
step is silent; after the first body step the two complete machine states
agree, including the returned stores, pending alternatives and continuations.
Thus `outline_observations` gives preservation and reflection, not only a
forward simulation. `outlined_let_answers` connects this operation to a nested
source `let`, using the existing normalization theorem.

Scope: slots have already been allocated by the enclosing source activation.
Outlining introduces a fresh *code address*, not another logical activation.
It neither freshens nor resolves captured references. It does not prove a
frontend's free-variable analysis or the equivalence of a different scheme
which allocates fresh logical parameters and then unifies them with captures.
The underlying `Code` calculus is cut-free. A source construct with local
commitment also needs a scope-preserving entry law for its cut-aware machine.
Values and stores are parametric, so closure-valued terms are permitted; no
claim about the complete semantics of a particular higher-order language is
made. This is a model of a compiler operation, not a verified C translation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeControlLifting

open DefunctionalizedEquationBodies
open Mettapedia.Machines.SharedContinuation
open Mettapedia.GSLT.Dynamics.ContextIndexedSwitching (repeats)
open CompiledContinuationAnswerProducer

section Generic

variable {Term Store Rel Op : Type} {L : TemplateLanguage Term}

section Support

variable (L) (S : StoreAlgebra Term Store Op)

theorem capture_congr {k : Nat} (frame frame' : Fin k → Term) (keep : Finset (Fin k))
    (agree : ∀ i ∈ keep, frame i = frame' i) :
    capture frame keep = capture frame' keep := by
  funext i
  by_cases kept : i ∈ keep
  · simp [capture, kept, agree i kept]
  · simp [capture, kept]

/-- Agreement on the body's support preserves its next operational boundary,
including the reference identities in a captured return frame. -/
theorem inspectCode_congr {k : Nat} (code : Code L Rel Op k)
    (frame frame' : Fin k → Term)
    (agree : ∀ i ∈ code.support L, frame i = frame' i) (σ : Store) :
    inspectCode L S frame σ code = inspectCode L S frame' σ code := by
  induction code generalizing σ with
  | ret t => simp [inspectCode, L.inst_congr t frame frame' agree]
  | fail => rfl
  | letCall p rel args body =>
      have ha := instArgs_congr L args frame frame' (fun i hi =>
        agree i (by simp [Code.support, hi]))
      have hc := capture_congr frame frame' (frameSupport L p body) (fun i hi =>
        agree i (by
          simp only [frameSupport, Finset.mem_union] at hi
          rcases hi with hi | hi <;> simp [Code.support, hi]))
      simp only [inspectCode, ha, hc]
  | letPrim p op args body ih =>
      have hp := L.inst_congr p frame frame' (fun i hi =>
        agree i (by simp [Code.support, hi]))
      have ha := instArgs_congr L args frame frame' (fun i hi =>
        agree i (by simp [Code.support, hi]))
      have hb := ih (fun i hi => agree i (by simp [Code.support, hi]))
      simp only [inspectCode, hp, ha]
      split
      · rfl
      · split
        · exact hb _
        · rfl
  | bind p v body ih =>
      have hp := L.inst_congr p frame frame' (fun i hi =>
        agree i (by simp [Code.support, hi]))
      have hv := L.inst_congr v frame frame' (fun i hi =>
        agree i (by simp [Code.support, hi]))
      have hb := ih (fun i hi => agree i (by simp [Code.support, hi]))
      simp only [inspectCode, hp, hv]
      split
      · exact hb _
      · rfl
  | ite op args yes no ihYes ihNo =>
      have ha := instArgs_congr L args frame frame' (fun i hi =>
        agree i (by simp [Code.support, hi]))
      have hy := ihYes (fun i hi => agree i (by simp [Code.support, hi]))
      have hn := ihNo (fun i hi => agree i (by simp [Code.support, hi]))
      simp only [inspectCode, ha]
      split
      · exact hy _
      · exact hn _
      · rfl
  | tail rel args =>
      have ha := instArgs_congr L args frame frame' agree
      simp only [inspectCode, ha]

variable [Inhabited Term]

/-- Discarding unread slots changes storage but not the executed instruction. -/
theorem inspect_captured {k : Nat} (code : Code L Rel Op k)
    (frame : Fin k → Term) (σ : Store) :
    inspectCode L S (reconstruct (capture frame (code.support L))) σ code =
      inspectCode L S frame σ code :=
  inspectCode_congr L S code _ frame
    (fun i hi => reconstruct_capture frame _ i hi) σ

end Support

/-! ## A table of local relations with separately supplied captures -/

structure LocalEntry (L : TemplateLanguage Term) (Rel Op : Type) where
  slots : Nat
  code : Code L Rel Op slots

abbrev LocalTable (L : TemplateLanguage Term) (Rel Op : Type) (n : Nat) :=
  Fin n → LocalEntry L Rel Op

/-- A new local address is zero; existing addresses shift by one. The sum of
external and local call types keeps local names separate from user relations. -/
def insert {n : Nat} (table : LocalTable L Rel Op n) (entry : LocalEntry L Rel Op) :
    LocalTable L Rel Op (n + 1) := Fin.cases entry table

@[simp] theorem insert_new {n : Nat} (table : LocalTable L Rel Op n)
    (entry : LocalEntry L Rel Op) : insert table entry 0 = entry := rfl

@[simp] theorem insert_old {n : Nat} (table : LocalTable L Rel Op n)
    (entry : LocalEntry L Rel Op) (i : Fin n) :
    insert table entry i.succ = table i := rfl

theorem inserted_address_fresh {n : Nat} (i : Fin n) : (0 : Fin (n + 1)) ≠ i.succ := by
  intro equal
  have := congrArg Fin.val equal
  simp only [Fin.val_zero, Fin.val_succ] at this
  omega

structure LocalCall {n : Nat} (table : LocalTable L Rel Op n) (Store : Type) where
  address : Fin n
  captured : Fin (table address).slots → Option Term
  store : Store

def outline {n k : Nat} (table : LocalTable L Rel Op n)
    (code : Code L Rel Op k) (frame : Fin k → Term) (σ : Store) :
    LocalCall (insert table ⟨k, code⟩) Store :=
  ⟨0, capture frame (code.support L), σ⟩

variable [Inhabited Term]

def enter {n : Nat} {table : LocalTable L Rel Op n} (call : LocalCall table Store) :
    Control L Rel Op Store :=
  ⟨(table call.address).slots, (table call.address).code,
    reconstruct call.captured, call.store⟩

/-- The new local invocation has exactly the caller's store. No fresh supply,
copying operation, or resolution is run at this administrative boundary. -/
@[simp] theorem enter_outline_store {n k : Nat} (table : LocalTable L Rel Op n)
    (code : Code L Rel Op k) (frame : Fin k → Term) (σ : Store) :
    (enter (outline table code frame σ)).store = σ := rfl

omit [Inhabited Term] in
theorem outline_capture_identity {n k : Nat} (table : LocalTable L Rel Op n)
    (code : Code L Rel Op k) (frame : Fin k → Term) (σ : Store)
    (i : Fin k) (used : i ∈ code.support L) :
    (outline table code frame σ).captured i = some (frame i) := by
  simp [outline, capture, used]

omit [Inhabited Term] in
theorem outline_drops_unused {n k : Nat} (table : LocalTable L Rel Op n)
    (code : Code L Rel Op k) (frame : Fin k → Term) (σ : Store)
    (i : Fin k) (unused : i ∉ code.support L) :
    (outline table code frame σ).captured i = none := by
  simp [outline, capture, unused]

/-! ## The executable extension -/

abbrev ExtControl {n : Nat} (table : LocalTable L Rel Op n) (Store : Type) :=
  Sum (Control L Rel Op Store) (LocalCall table Store)

abbrev ExtCall {n : Nat} (table : LocalTable L Rel Op n) (Store : Type) :=
  Sum (Call Term Store Rel) (LocalCall table Store)

def embedInstruction {n : Nat} (table : LocalTable L Rel Op n) :
    Instruction (Call Term Store Rel) (ReturnFrame L Rel Op) (Answer Term Store) →
      Instruction (ExtCall table Store) (ReturnFrame L Rel Op) (Answer Term Store)
  | .ret value => .ret value
  | .fail => .fail
  | .call call frame => .call (.inl call) frame
  | .tail call => .tail (.inl call)

def localProgram {n : Nat} (table : LocalTable L Rel Op n)
    (base : Program Unit (Control L Rel Op Store) (Call Term Store Rel)
      (ReturnFrame L Rel Op) (Answer Term Store)) :
    Program Unit (ExtControl table Store) (ExtCall table Store)
      (ReturnFrame L Rel Op) (Answer Term Store) where
  inspect
    | .inl control => embedInstruction table (base.inspect control)
    | .inr call => .tail (.inr call)
  branches context
    | .inl call => (base.branches context call).map fun branch => (branch.1, .inl branch.2)
    | .inr call => [(context, .inl (enter call))]
  resume context frame answer :=
    let next := base.resume context frame answer
    (next.1, .inl next.2)

def embedTask {n : Nat} (table : LocalTable L Rel Op n)
    (task : Task Unit (Control L Rel Op Store) (ReturnFrame L Rel Op)) :
    Task Unit (ExtControl table Store) (ReturnFrame L Rel Op) :=
  ⟨task.context, .inl task.control, task.returns⟩

def embedState {n : Nat} (table : LocalTable L Rel Op n)
    (state : State Unit (Control L Rel Op Store) (ReturnFrame L Rel Op) (Answer Term Store)) :
    State Unit (ExtControl table Store) (ReturnFrame L Rel Op) (Answer Term Store) :=
  ⟨state.frontier.map (embedTask table), state.emitted⟩

/-- Every ordinary machine step embeds into the extended machine, including
the complete alternative frontier and the returned store in each answer. -/
theorem step_embed {n : Nat} (table : LocalTable L Rel Op n)
    (base : Program Unit (Control L Rel Op Store) (Call Term Store Rel)
      (ReturnFrame L Rel Op) (Answer Term Store))
    (state : State Unit (Control L Rel Op Store) (ReturnFrame L Rel Op) (Answer Term Store)) :
    step (localProgram table base) (embedState table state) =
      embedState table (step base state) := by
  rcases state with ⟨frontier, emitted⟩
  cases frontier with
  | nil => rfl
  | cons task rest =>
      rcases task with ⟨context, control, pending⟩
      cases hi : base.inspect control with
      | ret answer =>
          cases pending <;> simp [step, localProgram, embedState, embedTask, hi, embedInstruction]
      | fail => simp [step, localProgram, embedState, embedTask, hi, embedInstruction]
      | call callee frame =>
          simp [step, localProgram, embedState, embedTask, hi, embedInstruction,
            List.map_map, Function.comp_def]
      | tail callee =>
          simp [step, localProgram, embedState, embedTask, hi, embedInstruction,
            List.map_map, Function.comp_def]

theorem steps_embed {n : Nat} (table : LocalTable L Rel Op n)
    (base : Program Unit (Control L Rel Op Store) (Call Term Store Rel)
      (ReturnFrame L Rel Op) (Answer Term Store))
    (count : Nat)
    (state : State Unit (Control L Rel Op Store) (ReturnFrame L Rel Op) (Answer Term Store)) :
    repeats (step (localProgram table base)) count (embedState table state) =
      embedState table (repeats (step base) count state) := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih => rw [repeats, step_embed, ih]; rfl

abbrev ReferenceState (L : TemplateLanguage Term) (Rel Op Store : Type) :=
  State Unit (Control L Rel Op Store) (ReturnFrame L Rel Op) (Answer Term Store)

def entryState {k : Nat} (code : Code L Rel Op k) (frame : Fin k → Term) (σ : Store)
    (pending : List (ReturnFrame L Rel Op))
    (rest : List (Task Unit (Control L Rel Op Store) (ReturnFrame L Rel Op)))
    (emitted : List (Unit × Answer Term Store)) : ReferenceState L Rel Op Store :=
  ⟨⟨(), ⟨k, code, frame, σ⟩, pending⟩ :: rest, emitted⟩

def outlineState {n k : Nat} (table : LocalTable L Rel Op n)
    (code : Code L Rel Op k) (frame : Fin k → Term) (σ : Store)
    (pending : List (ReturnFrame L Rel Op))
    (rest : List (Task Unit (Control L Rel Op Store) (ReturnFrame L Rel Op)))
    (emitted : List (Unit × Answer Term Store)) :
    State Unit (ExtControl (insert table ⟨k, code⟩) Store)
      (ReturnFrame L Rel Op) (Answer Term Store) :=
  ⟨⟨(), .inr (outline table code frame σ), pending⟩ ::
    rest.map (embedTask (insert table ⟨k, code⟩)), emitted⟩

/-- Entering the inserted relation is a genuine extra machine step. It keeps
the caller's return stack and every surrounding alternative unchanged. -/
theorem outline_enter {n k : Nat} (table : LocalTable L Rel Op n)
    (base : Program Unit (Control L Rel Op Store) (Call Term Store Rel)
      (ReturnFrame L Rel Op) (Answer Term Store))
    (code : Code L Rel Op k) (frame : Fin k → Term) (σ : Store)
    (pending : List (ReturnFrame L Rel Op))
    (rest : List (Task Unit (Control L Rel Op Store) (ReturnFrame L Rel Op)))
    (emitted : List (Unit × Answer Term Store)) :
    step (localProgram (insert table ⟨k, code⟩) base)
      (outlineState table code frame σ pending rest emitted) =
    embedState (insert table ⟨k, code⟩)
      (entryState code (reconstruct (capture frame (code.support L))) σ pending rest emitted) := by
  simp [step, localProgram, outlineState, outline, enter, embedState, embedTask, entryState]

variable (S : StoreAlgebra Term Store Op) [DecidableEq Rel]

theorem step_captured (P : EqProgram L Rel Op) {k : Nat}
    (code : Code L Rel Op k) (frame : Fin k → Term) (σ : Store)
    (pending : List (ReturnFrame L Rel Op))
    (rest : List (Task Unit (Control L Rel Op Store) (ReturnFrame L Rel Op)))
    (emitted : List (Unit × Answer Term Store)) :
    step (compiled L S P)
      (entryState code (reconstruct (capture frame (code.support L))) σ pending rest emitted) =
    step (compiled L S P) (entryState code frame σ pending rest emitted) := by
  simp only [step, entryState, compiled, inspect_captured]

/-- Operational preservation and reflection for a local code-table call.
After one additional entry step the exact finite run agrees, including
bindings made to previously unbound captured references. The law also holds
when the surrounding frontier or return continuation is nonempty. -/
theorem outline_steps {n k : Nat} (table : LocalTable L Rel Op n)
    (P : EqProgram L Rel Op) (code : Code L Rel Op k)
    (frame : Fin k → Term) (σ : Store)
    (pending : List (ReturnFrame L Rel Op))
    (rest : List (Task Unit (Control L Rel Op Store) (ReturnFrame L Rel Op)))
    (emitted : List (Unit × Answer Term Store)) (count : Nat) :
    repeats (step (localProgram (insert table ⟨k, code⟩) (compiled L S P))) (count + 2)
      (outlineState table code frame σ pending rest emitted) =
    embedState (insert table ⟨k, code⟩)
      (repeats (step (compiled L S P)) (count + 1)
        (entryState code frame σ pending rest emitted)) := by
  rw [show count + 2 = (count + 1) + 1 by omega, repeats, outline_enter, steps_embed]
  simp only [repeats, step_captured]

/-- Complete collections agree in both directions, with the one entry step
accounted for. The observation includes each answer's full branch store. -/
theorem outline_observations {n k : Nat} (table : LocalTable L Rel Op n)
    (P : EqProgram L Rel Op) (code : Code L Rel Op k)
    (frame : Fin k → Term) (σ : Store)
    (pending : List (ReturnFrame L Rel Op))
    (rest : List (Task Unit (Control L Rel Op Store) (ReturnFrame L Rel Op)))
    (emitted : List (Unit × Answer Term Store)) (count : Nat) :
    HostCalls.collectRun
        (localProgram (insert table ⟨k, code⟩) (compiled L S P)) (count + 2)
        (outlineState table code frame σ pending rest emitted) =
      HostCalls.collectRun (compiled L S P) (count + 1)
        (entryState code frame σ pending rest emitted) := by
  unfold HostCalls.collectRun
  rw [outline_steps S]
  simp only [embedState]
  generalize (repeats (step (compiled L S P)) (count + 1)
    (entryState code frame σ pending rest emitted)).frontier = frontier
  cases frontier <;> rfl

/-- The local call terminates with a given complete collection if and only if
the original body does. The quantified collection retains its stores and all
duplicate occurrences. No pre-existing denotation or termination hypothesis
is needed. -/
theorem outline_terminates_iff {n k : Nat} (table : LocalTable L Rel Op n)
    (P : EqProgram L Rel Op) (code : Code L Rel Op k)
    (frame : Fin k → Term) (σ : Store)
    (pending : List (ReturnFrame L Rel Op))
    (rest : List (Task Unit (Control L Rel Op Store) (ReturnFrame L Rel Op)))
    (emitted answers : List (Unit × Answer Term Store)) :
    (∃ count, HostCalls.collectRun
        (localProgram (insert table ⟨k, code⟩) (compiled L S P)) count
        (outlineState table code frame σ pending rest emitted) = some answers) ↔
      ∃ count, HostCalls.collectRun (compiled L S P) count
        (entryState code frame σ pending rest emitted) = some answers := by
  constructor
  · rintro ⟨count, completed⟩
    cases count with
    | zero => simp [HostCalls.collectRun, repeats, outlineState] at completed
    | succ count =>
        cases count with
        | zero =>
            simp [HostCalls.collectRun, repeats, outline_enter, embedState, entryState] at completed
        | succ count =>
            rw [outline_observations S] at completed
            exact ⟨count + 1, completed⟩
  · rintro ⟨count, completed⟩
    cases count with
    | zero => simp [HostCalls.collectRun, repeats, entryState] at completed
    | succ count =>
        exact ⟨count + 2, by rw [outline_observations S]; exact completed⟩

/-! ## The value-position `let` and its ordinary return frame -/

def localAnswers {n : Nat} {table : LocalTable L Rel Op n}
    (value : Call Term Store Rel → List (Answer Term Store)) (call : LocalCall table Store) :
    List (Answer Term Store) :=
  let entered := enter call
  (meaning L S entered.frame entered.store entered.code).eval value

omit [DecidableEq Rel] in
theorem outline_answers {n k : Nat} (table : LocalTable L Rel Op n)
    (value : Call Term Store Rel → List (Answer Term Store))
    (code : Code L Rel Op k) (frame : Fin k → Term) (σ : Store) :
    localAnswers S value (outline table code frame σ) =
      (meaning L S frame σ code).eval value := by
  unfold localAnswers enter outline
  dsimp only [insert, Fin.cases_zero]
  rw [meaning_congr L S code _ frame
    (fun i hi => reconstruct_capture frame _ i hi) σ]

def returnFrame {k : Nat} (pattern : L.Tmpl k) (body : Code L Rel Op k)
    (frame : Fin k → Term) : ReturnFrame L Rel Op :=
  ⟨k, pattern, body, capture frame (frameSupport L pattern body)⟩

omit [DecidableEq Rel] in
/-- Returning from a local body runs the caller in the *answer's* store. This
is the step that carries bindings of captured outer variables to the caller. -/
theorem returnFrame_answers {k : Nat}
    (value : Call Term Store Rel → List (Answer Term Store))
    (pattern : L.Tmpl k) (body : Code L Rel Op k) (frame : Fin k → Term)
    (answer : Answer Term Store) :
    (decodeFrame L S (returnFrame pattern body frame) answer).answers value =
      match S.unify (L.inst pattern frame) answer.1 answer.2 with
      | none => []
      | some σ' => (meaning L S frame σ' body).eval value := by
  have hp : L.inst pattern (reconstruct (capture frame (frameSupport L pattern body))) =
      L.inst pattern frame :=
    L.inst_congr pattern _ frame (fun i hi => reconstruct_capture frame _ i
      (by simp [frameSupport, hi]))
  have hb (σ : Store) := meaning_congr L S body
    (reconstruct (capture frame (frameSupport L pattern body))) frame
    (fun i hi => reconstruct_capture frame _ i (by simp [frameSupport, hi])) σ
  simp only [decodeFrame, resumeControl, returnFrame, hp]
  cases hu : S.unify (L.inst pattern frame) answer.1 answer.2 with
  | none => simp [decodeControl, meaning, Expr.lower, Body.answers]
  | some σ => simp [decodeControl, Expr.lower_answer, hb]

omit [DecidableEq Rel] in
/-- A selected nested expression is normalized once in a fresh local entry.
All of its answers resume the ordinary caller frame; none of its store
updates to captured references are discarded. -/
theorem outlined_let_answers {n k : Nat} (table : LocalTable L Rel Op n)
    (value : Call Term Store Rel → List (Answer Term Store))
    (pattern : L.Tmpl k) (bound body : Source L Rel Op k)
    (frame : Fin k → Term) (σ : Store) :
    (localAnswers S value (outline table (norm L bound) frame σ)).flatMap
        (fun answer => (decodeFrame L S (returnFrame pattern (norm L body) frame) answer).answers value) =
      (smeaning L S frame σ (.letE pattern bound body)).eval value := by
  rw [outline_answers S, norm_eval]
  simp only [returnFrame_answers, norm_eval, smeaning, Expr.eval]
  congr 1
  funext answer
  cases S.unify (L.inst pattern frame) answer.1 answer.2 <;> rfl

end Generic

/-! ## Controls over the existing first-order substitution store -/

namespace Controls

open Mettapedia.Logic.LP
open DestinationPassing.Controls

/-- An outer unbound reference is bound inside a value-position computation. -/
def bindsOuter : Source L Unit Empty 1 :=
  .letE (.var 0) (.ret (.const "Z")) (.ret (.const "OK"))

def caller : Code L Unit Empty 1 := .ret (.var 0)

def outerFrame : Fin 1 → Term sig := fun _ => .var 0

def emptyTable : LocalTable L Unit Empty 0 := Fin.elim0

def pendingCaller : List (ReturnFrame L Unit Empty) :=
  [returnFrame (.const "OK") caller outerFrame]

def liftedTable : LocalTable L Unit Empty 1 :=
  insert emptyTable ⟨1, norm L bindsOuter⟩

def nativeProgram := localProgram liftedTable (compiled L plusStore [])

def correctStart := outlineState emptyTable (norm L bindsOuter) outerFrame start pendingCaller [] []

/-- The one extra step is real: the direct body has finished in two steps,
whereas the outlined body needs three. Both bind and return the caller's `x`. -/
theorem outline_preserves_outer_binding :
    (repeats (step nativeProgram) 2 correctStart).frontier.length = 1 ∧
    (repeats (step nativeProgram) 3 correctStart).frontier = [] ∧
    (repeats (step nativeProgram) 3 correctStart).emitted.map
        (fun a => a.2.2.1.applyTerm a.2.1) = [.const "Z"] ∧
    (repeats (step (compiled L plusStore [])) 2
        (entryState (norm L bindsOuter) outerFrame start pendingCaller [] [])).emitted.map
        (fun a => a.2.2.1.applyTerm a.2.1) = [.const "Z"] := by
  unfold nativeProgram
  rw [show plusStore = substitutionStoreByFuel id noPrim noTest 32 from
    (substitutionStoreByFuel_eq id noPrim noTest 32).symm]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- An incorrect copy replaces the caller's open reference `0` with a fresh
reference `10`. The caller still refers to `0` and cannot see its binding. -/
def copiedStart :
    State Unit (ExtControl liftedTable (Subst sig × Nat))
      (ReturnFrame L Unit Empty) (Answer (Term sig) (Subst sig × Nat)) :=
  ⟨[⟨(), .inr ⟨0, fun _ => some (.var 10), (Subst.id sig, 11)⟩, pendingCaller⟩], []⟩

/-- Negative control: copying an unbound capture produces an unbound answer
that the correctly outlined source computation never produces. -/
theorem copying_open_capture_loses_binding :
    (repeats (step nativeProgram) 3 copiedStart).frontier = [] ∧
    (repeats (step nativeProgram) 3 copiedStart).emitted.map
        (fun a => a.2.2.1.applyTerm a.2.1) = [.var 0] ∧
    (repeats (step nativeProgram) 3 copiedStart).emitted.map
        (fun a => a.2.2.1.applyTerm a.2.1) ≠
      (repeats (step nativeProgram) 3 correctStart).emitted.map
        (fun a => a.2.2.1.applyTerm a.2.1) := by
  unfold nativeProgram
  rw [show plusStore = substitutionStoreByFuel id noPrim noTest 32 from
    (substitutionStoreByFuel_eq id noPrim noTest 32).symm]
  refine ⟨rfl, rfl, ?_⟩
  change ([Term.var 0] : List (Term sig)) ≠ [Term.const "Z"]
  intro equal
  cases equal

/-- Outlining does not itself allocate logical variables: this body preserves
the enclosing activation's fresh-variable supply. -/
theorem outlining_allocates_no_logical_variables :
    (repeats (step nativeProgram) 3 correctStart).emitted.map (fun a => a.2.2.2) = [10] := by
  unfold nativeProgram
  rw [show plusStore = substitutionStoreByFuel id noPrim noTest 32 from
    (substitutionStoreByFuel_eq id noPrim noTest 32).symm]
  decide

def twoEquations : EqProgram L Unit Empty :=
  [((), ⟨0, [], .ret (.const "Z")⟩), ((), ⟨0, [], .ret (.const "Z")⟩)]

def callsExternal : Code L Unit Empty 0 := .tail () []

/-- A local address and an external relation coexist without replacing each
other, and two equal equation answers remain two occurrences. -/
theorem local_call_keeps_external_alternatives :
    let program := localProgram (insert emptyTable ⟨0, callsExternal⟩)
      (compiled L plusStore twoEquations)
    let initial := outlineState emptyTable callsExternal Fin.elim0 start [] [] []
    (repeats (step program) 4 initial).frontier = [] ∧
    (repeats (step program) 4 initial).emitted.map (fun a => a.2.1) =
      [.const "Z", .const "Z"] := by
  rw [show plusStore = substitutionStoreByFuel id noPrim noTest 32 from
    (substitutionStoreByFuel_eq id noPrim noTest 32).symm]
  exact ⟨rfl, rfl⟩

end Controls

end Mettapedia.GSLT.LanguageDef.NativeControlLifting
