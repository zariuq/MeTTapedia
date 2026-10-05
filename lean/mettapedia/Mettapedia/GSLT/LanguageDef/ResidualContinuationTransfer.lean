import Mettapedia.GSLT.LanguageDef.DefunctionalizedEquationBodies
import Mettapedia.Machines.ConstraintPropagation

/-!
# Materializing a residual equation continuation

A suspended equation body already has an activation frame and a stack of
captured return frames. Its remaining templates can be instantiated without
running the body, allocating new activation slots, or invoking a call again.
The result is code in the existing equation-body language over literal terms.
This is proof notation for ready operands, not another runtime instruction set.

`materialize_meaning` proves template elimination by induction on the residual
code. `materializeFrame_exact` proves the return-pattern binding and the
captured caller's suffix together. `materializeResidual_exact` composes these
laws for an arbitrary entered return chain. The equalities keep the entire
branch store, not just the returned value; the concrete controls below include
bindings, suspended goals, the wake queue, the undo log, and an effect trace.

This theorem starts after a shared cell export has produced canonical terms.
It does not verify a C cell exporter, the selected type-protocol stage, program
leases, error handlers, or pre-entered collection and commitment scopes. Those
must agree with the source machine before this local law applies. In
particular, reconstructing already evaluated source expressions is not
materializing their remaining ready operations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ResidualContinuationTransfer

open CompiledContinuationAnswerProducer DefunctionalizedEquationBodies

variable {Term Store Rel Op : Type}

/-- Literal operands have no activation slots to read. -/
abbrev literals (Term : Type) : TemplateLanguage Term where
  Tmpl _ := Term
  inst t _ := t
  support _ := ∅
  inst_congr _ _ _ _ := rfl

def noSlots : Fin 0 → Term := Fin.elim0

/-- Instantiate the remaining templates once, without executing a call or a
store operation. Both branches of a test remain available. -/
def materialize (L : TemplateLanguage Term) {k : Nat} (frame : Fin k → Term) :
    Code L Rel Op k → Code (literals Term) Rel Op 0
  | .ret t => .ret (L.inst t frame)
  | .fail => .fail
  | .letCall p rel args body =>
      .letCall (L.inst p frame) rel (instArgs L args frame) (materialize L frame body)
  | .letPrim p op args body =>
      .letPrim (L.inst p frame) op (instArgs L args frame) (materialize L frame body)
  | .bind p v body =>
      .bind (L.inst p frame) (L.inst v frame) (materialize L frame body)
  | .ite op args yes no =>
      .ite op (instArgs L args frame) (materialize L frame yes) (materialize L frame no)
  | .tail rel args => .tail rel (instArgs L args frame)

@[simp] theorem literal_args {k : Nat} (args : List Term) (frame : Fin k → Term) :
    instArgs (literals Term) args frame = args := by
  simp [instArgs, literals]

@[simp] theorem literal_inst {k : Nat} (t : Term) (frame : Fin k → Term) :
    (literals Term).inst t frame = t := rfl

section Lowering

variable (L : TemplateLanguage Term) (S : StoreAlgebra Term Store Op) [Inhabited Term]

/-- Materialization commutes with every residual operation, including calls,
failed unifications and tests. No condition is imposed on the store payload. -/
theorem materialize_meaning {k : Nat} (code : Code L Rel Op k)
    (frame : Fin k → Term) (σ : Store) :
    meaning (literals Term) S noSlots σ (materialize L frame code) =
      meaning L S frame σ code := by
  induction code generalizing σ with
  | ret t => rfl
  | fail => rfl
  | letCall p rel args body ih =>
      simp only [materialize, meaning, literal_args, ih]
  | letPrim p op args body ih =>
      simp only [materialize, meaning, literal_args, ih]
  | bind p v body ih =>
      simp only [materialize, meaning, ih]
  | ite op args yes no ihYes ihNo =>
      simp only [materialize, meaning, literal_args, ihYes, ihNo]
  | tail rel args => simp only [materialize, meaning, literal_args]

/-- A shadow frame may leave unused slots alone. Every slot read by the suffix
must still contain the same exported term, including its logical variables. -/
theorem materialize_agree {k : Nat} (code : Code L Rel Op k)
    (frame shadow : Fin k → Term)
    (agree : ∀ i ∈ code.support L, shadow i = frame i) (σ : Store) :
    meaning (literals Term) S noSlots σ (materialize L shadow code) =
      meaning L S frame σ code := by
  rw [materialize_meaning]
  exact meaning_congr L S code shadow frame agree σ

/-- A return frame after all its captured templates have become ready terms. -/
structure ReadyReturn (Term Rel Op : Type) where
  pattern : Term
  body : Code (literals Term) Rel Op 0

def materializeFrame (f : ReturnFrame L Rel Op) : ReadyReturn Term Rel Op :=
  ⟨L.inst f.pattern (reconstruct f.captured),
    materialize L (reconstruct f.captured) f.body⟩

/-- Bind in the callee answer's complete store, then run the caller's suffix. -/
def readyResume (f : ReadyReturn Term Rel Op) (a : Answer Term Store) :
    Body (Call Term Store Rel) (Answer Term Store) :=
  match S.unify f.pattern a.1 a.2 with
  | none => .fail
  | some σ => (meaning (literals Term) S noSlots σ f.body).lower .answer

theorem materializeFrame_exact (f : ReturnFrame L Rel Op) (a : Answer Term Store) :
    readyResume S (materializeFrame L f) a = decodeFrame L S f a := by
  simp only [readyResume, materializeFrame, decodeFrame, resumeControl]
  cases S.unify (L.inst f.pattern (reconstruct f.captured)) a.1 a.2 with
  | none => rfl
  | some σ => simp only [decodeControl, materialize_meaning]

/-- Return to each entered caller in order; a failed return binding prevents
the remaining callers from running. -/
def resumeFrames : List (ReturnFrame L Rel Op) → Answer Term Store →
    Body (Call Term Store Rel) (Answer Term Store)
  | [], a => .answer a
  | f :: rest, a => (decodeFrame L S f a).bind (resumeFrames rest)

def resumeReadyFrames : List (ReadyReturn Term Rel Op) → Answer Term Store →
    Body (Call Term Store Rel) (Answer Term Store)
  | [], a => .answer a
  | f :: rest, a => (readyResume S f a).bind (resumeReadyFrames rest)

theorem materializeFrames_exact (frames : List (ReturnFrame L Rel Op))
    (a : Answer Term Store) :
    resumeReadyFrames S (frames.map (materializeFrame L)) a = resumeFrames L S frames a := by
  induction frames generalizing a with
  | nil => rfl
  | cons f rest ih =>
      simp only [List.map_cons, resumeReadyFrames, resumeFrames, materializeFrame_exact]
      exact congrArg (Body.bind (decodeFrame L S f a)) (funext ih)

/-- The complete current branch: remaining code followed by entered callers.
Older search alternatives are deliberately outside this local operation. -/
def materializeResidual (c : Control L Rel Op Store) (frames : List (ReturnFrame L Rel Op)) :
    Body (Call Term Store Rel) (Answer Term Store) :=
  ((meaning (literals Term) S noSlots c.store (materialize L c.frame c.code)).lower .answer).bind
    (resumeReadyFrames S (frames.map (materializeFrame L)))

theorem materializeResidual_exact (c : Control L Rel Op Store)
    (frames : List (ReturnFrame L Rel Op)) :
    materializeResidual L S c frames =
      (decodeControl L S c).bind (resumeFrames L S frames) := by
  simp only [materializeResidual, materialize_meaning, decodeControl]
  exact congrArg (Body.bind _) (funext (materializeFrames_exact L S frames))

/-- The complete ordered answer list is equal, so the lowering cannot add an
answer or discard a duplicate. The call interpretation may itself be effectful. -/
theorem materializeResidual_answers (value : Call Term Store Rel → List (Answer Term Store))
    (c : Control L Rel Op Store) (frames : List (ReturnFrame L Rel Op)) :
    (materializeResidual L S c frames).answers value =
      ((decodeControl L S c).answers value).flatMap
        (fun a => (resumeFrames L S frames a).answers value) := by
  rw [materializeResidual_exact, Body.answers_bind]

end Lowering

/-! ## Binding, suspension and effect controls

This small store instance gives the general equalities a discriminating
observation. It is not a replacement for the engine's term unifier. Its terms
are cell references and natural numbers; matching a reference with a number
wakes that reference's suspended goals through the existing constraint service.
The event trace records calls along the branch and is not in the undo log.
-/

namespace Controls

open Mettapedia.Machines.ConstraintPropagation

inductive CellTerm where
  | cell (index : Nat)
  | number (value : Nat)
  deriving DecidableEq, Repr

instance : Inhabited CellTerm := ⟨.number 0⟩

structure BranchStore where
  service : Service Nat Nat Nat
  events : List Nat
  nextCell : Nat

def initial : BranchStore := ⟨⟨⟨fun _ => none, fun _ => [], []⟩, []⟩, [], 2⟩

def bindCell (v n : Nat) (σ : BranchStore) : Option BranchStore :=
  match σ.service.state.value v with
  | none => some { σ with service := σ.service.bind v n }
  | some old => if old = n then some σ else none

def matchTerms : CellTerm → CellTerm → BranchStore → Option BranchStore
  | .cell v, .number n, σ => bindCell v n σ
  | .number n, .cell v, σ => bindCell v n σ
  | .number n, .number m, σ => if n = m then some σ else none
  | .cell v, .cell w, σ => if v = w then some σ else none

def operations : StoreAlgebra CellTerm BranchStore Unit where
  unify := matchTerms
  fresh σ k := (fun i => .cell (σ.nextCell + i.val), { σ with nextCell := σ.nextCell + k })
  prim _ args _ := args.head?
  test _ args _ := match args with
    | [.number n, .number m] => some (n == m)
    | _ => none

abbrev slots : TemplateLanguage CellTerm where
  Tmpl k := Fin k
  inst i frame := frame i
  support i := {i}
  inst_congr i frame frame' agree := agree i (by simp)

/-- A foreign call suspends goal 42 on cell 0 and performs event 10. -/
def hostEffect (σ : BranchStore) : BranchStore :=
  { σ with service := σ.service.suspend 0 42, events := σ.events ++ [10] }

/-- The foreign relation returns the same answer twice. Multiplicity matters. -/
def host (c : Call CellTerm BranchStore Unit) : List (Answer CellTerm BranchStore) :=
  let a := (CellTerm.number 7, hostEffect c.2.2)
  [a, a]

def resolved (t : CellTerm) (σ : BranchStore) : Option Nat :=
  match t with
  | .cell v => σ.service.state.value v
  | .number n => some n

def observe (a : Answer CellTerm BranchStore) : Option Nat × List Nat × List Nat :=
  (resolved a.1 a.2, a.2.service.state.woken, a.2.events)

/-- Two captured slots refer to the same logical cell. The host result binds
the first; the residual returns the second. -/
def source : Control slots Unit Unit BranchStore :=
  ⟨2, .letCall 0 () [] (.ret 1), fun _ => .cell 0, initial⟩

theorem source_wakes_once_per_answer :
    ((decodeControl slots operations source).answers host).map observe =
      [(some 7, [42], [10]), (some 7, [42], [10])] := by
  simp [decodeControl, source, meaning, Expr.lower, Body.answers, host, operations,
    matchTerms, bindCell, initial, hostEffect, observe, resolved, Service.suspend,
    Service.bind, Service.setValue, Service.setSuspended, Service.setWoken]

/-- Materialization keeps the host effect, both aliases, the wake-up, and both
copies of the answer while removing every source template. -/
theorem materialized_wakes_once_per_answer :
    ((materializeResidual slots operations source []).answers host).map observe =
      [(some 7, [42], [10]), (some 7, [42], [10])] := by
  rw [materializeResidual_answers]
  simpa [resumeFrames, Body.answers] using source_wakes_once_per_answer

/-- A return frame is already entered when its callee yields this answer. -/
def entered : ReturnFrame slots Unit Unit :=
  ⟨1, 0, .ret 0, fun _ => some (.cell 0)⟩

def pending : BranchStore := hostEffect initial

theorem materialized_return_wakes :
    ((readyResume operations (materializeFrame slots entered) (.number 7, pending)).answers
      host).map observe = [(some 7, [42], [10])] := by
  rw [materializeFrame_exact]
  simp [decodeFrame, decodeControl, resumeControl, entered, reconstruct, meaning,
    Expr.lower, Body.answers, operations, matchTerms, bindCell, pending, initial,
    hostEffect, observe, resolved, Service.suspend, Service.bind, Service.setValue,
    Service.setSuspended, Service.setWoken]

/-- Copying values keeps the apparent bindings and effect history but discards
the service ownership needed by the next bind and by a later retry. -/
def valuesOnly (σ : BranchStore) : BranchStore :=
  { σ with service := ⟨⟨σ.service.state.value, fun _ => [], []⟩, []⟩ }

theorem value_only_return_loses_wakeup :
    ((readyResume operations (materializeFrame slots entered)
      (.number 7, valuesOnly pending)).answers host).map observe = [(some 7, [], [10])] := by
  rw [materializeFrame_exact]
  simp [decodeFrame, decodeControl, resumeControl, entered, reconstruct, meaning,
    Expr.lower, Body.answers, operations, matchTerms, bindCell, valuesOnly, pending,
    initial, hostEffect, observe, resolved, Service.suspend, Service.bind,
    Service.setValue, Service.setSuspended, Service.setWoken]

theorem same_value_is_not_observable_state :
    ((readyResume operations (materializeFrame slots entered)
      (.number 7, valuesOnly pending)).answers host).map observe ≠
    ((readyResume operations (materializeFrame slots entered)
      (.number 7, pending)).answers host).map observe := by
  rw [value_only_return_loses_wakeup, materialized_return_wakes]
  decide

/-- A separate fresh export for the second slot breaks the alias even though
the host call and the value bound into the first slot are unchanged. -/
def splitAliases : Control slots Unit Unit BranchStore :=
  { source with frame := fun i => .cell i.val }

theorem separate_exports_lose_alias :
    ((materializeResidual slots operations splitAliases []).answers host).map observe =
      [(none, [42], [10]), (none, [42], [10])] := by
  rw [materializeResidual_answers]
  simp [decodeControl, splitAliases, source, meaning, Expr.lower, Body.answers,
    resumeFrames, host, operations, matchTerms, bindCell, initial, hostEffect,
    observe, resolved, Service.suspend, Service.bind, Service.setValue,
    Service.setSuspended, Service.setWoken, Function.update]

/-- Resuming the entered frame does not execute its completed host call again.
Replaying that call leaves a second event, even when the final value agrees. -/
theorem replay_repeats_effect :
    ((readyResume operations (materializeFrame slots entered)
      (.number 7, hostEffect pending)).answers host).map observe =
      [(some 7, [42, 42], [10, 10])] := by
  rw [materializeFrame_exact]
  simp [decodeFrame, decodeControl, resumeControl, entered, reconstruct, meaning,
    Expr.lower, Body.answers, operations, matchTerms, bindCell, pending, initial,
    hostEffect, observe, resolved, Service.suspend, Service.bind, Service.setValue,
    Service.setSuspended, Service.setWoken]

/-- Retrying uses the same mark for values and the suspension service. The
ordered external-event history is intentionally not claimed to roll back. -/
theorem retry_restores_service (σ : BranchStore)
    (ops : List (Mettapedia.Machines.ConstraintPropagation.Op Nat Nat Nat)) :
    rollback ((σ.service.exec ops).log.drop σ.service.log.length)
      (σ.service.exec ops).state = σ.service.state :=
  rollback_exec σ.service ops

end Controls

end Mettapedia.GSLT.LanguageDef.ResidualContinuationTransfer
