import Mettapedia.GSLT.LanguageDef.HostGoalDelimiters
import Mettapedia.Machines.Cursor.Fold
import Mettapedia.Machines.Cursor.Relational
import Mettapedia.Machines.Cursor.ClientMap
import Mettapedia.OSLF.Syntax.RewriteEventHistoryForward

/-!
# Host answer controls as providers of the common cursor protocol

This adapter connects `HostCalls.Pull` to `Machines.Cursor.Provider`. It
retains the real host residual after both a yield and a suspension. The
collector is a client of that existing protocol, so arbitrary chunking uses
the existing `Cursor.advance_add` law, with the same residual and receipts.

`advance_collect` identifies its completed observation with `HostCalls.collect`.
Its extra unit allows inspection of the client's return; on an unfinished run
it can instead perform one more poll. The comparison therefore does not equate
intermediate residuals or effects at that shifted fuel. `chunk_exact` preserves
the actual residual and receipt within this adapter. The receipt counts pulls,
not runtime instructions or wall time. This internal polling protocol does not
model handle allocation, affine ownership, disposal, faults, or exceptions.
Those are additional interface obligations, not implied by the adapter.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeControlCursor

open Mettapedia.TypeTheory
open Mettapedia.Machines.Cursor
open Mettapedia.GSLT.LanguageDef.HostCalls (Pull collect)
open _root_.CategoryTheory

variable {HState Answer : Type}

/-- A poll explicitly distinguishes suspension, exhaustion and an answer. -/
def protocol (Answer : Type) : IndexedPolynomial Unit (fun _ => Unit) where
  Shape _ _ := Unit
  Position _ := Pull Unit Answer
  next _ _ := ()

def provider (pull : HState → Pull HState Answer) : Provider (protocol Answer) where
  State _ _ := HState
  step h _ := match pull h with
    | .done => ⟨.done, h⟩
    | .yield a residual => ⟨.yield a (), residual⟩
    | .suspend residual => ⟨.suspend (), residual⟩

/-- The collector uses the common client type and existing fold-control states. -/
def client (Answer : Type) :
    Client (P := protocol Answer) (Return := fun _ _ => List Answer) where
  V _ _ := Fold.State (List Answer)
  str := fun _ _ => ↾(fun state => match state with
    | .finished values => ⟨.inl values, fun impossible => nomatch impossible⟩
    | .pulling reversed => ⟨.inr (), fun reply => match reply with
        | .done => .finished reversed.reverse
        | .yield value _ => .pulling (value :: reversed)
        | .suspend _ => .pulling reversed⟩)

def packet (pull : HState → Pull HState Answer) (cursor : HState) (reversed : List Answer) :
    Packet (provider pull) (client Answer) () := ⟨(), .pulling reversed, cursor⟩

/-- A paused client has no completed collection. -/
def published (pull : HState → Pull HState Answer) :
    Outcome (provider pull) (client Answer) () → Option (List Answer)
  | .paused _ => none
  | .done result => some result.2.1

theorem advance_poll (pull : HState → Pull HState Answer) (fuel : Nat)
    (cursor : HState) (reversed : List Answer) :
    advance (provider pull) (client Answer) (fun _ _ => 1) (fuel + 1)
        (packet pull cursor reversed) =
      let next : Packet (provider pull) (client Answer) () := match pull cursor with
        | .done => ⟨(), .finished reversed.reverse, cursor⟩
        | .yield a residual => packet pull residual (a :: reversed)
        | .suspend residual => packet pull residual reversed
      let result := advance (provider pull) (client Answer) (fun _ _ => 1) fuel next
      (1 + result.1, result.2) := by
  cases h : pull cursor <;>
    simp only [advance, packet, client, provider, protocol] <;>
    dsimp <;> rw [h] <;> rfl

/-- Equality of completed collection observations. The shifted client budget
may perform an extra poll when no collection is published, so this theorem
does not compare intermediate state or effects against the host collector. -/
theorem advance_collect (pull : HState → Pull HState Answer) :
    ∀ (fuel : Nat) (cursor : HState) (reversed : List Answer),
      published pull (advance (provider pull) (client Answer) (fun _ _ => 1)
        (fuel + 1) (packet pull cursor reversed)).2 =
      (collect pull fuel cursor).map (reversed.reverse ++ ·)
  | 0, cursor, reversed => by
      rw [advance_poll]
      cases pull cursor <;> rfl
  | fuel + 1, cursor, reversed => by
      rw [advance_poll]
      cases h : pull cursor with
      | done =>
          simp only [h, collect, Option.map_some, List.append_nil]
          rfl
      | yield value residual =>
          simp only [h, collect, Option.map_map, Function.comp_def]
          simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using
            advance_collect pull fuel residual (value :: reversed)
      | suspend residual =>
          simpa only [h, collect] using advance_collect pull fuel residual reversed

/-- A host control may be run in any budget partition without changing its
actual residual, completed result or pull count. -/
theorem chunk_exact (pull : HState → Pull HState Answer) (first second : Nat)
    (cursor : HState) (reversed : List Answer) :
    advance (provider pull) (client Answer) (fun _ _ => 1) (first + second)
      (packet pull cursor reversed) =
    resume (provider pull) (client Answer) (fun _ _ => 1) second
      (advance (provider pull) (client Answer) (fun _ _ => 1) first
        (packet pull cursor reversed)) :=
  advance_add _ _ _ first second _

/-- A local conservation law for the unfinished answer sequence gives a
sound completed collection. Suspended work is included in `remaining`; it
cannot be replaced by just the rows already prepared for publication. -/
theorem collect_sound (pull : HState → Pull HState Answer)
    (remaining : HState → List Answer)
    (preserves : ∀ state, match pull state with
      | .done => remaining state = []
      | .suspend next => remaining state = remaining next
      | .yield answer next => remaining state = answer :: remaining next)
    (fuel : Nat) (state : HState) (answers : List Answer)
    (completed : collect pull fuel state = some answers) :
    answers = remaining state := by
  induction fuel generalizing state answers with
  | zero => simp [collect] at completed
  | succ fuel ih =>
      have conserved := preserves state
      cases moved : pull state with
      | done =>
          simp only [moved] at conserved
          simpa [collect, moved, conserved] using completed.symm
      | suspend next =>
          simp only [moved] at conserved
          simp only [collect, moved] at completed
          exact (ih next answers completed).trans conserved.symm
      | yield answer next =>
          simp only [moved] at conserved
          simp only [collect, moved] at completed
          cases found : collect pull fuel next with
          | none => simp [found] at completed
          | some tail =>
              simp only [found, Option.map_some, Option.some.injEq] at completed
              subst answers
              rw [ih next tail found, conserved]

/-- A decreasing finite work measure proves exhaustion of a conserving
provider. This bound counts provider polls, not the work inside a primitive
or the time taken by that primitive. The running cursor need not compute it. -/
theorem collect_complete (pull : HState → Pull HState Answer)
    (remaining : HState → List Answer)
    (preserves : ∀ state, match pull state with
      | .done => remaining state = []
      | .suspend next => remaining state = remaining next
      | .yield answer next => remaining state = answer :: remaining next)
    (rank : HState → Nat)
    (decreases : ∀ state, match pull state with
      | .done => rank state = 0
      | .suspend next => rank next < rank state
      | .yield _ next => rank next < rank state)
    (fuel : Nat) (state : HState) (enough : rank state < fuel) :
    collect pull fuel state = some (remaining state) := by
  induction fuel generalizing state with
  | zero => omega
  | succ fuel ih =>
      have conserved := preserves state
      have decrease := decreases state
      cases moved : pull state with
      | done =>
          simp only [moved] at conserved
          simp [collect, moved, conserved]
      | suspend next =>
          simp only [moved] at conserved decrease
          have small : rank next < fuel := by omega
          simp [collect, moved, ih next small, conserved]
      | yield answer next =>
          simp only [moved] at conserved decrease
          have small : rank next < fuel := by omega
          simp [collect, moved, ih next small, conserved]

namespace Controls

def delayed : Nat → Pull Nat Nat
  | 0 => .suspend 1
  | 1 => .yield 7 2
  | 2 => .yield 7 3
  | _ => .done

theorem pending_keeps_residual :
    advance (provider delayed) (client Nat) (fun _ _ => 1) 1
      (packet delayed 0 []) = (1, .paused (packet delayed 1 [])) := rfl

theorem duplicate_occurrences :
    published delayed (advance (provider delayed) (client Nat) (fun _ _ => 1) 5
      (packet delayed 0 [])).2 = some [7, 7] := rfl

theorem completion_needs_exhaustion :
    published delayed (advance (provider delayed) (client Nat) (fun _ _ => 1) 3
      (packet delayed 0 [])).2 = none := rfl

/-- Restarting at a pause loses the completed observation available by resuming. -/
theorem restart_is_wrong :
    published delayed (advance (provider delayed) (client Nat) (fun _ _ => 1) 3
      (packet delayed 0 [])).2 ≠
    published delayed (resume (provider delayed) (client Nat) (fun _ _ => 1) 3
      (advance (provider delayed) (client Nat) (fun _ _ => 1) 2
        (packet delayed 0 []))).2 := by decide

end Controls

namespace ProtocolHistory

open Mettapedia.GSLT.ProofRelevant
open Mettapedia.OSLF.Binding.RewriteEventHistory
open Mettapedia.Machines
open Mettapedia.TypeTheory.IndexedPolynomial

universe u v

variable {Base : Type u} {Index : Base → Type u}
variable {P : IndexedPolynomial.{u,u,u,u} Base Index}
variable {Return : (base : Base) → Index base → Type u}
variable (M : Cursor.Provider P) (C : Cursor.Client (P := P) (Return := Return))

/-- An actual client inspection retains the selected protocol request and
its complete reply-dependent continuation. Return inspection is separate
from a provider request; completed outcomes have no event leaving them. -/
inductive Event (base : Base) : Cursor.Outcome M C base → Cursor.Outcome M C base → Type u
  | request {index : Index base} (control : C.V base index) (state : M.State base index)
      (request : P.Shape base index)
      (children : (reply : P.Position request) → C.V base (P.next request reply))
      (exposed : C.str base index control = ⟨.inr request, children⟩) :
      Event base (.paused ⟨index, control, state⟩)
        (.paused ⟨P.next request (M.step state request).1,
          children (M.step state request).1, (M.step state request).2⟩)
  | finish {index : Index base} (control : C.V base index) (state : M.State base index)
      (answer : Return base index)
      (children : (position : (P.withHoles Return).Position (.inl answer)) →
        C.V base ((P.withHoles Return).next (.inl answer) position))
      (exposed : C.str base index control = ⟨.inl answer, children⟩) :
      Event base (.paused ⟨index, control, state⟩) (.done ⟨index, answer, state⟩)

/-- The common protocol's exact operational interpretation keeps complete
outcomes as its terms. Equality here is equality of those outcomes, not a
quotient by answers, costs, or history endpoints. -/
abbrev theory (base : Base) : Mettapedia.GSLT.GSLT where
  Term := Cursor.Outcome M C base
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites before after := Nonempty (Event M C base before after)
  rewrites_resp_left := by
    intro before other after same step
    cases same
    exact ⟨after, step, rfl⟩
  rewrites_resp_right := by
    intro before after other step same
    cases same
    exact step

/-- The independently declared request and return-inspection events supply
the existing proof-relevant GSLT interface. Native event coverage and physical
service correctness are additional realization obligations. -/
abbrev system (base : Base) : ProofRelevantGSLT where
  theory := theory M C base
  steps := { Evidence := Event M C base, erases_iff := fun _ _ => Iff.rfl }

/-- A provider realization map preserves each actual client event, including
its retained continuation and capability. It does not choose target events
from equality of printed answers. -/
def homForward {source target : Cursor.Provider P} (h : Cursor.Hom source target)
    (base : Base) : ForwardEvidenceMap (system source C base) (system target C base) where
  mapTerm := h.outcome C
  mapEquiv := fun same => congrArg (h.outcome C) same
  mapEvidence := by
    intro before after event
    cases event with
    | request control state request children exposed =>
      have mapped := Event.request (M := target) (C := C) control (h.map state)
        request children exposed
      rw [← h.step state request] at mapped
      exact mapped
    | finish control state answer children exposed =>
      exact Event.finish (M := target) (C := C) control (h.map state) answer children exposed

/-- Mapping a protocol history commutes with its endpoint-step erasure.
This erasure deliberately forgets event evidence and supplies no decoder. -/
theorem hom_histories_erasure {source target : Cursor.Provider P}
    (h : Cursor.Hom source target) (base : Base) :
    (homForward C h base).histories ⋙ eraseHistory (system target C base) =
      eraseHistory (system source C base) ⋙ (homForward C h base).erasedHistories :=
  ForwardEvidenceMap.histories_erasure _

/-- Evaluate an ordered event history using the existing free-category run
account. The coefficient monoid need not commute: event order is retained. -/
def eventAccount {Coefficient : Type*} [Monoid Coefficient] (base : Base)
    (value : {before after : Cursor.Outcome M C base} → Event M C base before after →
      Coefficient) : Mettapedia.Effects.RunAccount (HistoryCategory (system M C base))
        Coefficient :=
  Mettapedia.Effects.RunAccount.ofFunctor (Paths.lift
    (show State (system M C base) ⥤q SingleObj Coefficientᵐᵒᵖ from
      { obj := fun _ => SingleObj.star _
        map := fun event => MulOpposite.op (value event) }))

/-- A singleton account is the chosen valuation of that actual event. -/
theorem eventAccount_generator {Coefficient : Type*} [Monoid Coefficient] (base : Base)
    (value : {before after : Cursor.Outcome M C base} → Event M C base before after →
      Coefficient) {before after : State (system M C base)} (event : before ⟶ after) :
    (eventAccount M C base value).of event.toPath = value event := by
  simp only [eventAccount, Mettapedia.Effects.RunAccount.ofFunctor, Paths.lift_toPath]
  rfl

/-- The independent provider meter charges requests, including fault replies.
Return inspection performs no provider request and has zero provider charge. -/
def eventExpense (charge : Cursor.Charge M) {base : Base} :
    {before after : Cursor.Outcome M C base} → Event M C base before after → Nat
  | _, _, .request _ state request _ _ => charge state request
  | _, _, .finish _ _ _ _ _ => 0

/-- An account in the additive natural metric reuses the monoidal history
account. It describes the declared provider meter, not machine instructions. -/
def providerAccount (charge : Cursor.Charge M) (base : Base) :
    Mettapedia.Effects.RunAccount (HistoryCategory (system M C base)) (Multiplicative Nat) :=
  eventAccount M C base (fun event => Multiplicative.ofAdd (eventExpense M C charge event))

/-- Construct the actual request history together with its account law.
The cursor result and request valuation are fixed independently; each branch
proves its local charge and composes the recursive account. The proof field
makes endpoint transport explicit when a reply changes capability. -/
def accountedAdvanceHistory (charge : Cursor.Charge M) :
    (allowance : Nat) → {base : Base} → (packet : Cursor.Packet M C base) →
    { history : History (system M C base) ⟨.paused packet⟩
        ⟨(Cursor.advance M C charge allowance packet).2⟩ //
      Multiplicative.toAdd ((providerAccount M C charge base).of history) =
        (Cursor.advance M C charge allowance packet).1 }
  | 0, _, _ => ⟨.nil, rfl⟩
  | allowance + 1, base, ⟨index, control, state⟩ =>
    match exposed : C.str base index control with
    | ⟨.inl answer, children⟩ => by
      have finished : { history : History (system M C base)
          ⟨.paused ⟨index, control, state⟩⟩ ⟨.done ⟨index, answer, state⟩⟩ //
        Multiplicative.toAdd ((providerAccount M C charge base).of history) = 0 } := by
        refine ⟨(show (⟨.paused ⟨index, control, state⟩⟩ : State (system M C base)) ⟶
            ⟨.done ⟨index, answer, state⟩⟩ from
          Event.finish (M := M) (C := C) control state answer children exposed).toPath, ?_⟩
        rw [providerAccount, eventAccount_generator]
        rfl
      have moved : Cursor.advance M C charge (allowance + 1)
          ⟨index, control, state⟩ = (0, .done ⟨index, answer, state⟩) := by
        simp only [Cursor.advance, exposed]
      exact moved.symm ▸ finished
    | ⟨.inr request, children⟩ => by
      let next : Cursor.Packet M C base :=
        ⟨_, children (M.step state request).1, (M.step state request).2⟩
      let tail := accountedAdvanceHistory charge allowance next
      let event : (⟨.paused ⟨index, control, state⟩⟩ : State (system M C base)) ⟶
          ⟨.paused next⟩ :=
        Event.request (M := M) (C := C) control state request children exposed
      have continued : { history : History (system M C base)
          ⟨.paused ⟨index, control, state⟩⟩
          ⟨(Cursor.advance M C charge allowance next).2⟩ //
        Multiplicative.toAdd ((providerAccount M C charge base).of history) =
          charge state request + (Cursor.advance M C charge allowance next).1 } := by
        refine ⟨event.toPath.comp tail.val, ?_⟩
        have composed := congrArg Multiplicative.toAdd
          ((providerAccount M C charge base).of_comp event.toPath tail.val)
        have single : Multiplicative.toAdd
            ((providerAccount M C charge base).of event.toPath) = charge state request := by
          rw [providerAccount, eventAccount_generator]
          rfl
        exact composed.trans (congrArg₂ (· + ·) single tail.property)
      have moved : Cursor.advance M C charge (allowance + 1)
          ⟨index, control, state⟩ =
          (charge state request + (Cursor.advance M C charge allowance next).1,
            (Cursor.advance M C charge allowance next).2) := by
        simp only [Cursor.advance, exposed]
        rfl
      exact moved.symm ▸ continued

/-- Every bounded execution of the existing cursor has a chronological path
of independently declared events. Empty allowance retains the empty path;
the last return inspection has no provider charge. This is a model history,
not evidence that a native recorder retained it. -/
def advanceHistory (charge : Cursor.Charge M) (allowance : Nat) {base : Base}
    (packet : Cursor.Packet M C base) :
    History (system M C base) ⟨.paused packet⟩
      ⟨(Cursor.advance M C charge allowance packet).2⟩ :=
  (accountedAdvanceHistory M C charge allowance packet).val

/-- A locally calibrated event account commutes with a lawful provider
realization on every chronological history. Transition preservation alone
is insufficient; the independently chosen valuations must agree locally. -/
theorem hom_account_preserved {source target : Cursor.Provider P}
    (h : Cursor.Hom source target) (base : Base)
    {LeftValue RightValue : Type v} [Monoid LeftValue] [Monoid RightValue]
    (leftValue : {before after : Cursor.Outcome source C base} →
      Event source C base before after → LeftValue)
    (rightValue : {before after : Cursor.Outcome target C base} →
      Event target C base before after → RightValue)
    (change : LeftValue →* RightValue)
    (localLaw : ∀ {before after} (event : Event source C base before after),
      rightValue ((homForward C h base).mapEvidence event) = change (leftValue event)) :
    (eventAccount target C base rightValue).comap (homForward C h base).histories =
      (eventAccount source C base leftValue).map change := by
  rw [← PathEvidenceMap.histories_ofForward]
  apply PathEvidenceMap.account_preserved
  intro before after event
  dsimp only [PathEvidenceMap.ofForward]
  rw [eventAccount_generator, eventAccount_generator]
  exact localLaw event

/-- The recursive construction proves the account of the actual history
against the already defined cursor meter. Its local request charges and
return-inspection charge are independently supplied by `providerAccount`. -/
theorem advanceHistory_paid (charge : Cursor.Charge M) (allowance : Nat) {base : Base}
    (packet : Cursor.Packet M C base) :
    Multiplicative.toAdd ((providerAccount M C charge base).of
      (advanceHistory M C charge allowance packet)) =
      (Cursor.advance M C charge allowance packet).1 :=
  (accountedAdvanceHistory M C charge allowance packet).property

/-- Resume only the retained outcome. The construction carries its suffix
account alongside the already paid prefix, using the existing cursor resume
transition; a completed result contributes the empty suffix. -/
def accountedResumeHistory (charge : Cursor.Charge M) (allowance : Nat) {base : Base} :
    (earlier : Nat × Cursor.Outcome M C base) →
    { history : History (system M C base) ⟨earlier.2⟩
        ⟨(Cursor.resume M C charge allowance earlier).2⟩ //
      earlier.1 + Multiplicative.toAdd ((providerAccount M C charge base).of history) =
        (Cursor.resume M C charge allowance earlier).1 }
  | ⟨paid, .done _result⟩ => ⟨.nil, Nat.add_zero paid⟩
  | ⟨paid, .paused packet⟩ =>
      ⟨advanceHistory M C charge allowance packet,
        congrArg (paid + ·) (advanceHistory_paid M C charge allowance packet)⟩

/-- The suffix begins at the exact retained outcome, including its live
capability, control, and provider state. It does not restart the client. -/
def resumeHistory (charge : Cursor.Charge M) (allowance : Nat) {base : Base}
    (earlier : Nat × Cursor.Outcome M C base) :
    History (system M C base) ⟨earlier.2⟩
      ⟨(Cursor.resume M C charge allowance earlier).2⟩ :=
  (accountedResumeHistory M C charge allowance earlier).val

theorem resumeHistory_paid (charge : Cursor.Charge M) (allowance : Nat) {base : Base}
    (earlier : Nat × Cursor.Outcome M C base) :
    earlier.1 + Multiplicative.toAdd ((providerAccount M C charge base).of
      (resumeHistory M C charge allowance earlier)) =
      (Cursor.resume M C charge allowance earlier).1 :=
  (accountedResumeHistory M C charge allowance earlier).property

/-- Concatenate actual prefix and suffix histories. Chronological composition
has the full combined account, and the existing split law identifies its
complete endpoint and paid meter with an unsplit cursor execution. This law
does not identify two native recording buffers. -/
theorem chunkHistory_paid (charge : Cursor.Charge M) (first second : Nat) {base : Base}
    (packet : Cursor.Packet M C base) :
    Multiplicative.toAdd ((providerAccount M C charge base).of
      ((advanceHistory M C charge first packet).comp
        (resumeHistory M C charge second (Cursor.advance M C charge first packet)))) =
      (Cursor.advance M C charge (first + second) packet).1 := by
  have composed := congrArg Multiplicative.toAdd
    ((providerAccount M C charge base).of_comp (advanceHistory M C charge first packet)
      (resumeHistory M C charge second (Cursor.advance M C charge first packet)))
  have earlierPaid := advanceHistory_paid M C charge first packet
  have suffix := resumeHistory_paid M C charge second (Cursor.advance M C charge first packet)
  have total := composed.trans
    ((congrArg (· + Multiplicative.toAdd ((providerAccount M C charge base).of
      (resumeHistory M C charge second (Cursor.advance M C charge first packet)))) earlierPaid).trans
      suffix)
  exact total.trans (congrArg Prod.fst (Cursor.advance_add M C charge first second packet)).symm

private theorem transportedValue {Key : Type*} {left right : Key}
    {Data : Key → Type*} {Property : (key : Key) → Data key → Prop}
    (same : left = right) (value : { data : Data left // Property left data }) :
    HEq ((same ▸ value : { data : Data right // Property right data }).val) value.val := by
  cases same
  rfl

/-- Empty allowance contains no inspection or provider event. -/
@[simp] theorem advanceHistory_zero (charge : Cursor.Charge M) {base : Base}
    (packet : Cursor.Packet M C base) :
    advanceHistory M C charge 0 packet = .nil := rfl

/-- A return inspection records exactly one finish event, independently of
unused allowance. Heterogeneous equality retains the dependent endpoint. -/
theorem advanceHistory_finish (charge : Cursor.Charge M) (allowance : Nat)
    {base : Base} {index : Index base} (control : C.V base index)
    (state : M.State base index) (answer : Return base index)
    (children : (position : (P.withHoles Return).Position (.inl answer)) →
      C.V base ((P.withHoles Return).next (.inl answer) position))
    (exposed : C.str base index control = ⟨.inl answer, children⟩) :
    HEq (advanceHistory M C charge (allowance + 1) ⟨index, control, state⟩)
      (show History (system M C base)
        ⟨.paused ⟨index, control, state⟩⟩ ⟨.done ⟨index, answer, state⟩⟩ from
        (show (⟨.paused ⟨index, control, state⟩⟩ : State (system M C base)) ⟶
          ⟨.done ⟨index, answer, state⟩⟩ from
          Event.finish (M := M) (C := C) control state answer children exposed).toPath) := by
  simp only [advanceHistory, accountedAdvanceHistory]
  split
  next value empty spotted =>
    have same := spotted.symm.trans exposed
    cases same
    exact transportedValue
      (Key := Nat × Cursor.Outcome M C base)
      (Data := fun result => History (system M C base)
        ⟨.paused ⟨index, control, state⟩⟩ ⟨result.2⟩)
      (Property := fun result history =>
        Multiplicative.toAdd ((providerAccount M C charge base).of history) = result.1) _ _
  next value branches spotted =>
    have same := congrArg Sigma.fst (spotted.symm.trans exposed)
    cases same

/-- A request event precedes the history of its actual reply-selected child.
This equation retains event data rather than merely its charge. -/
theorem advanceHistory_request (charge : Cursor.Charge M) (allowance : Nat)
    {base : Base} {index : Index base} (control : C.V base index)
    (state : M.State base index) (request : P.Shape base index)
    (children : (reply : P.Position request) → C.V base (P.next request reply))
    (exposed : C.str base index control = ⟨.inr request, children⟩) :
    let next : Cursor.Packet M C base :=
      ⟨_, children (M.step state request).1, (M.step state request).2⟩
    HEq (advanceHistory M C charge (allowance + 1) ⟨index, control, state⟩)
      ((show (⟨.paused ⟨index, control, state⟩⟩ : State (system M C base)) ⟶
          ⟨.paused next⟩ from
        Event.request (M := M) (C := C) control state request children exposed).toPath.comp
          (advanceHistory M C charge allowance next)) := by
  dsimp only
  simp only [advanceHistory, accountedAdvanceHistory]
  split
  next value empty spotted =>
    have same := congrArg Sigma.fst (spotted.symm.trans exposed)
    cases same
  next value branches spotted =>
    have same := spotted.symm.trans exposed
    cases same
    exact transportedValue
      (Key := Nat × Cursor.Outcome M C base)
      (Data := fun result => History (system M C base)
        ⟨.paused ⟨index, control, state⟩⟩ ⟨result.2⟩)
      (Property := fun result history =>
        Multiplicative.toAdd ((providerAccount M C charge base).of history) = result.1) _ _

/-- Paid-prefix bookkeeping does not add events to the resume suffix. -/
theorem resumeHistory_add_paid (charge : Cursor.Charge M) (allowance extra : Nat)
    {base : Base} (earlier : Nat × Cursor.Outcome M C base) :
    HEq (resumeHistory M C charge allowance (extra + earlier.1, earlier.2))
      (resumeHistory M C charge allowance earlier) := by
  rcases earlier with ⟨paid, outcome⟩
  cases outcome <;> rfl

private theorem composeHistoriesHEq {S : ProofRelevantGSLT.{u}}
    {before middleLeft middleRight afterLeft afterRight : State S}
    (middleSame : middleLeft = middleRight) (afterSame : afterLeft = afterRight)
    (leftPrefix : History S before middleLeft) (rightPrefix : History S before middleRight)
    (leftSuffix : History S middleLeft afterLeft) (rightSuffix : History S middleRight afterRight)
    (prefixSame : HEq leftPrefix rightPrefix) (suffixSame : HEq leftSuffix rightSuffix) :
    HEq (leftPrefix.comp leftSuffix) (rightPrefix.comp rightSuffix) := by
  cases middleSame
  cases afterSame
  exact heq_of_eq (congrArg₂ Quiver.Path.comp (eq_of_heq prefixSame) (eq_of_heq suffixSame))

/-- Every budget partition preserves the full chronological event path,
including repeated occurrences and the final uncharged return inspection.
Endpoint transport is along the independently proved complete cursor split
law; there is no quotient by costs or by endpoint-only observations. -/
theorem chunkHistory_exact (charge : Cursor.Charge M) (first second : Nat) {base : Base}
    (packet : Cursor.Packet M C base) :
    HEq (advanceHistory M C charge (first + second) packet)
      ((advanceHistory M C charge first packet).comp
        (resumeHistory M C charge second (Cursor.advance M C charge first packet))) := by
  induction first generalizing packet with
  | zero =>
      rw [Nat.zero_add]
      change HEq (advanceHistory M C charge second packet)
        (Quiver.Path.nil.comp (advanceHistory M C charge second packet))
      exact heq_of_eq (Quiver.Path.nil_comp _).symm
  | succ first ih =>
      rcases packet with ⟨index, control, state⟩
      rw [Nat.succ_add]
      cases layer : C.str base index control with
      | mk shape children =>
          cases shape with
          | inl answer =>
              have whole := advanceHistory_finish M C charge (first + second)
                control state answer children layer
              have earlier := advanceHistory_finish M C charge first
                control state answer children layer
              let finished : Cursor.Finished M base := ⟨index, answer, state⟩
              let event : (⟨.paused ⟨index, control, state⟩⟩ : State (system M C base)) ⟶
                  ⟨.done finished⟩ :=
                Event.finish (M := M) (C := C) control state answer children layer
              have moved : Cursor.advance M C charge (first + 1) ⟨index, control, state⟩ =
                  (0, .done finished) := by
                simp [Cursor.advance, layer, finished]
              have middleSame : (⟨(Cursor.advance M C charge (first + 1)
                  ⟨index, control, state⟩).2⟩ : State (system M C base)) = ⟨.done finished⟩ :=
                congrArg (fun result => (⟨result.2⟩ : State (system M C base))) moved
              have suffixSame :
                  HEq (resumeHistory M C charge second
                    (Cursor.advance M C charge (first + 1) ⟨index, control, state⟩))
                    (show History (system M C base) ⟨.done finished⟩ ⟨.done finished⟩ from .nil) := by
                rw [moved]
                rfl
              have afterSame : (⟨(Cursor.resume M C charge second
                  (Cursor.advance M C charge (first + 1) ⟨index, control, state⟩)).2⟩ :
                  State (system M C base)) = ⟨.done finished⟩ := by
                rw [moved]
                rfl
              have chunkSame := composeHistoriesHEq middleSame afterSame
                (advanceHistory M C charge (first + 1) ⟨index, control, state⟩) event.toPath
                (resumeHistory M C charge second
                  (Cursor.advance M C charge (first + 1) ⟨index, control, state⟩))
                (show History (system M C base) ⟨.done finished⟩ ⟨.done finished⟩ from .nil)
                earlier suffixSame
              exact whole.trans
                (chunkSame.trans (heq_of_eq (Quiver.Path.comp_nil event.toPath))).symm
          | inr request =>
              dsimp only [withHoles] at children
              let next : Cursor.Packet M C base :=
                ⟨_, children (M.step state request).1, (M.step state request).2⟩
              let event : (⟨.paused ⟨index, control, state⟩⟩ : State (system M C base)) ⟶
                  ⟨.paused next⟩ :=
                Event.request (M := M) (C := C) control state request children layer
              let earlier := Cursor.advance M C charge first next
              have moved : Cursor.advance M C charge (first + 1) ⟨index, control, state⟩ =
                  (charge state request + earlier.1, earlier.2) := by
                simp only [Cursor.advance, layer]
                rfl
              have middleSame : (⟨(Cursor.advance M C charge (first + 1)
                  ⟨index, control, state⟩).2⟩ : State (system M C base)) = ⟨earlier.2⟩ :=
                congrArg (fun result => (⟨result.2⟩ : State (system M C base))) moved
              have suffixSame :
                  HEq (resumeHistory M C charge second
                    (Cursor.advance M C charge (first + 1) ⟨index, control, state⟩))
                    (resumeHistory M C charge second earlier) := by
                rw [moved]
                exact resumeHistory_add_paid M C charge second (charge state request) earlier
              have afterSame : (⟨(Cursor.resume M C charge second
                  (Cursor.advance M C charge (first + 1) ⟨index, control, state⟩)).2⟩ :
                  State (system M C base)) = ⟨(Cursor.resume M C charge second earlier).2⟩ := by
                rw [moved, Cursor.resume_add_charge]
              have prefixSame := advanceHistory_request M C charge first
                control state request children layer
              have chunkSame := composeHistoriesHEq middleSame afterSame
                (advanceHistory M C charge (first + 1) ⟨index, control, state⟩)
                (event.toPath.comp (advanceHistory M C charge first next))
                (resumeHistory M C charge second
                  (Cursor.advance M C charge (first + 1) ⟨index, control, state⟩))
                (resumeHistory M C charge second earlier) prefixSame suffixSame
              have splitEndpoint : (⟨(Cursor.advance M C charge (first + second) next).2⟩ :
                  State (system M C base)) = ⟨(Cursor.resume M C charge second earlier).2⟩ :=
                congrArg (fun result => (⟨result.2⟩ : State (system M C base)))
                  (Cursor.advance_add M C charge first second next)
              have tailSame := composeHistoriesHEq rfl splitEndpoint event.toPath event.toPath
                (advanceHistory M C charge (first + second) next)
                ((advanceHistory M C charge first next).comp (resumeHistory M C charge second earlier))
                (HEq.rfl) (ih next)
              have associated := heq_of_eq
                (Quiver.Path.comp_assoc event.toPath (advanceHistory M C charge first next)
                  (resumeHistory M C charge second earlier)).symm
              exact (advanceHistory_request M C charge (first + second)
                control state request children layer).trans
                  (tailSame.trans (associated.trans chunkSame.symm))

/-- Resuming an already paid outcome obeys the same complete history split
law. Prefix bookkeeping is retained without becoming another event. -/
theorem resumeHistory_add_exact (charge : Cursor.Charge M) (first second : Nat)
    {base : Base} (previous : Nat × Cursor.Outcome M C base) :
    HEq (resumeHistory M C charge (first + second) previous)
      ((resumeHistory M C charge first previous).comp
        (resumeHistory M C charge second (Cursor.resume M C charge first previous))) := by
  rcases previous with ⟨paid, outcome⟩
  cases outcome with
  | done result => rfl
  | paused packet =>
      let earlier := Cursor.advance M C charge first packet
      have suffixSame :
          HEq (resumeHistory M C charge second
            (Cursor.resume M C charge first (paid, .paused packet)))
            (resumeHistory M C charge second earlier) :=
        resumeHistory_add_paid M C charge second paid earlier
      have afterSame : (⟨(Cursor.resume M C charge second
          (Cursor.resume M C charge first (paid, .paused packet))).2⟩ :
          State (system M C base)) = ⟨(Cursor.resume M C charge second earlier).2⟩ := by
        change (⟨(Cursor.resume M C charge second (paid + earlier.1, earlier.2)).2⟩ :
          State (system M C base)) = _
        rw [Cursor.resume_add_charge]
      have chunks := composeHistoriesHEq rfl afterSame
        (resumeHistory M C charge first (paid, .paused packet))
        (advanceHistory M C charge first packet)
        (resumeHistory M C charge second
          (Cursor.resume M C charge first (paid, .paused packet)))
        (resumeHistory M C charge second earlier) (HEq.rfl) suffixSame
      exact (chunkHistory_exact M C charge first second packet).trans chunks.symm

namespace Controls

/-- The delayed duplicate-producing client retains the full event path over
a two-plus-three split, including its suspension and uncharged finish. -/
theorem delayed_chunk_keeps_occurrences :
    HEq (advanceHistory (provider NativeControlCursor.Controls.delayed) (client Nat)
      (fun _ _ => 1) 5 (packet NativeControlCursor.Controls.delayed 0 []))
      ((advanceHistory (provider NativeControlCursor.Controls.delayed) (client Nat)
        (fun _ _ => 1) 2 (packet NativeControlCursor.Controls.delayed 0 [])).comp
        (resumeHistory (provider NativeControlCursor.Controls.delayed) (client Nat)
          (fun _ _ => 1) 3
          (Cursor.advance (provider NativeControlCursor.Controls.delayed) (client Nat)
            (fun _ _ => 1) 2 (packet NativeControlCursor.Controls.delayed 0 [])))) :=
  chunkHistory_exact _ _ _ 2 3 _

/-- Equal full endpoints and meters do not determine occurrence histories.
Two uncharged suspensions can revisit the same state; their two occurrences
remain different from the single-event prefix. -/
theorem endpoint_meter_can_hide_occurrences :
    let pull : Unit → Pull Unit Nat := fun state => .suspend state
    let initial := packet pull () []
    Cursor.advance (provider pull) (client Nat) (fun _ _ => 0) 1 initial =
        Cursor.advance (provider pull) (client Nat) (fun _ _ => 0) 2 initial ∧
      (advanceHistory (provider pull) (client Nat) (fun _ _ => 0) 1 initial).length ≠
        (advanceHistory (provider pull) (client Nat) (fun _ _ => 0) 2 initial).length := by
  constructor
  · rfl
  · decide

/-- Suspension and two duplicate yields remain in the chronological path;
exhaustion and return inspection are separate events. -/
theorem delayed_history_keeps_inspections :
    (advanceHistory (provider NativeControlCursor.Controls.delayed) (client Nat)
      (fun _ _ => 1) 5 (packet NativeControlCursor.Controls.delayed 0 [])).length = 5 := rfl

/-- Four actual provider polls precede the final, uncharged return inspection. -/
theorem delayed_history_paid :
    Multiplicative.toAdd
      ((providerAccount (provider NativeControlCursor.Controls.delayed) (client Nat)
        (fun _ _ => 1) ()).of
          (advanceHistory (provider NativeControlCursor.Controls.delayed) (client Nat)
            (fun _ _ => 1) 5 (packet NativeControlCursor.Controls.delayed 0 []))) = 4 := by
  rw [advanceHistory_paid]
  rfl

/-- A paused duplicate-producing collector resumes its retained occurrence
history. The two already performed polls remain paid exactly once. -/
theorem delayed_chunk_keeps_paid_prefix :
    Multiplicative.toAdd
      ((providerAccount (provider NativeControlCursor.Controls.delayed) (client Nat)
        (fun _ _ => 1) ()).of
          ((advanceHistory (provider NativeControlCursor.Controls.delayed) (client Nat)
            (fun _ _ => 1) 2 (packet NativeControlCursor.Controls.delayed 0 [])).comp
          (resumeHistory (provider NativeControlCursor.Controls.delayed) (client Nat)
            (fun _ _ => 1) 3
            (Cursor.advance (provider NativeControlCursor.Controls.delayed) (client Nat)
              (fun _ _ => 1) 2 (packet NativeControlCursor.Controls.delayed 0 []))))) = 4 := by
  rw [chunkHistory_paid]
  rfl

/-- A completed collector cannot gain another request, poll charge, or event
when it is resumed with a larger allowance. -/
theorem completed_resume_history_is_empty :
    (resumeHistory (provider NativeControlCursor.Controls.delayed) (client Nat)
      (fun _ _ => 1) 10
      (Cursor.advance (provider NativeControlCursor.Controls.delayed) (client Nat)
        (fun _ _ => 1) 5 (packet NativeControlCursor.Controls.delayed 0 []))).length = 0 := rfl

/-- Charging only successful yields drops the suspension and exhaustion
requests and cannot represent this provider account. -/
theorem counting_yields_is_not_provider_account :
    Multiplicative.toAdd
      ((providerAccount (provider NativeControlCursor.Controls.delayed) (client Nat)
        (fun _ _ => 1) ()).of
          (advanceHistory (provider NativeControlCursor.Controls.delayed) (client Nat)
            (fun _ _ => 1) 5 (packet NativeControlCursor.Controls.delayed 0 []))) ≠ 2 := by
  rw [delayed_history_paid]
  decide

end Controls



/-- Mapping a retained path respects explicit dependent endpoint transport. -/
private theorem mapHistoryHEq {S T : ProofRelevantGSLT.{u}}
    (f : ForwardEvidenceMap S T)
    {before leftAfter rightAfter : State S}
    (same : leftAfter = rightAfter)
    (left : History S before leftAfter) (right : History S before rightAfter)
    (paths : HEq left right) :
    HEq (f.histories.map left) (f.histories.map right) := by
  cases same
  exact heq_of_eq (congrArg f.histories.map (eq_of_heq paths))

private theorem eventPathHEq {S : ProofRelevantGSLT.{u}}
    {before leftAfter rightAfter : State S}
    (same : leftAfter = rightAfter)
    (left : before ⟶ leftAfter) (right : before ⟶ rightAfter)
    (events : HEq left right) : HEq left.toPath right.toPath := by
  cases same
  exact heq_of_eq (congrArg Quiver.Hom.toPath (eq_of_heq events))

/-- Generate an actual bounded history after a lawful provider translation,
or translate the generated history. Both retain the same events, replies,
continuations and occurrence order. Local cost calibration is separate. -/
theorem hom_advanceHistory {source target : Cursor.Provider P}
    (h : Cursor.Hom source target)
    (sourceCharge : Cursor.Charge source) (targetCharge : Cursor.Charge target)
    (allowance : Nat) {base : Base} (packet : Cursor.Packet source C base) :
    HEq ((homForward C h base).histories.map
      (advanceHistory source C sourceCharge allowance packet))
      (advanceHistory target C targetCharge allowance (h.packet C packet)) := by
  induction allowance generalizing packet with
  | zero =>
      simp only [advanceHistory_zero]
      rfl
  | succ allowance ih =>
      rcases packet with ⟨index, control, state⟩
      cases exposed : C.str base index control with
      | mk shape children =>
          cases shape with
          | inl answer =>
              have sourceEnd :
                  (⟨(Cursor.advance source C sourceCharge (allowance + 1)
                    ⟨index,control,state⟩).2⟩ : State (system source C base)) =
                    ⟨.done ⟨index,answer,state⟩⟩ := by
                simp only [Cursor.advance,exposed]
              have mapped := mapHistoryHEq (homForward C h base) sourceEnd _ _
                (advanceHistory_finish source C sourceCharge allowance control state
                  answer children exposed)
              have targetHistory := advanceHistory_finish target C targetCharge allowance
                control (h.map state) answer children exposed
              apply HEq.trans mapped
              rw [ForwardEvidenceMap.histories_generator]
              exact HEq.trans (by rfl) targetHistory.symm
          | inr request =>
              dsimp only [withHoles] at children
              let next : Cursor.Packet source C base :=
                ⟨_,children (source.step state request).1,(source.step state request).2⟩
              have sourceEnd :
                  (⟨(Cursor.advance source C sourceCharge (allowance + 1)
                    ⟨index,control,state⟩).2⟩ : State (system source C base)) =
                    ⟨(Cursor.advance source C sourceCharge allowance next).2⟩ := by
                simp only [Cursor.advance,exposed]
                rfl
              have mapped := mapHistoryHEq (homForward C h base) sourceEnd _ _
                (advanceHistory_request source C sourceCharge allowance control state
                  request children exposed)
              have targetHistory := advanceHistory_request target C targetCharge allowance
                control (h.map state) request children exposed
              apply HEq.trans mapped
              erw [Functor.map_comp]
              rw [ForwardEvidenceMap.histories_generator]
              have nextSame : h.packet C next =
                  ⟨_,children (target.step (h.map state) request).1,
                    (target.step (h.map state) request).2⟩ := by
                dsimp only [Cursor.Hom.packet,next]
                rw [← h.step state request]
              have afterSame :
                  (⟨h.outcome C (Cursor.advance source C sourceCharge allowance next).2⟩ :
                    State (system target C base)) =
                  ⟨(Cursor.advance target C targetCharge allowance (h.packet C next)).2⟩ := by
                exact congrArg State.mk (h.advance C sourceCharge targetCharge allowance next)
              have tailSame := ih next
              rw [nextSame] at tailSame afterSame
              have prefixSame : HEq
                  ((homForward C h base).mapEvidence
                    (Event.request (M:=source) (C:=C) control state request children exposed))
                  (Event.request (M:=target) (C:=C) control (h.map state)
                    request children exposed) := by
                dsimp only [homForward]
                exact cast_heq _ _
              have middleSame :
                  (⟨h.outcome C (.paused next)⟩ : State (system target C base)) =
                    ⟨.paused ⟨_,children (target.step (h.map state) request).1,
                      (target.step (h.map state) request).2⟩⟩ :=
                congrArg (fun value => (⟨.paused value⟩ : State (system target C base))) nextSame
              exact HEq.trans (composeHistoriesHEq middleSame
                afterSame _ _ _ _ (eventPathHEq middleSame _ _ prefixSame)
                tailSame) targetHistory.symm



/-- Two successive provider interpretations agree with executing their
composite on the full generated history, not just on terminal values. -/
theorem hom_advanceHistory_comp {first middle last : Cursor.Provider P}
    (earlier : Cursor.Hom first middle) (later : Cursor.Hom middle last)
    (firstCharge : Cursor.Charge first) (middleCharge : Cursor.Charge middle)
    (lastCharge : Cursor.Charge last) (allowance : Nat) {base : Base}
    (packet : Cursor.Packet first C base) :
    HEq ((homForward C later base).histories.map
      ((homForward C earlier base).histories.map
        (advanceHistory first C firstCharge allowance packet)))
      (advanceHistory last C lastCharge allowance ((earlier.comp later).packet C packet)) := by
  have endpoint :
      (⟨earlier.outcome C (Cursor.advance first C firstCharge allowance packet).2⟩ :
        State (system middle C base)) =
      ⟨(Cursor.advance middle C middleCharge allowance (earlier.packet C packet)).2⟩ :=
    congrArg State.mk (earlier.advance C firstCharge middleCharge allowance packet)
  have mapped := mapHistoryHEq (homForward C later base) endpoint _ _
    (hom_advanceHistory C earlier firstCharge middleCharge allowance packet)
  exact mapped.trans (hom_advanceHistory C later middleCharge lastCharge allowance
    (earlier.packet C packet))


/-- A many-valued provider relation has one constructed common history whose
projections are the independently generated histories on both sides. The
common provider is a mathematical span; this does not run two native effects
or select one physical representative from a relation's fibre. -/
theorem coupled_advance_histories {source target : Cursor.Provider P}
    (rel : Cursor.StateRel source target) (localLaw : Cursor.Bisimulation rel)
    (commonCharge : Cursor.Charge (Cursor.Bisimulation.coupledProvider rel localLaw))
    (sourceCharge : Cursor.Charge source) (targetCharge : Cursor.Charge target)
    (allowance : Nat) {base : Base} {index : Index base}
    (control : C.V base index) (left : source.State base index)
    (right : target.State base index) (related : rel left right) :
    let common : Cursor.Packet (Cursor.Bisimulation.coupledProvider rel localLaw) C base :=
      ⟨index,control,⟨(left,right),related⟩⟩
    let history := advanceHistory (Cursor.Bisimulation.coupledProvider rel localLaw)
      C commonCharge allowance common
    HEq ((homForward C (Cursor.Bisimulation.leftProjection rel localLaw) base).histories.map
        history) (advanceHistory source C sourceCharge allowance ⟨index,control,left⟩) ∧
      HEq ((homForward C (Cursor.Bisimulation.rightProjection rel localLaw) base).histories.map
        history) (advanceHistory target C targetCharge allowance ⟨index,control,right⟩) := by
  dsimp only
  exact ⟨hom_advanceHistory C (Cursor.Bisimulation.leftProjection rel localLaw)
      commonCharge sourceCharge allowance _,
    hom_advanceHistory C (Cursor.Bisimulation.rightProjection rel localLaw)
      commonCharge targetCharge allowance _⟩

/-- Resuming a retained outcome commutes with a lawful provider map on the
full chronological suffix. The paid prefix remains bookkeeping; comparing
its valuation requires the independently stated local account law. -/
theorem hom_resumeHistory {source target : Cursor.Provider P}
    (h : Cursor.Hom source target)
    (sourceCharge : Cursor.Charge source) (targetCharge : Cursor.Charge target)
    (allowance : Nat) {base : Base} (earlier : Nat × Cursor.Outcome source C base) :
    HEq ((homForward C h base).histories.map
      (resumeHistory source C sourceCharge allowance earlier))
      (resumeHistory target C targetCharge allowance
        (earlier.1,h.outcome C earlier.2)) := by
  rcases earlier with ⟨paid,outcome⟩
  cases outcome with
  | done result => rfl
  | paused packet => exact hom_advanceHistory C h sourceCharge targetCharge allowance packet

namespace ClientTransport

variable {first second : Cursor.Client (P := P) (Return := Return)}

/-- A continuation representation map changes client control while retaining
actual provider requests, replies, worlds and capability indices. Its local
coalgebra law is required; arbitrary source rewriting is not such a map. -/
def forward (h : first ⟶ second) (base : Base) :
    ForwardEvidenceMap (system M first base) (system M second base) where
  mapTerm := Cursor.ClientMap.outcome M h
  mapEquiv := fun same => congrArg (Cursor.ClientMap.outcome M h) same
  mapEvidence := by
    intro before after event
    cases event with
    | request control state request children exposed =>
      have law := congrArg (fun mapping => mapping base _ control) h.h
      change Extension.map (P.withHoles Return) (fun b i => h.f b i)
          (first.str base _ control) = second.str base _ (h.f base _ control) at law
      rw [exposed] at law
      exact Event.request (M := M) (C := second) (h.f base _ control) state request
        (fun reply => h.f base _ (children reply)) law.symm
    | finish control state answer children exposed =>
      have law := congrArg (fun mapping => mapping base _ control) h.h
      change Extension.map (P.withHoles Return) (fun b i => h.f b i)
          (first.str base _ control) = second.str base _ (h.f base _ control) at law
      rw [exposed] at law
      exact Event.finish (M := M) (C := second) (h.f base _ control) state answer
        (fun reply => h.f base _ (children reply)) law.symm

/-- Continuation translation commutes with the declared endpoint-step
readout. This readout forgets evidence and provides no event decoder. -/
theorem histories_erasure (h : first ⟶ second) (base : Base) :
    (forward M h base).histories ⋙ eraseHistory (system M second base) =
      eraseHistory (system M first base) ⋙ (forward M h base).erasedHistories :=
  ForwardEvidenceMap.histories_erasure _

/-- A translated event retains the provider's actual pre-state and request,
so its independently declared provider charge is unchanged. -/
theorem eventExpense_preserved (h : first ⟶ second) (charge : Cursor.Charge M)
    {base : Base} {before after : Cursor.Outcome M first base}
    (event : Event M first base before after) :
    eventExpense M second charge ((forward M h base).mapEvidence event) =
      eventExpense M first charge event := by
  cases event <;> rfl


/-- A locally calibrated chronological account survives continuation
translation. Its monoid can retain ordered words or several cost components. -/
theorem account_preserved (h : first ⟶ second) (base : Base)
    {LeftValue RightValue : Type v} [Monoid LeftValue] [Monoid RightValue]
    (leftValue : {before after : Cursor.Outcome M first base} →
      Event M first base before after → LeftValue)
    (rightValue : {before after : Cursor.Outcome M second base} →
      Event M second base before after → RightValue)
    (change : LeftValue →* RightValue)
    (localLaw : ∀ {before after} (event : Event M first base before after),
      rightValue ((forward M h base).mapEvidence event) = change (leftValue event)) :
    (eventAccount M second base rightValue).comap (forward M h base).histories =
      (eventAccount M first base leftValue).map change := by
  rw [← PathEvidenceMap.histories_ofForward]
  apply PathEvidenceMap.account_preserved
  intro before after event
  dsimp only [PathEvidenceMap.ofForward]
  rw [eventAccount_generator, eventAccount_generator]
  exact localLaw event

/-- Translating client continuations before execution or afterward produces
the same full generated history. Local coalgebra preservation fixes each
request and every reply-indexed continuation, without replaying the provider. -/
theorem advanceHistory_map (h : first ⟶ second) (charge : Cursor.Charge M)
    (allowance : Nat) {base : Base} (packet : Cursor.Packet M first base) :
    HEq ((forward M h base).histories.map
      (advanceHistory M first charge allowance packet))
      (advanceHistory M second charge allowance (Cursor.ClientMap.packet M h packet)) := by
  induction allowance generalizing packet with
  | zero =>
      simp only [advanceHistory_zero]
      rfl
  | succ allowance ih =>
      rcases packet with ⟨index, control, state⟩
      have law := congrArg (fun mapping => mapping base index control) h.h
      change Extension.map (P.withHoles Return) (fun b i => h.f b i)
          (first.str base index control) = second.str base index (h.f base index control) at law
      cases exposed : first.str base index control with
      | mk shape children =>
          rw [exposed] at law
          cases shape with
          | inl answer =>
              have targetExposed : second.str base index (h.f base index control) =
                  ⟨.inl answer, fun position => h.f base _ (children position)⟩ := law.symm
              have sourceEnd :
                  (⟨(Cursor.advance M first charge (allowance + 1)
                    ⟨index,control,state⟩).2⟩ : State (system M first base)) =
                    ⟨.done ⟨index,answer,state⟩⟩ := by
                simp only [Cursor.advance,exposed]
              have mapped := mapHistoryHEq (forward M h base) sourceEnd _ _
                (advanceHistory_finish M first charge allowance control state
                  answer children exposed)
              have targetHistory := advanceHistory_finish M second charge allowance
                (h.f base index control) state answer
                (fun position => h.f base _ (children position)) targetExposed
              apply HEq.trans mapped
              rw [ForwardEvidenceMap.histories_generator]
              exact HEq.trans (by rfl) targetHistory.symm
          | inr request =>
              dsimp only [withHoles] at children
              have targetExposed : second.str base index (h.f base index control) =
                  ⟨.inr request, fun reply => h.f base _ (children reply)⟩ := law.symm
              let next : Cursor.Packet M first base :=
                ⟨_,children (M.step state request).1,(M.step state request).2⟩
              have sourceEnd :
                  (⟨(Cursor.advance M first charge (allowance + 1)
                    ⟨index,control,state⟩).2⟩ : State (system M first base)) =
                    ⟨(Cursor.advance M first charge allowance next).2⟩ := by
                simp only [Cursor.advance,exposed]
                rfl
              have mapped := mapHistoryHEq (forward M h base) sourceEnd _ _
                (advanceHistory_request M first charge allowance control state
                  request children exposed)
              have targetHistory := advanceHistory_request M second charge allowance
                (h.f base index control) state request
                (fun reply => h.f base _ (children reply)) targetExposed
              apply HEq.trans mapped
              erw [Functor.map_comp]
              rw [ForwardEvidenceMap.histories_generator]
              have afterSame :
                  (⟨Cursor.ClientMap.outcome M h
                    (Cursor.advance M first charge allowance next).2⟩ :
                    State (system M second base)) =
                  ⟨(Cursor.advance M second charge allowance
                    (Cursor.ClientMap.packet M h next)).2⟩ :=
                congrArg State.mk
                  (congrArg Prod.snd (Cursor.ClientMap.advance M h charge allowance next))
              have tailSame := ih next
              have prefixSame : HEq
                  ((forward M h base).mapEvidence
                    (Event.request (M:=M) (C:=first) control state request children exposed))
                  (Event.request (M:=M) (C:=second) (h.f base index control) state request
                    (fun reply => h.f base _ (children reply)) targetExposed) := by rfl
              have middleSame :
                  (⟨Cursor.ClientMap.outcome M h (.paused next)⟩ :
                    State (system M second base)) =
                  ⟨.paused ⟨_, h.f base _ (children (M.step state request).1),
                    (M.step state request).2⟩⟩ := rfl
              exact HEq.trans (composeHistoriesHEq middleSame afterSame _ _ _ _
                (eventPathHEq middleSame _ _ prefixSame) tailSame) targetHistory.symm

/-- A resumed suffix keeps its exact chronological history under a lawful
continuation translation, including the empty suffix of a completed result. -/
theorem resumeHistory_map (h : first ⟶ second) (charge : Cursor.Charge M)
    (allowance : Nat) {base : Base} (earlier : Nat × Cursor.Outcome M first base) :
    HEq ((forward M h base).histories.map
      (resumeHistory M first charge allowance earlier))
      (resumeHistory M second charge allowance
        (earlier.1,Cursor.ClientMap.outcome M h earlier.2)) := by
  rcases earlier with ⟨paid,outcome⟩
  cases outcome with
  | done result => rfl
  | paused packet => exact advanceHistory_map M h charge allowance packet

/-- Composition changes the control layout twice while retaining one actual
provider execution and its complete history. -/
theorem advanceHistory_map_comp
    {middle last : Cursor.Client (P := P) (Return := Return)}
    (earlier : first ⟶ middle) (later : middle ⟶ last) (charge : Cursor.Charge M)
    (allowance : Nat) {base : Base} (packet : Cursor.Packet M first base) :
    HEq ((forward M later base).histories.map
      ((forward M earlier base).histories.map
        (advanceHistory M first charge allowance packet)))
      (advanceHistory M last charge allowance
        (Cursor.ClientMap.packet M (earlier ≫ later) packet)) := by
  have endpoint :
      (⟨Cursor.ClientMap.outcome M earlier
        (Cursor.advance M first charge allowance packet).2⟩ :
        State (system M middle base)) =
      ⟨(Cursor.advance M middle charge allowance
        (Cursor.ClientMap.packet M earlier packet)).2⟩ :=
    congrArg State.mk
      (congrArg Prod.snd (Cursor.ClientMap.advance M earlier charge allowance packet))
  have mapped := mapHistoryHEq (forward M later base) endpoint _ _
    (advanceHistory_map M earlier charge allowance packet)
  exact mapped.trans (advanceHistory_map M later charge allowance
    (Cursor.ClientMap.packet M earlier packet))


namespace Controls

/-- This representation counts every actual provider reply in its control.
The count is independent of equal answer payloads and of the provider state. -/
def taggedCollector (Answer : Type) :
    Cursor.Client (P := protocol Answer) (Return := fun _ _ => List Answer) where
  V _ _ := Nat × Cursor.Fold.State (List Answer)
  str := fun _ _ => ↾(fun state => match state.2 with
    | .finished values => ⟨.inl values, fun impossible => nomatch impossible⟩
    | .pulling reversed => ⟨.inr (), fun reply => match reply with
        | .done => (state.1 + 1,.finished reversed.reverse)
        | .yield value _ => (state.1 + 1,.pulling (value :: reversed))
        | .suspend _ => (state.1 + 1,.pulling reversed)⟩)

/-- The actual control representation maps to the independently defined
collector, preserving its request and all possible reply-selected children. -/
def forgetCollectorTag (Answer : Type) : taggedCollector Answer ⟶ client Answer where
  f := fun _ _ => ↾(fun state => state.2)
  h := by
    funext base index
    apply ConcreteCategory.hom_ext
    intro state
    change Extension.map ((protocol Answer).withHoles (fun _ _ => List Answer))
        (fun _ _ (value : Nat × Cursor.Fold.State (List Answer)) => value.2)
        ((taggedCollector Answer).str base index state) =
      (client Answer).str base index state.2
    rcases state with ⟨tag,state⟩
    cases state with
    | finished values =>
        refine Sigma.ext (by rfl) ?_
        apply heq_of_eq
        funext impossible
        exact nomatch impossible
    | pulling reversed =>
        refine Sigma.ext (by rfl) ?_
        apply heq_of_eq
        funext reply
        cases reply <;> rfl

/-- A suspension and a yield advance the private control count separately.
Forgetting the count retains all five generated event occurrences. -/
theorem tagged_control_keeps_occurrences :
    Cursor.advance (provider NativeControlCursor.Controls.delayed) (taggedCollector Nat)
        (fun _ _ => 1) 2 (base := ()) ⟨(),(42,.pulling []),(0 : Nat)⟩ =
      (2,.paused ⟨(),(44,.pulling [7]),(2 : Nat)⟩) ∧
    ((forward (provider NativeControlCursor.Controls.delayed) (forgetCollectorTag Nat) ()).histories.map (advanceHistory (provider NativeControlCursor.Controls.delayed)
        (taggedCollector Nat) (fun _ _ => 1) 5 (base := ()) ⟨(),(42,.pulling []),(0 : Nat)⟩)).length = 5 := by
  constructor
  · rfl
  · have mapped := advanceHistory_map (provider NativeControlCursor.Controls.delayed)
      (forgetCollectorTag Nat) (fun _ _ => 1) 5
      (base := ()) (packet := ⟨(),(42,.pulling []),(0 : Nat)⟩)
    exact (congrArg Quiver.Path.length (eq_of_heq mapped)).trans (by rfl)

/-- Returning a known answer bag immediately is not a lawful continuation
translation of a pending poll. The two expose different actual operations. -/
theorem precomputed_bag_is_not_a_control_map :
    ¬ ∃ h : client Nat ⟶ client Nat,
      h.f () () (.pulling []) = .finished [7,7] := by
  rintro ⟨h,initial⟩
  have law := congrArg (fun mapping => mapping () () (.pulling [])) h.h
  change Extension.map ((protocol Nat).withHoles (fun _ _ => List Nat))
      (fun b i => h.f b i) ((client Nat).str () () (.pulling [])) =
    (client Nat).str () () (h.f () () (.pulling [])) at law
  rw [initial] at law
  have different := congrArg Sigma.fst law
  change Sum.inr () = Sum.inl [7,7] at different
  cases different

end Controls

end ClientTransport


namespace Controls

/-- The source retains an extra representation word through every real poll. -/
def taggedDelayed (state : Nat × Nat) : Pull (Nat × Nat) Nat :=
  match NativeControlCursor.Controls.delayed state.1 with
  | .done => .done
  | .yield value next => .yield value (next,state.2)
  | .suspend next => .suspend (next,state.2)

/-- Forgetting the representation word leaves each chosen reply intact. -/
def forgetDelayedTag : Cursor.Hom (provider taggedDelayed)
    (provider NativeControlCursor.Controls.delayed) where
  map state := state.1
  step state request := by
    rcases state with ⟨position,tag⟩
    cases observed : NativeControlCursor.Controls.delayed position <;>
      simp [provider,taggedDelayed,observed]

/-- A nonidentity representation map preserves all five actual occurrences:
suspension, two equal yields, exhaustion and final return inspection. -/
theorem tag_erasure_keeps_generated_occurrences :
    ((homForward (client Nat) forgetDelayedTag ()).histories.map
      (advanceHistory (provider taggedDelayed) (client Nat) (fun _ _ => 1) 5
        (packet taggedDelayed (0,42) []))).length = 5 := by
  have mapped := hom_advanceHistory (client Nat) forgetDelayedTag
    (fun _ _ => 1) (fun _ _ => 1) 5 (packet taggedDelayed (0,42) [])
  exact (congrArg Quiver.Path.length (eq_of_heq mapped)).trans (by rfl)

/-- An answer-only accelerator removes the initial suspension. -/
def skipInitialSuspension : Nat → Pull Nat Nat
  | 0 => .yield 7 2
  | state => NativeControlCursor.Controls.delayed state

/-- The accelerator cannot implement a lawful reply map at the same initial
state, although the completed printed answer bag remains the same. -/
theorem omitted_suspension_is_not_a_lawful_reply_map :
    ¬ ∃ h : Cursor.Hom (provider NativeControlCursor.Controls.delayed)
        (provider skipInitialSuspension), h.map (base:=()) (index:=()) (0 : Nat) = (0 : Nat) := by
  rintro ⟨h,initial⟩
  have response := congrArg Sigma.fst (h.step (base:=()) (index:=()) (0 : Nat) ())
  rw [initial] at response
  change (Pull.suspend () : Pull Unit Nat) = .yield 7 () at response
  cases response

/-- The same two answers do not certify the discarded suspension event. -/
theorem skipping_suspension_keeps_bag_but_changes_history :
    published NativeControlCursor.Controls.delayed
        (Cursor.advance (provider NativeControlCursor.Controls.delayed) (client Nat)
          (fun _ _ => 1) 5 (packet NativeControlCursor.Controls.delayed 0 [])).2 =
      published skipInitialSuspension
        (Cursor.advance (provider skipInitialSuspension) (client Nat)
          (fun _ _ => 1) 5 (packet skipInitialSuspension 0 [])).2 ∧
    (advanceHistory (provider NativeControlCursor.Controls.delayed) (client Nat)
        (fun _ _ => 1) 5 (packet NativeControlCursor.Controls.delayed 0 [])).length ≠
      (advanceHistory (provider skipInitialSuspension) (client Nat)
        (fun _ _ => 1) 5 (packet skipInitialSuspension 0 [])).length := by
  constructor
  · rfl
  · decide

end Controls

/-- A completed outcome cannot acquire a spurious new protocol event. -/
theorem done_has_no_event (base : Base) (result : Cursor.Finished M (Return := Return) base)
    (after : Cursor.Outcome M C base) :
    IsEmpty (Event M C base (.done result) after) :=
  ⟨fun event => nomatch event⟩

end ProtocolHistory

end Mettapedia.GSLT.LanguageDef.NativeControlCursor
