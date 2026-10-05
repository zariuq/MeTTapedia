import Mettapedia.GSLT.Core.InferenceControl
import Mettapedia.GSLT.Core.RouteTrace
import Mettapedia.OSLF.Syntax.RewriteEventHistoryForward
import Mettapedia.CategoryTheory.RunAccount
import Mathlib.Algebra.FreeMonoid.Basic

/-!
# Executable occurrence traces as event histories

Successor positions of a finite-branching machine are the generators of the
existing proof-relevant history category. Replaying their index lists agrees
with the machine's independently defined `follow` function. Equal endpoints
do not identify parallel occurrences.

Replay here fixes the machine and initial state. An index list alone does not
identify a source version, an external-service response, or a physical worker
schedule. These are separate requirements of a concrete replay interface.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.OccurrenceMachineHistory

open _root_.CategoryTheory
open Mettapedia.Machines
open Mettapedia.GSLT.ProofRelevant
open Mettapedia.GSLT.Core.InferenceControl

open Mettapedia.OSLF.Binding

variable {Term State Answer : Type}
variable {V : Type} [Monoid V]

/-- The endpoint relation forgets only the successor position. -/
abbrev theory (machine : OccurrenceMachineCore Term State Answer) : GSLT where
  Term := State
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites source target := target ∈ machine.next source
  rewrites_resp_left := by
    intro source source' target equal step
    subst source'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst target'
    exact step

/-- Two positions remain two events even when their successor states agree. -/
abbrev system (machine : OccurrenceMachineCore Term State Answer) : ProofRelevantGSLT where
  theory := theory machine
  steps := {
    Evidence := fun source target => {index : Nat // (machine.next source)[index]? = some target}
    erases_iff := by
      intro source target
      constructor
      · rintro ⟨⟨index, found⟩⟩
        exact List.mem_iff_getElem?.mpr ⟨index, found⟩
      · intro member
        obtain ⟨index, found⟩ := List.mem_iff_getElem?.mp member
        exact ⟨⟨index, found⟩⟩ }

abbrev History (machine : OccurrenceMachineCore Term State Answer) (source target : State) :=
  RewriteEventHistory.History (system machine) ⟨source⟩ ⟨target⟩

/-- Read the ordered successor positions from the retained event path. -/
def indices (machine : OccurrenceMachineCore Term State Answer)
    {source target : RewriteEventHistory.State (system machine)} : RewriteEventHistory.History (system machine) source target → List Nat
  | .nil => []
  | .cons past event => indices machine past ++ [event.val]

@[simp] theorem indices_nil (machine : OccurrenceMachineCore Term State Answer)
    (source : RewriteEventHistory.State (system machine)) : indices machine (.nil : Quiver.Path source source) = [] := rfl

theorem indices_comp (machine : OccurrenceMachineCore Term State Answer)
    {source middle target : RewriteEventHistory.State (system machine)}
    (first : Quiver.Path source middle) (second : Quiver.Path middle target) :
    indices machine (first.comp second) = indices machine first ++ indices machine second := by
  induction second with
  | nil => simp [Quiver.Path.comp, indices]
  | cons past event ih => simp [Quiver.Path.comp, indices, ih, List.append_assoc]

/-- Every retained event path is accepted by the executable replay function. -/
theorem follow_indices (machine : OccurrenceMachineCore Term State Answer)
    {source target : RewriteEventHistory.State (system machine)}
    (history : RewriteEventHistory.History (system machine) source target) :
    machine.follow source.term (indices machine history) = some target.term := by
  induction history with
  | nil => rfl
  | cons past event ih =>
      rw [indices, WorkOccurrence.follow_append, ih]
      simp [OccurrenceMachineCore.follow, event.property]

/-- Construct a history only after every selected successor position exists.
No answer-value equality is used to select or merge events. -/
def ofTrace (machine : OccurrenceMachineCore Term State Answer) :
    {source target : State} → (trace : List Nat) →
      machine.follow source trace = some target → History machine source target
  | source, target, [], accepted => by
      have equal : source = target := Option.some.inj accepted
      subst target
      exact .nil
  | source, target, index :: rest, accepted =>
      match found : (machine.next source)[index]? with
      | none => by simp [OccurrenceMachineCore.follow, found] at accepted
      | some middle =>
          (Quiver.Hom.toPath (⟨index, found⟩ :
            (⟨source⟩ : RewriteEventHistory.State (system machine)) ⟶ ⟨middle⟩)).comp
              (ofTrace machine rest (by
                simpa [OccurrenceMachineCore.follow, found] using accepted))

/-- Validation and construction preserve the exact occurrence list. -/
theorem indices_ofTrace (machine : OccurrenceMachineCore Term State Answer)
    {source target : State} (trace : List Nat)
    (accepted : machine.follow source trace = some target) :
    indices machine (ofTrace machine trace accepted) = trace := by
  induction trace generalizing source with
  | nil =>
      have equal : source = target := Option.some.inj accepted
      subst target
      rfl
  | cons index rest ih =>
      simp only [ofTrace]
      split
      · next found => simp [OccurrenceMachineCore.follow, found] at accepted
      · rw [indices_comp, ih]
        rfl

/-- A supplied trace denotes exactly a history with those occurrences. -/
theorem follow_iff_history (machine : OccurrenceMachineCore Term State Answer)
    {source target : State} (trace : List Nat) :
    machine.follow source trace = some target ↔
      ∃ history : History machine source target, indices machine history = trace := by
  constructor
  · intro accepted
    exact ⟨ofTrace machine trace accepted, indices_ofTrace machine trace accepted⟩
  · rintro ⟨history, equal⟩
    rw [← equal]
    exact follow_indices machine history

/-- The replay certificate is relative to its starting state. -/
theorem replay_endpoint_unique (machine : OccurrenceMachineCore Term State Answer)
    {source first second : State} {trace : List Nat}
    (one : machine.follow source trace = some first)
    (two : machine.follow source trace = some second) : first = second :=
  Option.some.inj (one.symm.trans two)

/-- Interpret each real event in a monoid, keeping chronological multiplication.
This uses the existing free history category and run-account interface. -/
def eventAccount (machine : OccurrenceMachineCore Term State Answer)
    (value : State → State → Nat → V) :
    Mettapedia.Effects.RunAccount (RewriteEventHistory.HistoryCategory (system machine)) V :=
  Mettapedia.Effects.RunAccount.ofFunctor
    (RewriteEventHistory.interpret (system machine) {
      obj _ := SingleObj.star Vᵐᵒᵖ
      map {source target} event := MulOpposite.op (value source.term target.term event.val) })

/-- A one-event account is the supplied value of that occurrence. -/
theorem eventAccount_generator (machine : OccurrenceMachineCore Term State Answer)
    (value : State → State → Nat → V)
    {source target : RewriteEventHistory.State (system machine)} (event : source ⟶ target) :
    (eventAccount machine value).of event.toPath = value source.term target.term event.val := by
  dsimp only [eventAccount, Mettapedia.Effects.RunAccount.ofFunctor]
  rw [RewriteEventHistory.interpret_generator]
  rfl

/-- Extending a history multiplies by the new event on the right. -/
theorem eventAccount_cons (machine : OccurrenceMachineCore Term State Answer)
    (value : State → State → Nat → V)
    {source middle target : RewriteEventHistory.State (system machine)}
    (history : Quiver.Path source middle) (event : middle ⟶ target) :
    (eventAccount machine value).of (history.cons event) =
      (eventAccount machine value).of history * value middle.term target.term event.val := by
  calc
    _ = (eventAccount machine value).of history *
        (eventAccount machine value).of event.toPath :=
      (eventAccount machine value).of_comp history event.toPath
    _ = _ := by rw [eventAccount_generator]

/-- Changing the account algebra commutes with interpreting a history.
The homomorphism must preserve ordered multiplication, not just final values. -/
theorem eventAccount_map {W : Type} [Monoid W]
    (machine : OccurrenceMachineCore Term State Answer)
    (value : State → State → Nat → V) (change : V →* W) :
    (eventAccount machine value).map change =
      eventAccount machine (fun before after index => change (value before after index)) := by
  apply Mettapedia.Effects.RunAccount.ext
  funext source target history
  change change ((eventAccount machine value).of history) = _
  induction history with
  | nil => exact change.map_one
  | cons past event ih =>
      erw [eventAccount_cons, change.map_mul, ih, eventAccount_cons]

open Mettapedia.GSLT.Ultrainfinite.Route

/-- A history realizes its declared observations while retaining the count
of every underlying machine step, including steps with no visible event. -/
theorem history_observed_trace {Event : Type}
    (machine : OccurrenceMachineCore Term State Answer)
    (observe : State → State → Nat → List Event)
    {source target : RewriteEventHistory.State (system machine)}
    (history : Quiver.Path source target) :
    ObservedTrace (Step := (system machine).steps.Evidence)
      (fun {before after} event => observe before after event.val)
      (indices machine history).length source.term target.term
      (FreeMonoid.toList ((eventAccount machine
        (fun before after index => FreeMonoid.ofList (observe before after index))).of history)) := by
  induction history with
  | nil => exact .refl _
  | @cons middle after past event ih =>
      have last : ObservedTrace (Step := (system machine).steps.Evidence)
          (fun {before after} event => observe before after event.val)
          1 middle.term after.term (observe middle.term after.term event.val) := by
        simpa using ObservedTrace.cons
          (Step := (system machine).steps.Evidence)
          (observe := fun {before after} event => observe before after event.val)
          (edge := ⟨event.val, event.property⟩) (ObservedTrace.refl after.term)
      have joined := ObservedTrace.comp _ ih last
      simpa only [indices, List.length_append, List.length_singleton,
        eventAccount_cons, FreeMonoid.toList_mul, FreeMonoid.toList_ofList] using joined

/-- Every trace of actual step evidence is covered by a history. The event
observation need not identify that history uniquely. -/
theorem observed_trace_history {Event : Type}
    (machine : OccurrenceMachineCore Term State Answer)
    (observe : State → State → Nat → List Event)
    {count : Nat} {source target : State} {observations : List Event}
    (admitted : ObservedTrace (Step := (system machine).steps.Evidence)
      (fun {before after} event => observe before after event.val)
      count source target observations) :
    ∃ history : History machine source target,
      (indices machine history).length = count ∧
      FreeMonoid.toList ((eventAccount machine
        (fun before after index => FreeMonoid.ofList (observe before after index))).of history) =
          observations := by
  induction admitted with
  | refl state => exact ⟨.nil, rfl, rfl⟩
  | @cons count before middle after observations edge rest ih =>
      obtain ⟨history, length, events⟩ := ih
      let event : (⟨before⟩ : RewriteEventHistory.State (system machine)) ⟶ ⟨middle⟩ := edge
      refine ⟨event.toPath.comp history, ?_, ?_⟩
      · rw [indices_comp]
        change ([edge.val] ++ indices machine history).length = _
        simp [length]
      · change FreeMonoid.toList
          ((eventAccount machine
            (fun before after index => FreeMonoid.ofList (observe before after index))).of
              (event.toPath ≫ history)) = _
        erw [Mettapedia.Effects.RunAccount.of_comp, FreeMonoid.toList_mul, events]
        rw [eventAccount_generator]
        rfl

/-- The ordered trace is an instance of the shared compositional run account.
Its multiplication is concatenation, with no exchange law. -/
def traceAccount (machine : OccurrenceMachineCore Term State Answer) :
    Mettapedia.Effects.RunAccount
      (RewriteEventHistory.HistoryCategory (system machine)) (FreeMonoid Nat) where
  of history := FreeMonoid.ofList (indices machine history)
  of_id _ := rfl
  of_comp first second := indices_comp machine first second

/-- Recording successor indices is the free-monoid instance of event accounting. -/
theorem eventAccount_trace (machine : OccurrenceMachineCore Term State Answer) :
    eventAccount machine (fun _ _ index => FreeMonoid.of index) = traceAccount machine := by
  apply Mettapedia.Effects.RunAccount.ext
  funext source target history
  induction history with
  | nil => rfl
  | cons past event ih =>
      erw [eventAccount_cons, ih]
      rfl

/-- The same index sequence is replayable after a position-preserving change
of machine representation. The hypothesis retains duplicates and branch order. -/
def forward {TargetTerm TargetState TargetAnswer : Type}
    (machine : OccurrenceMachineCore Term State Answer)
    (target : OccurrenceMachineCore TargetTerm TargetState TargetAnswer)
    (mapState : State → TargetState)
    (next : ∀ state, target.next (mapState state) = (machine.next state).map mapState) :
    RewriteEventHistory.ForwardEvidenceMap (system machine) (system target) where
  mapTerm := mapState
  mapEquiv := fun equal => congrArg mapState equal
  mapEvidence := by
    intro source destination event
    refine ⟨event.val, ?_⟩
    rw [next, List.getElem?_map, event.property]
    rfl

/-- Transport changes states and their representation, preserving every
selected occurrence in its original order. -/
theorem forward_indices {TargetTerm TargetState TargetAnswer : Type}
    (machine : OccurrenceMachineCore Term State Answer)
    (target : OccurrenceMachineCore TargetTerm TargetState TargetAnswer)
    (mapState : State → TargetState)
    (next : ∀ state, target.next (mapState state) = (machine.next state).map mapState)
    {source destination : RewriteEventHistory.State (system machine)}
    (history : Quiver.Path source destination) :
    indices target ((forward machine target mapState next).histories.map history) =
      indices machine history := by
  induction history with
  | nil => rfl
  | cons past event ih =>
      change indices target
          (((forward machine target mapState next).histories.map past).cons
            ((forward machine target mapState next).mapEvidence event)) = _
      simp only [indices, ih]
      rfl

/-- The history transport theorem gives replay preservation against the
independently executable target machine. -/
theorem forward_replay {TargetTerm TargetState TargetAnswer : Type}
    (machine : OccurrenceMachineCore Term State Answer)
    (target : OccurrenceMachineCore TargetTerm TargetState TargetAnswer)
    (mapState : State → TargetState)
    (next : ∀ state, target.next (mapState state) = (machine.next state).map mapState)
    {source destination : State} {trace : List Nat}
    (accepted : machine.follow source trace = some destination) :
    target.follow (mapState source) trace = some (mapState destination) := by
  have replay := follow_indices target
    ((forward machine target mapState next).histories.map (ofTrace machine trace accepted))
  rw [forward_indices, indices_ofTrace] at replay
  exact replay

/-- Position-preserving representation change reflects failed as well as
successful replay. No target branch is introduced at a represented state. -/
theorem follow_map {TargetTerm TargetState TargetAnswer : Type}
    (machine : OccurrenceMachineCore Term State Answer)
    (target : OccurrenceMachineCore TargetTerm TargetState TargetAnswer)
    (mapState : State → TargetState)
    (next : ∀ state, target.next (mapState state) = (machine.next state).map mapState)
    (source : State) (trace : List Nat) :
    target.follow (mapState source) trace = (machine.follow source trace).map mapState := by
  induction trace generalizing source with
  | nil => rfl
  | cons index rest ih =>
      simp only [OccurrenceMachineCore.follow, next, List.getElem?_map]
      cases found : (machine.next source)[index]? with
      | none => rfl
      | some middle => simpa using ih middle

/-- Every replayed target endpoint from an image state comes from a source
history with the same occurrence list. -/
theorem replay_reflects {TargetTerm TargetState TargetAnswer : Type}
    (machine : OccurrenceMachineCore Term State Answer)
    (target : OccurrenceMachineCore TargetTerm TargetState TargetAnswer)
    (mapState : State → TargetState)
    (next : ∀ state, target.next (mapState state) = (machine.next state).map mapState)
    {source : State} {destination : TargetState} {trace : List Nat}
    (accepted : target.follow (mapState source) trace = some destination) :
    ∃ endpoint, machine.follow source trace = some endpoint ∧ mapState endpoint = destination := by
  rw [follow_map machine target mapState next] at accepted
  cases replay : machine.follow source trace with
  | none => simp [replay] at accepted
  | some endpoint =>
      refine ⟨endpoint, rfl, ?_⟩
      simpa [replay] using accepted

/-- Pulling back the target's account along the existing history functor
recovers the source account. Identity and composition of these functors are
the shared `ForwardEvidenceMap.histories_id` and `histories_comp` laws. -/
theorem forward_account {TargetTerm TargetState TargetAnswer : Type}
    (machine : OccurrenceMachineCore Term State Answer)
    (target : OccurrenceMachineCore TargetTerm TargetState TargetAnswer)
    (mapState : State → TargetState)
    (next : ∀ state, target.next (mapState state) = (machine.next state).map mapState) :
    (traceAccount target).comap (forward machine target mapState next).histories =
      traceAccount machine := by
  apply Mettapedia.Effects.RunAccount.ext
  funext source destination history
  exact congrArg FreeMonoid.ofList (forward_indices machine target mapState next history)

/-- Preservation on primitive events extends to every history, including a
change of coefficient monoid. No exchange or commutativity law is used. -/
theorem eventAccount_forward {TargetTerm TargetState TargetAnswer W : Type} [Monoid W]
    (machine : OccurrenceMachineCore Term State Answer)
    (target : OccurrenceMachineCore TargetTerm TargetState TargetAnswer)
    (mapState : State → TargetState)
    (next : ∀ state, target.next (mapState state) = (machine.next state).map mapState)
    (sourceValue : State → State → Nat → V)
    (targetValue : TargetState → TargetState → Nat → W) (mapValue : V →* W)
    (onEvent : ∀ (source destination : State) (index : Nat),
      (machine.next source)[index]? = some destination →
      targetValue (mapState source) (mapState destination) index =
        mapValue (sourceValue source destination index)) :
    (eventAccount target targetValue).comap (forward machine target mapState next).histories =
      (eventAccount machine sourceValue).map mapValue := by
  apply RewriteEventHistory.PathEvidenceMap.account_preserved
    (RewriteEventHistory.PathEvidenceMap.ofForward (forward machine target mapState next))
    (eventAccount machine sourceValue) (eventAccount target targetValue) mapValue
  intro source destination event
  simp only [RewriteEventHistory.PathEvidenceMap.ofForward, eventAccount_generator]
  exact onEvent source.term destination.term event.val event.property

/-- Replay of a path-valued interpretation uses the implementing occurrence
list. The original list generally has a different length and is not a valid
target replay certificate. -/
theorem path_replay {TargetTerm TargetState TargetAnswer : Type}
    (machine : OccurrenceMachineCore Term State Answer)
    (target : OccurrenceMachineCore TargetTerm TargetState TargetAnswer)
    (realization : RewriteEventHistory.PathEvidenceMap (system machine) (system target))
    {source destination : State} {trace : List Nat}
    (accepted : machine.follow source trace = some destination) :
    target.follow (realization.mapTerm source)
      (indices target (realization.histories.map (ofTrace machine trace accepted))) =
        some (realization.mapTerm destination) :=
  follow_indices target (realization.histories.map (ofTrace machine trace accepted))

def duplicateFirst : History OccurrenceMachineCore.duplicateExample .root .done :=
  ofTrace _ [0] rfl

def duplicateSecond : History OccurrenceMachineCore.duplicateExample .root .done :=
  ofTrace _ [1] rfl

/-- Equal endpoints do not collapse two physical successor occurrences. -/
theorem duplicate_histories_distinct : duplicateFirst ≠ duplicateSecond := by
  intro equal
  have traces := congrArg (indices OccurrenceMachineCore.duplicateExample) equal
  have impossible : ([0] : List Nat) = [1] := traces
  cases impossible

/-- Replay rejects a missing occurrence even when another occurrence reaches
the requested endpoint. -/
theorem missing_occurrence_rejected :
    ¬ ∃ history : History OccurrenceMachineCore.duplicateExample .root .done,
      indices OccurrenceMachineCore.duplicateExample history = [2] := by
  rw [← follow_iff_history]
  decide

namespace Controls

private def alternating : OccurrenceMachineCore Unit Bool Empty where
  load _ := false
  next state := [!state]
  answer _ := none
  answer_final _ _ returned := by cases returned

private def twoEvents : History alternating false false := ofTrace _ [0, 0] rfl

/-- The two executed events retain their original order. -/
theorem history_account_is_ordered :
    (eventAccount alternating (fun before _ _ => FreeMonoid.of before)).of twoEvents =
      FreeMonoid.ofList [false, true] := rfl

/-- Reversing an account fails even though the history returns to its source. -/
theorem reversing_event_account_changes_observation :
    (eventAccount alternating (fun before _ _ => FreeMonoid.of before)).of twoEvents ≠
      FreeMonoid.ofList [true, false] := by
  rw [history_account_is_ordered]
  change ([false, true] : List Bool) ≠ [true, false]
  decide

/-- A vanishing coefficient does not erase the two physical events. -/
theorem zero_account_keeps_both_events :
    (eventAccount alternating (fun _ _ _ => (0 : Nat))).of twoEvents = 0 ∧
      indices alternating twoEvents = [0, 0] := ⟨rfl, rfl⟩

/-- A declared observer may suppress every label while the trace judgment
still retains the actual number of transitions. -/
theorem unobserved_steps_still_count :
    ObservedTrace (Step := (system alternating).steps.Evidence)
      (fun {_ _} _ => ([] : List Nat)) 2 false false [] :=
  history_observed_trace alternating (fun _ _ _ => ([] : List Nat)) twoEvents

/-- Equal observation records do not reconstruct the hidden history. Here
the empty run and a two-step cycle both report the empty record. -/
theorem empty_record_does_not_recover_history :
    (eventAccount alternating (fun _ _ _ => FreeMonoid.ofList ([] : List Nat))).of twoEvents =
      (eventAccount alternating (fun _ _ _ => FreeMonoid.ofList ([] : List Nat))).of
        (Quiver.Path.nil : History alternating false false) ∧
    indices alternating twoEvents ≠
      indices alternating (Quiver.Path.nil : History alternating false false) :=
  ⟨rfl, by decide⟩

end Controls

namespace LoweringControls

inductive TargetState where
  | root
  | prepared
  | done
deriving DecidableEq

/-- The first source choice takes a preparation step. The optional third
edge is an unauthorized duplicate answer, used only by the negative control. -/
def target (extra : Bool) : OccurrenceMachineCore Unit TargetState Nat where
  load _ := .root
  next
    | .root => if extra then [.prepared, .done, .done] else [.prepared, .done]
    | .prepared => [.done]
    | .done => []
  answer
    | .done => some 7
    | _ => none
  answer_final := by
    intro state answer returned
    cases state <;> simp_all

def lowerState : OccurrenceMachineCore.DuplicateExampleState → TargetState
  | .root => .root
  | .done => .done

/-- Two equal source endpoints receive different implementing paths because
the source occurrence index is retained. -/
def lowering (extra : Bool) :
    RewriteEventHistory.PathEvidenceMap
      (system OccurrenceMachineCore.duplicateExample) (system (target extra)) where
  mapTerm := lowerState
  mapEquiv := fun equal => congrArg lowerState equal
  mapEvidence := by
    intro before after event
    obtain ⟨index, found⟩ := event
    cases before with
    | done => simp [OccurrenceMachineCore.duplicateExample] at found
    | root =>
        cases index with
        | zero =>
            simp [OccurrenceMachineCore.duplicateExample] at found
            subst after
            exact ofTrace (target extra) [0, 0] (by cases extra <;> rfl)
        | succ index =>
            cases index with
            | zero =>
                simp [OccurrenceMachineCore.duplicateExample] at found
                subst after
                exact ofTrace (target extra) [1] (by cases extra <;> rfl)
            | succ index => simp [OccurrenceMachineCore.duplicateExample] at found

def fuseState : TargetState → OccurrenceMachineCore.DuplicateExampleState
  | .root | .prepared => .root
  | .done => .done

/-- The preparation is administrative under the answer observation. The
following commit retains the first choice, and the direct path retains the
second. This is a nontrivial fusion of a two-step implementation. -/
def fusion : RewriteEventHistory.PathEvidenceMap
    (system (target false)) (system OccurrenceMachineCore.duplicateExample) where
  mapTerm := fuseState
  mapEquiv := fun equal => congrArg fuseState equal
  mapEvidence := by
    intro before after event
    obtain ⟨index, found⟩ := event
    cases before with
    | done => simp [target] at found
    | prepared =>
        cases index with
        | zero =>
            simp [target] at found
            subst after
            exact duplicateFirst
        | succ index => simp [target] at found
    | root =>
        cases index with
        | zero =>
            simp [target] at found
            subst after
            exact Quiver.Path.nil
        | succ index =>
            cases index with
            | zero =>
                simp [target] at found
                subst after
                exact duplicateSecond
            | succ index => simp [target] at found

/-- Fusion preserves the independently declared answer observation at every
target state, including the intermediate preparation state. -/
theorem fusion_preserves_answer (state : TargetState) :
    OccurrenceMachineCore.duplicateExample.answer (fuseState state) =
      (target false).answer state := by
  cases state <;> rfl

/-- Lowering followed by fusion recovers every source history, not merely
its final answer or its number of transitions. -/
theorem fusion_retracts_lowering :
    ((lowering false).comp fusion).histories =
      𝟭 (RewriteEventHistory.HistoryCategory (system OccurrenceMachineCore.duplicateExample)) := by
  symm
  apply Paths.lift_unique
  fapply Prefunctor.ext
  · intro state
    obtain ⟨state⟩ := state
    cases state <;> rfl
  · intro a b event
    obtain ⟨before⟩ := a
    obtain ⟨after⟩ := b
    obtain ⟨index, found⟩ := event
    cases before with
    | done => simp [OccurrenceMachineCore.duplicateExample] at found
    | root =>
        cases index with
        | zero =>
            simp [OccurrenceMachineCore.duplicateExample] at found
            subst after
            rfl
        | succ index =>
            cases index with
            | zero =>
                simp [OccurrenceMachineCore.duplicateExample] at found
                subst after
                rfl
            | succ index => simp [OccurrenceMachineCore.duplicateExample] at found

def sourceWord (_before _after : OccurrenceMachineCore.DuplicateExampleState)
    (index : Nat) : FreeMonoid Nat :=
  if index = 0 then FreeMonoid.ofList [10, 11] else FreeMonoid.of 20

def targetWord (before _after : TargetState) (index : Nat) : FreeMonoid Nat :=
  match before with
  | .root => if index = 0 then FreeMonoid.of 10 else FreeMonoid.of 20
  | .prepared => FreeMonoid.of 11
  | .done => 1

/-- The account on the two source choices is checked against the actual
implementing events. Chronological multiplication is preserved without
assuming that coefficients commute. -/
theorem lowering_preserves_ordered_account :
    (eventAccount (target false) targetWord).comap (lowering false).histories =
      eventAccount OccurrenceMachineCore.duplicateExample sourceWord := by
  have preserved := RewriteEventHistory.PathEvidenceMap.account_preserved
    (lowering false) (eventAccount OccurrenceMachineCore.duplicateExample sourceWord)
    (eventAccount (target false) targetWord) (MonoidHom.id (FreeMonoid Nat))
  apply preserved
  intro a b event
  obtain ⟨before⟩ := a
  obtain ⟨after⟩ := b
  obtain ⟨index, found⟩ := event
  cases before with
  | done => simp [OccurrenceMachineCore.duplicateExample] at found
  | root =>
      cases index with
      | zero =>
          simp [OccurrenceMachineCore.duplicateExample] at found
          subst after
          rfl
      | succ index =>
          cases index with
          | zero =>
              simp [OccurrenceMachineCore.duplicateExample] at found
              subst after
              rfl
          | succ index => simp [OccurrenceMachineCore.duplicateExample] at found

/-- Equal endpoints do not fix the cost of their implementing paths. -/
theorem implementing_work_differs :
    (eventAccount (target false) (fun _ _ _ => Multiplicative.ofAdd (1 : Nat))).of
        ((lowering false).histories.map duplicateFirst) = Multiplicative.ofAdd 2 ∧
      (eventAccount (target false) (fun _ _ _ => Multiplicative.ofAdd (1 : Nat))).of
        ((lowering false).histories.map duplicateSecond) = Multiplicative.ofAdd 1 :=
  ⟨rfl, rfl⟩

/-- Answer-preserving fusion cannot also preserve a unit charge for every
physical target event: the administrative preparation has been removed. -/
theorem fusion_does_not_preserve_unit_work :
    (eventAccount OccurrenceMachineCore.duplicateExample
      (fun _ _ _ => Multiplicative.ofAdd (1 : Nat))).comap fusion.histories ≠
        eventAccount (target false) (fun _ _ _ => Multiplicative.ofAdd (1 : Nat)) := by
  intro equal
  have preparation := congrArg
    (fun account : Mettapedia.Effects.RunAccount
        (RewriteEventHistory.HistoryCategory (system (target false))) (Multiplicative Nat) =>
      account.of (ofTrace (target false) (source := .root) (target := .prepared) [0] rfl)) equal
  have impossible : (0 : Nat) = 1 := congrArg Multiplicative.toAdd preparation
  cases impossible

/-- Lowering retains both authored choices even though their implementations
have different lengths and the same answer. -/
theorem distinct_implementing_paths (extra : Bool) :
    indices (target extra) ((lowering extra).histories.map duplicateFirst) = [0, 0] ∧
      indices (target extra) ((lowering extra).histories.map duplicateSecond) = [1] := by
  cases extra <;> exact ⟨rfl, rfl⟩

/-- The two native trace certificates execute against the target machine. -/
theorem implementing_paths_replay :
    (target false).follow .root [0, 0] = some .done ∧
      (target false).follow .root [1] = some .done ∧
      (target false).follow .root [0] = some .prepared := ⟨rfl, rfl, rfl⟩

/-- The shorter cut retains the unfinished first branch. A source depth
budget cannot simply be reused as a target depth budget. -/
theorem lowering_changes_depth_cut :
    OccurrenceMachineCore.duplicateExample.expand 1 .root =
      ⟨[(7, [0]), (7, [1])], []⟩ ∧
    (target false).expand 1 .root =
      ⟨[(7, [1])], [(.prepared, [0])]⟩ := ⟨rfl, rfl⟩

/-- Beyond its actual maximum depth, the target has exactly the two
implementations and no residual. This checks the target exploration itself. -/
theorem complete_lowered_search (extraFuel : Nat) :
    (target false).expand (extraFuel + 2) .root =
      ⟨[(7, [0, 0]), (7, [1])], []⟩ := by
  cases extraFuel <;> rfl

/-- Both source choices have implementations even in the bad target, which
also emits an unauthorized third occurrence. Forward realization alone
therefore does not establish multiplicity-preserving hosting. -/
theorem forward_realization_allows_extra_answer (extraFuel : Nat) :
    (target true).expand (extraFuel + 2) .root =
      ⟨[(7, [0, 0]), (7, [1]), (7, [2])], []⟩ ∧
      (target true).answerOccurrences (extraFuel + 2) .root ≠
        OccurrenceMachineCore.duplicateExample.answerOccurrences (extraFuel + 1) .root := by
  cases extraFuel <;> refine ⟨rfl, ?_⟩ <;>
    change ([7, 7, 7] : List Nat) ≠ [7, 7] <;> decide

end LoweringControls

end Mettapedia.GSLT.Causality.OccurrenceMachineHistory
