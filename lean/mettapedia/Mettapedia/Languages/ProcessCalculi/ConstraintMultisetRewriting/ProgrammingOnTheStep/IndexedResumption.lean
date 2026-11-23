import Mettapedia.GSLT.Dynamics.IndexedPolynomialProtocol
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.Counting

/-!
# A dependent protocol round as an occurrence commit

A suspended round retains a continuation at each possible response's
successor. Its reply is a separate occurrence with a ticket and command.
A resume consumes the reply, takes or reads the continuation, and publishes
the result in the fibre selected by that reply. The rules use closed
protocol values. The continuation can have genuinely different fibres.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgrammingOnTheStep.IndexedResumption

open Mettapedia.GSLT.Dynamics.IndexedPolynomialProtocol
open RuleSyntax RuleSyntax.OneFrame
open MeTTaCalculus.OccurrenceCommits (Enabled mem_fire)

universe uI uC uR uV

variable {Index : Type uI}
  {protocol : ProtocolPolynomial.{uI, uC, uR} Index} {Value : Index → Type uV}

/-- The two policies for using an already suspended continuation. -/
inductive Shot where
  | one | many

/-- The ticket is carried in all three labels. An offered reply already
belongs to its command's response type. -/
inductive Row (protocol : ProtocolPolynomial.{uI, uC, uR} Index) (Value : Index → Type uV) where
  | suspended (ticket : Nat) {source : Index} (round : OneRound protocol Value source)
  | offered (ticket : Nat) {source : Index} (command : Command protocol source)
      (reply : Response protocol command)
  | completed (ticket : Nat) {source : Index}
      (outcome : Sigma fun event : (interaction protocol).Enabled source => Value event.target)

/-- One instance of the resume rule, independent of the current inventory. -/
structure Resume (protocol : ProtocolPolynomial.{uI, uC, uR} Index) (Value : Index → Type uV) where
  ticket : Nat
  source : Index
  round : OneRound protocol Value source
  reply : Response protocol round.1

abbrev action (protocol : ProtocolPolynomial.{uI, uC, uR} Index) (Value : Index → Type uV) :=
  RuleSyntax.RuleOccurrences.Closed.action (Row protocol Value)

abbrev Inventory (protocol : ProtocolPolynomial.{uI, uC, uR} Index) (Value : Index → Type uV) :=
  RuleSyntax.State (Terms (Row protocol Value)) Nat

namespace Resume

variable (request : Resume protocol Value)

def outcome : Row protocol Value :=
  .completed request.ticket (selectResponse protocol request.round request.reply)

def rule (shot : Shot) : Rule (Terms (Row protocol Value)) :=
  let suspended := Row.suspended request.ticket request.round
  let reply := Row.offered request.ticket request.round.1 request.reply
  let (take, read) := match shot with
    | .one => ([suspended, reply], [])
    | .many => ([reply], [suspended])
  ⟨PUnit.unit, ⟨take, read, [], [], [request.outcome]⟩, []⟩

def selection (shot : Shot) (handle delivery receipt : Nat) : Selection Nat :=
  match shot with
  | .one => ⟨[handle, delivery], [], [receipt]⟩
  | .many => ⟨[delivery], [handle], [receipt]⟩

end Resume

variable (protocol Value) in
def program (shot : Shot) : RuleSyntax.Program (Terms (Row protocol Value)) :=
  Set.range (fun request : Resume protocol Value => request.rule shot)

variable (protocol Value) in
abbrev machine (shot : Shot) :=
  RuleSyntax.step (frames (action protocol Value)) Nat (ext (action protocol Value))
    (program protocol Value shot)

variable (request : Resume protocol Value) (shot : Shot)
  (before : Inventory protocol Value) (handle delivery receipt : Nat)

def firing :
    Firing Nat (ext (action protocol Value)) (program protocol Value shot) before.frame :=
  ⟨request.rule shot, ⟨request, rfl⟩, PUnit.unit, PUnit.unit,
    Resume.selection shot handle delivery receipt, []⟩

private theorem models_iff {target : PUnit.{1}} (σ : PUnit.{1}) :
    (frames (action protocol Value)).Models (b := target) σ
      ((firing request shot before handle delivery receipt).information
        (frames (action protocol Value)) before) ↔
      (∀ e ∈ before.knowledge, e.1 = e.2) ∧
      before.label handle = .suspended request.ticket request.round ∧
      before.label delivery = .offered request.ticket request.round.1 request.reply := by
  let X := frames (action protocol Value)
  have old : X.applyStore (X.id before.frame) before.knowledge = before.knowledge :=
    Interface.Frames.applyStore_id (X := X) _
  cases shot with
  | one =>
    change X.Models σ (X.applyStore (X.id before.frame) before.knowledge ++
      [(Row.suspended request.ticket request.round, before.label handle),
       (Row.offered request.ticket request.round.1 request.reply, before.label delivery)] ++
      [] ++ []) ↔ _
    rw [old, List.append_nil, List.append_nil, X.models_append]
    constructor
    · rintro ⟨known, selected⟩
      exact ⟨known, (selected (.suspended request.ticket request.round, before.label handle) (by simp)).symm,
        (selected (.offered request.ticket request.round.1 request.reply, before.label delivery) (by simp)).symm⟩
    · rintro ⟨known, parked, ready⟩
      refine ⟨known, ?_⟩
      intro e inside
      rcases (List.mem_cons.mp inside) with rfl | inside
      · exact parked.symm
      · obtain rfl := List.mem_singleton.mp inside
        exact ready.symm
  | many =>
    change X.Models σ (X.applyStore (X.id before.frame) before.knowledge ++
      [(Row.offered request.ticket request.round.1 request.reply, before.label delivery)] ++
      [(Row.suspended request.ticket request.round, before.label handle)] ++ []) ↔ _
    rw [old, List.append_nil, X.models_append, X.models_append]
    constructor
    · rintro ⟨⟨known, ready⟩, parked⟩
      exact ⟨known, (parked (.suspended request.ticket request.round, before.label handle) (by simp)).symm,
        (ready (.offered request.ticket request.round.1 request.reply, before.label delivery) (by simp)).symm⟩
    · rintro ⟨known, parked, ready⟩
      refine ⟨⟨known, ?_⟩, ?_⟩
      · intro e member
        obtain rfl := List.mem_singleton.mp member
        exact ready.symm
      · intro e member
        obtain rfl := List.mem_singleton.mp member
        exact parked.symm

/-- An actual admitted resume uses the exact suspended round and the
exact response delivery. Both identities must be live and the result
identity fresh. The result's index comes from the matched response. -/
theorem admits_iff :
    (machine protocol Value shot).Admits (s := before) (firing request shot before handle delivery receipt) ↔
      handle ≠ delivery ∧ handle ∈ before.present ∧ delivery ∈ before.present ∧
      receipt ∉ before.present ∧ (∀ e ∈ before.knowledge, e.1 = e.2) ∧
      before.label handle = .suspended request.ticket request.round ∧
      before.label delivery = .offered request.ticket request.round.1 request.reply := by
  let f := firing request shot before handle delivery receipt
  let X := frames (action protocol Value)
  constructor
  · intro admitted
    have enabled : Enabled (fun _ : Nat => ()) before.present (f.selection.commit (T := Unit)) :=
      admitted.2.1
    obtain ⟨target, σ, solved⟩ := admitted.2.2.1
    have labels := (models_iff request shot before handle delivery receipt (target := target) σ).mp solved
    have distinct : handle ≠ delivery := by
      intro same
      rw [same, labels.2.2] at labels
      cases labels.2.1
    have fresh : receipt ∉ before.present := fun present =>
      (Finset.disjoint_left.mp enabled.fresh)
        (by cases shot <;> simp [f, firing, Resume.selection, Selection.commit]) present
    have available : handle ∈ before.present ∧ delivery ∈ before.present := by
      cases shot with
      | one =>
        exact ⟨enabled.taken_subset (by simp [f, firing, Resume.selection, Selection.commit]),
          enabled.taken_subset (by simp [f, firing, Resume.selection, Selection.commit])⟩
      | many =>
        exact ⟨enabled.kept_subset (by simp [f, firing, Resume.selection, Selection.commit]),
          enabled.taken_subset (by simp [f, firing, Resume.selection, Selection.commit])⟩
    exact ⟨distinct, available.1, available.2, fresh, labels⟩
  · rintro ⟨apart, parked, offered, fresh, knowledge, handleLabel, deliveryLabel⟩
    have opened : f.Fresh X before := by
      intro b g h
      exact ⟨PUnit.unit, fun _ _ => rfl, fun _ _ => rfl⟩
    have consistent : X.Solvable (f.information X before) :=
      ⟨PUnit.unit, PUnit.unit, (models_iff request shot before handle delivery receipt PUnit.unit).mpr
        ⟨knowledge, handleLabel, deliveryLabel⟩⟩
    have guards : X.Entails (f.information X before) (fun b σ => f.Holds X before (b := b) σ) := by
      intro b σ _
      cases shot <;> simp [f, firing, Resume.rule, Firing.Holds, Firing.opened, Firing.collectOpened,
        RuleInstance.map]
    have shapes : f.Shapes X before := by
      cases shot <;> exact ⟨opened,
        by simp [f, firing, Resume.selection, apart], by simp [f, firing, Resume.selection],
        rfl, rfl, rfl, rfl⟩
    refine ⟨shapes, ?_, consistent, guards⟩
    have reverseApart : delivery ≠ handle := Ne.symm apart
    cases shot <;>
      constructor <;>
      simp_all [f, firing, Resume.selection, Selection.commit, Finset.disjoint_left,
        Finset.insert_subset_iff]

variable {request shot before handle delivery receipt}

abbrev after (admitted :
    (machine protocol Value shot).Admits (s := before) (firing request shot before handle delivery receipt)) :=
  (machine protocol Value shot).result (s := before) (firing request shot before handle delivery receipt) admitted

theorem published_outcome (admitted :
    (machine protocol Value shot).Admits (s := before) (firing request shot before handle delivery receipt)) :
    receipt ∈ (after admitted).present ∧ (after admitted).label receipt = request.outcome := by
  cases shot <;> simp [after, result_eq, Firing.result, firing, Resume.selection, Resume.rule,
    Selection.commit, Firing.opened, RuleInstance.map, relabel, mem_fire,
    Interface.Frames.ofSubstitution, RuleSyntax.RuleOccurrences.Closed.action]

theorem delivery_spent (admitted :
    (machine protocol Value shot).Admits (s := before) (firing request shot before handle delivery receipt)) :
    delivery ∉ (after admitted).present := by
  have admission := (admits_iff request shot before handle delivery receipt).mp admitted
  have apart : delivery ≠ receipt := fun same => admission.2.2.2.1 (same ▸ admission.2.2.1)
  cases shot <;> simp [after, result_eq, Firing.result, firing, Resume.selection,
    Selection.commit, mem_fire, apart]

theorem one_shot_spent (admitted :
    (machine protocol Value .one).Admits (s := before) (firing request .one before handle delivery receipt)) :
    handle ∉ (after admitted).present := by
  have admission := (admits_iff request .one before handle delivery receipt).mp admitted
  have apart : handle ≠ receipt := fun same => admission.2.2.2.1 (same ▸ admission.2.1)
  simp [after, result_eq, Firing.result, firing, Resume.selection, Selection.commit, mem_fire, apart]

theorem multi_shot_retains (admitted :
    (machine protocol Value .many).Admits (s := before) (firing request .many before handle delivery receipt)) :
    handle ∈ (after admitted).present ∧ (after admitted).label handle = before.label handle := by
  have admission := (admits_iff request .many before handle delivery receipt).mp admitted
  have apart : handle ≠ receipt := fun same => admission.2.2.2.1 (same ▸ admission.2.1)
  simp [after, result_eq, Firing.result, firing, Resume.selection, Selection.commit, mem_fire,
    Firing.opened, Firing.row, relabel, Resume.rule, RuleInstance.map, apart, admission.1, admission.2.1,
    Interface.Frames.ofSubstitution, RuleSyntax.RuleOccurrences.Closed.action]

/-- In the closed instance the selected equations remain true, and can
be used as knowledge by a later resume. -/
theorem result_models (admitted :
    (machine protocol Value shot).Admits (s := before) (firing request shot before handle delivery receipt)) :
    ∀ e ∈ (after admitted).knowledge, e.1 = e.2 := by
  obtain ⟨_, _, solved⟩ := admitted.2.2.1
  exact solved

namespace VaryingFibre

open Mettapedia.GSLT.Dynamics.IndexedPolynomialProtocol.VaryingCanary

def choice (reply : Bool) : Resume query Result := ⟨7, .start, round, reply⟩

/-- One suspended dependent round, with both response occurrences present. -/
def start : Inventory query Result :=
  ⟨PUnit.unit, [], {0, 1, 2}, fun
    | 0 => .suspended 7 round
    | 1 => .offered 7 .ask false
    | _ => .offered 7 .ask true⟩

theorem first_admitted (shot : Shot) :
    (machine query Result shot).Admits (s := start) (firing (choice false) shot start 0 1 3) := by
  apply (admits_iff (choice false) shot start 0 1 3).mpr
  exact ⟨by decide, by decide, by decide, by decide, by simp [start], rfl, rfl⟩

/-- Consuming the continuation blocks the second response even though it
was offered before the first firing. -/
theorem one_shot_blocks_second :
    ¬ (machine query Result .one).Admits (s := after (first_admitted .one))
      (firing (choice true) .one (after (first_admitted .one)) 0 2 4) :=
  fun admitted => one_shot_spent (first_admitted .one)
    ((admits_iff _ _ _ _ _ _).mp admitted).2.1

/-- Keeping the continuation admits the second response. Each response
can be used once even though the continuation is available twice. -/
theorem multi_shot_admits_second :
    (machine query Result .many).Admits (s := after (first_admitted .many))
      (firing (choice true) .many (after (first_admitted .many)) 0 2 4) := by
  apply (admits_iff (choice true) .many (after (first_admitted .many)) 0 2 4).mpr
  have retained := multi_shot_retains (first_admitted .many)
  refine ⟨by decide, retained.1, by decide, by decide, result_models (first_admitted .many),
    retained.2.trans rfl, rfl⟩

/-- The actual publications retain the exact selected result, in the
unit and Boolean fibres respectively. -/
theorem different_fibres_published :
    (after (first_admitted .many)).label 3 = .completed 7 unitOutcome ∧
    (after multi_shot_admits_second).label 4 = .completed 7 boolOutcome :=
  ⟨(published_outcome (first_admitted .many)).2, (published_outcome multi_shot_admits_second).2⟩

end VaryingFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgrammingOnTheStep.IndexedResumption
