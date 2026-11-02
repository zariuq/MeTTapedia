import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LinearHornAdequacy

/-!
# Horn proofs retain installed schemas and computed activation origins

An activation receipt records its installed source schema, inputs, concrete
rule and actual successful activation equation. Each logical rule use keeps
that receipt. Pure ordinary CMR schedules construct independent Horn proofs
with the same ordered activation receipts; sequentializing such a proof lifts
back to real physical selections with those origins retained.

The activation function is supplied by an existing schema profile. This file
adds proof objects and origin-preserving comparisons, not another activation
engine or transition interpreter. Scope allocation, contextual stored-row
views and publication authority remain profile obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ActivatedHornProofs

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open Mettapedia.GSLT.Causality
open Mettapedia.Logic
open PositiveResourceProjection

universe uT uS uO uR uX
variable {T : Type uT} {S : Type uS} {O : Type uO} {R : Type uR} {X : Type uX}
  [DecidableEq O] (A : SubstitutionAction T S)
  (activate : R → X → Option (RuleInstance T)) (installed : Set R)

structure Origin where
  schema : R
  member : schema ∈ installed
  inputs : X
  rule : RuleInstance T
  computed : activate schema inputs = some rule

abbrev Selected := Origin activate installed × Selection O

def ordinary (selected : Selected (O := O) activate installed) : ConditionalSchedule.Firing T O :=
  (selected.1.rule, selected.2)

def AdmittedOrigin (assignment : S) :=
  {origin : Origin activate installed // origin.rule.read = [] ∧ origin.rule.checks = [] ∧
    A.Models assignment origin.rule.tell}

def system (assignment : S) : ResourceInteraction.System.{uT, max uT uR uX} T where
  Site := AdmittedOrigin A activate installed assignment
  Instance _ := PUnit.{(max uT uR uX) + 1}
  consume := fun {origin} _ => (origin.val.rule.take.map (A.apply assignment) : Multiset T)
  read _ := 0
  produce := fun {origin} _ => (origin.val.rule.produce.map (A.apply assignment) : Multiset T)

abbrev Proof (assignment : S) (before after : Multiset T) :=
  (system A activate installed assignment).HornProof before after

def originOf (assignment : S) (entry : (system A activate installed assignment).Entry) :
    Origin activate installed := entry.1.val

/-- Source uses retain their chosen activation receipts, even when two
different origins happen to compute equal concrete rules. -/
theorem proof_of_schedule [DecidableEq T] (assignment : S) (label : O → T)
    (structural : A.E = Eq) :
    ∀ (selected : List (Selected (O := O) activate installed)) (before : Configuration T O),
      ConditionalSchedule.Executable A label before (selected.map (ordinary activate installed)) →
      LinearHornAdequacy.Pure (selected.map (ordinary activate installed)) →
      A.Models assignment (ConditionalSchedule.follow label before (selected.map (ordinary activate installed))).equations →
      ∃ proof : Proof A activate installed assignment (labels (realized A assignment label) before.present)
          (labels (realized A assignment label)
            (ConditionalSchedule.follow label before (selected.map (ordinary activate installed))).present),
        proof.uses.map (originOf A activate installed assignment) = selected.map Prod.fst
  | [], _before, _, _, _ => ⟨.identity _, rfl⟩
  | selected :: rest, before, executable, pure, solved => by
      have middleModel := PositiveResourceSchedules.final_model_models_prefix A assignment label
        (rest.map (ordinary activate installed)) (selected.2.result label selected.1.rule before) executable.2 solved
      have currentPure := pure (ordinary activate installed selected) (List.mem_cons_self ..)
      have tells := (Selection.models_problem A executable.1 middleModel).2.2.2
      let admitted : AdmittedOrigin A activate installed assignment := ⟨selected.1, currentPure.1, currentPure.2, tells⟩
      let entry : (system A activate installed assignment).Entry := ⟨admitted, PUnit.unit⟩
      obtain ⟨frame, source, target, _⟩ := observed_frame A structural executable.1 middleModel
      dsimp only [ordinary] at source target
      have headProof : ∃ proof : Proof A activate installed assignment
          (labels (realized A assignment label) before.present)
          (labels (realized A assignment label) (selected.2.result label selected.1.rule before).present),
          proof.uses = [entry] := by
        rw [source, target]
        exact ⟨.tensor (.identity frame) (.rule entry), rfl⟩
      obtain ⟨head, headUses⟩ := headProof
      obtain ⟨tail, tailUses⟩ := proof_of_schedule assignment label structural rest
        (selected.2.result label selected.1.rule before) executable.2
        (fun chosen member => pure chosen (List.mem_cons_of_mem _ member)) solved
      refine ⟨.cut head tail, ?_⟩
      change (head.uses ++ tail.uses).map (originOf A activate installed assignment) = selected.1 :: rest.map Prod.fst
      rw [List.map_append, headUses]
      change originOf A activate installed assignment entry :: tail.uses.map (originOf A activate installed assignment) =
        selected.1 :: rest.map Prod.fst
      rw [tailUses]
      rfl

theorem schedule_of_resource_fires [DecidableEq T] (assignment : S) (label : O → T)
    (structural : A.E = Eq)
    (supply : ∀ (used : Finset O) (value : T), ∃ occurrence, occurrence ∉ used ∧ label occurrence = value) :
    ∀ (trace : List (system A activate installed assignment).Entry) (before : Configuration T O) (afterBag : Multiset T),
      A.Models assignment before.equations →
      (system A activate installed assignment).Fires trace (labels (realized A assignment label) before.present) afterBag →
      ∃ selected : List (Selected (O := O) activate installed),
        ConditionalSchedule.Executable A label before (selected.map (ordinary activate installed)) ∧
        LinearHornAdequacy.Pure (selected.map (ordinary activate installed)) ∧
        A.Models assignment (ConditionalSchedule.follow label before (selected.map (ordinary activate installed))).equations ∧
        labels (realized A assignment label)
          (ConditionalSchedule.follow label before (selected.map (ordinary activate installed))).present = afterBag ∧
        selected.map Prod.fst = trace.map (originOf A activate installed assignment)
  | [], _before, _afterBag, oldModel, fired => by
      exact ⟨[], ⟨assignment, oldModel⟩, by simp [LinearHornAdequacy.Pure], oldModel, fired.symm, rfl⟩
  | entry :: rest, before, afterBag, oldModel, fired => by
      obtain ⟨frame, source, target⟩ := ((system A activate installed assignment).enables_fire_iff_frame
        (labels (realized A assignment label) before.present)
        ((system A activate installed assignment).fire (labels (realized A assignment label) before.present) entry.2)
        entry.2 rfl).mp ⟨fired.1, rfl⟩
      obtain ⟨selection, valid, solved, observed⟩ := lift_no_read_frame A assignment label structural supply
        entry.1.val.rule entry.1.property.1 entry.1.property.2.1 before oldModel entry.1.property.2.2 frame source
      have nextObserved : labels (realized A assignment label)
          (selection.result label entry.1.val.rule before).present =
          (system A activate installed assignment).fire (labels (realized A assignment label) before.present) entry.2 :=
        observed.trans target.symm
      have tailFires : (system A activate installed assignment).Fires rest
          (labels (realized A assignment label) (selection.result label entry.1.val.rule before).present) afterBag := by
        rw [nextObserved]
        exact fired.2
      obtain ⟨selected, executable, pure, finalModel, finalBag, origins⟩ :=
        schedule_of_resource_fires assignment label structural supply rest
          (selection.result label entry.1.val.rule before) afterBag solved tailFires
      refine ⟨(entry.1.val, selection) :: selected, ⟨valid, executable⟩, ?_, finalModel, finalBag, ?_⟩
      · intro chosen member
        rcases List.mem_cons.mp member with rfl | later
        · exact ⟨entry.1.property.1, entry.1.property.2.1⟩
        · exact pure chosen later
      · change entry.1.val :: selected.map Prod.fst =
          originOf A activate installed assignment entry :: rest.map (originOf A activate installed assignment)
        rw [origins]
        rfl

/-- Independent logical proofs lift to actual occurrence choices while
preserving each installed source schema and successful activation receipt. -/
theorem schedule_of_proof [DecidableEq T] (assignment : S) (label : O → T)
    (structural : A.E = Eq)
    (supply : ∀ (used : Finset O) (value : T), ∃ occurrence, occurrence ∉ used ∧ label occurrence = value)
    (before : Configuration T O) (oldModel : A.Models assignment before.equations)
    (afterBag : Multiset T) (proof : Proof A activate installed assignment
      (labels (realized A assignment label) before.present) afterBag) :
    ∃ selected : List (Selected (O := O) activate installed),
      ConditionalSchedule.Executable A label before (selected.map (ordinary activate installed)) ∧
      LinearHornAdequacy.Pure (selected.map (ordinary activate installed)) ∧
      A.Models assignment (ConditionalSchedule.follow label before (selected.map (ordinary activate installed))).equations ∧
      labels (realized A assignment label)
        (ConditionalSchedule.follow label before (selected.map (ordinary activate installed))).present = afterBag ∧
      selected.map Prod.fst = proof.uses.map (originOf A activate installed assignment) :=
  schedule_of_resource_fires A activate installed assignment label structural supply proof.uses before afterBag oldModel
    ((system A activate installed assignment).horn_proof_fires (fun _ => rfl) proof)

theorem pure_schedule_iff_proof [DecidableEq T] (assignment : S) (label : O → T)
    (structural : A.E = Eq)
    (supply : ∀ (used : Finset O) (value : T), ∃ occurrence, occurrence ∉ used ∧ label occurrence = value)
    (before : Configuration T O) (oldModel : A.Models assignment before.equations) (afterBag : Multiset T) :
    (∃ selected : List (Selected (O := O) activate installed),
      ConditionalSchedule.Executable A label before (selected.map (ordinary activate installed)) ∧
      LinearHornAdequacy.Pure (selected.map (ordinary activate installed)) ∧
      A.Models assignment (ConditionalSchedule.follow label before (selected.map (ordinary activate installed))).equations ∧
      labels (realized A assignment label)
        (ConditionalSchedule.follow label before (selected.map (ordinary activate installed))).present = afterBag) ↔
      Nonempty (Proof A activate installed assignment (labels (realized A assignment label) before.present) afterBag) := by
  constructor
  · rintro ⟨selected, executable, pure, solved, observed⟩
    obtain ⟨proof, _⟩ := proof_of_schedule A activate installed assignment label structural selected before executable pure solved
    exact ⟨observed ▸ proof⟩
  · rintro ⟨proof⟩
    obtain ⟨selected, executable, pure, solved, observed, _⟩ :=
      schedule_of_proof A activate installed assignment label structural supply before oldModel afterBag proof
    exact ⟨selected, executable, pure, solved, observed⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ActivatedHornProofs
