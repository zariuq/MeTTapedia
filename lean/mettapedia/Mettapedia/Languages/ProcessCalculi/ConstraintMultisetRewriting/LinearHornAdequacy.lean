import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PositiveResourceSchedules
import Mettapedia.GSLT.Causality.ResourceLinearHorn

/-!
# Pure constraint schedules and independent multiplicative Horn proofs

The declared logical rules are structural no-read/no-check instances whose
tells hold under one shared substitution. Ordinary firing receipts construct
independent identity/rule/tensor/cut proofs. Conversely, sequentializing such
a logical proof and lifting its bag frames constructs an actual CMR schedule
with distinct takes, fresh raw outputs and the same complete-store model.

The comparison observes full bags, including the residual frame, and retains
the raw rule-use list. It does not identify physical selections, ordered
enumeration multiplicities, shared-read concurrency or connection matings.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LinearHornAdequacy

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open Mettapedia.GSLT.Causality
open Mettapedia.Logic
open PositiveResourceProjection

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]
  (A : SubstitutionAction T S) (program : Set (RuleInstance T))

def AdmittedRule (assignment : S) :=
  {rule : RuleInstance T // rule ∈ program ∧ rule.read = [] ∧ rule.checks = [] ∧ A.Models assignment rule.tell}

def system (assignment : S) : ResourceInteraction.System.{uT, uT} T where
  Site := AdmittedRule A program assignment
  Instance _ := PUnit.{uT + 1}
  consume := fun {rule} _ => (rule.val.take.map (A.apply assignment) : Multiset T)
  read _ := 0
  produce := fun {rule} _ => (rule.val.produce.map (A.apply assignment) : Multiset T)

abbrev Proof (assignment : S) (before after : Multiset T) :=
  (system A program assignment).HornProof before after

def rawRule (assignment : S) (entry : (system A program assignment).Entry) : RuleInstance T := entry.1.val

def Pure (schedule : List (ConditionalSchedule.Firing T O)) : Prop :=
  ∀ firing ∈ schedule, firing.1.read = [] ∧ firing.1.checks = []

def Declared (schedule : List (ConditionalSchedule.Firing T O)) : Prop :=
  ∀ firing ∈ schedule, firing.1 ∈ program

theorem proof_of_constraint_schedule [DecidableEq T] (assignment : S) (label : O → T)
    (structural : A.E = Eq) :
    ∀ (schedule : List (ConditionalSchedule.Firing T O)) (before : Configuration T O),
      ConditionalSchedule.Executable A label before schedule → Pure schedule → Declared program schedule →
      A.Models assignment (ConditionalSchedule.follow label before schedule).equations →
      ∃ proof : Proof A program assignment (labels (realized A assignment label) before.present)
          (labels (realized A assignment label) (ConditionalSchedule.follow label before schedule).present),
        proof.uses.map (rawRule A program assignment) = schedule.map Prod.fst
  | [], _before, _, _, _, _ => ⟨.identity _, rfl⟩
  | firing :: rest, before, executable, pure, declared, solved => by
      have middleModel := PositiveResourceSchedules.final_model_models_prefix A assignment label rest
        (firing.2.result label firing.1 before) executable.2 solved
      have currentPure := pure firing (List.mem_cons_self ..)
      have tells := (Selection.models_problem A executable.1 middleModel).2.2.2
      let admitted : AdmittedRule A program assignment := ⟨firing.1, declared firing (List.mem_cons_self ..), currentPure.1, currentPure.2, tells⟩
      let entry : (system A program assignment).Entry := ⟨admitted, PUnit.unit⟩
      obtain ⟨frame, source, target, _⟩ := observed_frame A structural executable.1 middleModel
      have headProof : ∃ proof : Proof A program assignment
          (labels (realized A assignment label) before.present)
          (labels (realized A assignment label) (firing.2.result label firing.1 before).present),
          proof.uses = [entry] := by
        rw [source, target]
        exact ⟨.tensor (.identity frame) (.rule entry), rfl⟩
      obtain ⟨head, headUses⟩ := headProof
      obtain ⟨tail, tailUses⟩ := proof_of_constraint_schedule assignment label structural rest
        (firing.2.result label firing.1 before) executable.2
        (fun selected member => pure selected (List.mem_cons_of_mem _ member))
        (fun selected member => declared selected (List.mem_cons_of_mem _ member)) solved
      refine ⟨.cut head tail, ?_⟩
      change (head.uses ++ tail.uses).map (rawRule A program assignment) = firing.1 :: rest.map Prod.fst
      rw [List.map_append, headUses]
      change rawRule A program assignment entry :: tail.uses.map (rawRule A program assignment) = firing.1 :: rest.map Prod.fst
      rw [tailUses]
      rfl

theorem constraint_schedule_of_resource_fires [DecidableEq T] (assignment : S) (label : O → T)
    (structural : A.E = Eq)
    (supply : ∀ (used : Finset O) (value : T), ∃ occurrence, occurrence ∉ used ∧ label occurrence = value) :
    ∀ (trace : List (system A program assignment).Entry) (before : Configuration T O) (afterBag : Multiset T),
      A.Models assignment before.equations →
      (system A program assignment).Fires trace (labels (realized A assignment label) before.present) afterBag →
      ∃ schedule : List (ConditionalSchedule.Firing T O),
        ConditionalSchedule.Executable A label before schedule ∧ Pure schedule ∧ Declared program schedule ∧
        A.Models assignment (ConditionalSchedule.follow label before schedule).equations ∧
        labels (realized A assignment label) (ConditionalSchedule.follow label before schedule).present = afterBag ∧
        schedule.map Prod.fst = trace.map (rawRule A program assignment)
  | [], before, afterBag, oldModel, fired => by
      exact ⟨[], ⟨assignment, oldModel⟩, by simp [Pure], by simp [Declared], oldModel, fired.symm, rfl⟩
  | entry :: rest, before, afterBag, oldModel, fired => by
      obtain ⟨frame, source, target⟩ := ((system A program assignment).enables_fire_iff_frame
        (labels (realized A assignment label) before.present)
        ((system A program assignment).fire (labels (realized A assignment label) before.present) entry.2)
        entry.2 rfl).mp ⟨fired.1, rfl⟩
      obtain ⟨selection, valid, solved, observed⟩ := lift_no_read_frame A assignment label structural supply
        entry.1.val entry.1.property.2.1 entry.1.property.2.2.1 before oldModel entry.1.property.2.2.2 frame source
      have nextObserved : labels (realized A assignment label) (selection.result label entry.1.val before).present =
          (system A program assignment).fire (labels (realized A assignment label) before.present) entry.2 :=
        observed.trans target.symm
      have tailFires : (system A program assignment).Fires rest
          (labels (realized A assignment label) (selection.result label entry.1.val before).present) afterBag := by
        rw [nextObserved]
        exact fired.2
      obtain ⟨schedule, executable, pure, declared, finalModel, finalBag, rules⟩ :=
        constraint_schedule_of_resource_fires assignment label structural supply rest
          (selection.result label entry.1.val before) afterBag solved tailFires
      refine ⟨(entry.1.val, selection) :: schedule, ⟨valid, executable⟩, ?_, ?_, finalModel, finalBag, ?_⟩
      · intro selected member
        rcases List.mem_cons.mp member with rfl | later
        · exact ⟨entry.1.property.2.1, entry.1.property.2.2.1⟩
        · exact pure selected later
      · intro selected member
        rcases List.mem_cons.mp member with rfl | later
        · exact entry.1.property.1
        · exact declared selected later
      · change entry.1.val :: schedule.map Prod.fst = rawRule A program assignment entry :: rest.map (rawRule A program assignment)
        rw [rules]
        rfl

/-- The backward direction uses the independent logical proof: its actual
sequentialization supplies the frames which are lifted to fresh CMR choices. -/
theorem constraint_schedule_of_proof [DecidableEq T] (assignment : S) (label : O → T)
    (structural : A.E = Eq)
    (supply : ∀ (used : Finset O) (value : T), ∃ occurrence, occurrence ∉ used ∧ label occurrence = value)
    (before : Configuration T O) (oldModel : A.Models assignment before.equations)
    (afterBag : Multiset T) (proof : Proof A program assignment
      (labels (realized A assignment label) before.present) afterBag) :
    ∃ schedule : List (ConditionalSchedule.Firing T O),
      ConditionalSchedule.Executable A label before schedule ∧ Pure schedule ∧ Declared program schedule ∧
      A.Models assignment (ConditionalSchedule.follow label before schedule).equations ∧
      labels (realized A assignment label) (ConditionalSchedule.follow label before schedule).present = afterBag ∧
      schedule.map Prod.fst = proof.uses.map (rawRule A program assignment) :=
  constraint_schedule_of_resource_fires A program assignment label structural supply proof.uses before afterBag oldModel
    ((system A program assignment).horn_proof_fires (fun _ => rfl) proof)

theorem pure_schedule_iff_horn_proof [DecidableEq T] (assignment : S) (label : O → T)
    (structural : A.E = Eq)
    (supply : ∀ (used : Finset O) (value : T), ∃ occurrence, occurrence ∉ used ∧ label occurrence = value)
    (before : Configuration T O) (oldModel : A.Models assignment before.equations) (afterBag : Multiset T) :
    (∃ schedule : List (ConditionalSchedule.Firing T O),
      ConditionalSchedule.Executable A label before schedule ∧ Pure schedule ∧ Declared program schedule ∧
      A.Models assignment (ConditionalSchedule.follow label before schedule).equations ∧
      labels (realized A assignment label) (ConditionalSchedule.follow label before schedule).present = afterBag) ↔
        Nonempty (Proof A program assignment (labels (realized A assignment label) before.present) afterBag) := by
  constructor
  · rintro ⟨schedule, executable, pure, declared, solved, observed⟩
    obtain ⟨proof, _⟩ := proof_of_constraint_schedule A program assignment label structural schedule before executable pure declared solved
    exact ⟨observed ▸ proof⟩
  · rintro ⟨proof⟩
    obtain ⟨schedule, executable, pure, declared, solved, observed, _⟩ :=
      constraint_schedule_of_proof A program assignment label structural supply before oldModel afterBag proof
    exact ⟨schedule, executable, pure, declared, solved, observed⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LinearHornAdequacy
