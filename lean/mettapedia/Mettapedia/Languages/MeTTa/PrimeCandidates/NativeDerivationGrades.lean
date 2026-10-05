import Mettapedia.Languages.MeTTa.PrimeCandidates.NativeCandidateGrades
import Mettapedia.GSLT.Core.WeightedMuScheduler
import Mettapedia.GSLT.Core.RouteTrace
import Mettapedia.GSLT.Logic.GradedSupport
import Mettapedia.GSLT.Dynamics.SemiringTraversal
import Mettapedia.GSLT.Dynamics.ProvenanceInterpretation

/-!
# Physical native equation choices and graded interpretations

The graded transition list is constructed from the actual Need successors.
A newly recorded equation-choice receipt identifies the physical row, and
its still-unforced local state supplies the candidate cell environment.
Administrative instructions have unit grade. The interpretation uses the
existing graded-where language, semiring traversal and provenance algebra.

This is a semantic grade: zero disables a weighted edge in its support
interpretation. A zero scheduling priority does not do that; advisory work
has a separate source-preserving projection in `NativeCandidateGrades`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.NativeDerivationGrades

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Machines.BranchLocalNeed
open NeedReference
open Mettapedia.GSLT.Core
open WeightedMuScheduler
open NativeEquationNeed NativeCandidateGrades

open Mettapedia.GSLT
open Mettapedia.GSLT.Dynamics

/-- Detect a new physical equation choice, before executing its RHS. The
serial check prevents a retained receipt from being charged again by later
instructions that do not append receipts. -/
def newRow (before after : NativeMachine) : Option Row :=
  if before.world.receipts.nextSerial < after.world.receipts.nextSerial then
    match after.world.receipts.nodes, after.control with
    | receipt :: _, .run (.evaluate body environment) _ =>
        match receipt.payload with
        | .chooseRule _ (.equation index) => some ⟨index, body, environment⟩
        | _ => none
    | _, _ => none
  else none

/-- This is the actual capture construction, not an assumed grade oracle. -/
theorem captured_choice (machine : NativeMachine) (base : NativeWorld)
    (cell : CellId) (record : CellRecord Origin Atom Empty) (owner : EvaluatorId)
    (stack : List (Frame Resume)) (ordinal : Nat) (row : Row)
    (serial : base.receipts.nextSerial = machine.world.receipts.nextSerial) :
    newRow machine (captureOne machine base cell record owner stack ordinal row).body =
      some row := by
  simp [newRow, captureOne, Captured.body, recorded, World.record, World.fork,
    World.setKnownCache, ReceiptGraph.append, serial]

private theorem captured_rows_choice (machine : NativeMachine) (base : NativeWorld)
    (cell : CellId) (record : CellRecord Origin Atom Empty) (owner : EvaluatorId)
    (stack : List (Frame Resume)) (ordinal : Nat) (admitted : List Row)
    (serial : base.receipts.nextSerial = machine.world.receipts.nextSerial)
    (capture : Captured)
    (member : capture ∈ captureRows machine base cell record owner stack ordinal admitted) :
    newRow machine capture.body = some capture.row := by
  induction admitted generalizing ordinal with
  | nil => simp [captureRows] at member
  | cons row rest ih =>
      rcases List.mem_cons.mp member with same | tail
      · subst capture
        exact captured_choice machine base cell record owner stack ordinal row serial
      · exact ih (ordinal + 1) tail

theorem application_capture_choice (program : Program) (head : String)
    (arguments : List CellId) (machine : NativeMachine) (cell : CellId)
    (stack : List (Frame Resume)) (capture : Captured)
    (member : capture ∈ captureApplication program head arguments machine cell stack) :
    newRow machine capture.body = some capture.row :=
  captured_rows_choice machine
    { machine.world with nextEvaluator := machine.world.nextEvaluator + 1 }
    cell ⟨.application head arguments, .suspended⟩ machine.world.nextEvaluator stack 0
    (rows program head arguments) rfl capture member

/-- On an actual suspended application, extracting a newly charged physical
row is equivalent in both directions to independent authored activation. -/
theorem native_choice_iff_activation (program : Program) (head : String)
    (arguments : List CellId) (machine : NativeMachine) (cell : CellId)
    (stack : List (Frame Resume))
    (forcing : machine.control = .force cell stack)
    (present : machine.world.heap.lookup cell =
      some ⟨.application head arguments, .suspended⟩)
    (nonempty : rowCandidates program head arguments ≠ []) (row : Row) :
    (∃ next ∈ NeedReference.step (specification program) machine,
      newRow machine next = some row) ↔
      Activates program head arguments (.equation row.index)
        (.evaluate row.body row.environment) := by
  rw [← captured_admission_iff program head arguments machine cell stack row]
  rw [← captures_are_native_step program head arguments machine cell stack forcing present nonempty]
  constructor
  · rintro ⟨next, member, chosen⟩
    obtain ⟨capture, admitted, rfl⟩ := List.mem_map.mp member
    have actual := application_capture_choice program head arguments machine cell stack capture admitted
    exact ⟨capture, admitted, Option.some.inj (actual.symm.trans chosen)⟩
  · rintro ⟨capture, admitted, same⟩
    exact ⟨capture.body, List.mem_map.mpr ⟨capture, admitted, rfl⟩,
      (application_capture_choice program head arguments machine cell stack capture admitted).trans
        (congrArg some same)⟩

/-- Every equation receipt extracted from an actual native transition comes
from a suspended application and an independently admitted source activation.
Cached observations, allocation and administrative steps cannot forge a row. -/
theorem native_row_has_activation (program : Program) (before after : NativeMachine)
    (row : Row) (member : after ∈ NeedReference.step (specification program) before)
    (chosen : newRow before after = some row) :
    ∃ (cell : CellId) (stack : List (Frame Resume)) (head : String) (arguments : List CellId),
      before.control = .force cell stack ∧
      before.world.heap.lookup cell = some ⟨.application head arguments, .suspended⟩ ∧
      Activates program head arguments (.equation row.index)
        (.evaluate row.body row.environment) := by
  rcases before with ⟨world, control, work⟩
  cases control with
  | halted outcome => simp [NeedReference.step] at member
  | force cell stack =>
      simp only [NeedReference.step] at member
      split at member
      · simp only [List.mem_singleton] at member
        subst after
        simp [newRow, retryMachine, finished, recorded, World.record, ReceiptGraph.append] at chosen
      · rename_i record present
        rcases record with ⟨origin, cache⟩
        cases cache with
        | value value =>
            simp only [List.mem_singleton] at member
            subst after
            simp [newRow, finished, recorded, World.record, ReceiptGraph.append] at chosen
        | stableFault fault => cases fault
        | evaluating owner =>
            simp only [List.mem_singleton] at member
            subst after
            simp [newRow, retryMachine, finished, recorded, World.record, ReceiptGraph.append] at chosen
        | suspended =>
            cases origin with
            | expression term environment =>
                simp only [specification, alternatives, branchAlternatives, List.mem_cons,
                  List.not_mem_nil, or_false] at member
                subst after
                cases started : start program term environment <;>
                  simp [newRow, finished, recorded, World.record, World.fork,
                    World.setKnownCache, ReceiptGraph.append, started] at chosen
            | application head arguments =>
                by_cases noRows : rowCandidates program head arguments = []
                · simp only [specification, alternatives, noRows, List.mem_singleton] at member
                  subst after
                  simp [newRow, retryMachine, finished, recorded, World.record,
                    ReceiptGraph.append] at chosen
                · refine ⟨cell, stack, head, arguments, rfl, present, ?_⟩
                  exact (native_choice_iff_activation program head arguments
                    ⟨world, .force cell stack, work⟩ cell stack rfl present noRows row).mp
                    ⟨after, by simpa only [NeedReference.step, present] using member, chosen⟩
  | run state stack =>
      simp only [NeedReference.step] at member
      split at member <;>
        repeat' first
          | split at member
          | simp only [List.mem_singleton] at member
            subst after
            simp [newRow, retryMachine, finished, recorded, World.record,
              ReceiptGraph.append] at chosen
      all_goals
        first
        | cases_type Empty
        | rename_i action source resume actionEq recordOption record present
            allocation allocatedWorld allocatedCell allocationEq
          guard_hyp actionEq : (specification program).action state = .resample source resume
          cases next : afterAllocation resume allocatedCell <;>
            simp [specification, next] at chosen
        | skip
      all_goals
        rename_i action origin resume actionEq allocation allocatedWorld allocatedCell allocationEq
        simp only [World.allocate?] at allocationEq
        split at allocationEq
        · contradiction
        · simp only [Option.some.injEq, Prod.mk.injEq] at allocationEq
          rw [← allocationEq.1] at chosen
          cases advanced : (specification program).afterAllocation resume allocatedCell <;>
            simp [World.record, ReceiptGraph.append, advanced] at chosen
  | returned outcome stack =>
      simp only [NeedReference.step] at member
      split at member <;>
        repeat' first
          | split at member
          | simp only [List.mem_singleton] at member
            subst after
            simp [newRow, retryMachine, finished, recorded, World.record,
              ReceiptGraph.append, World.setKnownCache] at chosen


theorem unchanged_receipts_no_grade (before after : NativeMachine)
    (same : after.world.receipts.nextSerial = before.world.receipts.nextSerial) :
    newRow before after = none := by simp [newRow, same]

def edgeGrade {V : Type} [Semiring V] (clause : WeighClause V Row)
    (before after : NativeMachine) : V :=
  match newRow before after with
  | some row => WeighClause.eval row clause
  | none => 1

def gradedStep {V : Type} [Semiring V] (program : Program)
    (clause : WeighClause V Row) (before : NativeMachine) : List (NativeMachine × V) :=
  (NeedReference.step (specification program) before).map
    (fun after => (after, edgeGrade clause before after))

theorem graded_step_iff {V : Type} [Semiring V] (program : Program)
    (clause : WeighClause V Row) (before after : NativeMachine) (grade : V) :
    (after, grade) ∈ gradedStep program clause before ↔
      after ∈ NeedReference.step (specification program) before ∧
        grade = edgeGrade clause before after := by
  simp only [gradedStep, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨next, member, rfl, equal⟩; exact ⟨member, equal.symm⟩
  · rintro ⟨member, rfl⟩; exact ⟨after, member, rfl, rfl⟩

theorem graded_step_multiplicity {V : Type} [Semiring V] (program : Program)
    (clause : WeighClause V Row) (before : NativeMachine) :
    (gradedStep program clause before).length =
      (NeedReference.step (specification program) before).length := by simp [gradedStep]

private theorem occurrence_of_member (program : Program) (before after : NativeMachine)
    (member : after ∈ NeedReference.step (specification program) before) :
    Nonempty (StepOccurrence (specification program) before after) := by
  obtain ⟨index, bound, equal⟩ := List.mem_iff_getElem.mp member
  exact ⟨⟨index, (List.getElem?_eq_some_iff).mpr ⟨bound, equal⟩⟩⟩

/-- Semantic weighting can suppress an edge, but cannot invent a native
transition or replace the environment in which an equation is activated. -/
theorem enabled_path_erases {V : Type} [Semiring V] (program : Program)
    (clause : WeighClause V Row) {count : Nat} {before after : NativeMachine}
    (path : GradedSupport.Reach (gradedStep program clause) count before after) :
    Steps (specification program) count before after := by
  induction path with
  | refl state => exact .refl state
  | @fire count state final edge member _ _ ih =>
      have member' := ((graded_step_iff program clause state edge.1 edge.2).mp member).1
      obtain ⟨occurrence⟩ := occurrence_of_member program state edge.1 member'
      exact .cons occurrence ih

@[simp] theorem unit_edge_grade {V : Type} [Semiring V] (before after : NativeMachine) :
    edgeGrade (.scalar (1 : V)) before after = 1 := by
  simp only [edgeGrade]
  split <;> rfl

/-- A unit semantic annotation conservatively embeds the ordinary native
execution, including duplicate rows and cached-argument steps. -/
theorem unit_path_iff {V : Type} [Semiring V] [Nontrivial V] (program : Program)
    (count : Nat) (before after : NativeMachine) :
    GradedSupport.Reach (gradedStep program (.scalar (1 : V))) count before after ↔
      Steps (specification program) count before after := by
  constructor
  · exact enabled_path_erases program _
  · intro path
    induction path with
    | refl state => exact .refl state
    | @cons count state next final occurrence _ ih =>
        exact GradedSupport.Reach.fire
          ((graded_step_iff program (.scalar (1 : V)) state next 1).mpr
            ⟨occurrence.mem _, (unit_edge_grade state next).symm⟩)
          one_ne_zero ih

/-- The machine heap is a mathematical map, so equality of arbitrary source
states is used only by this noncomputable coefficient denotation. Native
transition generation and advisory evaluation remain executable. -/
noncomputable def coefficient {V : Type} [Semiring V] [DecidableEq V]
    (program : Program) (clause : WeighClause V Row)
    (budget : Nat) (before after : NativeMachine) : V := by
  classical
  exact GradedSupport.denote (gradedStep program clause) budget before after

theorem coefficient_support_iff {V : Type} [Semiring V] [DecidableEq V]
    (noCancellation : GradedSupport.NoCancellation V) (program : Program) (clause : WeighClause V Row)
    (budget : Nat) (before after : NativeMachine) :
    coefficient program clause budget before after ≠ 0 ↔
      GradedSupport.ReachIn (gradedStep program clause) budget before after := by
  classical
  exact GradedSupport.denote_ne_zero_iff_reachIn noCancellation

/-- Even in a cancelling algebra, every nonzero native coefficient has an
independently valid source path within the budget. -/
theorem coefficient_source_path {V : Type} [Semiring V] [DecidableEq V]
    (program : Program) (clause : WeighClause V Row) (budget : Nat)
    (before after : NativeMachine) (nonzero : coefficient program clause budget before after ≠ 0) :
    ∃ count ≤ budget, Steps (specification program) count before after := by
  classical
  have reached := GradedSupport.reachIn_of_denote_ne_zero nonzero
  obtain ⟨count, bound, path, _⟩ := GradedSupport.reach_of_reachIn reached
  exact ⟨count, bound, enabled_path_erases program clause path⟩

/-- Source paths decorated by the actual newly observed physical choices.
This relation also retains administrative steps, which contribute no cause. -/
abbrev RowTrace (program : Program) :=
  Mettapedia.GSLT.Ultrainfinite.Route.ObservedTrace
    (Step := StepOccurrence (specification program))
    (fun {before after} _ => (newRow before after).toList)

theorem row_trace_source (program : Program) {count : Nat} {before after : NativeMachine}
    {choices : List Row} (trace : RowTrace program count before after choices) :
    Steps (specification program) count before after := by
  induction trace with
  | refl state => exact .refl state
  | cons edge _ ih => exact .cons edge ih

theorem source_has_row_trace (program : Program) {count : Nat} {before after : NativeMachine}
    (path : Steps (specification program) count before after) :
    ∃ choices, RowTrace program count before after choices := by
  induction path with
  | refl state => exact ⟨[], .refl state⟩
  | cons edge _ ih =>
      obtain ⟨choices, trace⟩ := ih
      exact ⟨_, .cons edge trace⟩

/-- Every recorded row is licensed by the authored program with its captured
arguments. The trace still distinguishes repeated firings of the same row. -/
theorem row_trace_admitted (program : Program) {count : Nat} {before after : NativeMachine}
    {choices : List Row} (trace : RowTrace program count before after choices)
    (row : Row) (member : row ∈ choices) :
    ∃ (head : String) (arguments : List CellId),
      Activates program head arguments (.equation row.index)
        (.evaluate row.body row.environment) := by
  obtain ⟨source, target, edge, reported⟩ :=
    Mettapedia.GSLT.Ultrainfinite.Route.ObservedTrace.mem_has_step _ trace row member
  have chosen : newRow source target = some row := by simpa using reported
  obtain ⟨_, _, head, arguments, _, _, admitted⟩ :=
    native_row_has_activation program source target row (edge.mem _) chosen
  exact ⟨head, arguments, admitted⟩

def interpret {V : Type} [Semiring V] (clause : WeighClause V Row)
    (choices : List Row) : V := ProvenanceInterpretation.interpDeriv (fun row => WeighClause.eval row clause) choices

theorem interpret_transition {V : Type} [Semiring V] (clause : WeighClause V Row)
    (before after : NativeMachine) (rest : List Row) :
    interpret clause ((newRow before after).toList ++ rest) =
      edgeGrade clause before after * interpret clause rest := by
  cases choice : newRow before after <;>
    simp [interpret, ProvenanceInterpretation.interpDeriv, edgeGrade, choice]

/-- Alternative native derivations add; using one physical row several times
retains repeated uses of that same cause. Duplicate authored rows have
different indices and therefore different causes. -/
def aggregate {V : Type} [Semiring V] (clause : WeighClause V Row)
    (derivations : List (List Row)) : V := SemiringTraversal.weightSum (interpret clause) derivations

theorem aggregate_permutation {V : Type} [Semiring V] (clause : WeighClause V Row)
    {left right : List (List Row)} (same : left.Perm right) :
    aggregate clause left = aggregate clause right := SemiringTraversal.weightSum_perm _ same

theorem aggregate_product {V : Type} [Semiring V] (clause : WeighClause V Row)
    (families : List (List (List Row))) :
    SemiringTraversal.weightSum (SemiringTraversal.tupleWeight (interpret clause)) (SemiringTraversal.orderedProd families) =
      (families.map (aggregate clause)).prod := SemiringTraversal.weightSum_orderedProd _ _

/-- Native physical-row provenance is interpreted by the existing universal
semiring homomorphism. No probability independence claim follows from it. -/
theorem provenance_interpretation {V : Type} [CommSemiring V]
    (clause : WeighClause V Row) (derivations : List (List Row)) :
    MvPolynomial.eval₂ (Nat.castRingHom V) (fun row => WeighClause.eval row clause)
      (ProvenanceInterpretation.provenance derivations) = aggregate clause derivations :=
  ProvenanceInterpretation.interp_provenance _ _

end Mettapedia.Languages.MeTTa.PrimeCandidates.NativeDerivationGrades
