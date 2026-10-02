import Mettapedia.Languages.MeTTa.PrimeCandidates.NativeEquationNeed

/-!
# Source preparation and finite native Need instructions

The admitted equation reader consumes ordinary parsed `defineEq` commands.
Finite candidate scans preserve physical row multiplicity. Local instructions
allocate or demand one cell, retain a return, or publish one finite value;
recursive body evaluation remains subsequent owned work.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.NativeEquationNeed

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Machines.BranchLocalNeed.NeedReference
open Mettapedia.OSLF.MeTTaIL.MeTTaSyntaxQuotation (ProgramCommand)

def parameterNames : List Atom → Option (List String)
  | [] => some []
  | .var name :: rest => (parameterNames rest).map (name :: ·)
  | _ => none

theorem parameterNames_variables (names : List String) :
    parameterNames (names.map Atom.var) = some names := by
  induction names with
  | nil => rfl
  | cons name rest ih => simp [parameterNames, ih]

def readEquation : ProgramCommand Atom → Option Equation
  | .defineEq (.expression (.symbol head :: parameters)) body =>
      (parameterNames parameters).map (fun names => ⟨head, names, body⟩)
  | _ => none

theorem read_authored_equation (equation : Equation) :
    readEquation equation.command = some equation := by
  cases equation
  simp [readEquation, Equation.command, Equation.lhs, parameterNames_variables]

def authored (program : Program) : List (ProgramCommand Atom) :=
  program.map Equation.command

theorem read_authored_program (program : Program) :
    (authored program).filterMap readEquation = program := by
  induction program with
  | nil => rfl
  | cons equation rest ih => simp [authored, read_authored_equation]

/-- The reader rejects a constrained pattern from this fragment. It does not
invent a positional variable binding for that pattern. -/
example : readEquation (.defineEq (.expression [.symbol "unbox",
    .expression [.symbol "Box", .var "x"]]) (.var "x")) = none := rfl

theorem rowCandidates_length (program : Program) (head : String) (arguments : List CellId) :
    (rowCandidates program head arguments).length ≤ program.length := by
  exact (List.length_filterMap_le _ _).trans_eq (List.length_zipIdx)

theorem alternatives_length (program : Program) (origin : Origin) :
    ((specification program).alternatives origin).length ≤ max 1 program.length := by
  cases origin with
  | expression term environment =>
      exact Nat.le_max_left _ _
  | application head arguments =>
      exact le_trans (rowCandidates_length program head arguments) (Nat.le_max_right _ _)

/-- One force can fork only as many physical rows as the finite source scan
admits. This bound is size dependent, rather than a constant-time claim. -/
theorem force_fork_bound (program : Program) (machine : NativeMachine)
    (cell : CellId) (stack : List (Frame Resume))
    (record : CellRecord Origin Atom Empty)
    (control : machine.control = .force cell stack)
    (found : machine.world.heap.lookup cell = some record)
    (suspended : record.cache = .suspended)
    (nonempty : (specification program).alternatives record.origin ≠ []) :
    (step (specification program) machine).length ≤ max 1 program.length := by
  rw [suspended_step_preserves_multiplicity (specification program) machine cell stack
    record control found suspended nonempty]
  exact alternatives_length program record.origin

/-- These are the finite structural visits performed by local instruction
construction, separate from heap lookup/update operations and body execution.
The persistent lists retained in returns explain the nonconstant terms. -/
def instructionVisits : Local → Nat
  | .evaluate _ _ => 1
  | .output _ => 1
  | .forward _ => 1
  | .bind _ _ _ _ => 1
  | .arguments _ _ (_ :: _) _ => 1
  | .arguments _ cells [] _ => cells.length + 2
  | .normalize _ _ (_ :: _) => 1
  | .normalize _ values [] => values.length + 2

def allocationReturnVisits : Resume → Nat
  | .allocatedArgument _ cells _ _ => cells.length + 1
  | _ => 1

def demandReturnVisits : Resume → Nat
  | .normalizedChild _ values _ => values.length + 1
  | _ => 1

theorem instruction_positive (state : Local) : 0 < instructionVisits state := by
  cases state <;> simp [instructionVisits]
  · split <;> simp
  · split <;> simp

/-- Primitive equality probes and list visits are the units of the following
metered realization. Equality on a string or an integer is one declared
operation; its byte/bit cost, heap operations and C execution are separate. -/
def memberMeter (name : String) : List String → Bool × Nat
  | [] => (false, 1)
  | first :: rest =>
      if name = first then (true, 1)
      else let suffix := memberMeter name rest; (suffix.1, suffix.2 + 1)

theorem memberMeter_correct (name : String) (names : List String) :
    (memberMeter name names).1 = true ↔ name ∈ names := by
  induction names with
  | nil => simp [memberMeter]
  | cons first rest ih =>
      simp only [memberMeter]
      split
      next same => simp [same]
      next different => simpa [different] using ih

theorem memberMeter_bound (name : String) (names : List String) :
    (memberMeter name names).2 ≤ names.length + 1 := by
  induction names with
  | nil => simp [memberMeter]
  | cons first rest ih =>
      simp only [memberMeter]
      split <;> simp_all

def distinctMeter : List String → Bool × Nat
  | [] => (true, 1)
  | first :: rest =>
      let member := memberMeter first rest
      if member.1 then (false, member.2 + 1)
      else let suffix := distinctMeter rest
           (suffix.1, member.2 + suffix.2 + 1)

theorem distinctMeter_correct (names : List String) :
    (distinctMeter names).1 = true ↔ names.Nodup := by
  induction names with
  | nil => simp [distinctMeter]
  | cons first rest ih =>
      simp only [distinctMeter]
      split
      next present =>
        have member := (memberMeter_correct first rest).mp present
        simp [List.nodup_cons, member]
      next absent =>
        have notMember : first ∉ rest := by
          intro member
          exact absent ((memberMeter_correct first rest).mpr member)
        simpa [List.nodup_cons, notMember] using ih

theorem distinctMeter_bound (names : List String) :
    (distinctMeter names).2 ≤ (names.length + 1) ^ 2 := by
  induction names with
  | nil => simp [distinctMeter]
  | cons first rest ih =>
      have member := memberMeter_bound first rest
      simp only [distinctMeter]
      split <;> simp only [List.length_cons]
      · nlinarith
      · nlinarith

def rowMeter (head : String) (arguments : List CellId) (row : Equation × Nat) :
    Option (Rule × Local) × Nat :=
  let distinct := distinctMeter row.1.parameters
  let visits := distinct.2 + 2 * row.1.parameters.length + arguments.length + 3
  if row.1.head = head ∧ distinct.1 = true ∧ row.1.parameters.length = arguments.length then
    (some (.equation row.2, .evaluate row.1.body (row.1.parameters.zip arguments)), visits)
  else (none, visits)

def scanMeter (head : String) (arguments : List CellId) :
    List (Equation × Nat) → List (Rule × Local) × Nat
  | [] => ([], 1)
  | row :: rest =>
      let current := rowMeter head arguments row
      let suffix := scanMeter head arguments rest
      (current.1.toList ++ suffix.1, current.2 + suffix.2 + 1)

theorem scanMeter_correct (head : String) (arguments : List CellId)
    (rows : List (Equation × Nat)) :
    (scanMeter head arguments rows).1 = rows.filterMap (fun (equation, row) =>
      if equation.head = head ∧ equation.parameters.Nodup ∧
          equation.parameters.length = arguments.length then
        some (.equation row, .evaluate equation.body (equation.parameters.zip arguments))
      else none) := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
      simp only [scanMeter, rowMeter, distinctMeter_correct, List.filterMap_cons]
      split <;> simp_all

theorem scanMeter_bound (head : String) (arguments : List CellId)
    (rows : List (Equation × Nat)) :
    (scanMeter head arguments rows).2 ≤
      1 + (rows.map fun row => (row.1.parameters.length + 1) ^ 2 +
        2 * row.1.parameters.length + arguments.length + 4).sum := by
  induction rows with
  | nil => simp [scanMeter]
  | cons row rest ih =>
      have distinct := distinctMeter_bound row.1.parameters
      simp only [scanMeter, rowMeter, List.map_cons, List.sum_cons]
      split <;> simp only <;> omega

def meteredCandidates (program : Program) (head : String) (arguments : List CellId) :=
  let scanned := scanMeter head arguments program.zipIdx
  (scanned.1, scanned.2 + program.length)

/-- The costed algorithm has the actual source successors, including physical
row identities and positional environments. It is not defined by those
successors: it executes its own duplicate checks and finite row scan. -/
theorem meteredCandidates_correct (program : Program) (head : String)
    (arguments : List CellId) :
    (meteredCandidates program head arguments).1 = rowCandidates program head arguments :=
  scanMeter_correct head arguments program.zipIdx

/-- Candidate scans inspect finite rows and parameter lists, never recursively
generated body answers. Duplicate checking is quadratic in parameter count. -/
def admissionVisits (program : Program) (origin : Origin) : Nat :=
  match origin with
  | .expression _ environment => environment.length + program.length + 8
  | .application _ arguments =>
      program.length + 1 +
        (program.zipIdx.map fun row => (row.1.parameters.length + 1) ^ 2 +
          2 * row.1.parameters.length + arguments.length + 4).sum

theorem meteredCandidates_bound (program : Program) (head : String)
    (arguments : List CellId) :
    (meteredCandidates program head arguments).2 ≤
      admissionVisits program (.application head arguments) := by
  have bound := scanMeter_bound head arguments program.zipIdx
  dsimp [meteredCandidates, admissionVisits]
  omega

theorem admission_positive (program : Program) (origin : Origin) :
    0 < admissionVisits program origin := by
  cases origin <;> simp [admissionVisits]

/-- Exact budget splitting for the concrete authored program instance. The
entire state, not just its visible answers, occurs on both sides. -/
theorem native_resume_exact (program : Program) (goal : List (Outcome × List Nat) → Bool)
    (first second : Nat)
    (state : Mettapedia.GSLT.Core.InferenceControl.Snapshot
      (Mettapedia.GSLT.Core.InferenceControl.WorkOccurrence NativeMachine)
      (Outcome × List Nat) Unit) :
    Mettapedia.GSLT.Core.DemandExecution.run (occurrenceSystem program)
      (Mettapedia.GSLT.Core.InferenceControl.Controller.fixed
        Mettapedia.GSLT.Core.BranchingTemporal.Scheduler.breadthFirst)
      goal (first + second) state =
    Mettapedia.GSLT.Core.DemandExecution.run (occurrenceSystem program)
      (Mettapedia.GSLT.Core.InferenceControl.Controller.fixed
        Mettapedia.GSLT.Core.BranchingTemporal.Scheduler.breadthFirst)
      goal second
      (Mettapedia.GSLT.Core.DemandExecution.run (occurrenceSystem program)
        (Mettapedia.GSLT.Core.InferenceControl.Controller.fixed
          Mettapedia.GSLT.Core.BranchingTemporal.Scheduler.breadthFirst)
        goal first state) :=
  Mettapedia.GSLT.Core.DemandExecution.run_add _ _ _ _ _ _

end Mettapedia.Languages.MeTTa.PrimeCandidates.NativeEquationNeed
