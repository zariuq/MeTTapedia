import Mettapedia.GSLT.Parsing.HornGroundMatching
import Mettapedia.GSLT.Parsing.HornCertificateGSLT
import Mathlib.Data.List.Perm.Basic

/-!
# Occurrence-sensitive translation validation for finite fact tables

An external compiler supplies cells `(source occurrence, ground atom)`.
This validator independently enumerates ground instances of the original
fact rules over a declared finite domain. Permutation equality permits only
reordering: it cannot discard duplicates or conflate source occurrences.

The semantic specification is substitution into an actual source occurrence,
not acceptance by the compiler or its output. Premise-bearing rules are not
facts and are never silently admitted by this validator.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.FiniteFactTable

open HornCertificate HornSideAdmission HornGroundMatching HornCertificateGSLT

abbrev Cell := Nat × GroundAtom

/-- Independent source-instance meaning, retaining the source list index. -/
def SourceInstance (program : Program) (occurrence : Nat) (goal : GroundAtom) : Prop :=
  ∃ rule, program[occurrence]? = some rule ∧ rule.body = [] ∧
    ∃ substitution, substitutionValid substitution = true ∧
      instantiateAtom substitution rule.head = some goal

def matchesAt (program : Program) (occurrence : Nat) (goal : GroundAtom) : Bool :=
  match program[occurrence]? with
  | none => false
  | some rule => rule.body.isEmpty && (matchGroundAtom rule.head goal).isSome

theorem matchesAt_iff (program : Program) (occurrence : Nat) (goal : GroundAtom) :
    matchesAt program occurrence goal = true ↔ SourceInstance program occurrence goal := by
  cases selected : program[occurrence]? with
  | none => simp [matchesAt, SourceInstance, selected]
  | some rule =>
      simp only [matchesAt, selected, Bool.and_eq_true,
        List.isEmpty_iff, Option.isSome_iff_exists]
      rw [matchGroundAtom_iff_instance]
      simp [SourceInstance, selected]

def occurrences (program : Program) (goal : GroundAtom) : List Nat :=
  (List.range program.length).filter (fun occurrence => matchesAt program occurrence goal)

theorem mem_occurrences_iff (program : Program) (occurrence : Nat) (goal : GroundAtom) :
    occurrence ∈ occurrences program goal ↔ SourceInstance program occurrence goal := by
  simp only [occurrences, List.mem_filter, List.mem_range, matchesAt_iff]
  constructor
  · exact And.right
  · intro source
    refine ⟨?_, source⟩
    obtain ⟨rule, selected, _⟩ := source
    exact (List.getElem?_eq_some_iff.mp selected).1

def expected (program : Program) (domain : List GroundAtom) : List Cell :=
  domain.flatMap fun goal => (occurrences program goal).map fun occurrence => (occurrence, goal)

theorem mem_expected_iff (program : Program) (domain : List GroundAtom) (cell : Cell) :
    cell ∈ expected program domain ↔
      cell.2 ∈ domain ∧ SourceInstance program cell.1 cell.2 := by
  rcases cell with ⟨occurrence, goal⟩
  simp [expected, mem_occurrences_iff, and_left_comm]

/-- The supplied table must contain every expected occurrence exactly as many
times as the domain requests it. No hash or set conversion is involved. -/
def check (program : Program) (domain : List GroundAtom) (table : List Cell) : Bool :=
  decide (table.Perm (expected program domain))

theorem checked_iff_instances {program : Program} {domain : List GroundAtom}
    {table : List Cell} (checked : check program domain table = true) (cell : Cell) :
    cell ∈ table ↔ cell.2 ∈ domain ∧ SourceInstance program cell.1 cell.2 := by
  have permutation : table.Perm (expected program domain) := by
    simpa [check] using checked
  exact permutation.mem_iff.trans (mem_expected_iff program domain cell)

/-- The stronger multiplicity statement, separate from membership exactness. -/
theorem checked_counts {program : Program} {domain : List GroundAtom}
    {table : List Cell} (checked : check program domain table = true) (cell : Cell) :
    table.count cell = (expected program domain).count cell := by
  have permutation : table.Perm (expected program domain) := by
    simpa [check] using checked
  exact permutation.count_eq cell

theorem sourceInstance_terminal_path {program : Program} {occurrence : Nat}
    {goal : GroundAtom} (source : SourceInstance program occurrence goal) :
    (theory program).MultiStep [(1, goal)] [] := by
  obtain ⟨rule, selected, emptyBody, substitution, valid, head⟩ := source
  apply (derivesWithin_iff_terminal_path program 1 goal).mp
  exact .apply 0 goal rule (List.mem_of_getElem? selected) substitution valid [] head
    (by simp [instantiateAtoms, emptyBody]) (.nil 0)

theorem checked_cell_terminal_path {program : Program} {domain : List GroundAtom}
    {table : List Cell} (checked : check program domain table = true)
    {cell : Cell} (member : cell ∈ table) :
    (theory program).MultiStep [(1, cell.2)] [] :=
  sourceInstance_terminal_path ((checked_iff_instances checked cell).mp member).2

private def duplicateProgram : Program :=
  [⟨"first", ⟨"p", .cons (.var 0) .nil⟩, []⟩,
   ⟨"second", ⟨"p", .cons (.var 0) .nil⟩, []⟩]

private def goal : GroundAtom := ⟨"p", .cons (.atom "a") .nil⟩

theorem equal_answers_preserve_both_occurrences :
    check duplicateProgram [goal] [(0, goal), (1, goal)] = true := by decide

theorem reordered_table_is_valid :
    check duplicateProgram [goal] [(1, goal), (0, goal)] = true := by decide

theorem erased_occurrence_is_refused :
    check duplicateProgram [goal] [(0, goal)] = false := by decide

theorem repeated_output_is_refused :
    check duplicateProgram [goal] [(0, goal), (1, goal), (1, goal)] = false := by decide

/-- Set membership alone cannot distinguish a valid occurrence table from one
that spuriously repeats an output occurrence. -/
theorem membership_agreement_does_not_validate_multiplicity :
    (∀ cell : Cell,
      cell ∈ [(0, goal), (1, goal), (1, goal)] ↔ cell ∈ [(0, goal), (1, goal)]) ∧
      check duplicateProgram [goal] [(0, goal), (1, goal), (1, goal)] = false := by
  constructor
  · intro cell
    simp
  · exact repeated_output_is_refused

theorem repeated_domain_preserves_requested_multiplicity :
    check duplicateProgram [goal, goal]
      [(0, goal), (1, goal), (0, goal), (1, goal)] = true := by decide

theorem premise_bearing_rule_is_not_a_fact :
    matchesAt [⟨"conditional", ⟨"p", .cons (.var 0) .nil⟩, [⟨"needed", .nil⟩]⟩]
      0 goal = false := by decide

#print axioms checked_iff_instances
#print axioms checked_counts
#print axioms checked_cell_terminal_path

end Mettapedia.GSLT.Parsing.FiniteFactTable
