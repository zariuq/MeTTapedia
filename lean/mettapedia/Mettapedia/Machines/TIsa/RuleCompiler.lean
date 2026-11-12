import Mettapedia.Machines.TIsa.RuleTable
import Mathlib.Data.List.Indexes

/-!
# Coordinate compilation of declarative tuple rules

Variable origins are source coordinates. Their validity is a finite syntactic
property of the pattern table, independent of any execution result. The
compiler emits equality guards and a gather plan; the source still quantifies
over one assignment shared by all premise patterns.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.RuleTable

abbrev Origins := Nat → Coordinate

def Atom.source (origins : Origins) : Atom → Source
  | .variable name => .field (origins name)
  | .literal value => .literal value

def Rule.at? (rule : Rule) (coordinate : Coordinate) : Option Atom := do
  let pattern ← rule.premises[coordinate.premise]?
  pattern.fields[coordinate.field]?

def Rule.entries (rule : Rule) : List (Coordinate × Atom) :=
  rule.premises.zipIdx.flatMap fun (pattern, premise) =>
    pattern.fields.zipIdx.map fun (atom, field) => (⟨premise, field⟩, atom)

def Rule.atoms (rule : Rule) : List Atom :=
  rule.premises.flatMap Pattern.fields ++ rule.conclusion.fields

def Rule.ValidOrigins (rule : Rule) (origins : Origins) : Prop :=
  ∀ name, Atom.variable name ∈ rule.atoms → rule.at? (origins name) = some (.variable name)

def Rule.compile (rule : Rule) (origins : Origins) : Plan where
  inputs := rule.premises.map Pattern.shape
  guards := rule.entries.map fun (coordinate, atom) =>
    ⟨.field coordinate, atom.source origins⟩
  outputTag := rule.conclusion.tag
  outputFields := rule.conclusion.fields.map (Atom.source origins)

theorem Rule.mem_entries_iff (rule : Rule) (coordinate : Coordinate) (atom : Atom) :
    (coordinate, atom) ∈ rule.entries ↔ rule.at? coordinate = some atom := by
  constructor
  · intro member
    obtain ⟨⟨pattern, premise⟩, inPremises, inMap⟩ :=
      List.mem_flatMap.mp member
    obtain ⟨⟨found, field⟩, inFields, same⟩ := List.mem_map.mp inMap
    cases same
    have patternAt := List.mem_zipIdx_iff_getElem?.mp inPremises
    have atomAt := List.mem_zipIdx_iff_getElem?.mp inFields
    simp [at?, patternAt, atomAt]
  · intro found
    cases patternAt : rule.premises[coordinate.premise]? with
    | none => simp [at?, patternAt] at found
    | some pattern =>
        have atomAt : pattern.fields[coordinate.field]? = some atom := by
          simpa [at?, patternAt] using found
        apply List.mem_flatMap.mpr
        refine ⟨(pattern, coordinate.premise), List.mem_zipIdx_iff_getElem?.mpr patternAt, ?_⟩
        apply List.mem_map.mpr
        exact ⟨(atom, coordinate.field), List.mem_zipIdx_iff_getElem?.mpr atomAt,
          by cases coordinate; rfl⟩

theorem Rule.read_instantiated (rule : Rule) (coordinate : Coordinate) (atom : Atom)
    (found : rule.at? coordinate = some atom) (assignment : Assignment) :
    coordinate.read (rule.premises.map (Pattern.instantiate assignment)) =
      some (atom.evaluate assignment) := by
  cases patternAt : rule.premises[coordinate.premise]? with
  | none => simp [at?, patternAt] at found
  | some pattern =>
      have atomAt : pattern.fields[coordinate.field]? = some atom := by
        simpa [at?, patternAt] using found
      simp [Coordinate.read, patternAt, Pattern.instantiate, atomAt]

theorem Atom.source_read_instantiated (rule : Rule) (origins : Origins)
    (valid : rule.ValidOrigins origins) (atom : Atom) (member : atom ∈ rule.atoms)
    (assignment : Assignment) :
    (atom.source origins).read (rule.premises.map (Pattern.instantiate assignment)) =
      some (atom.evaluate assignment) := by
  cases atom with
  | literal value => rfl
  | «variable» name =>
      exact rule.read_instantiated (origins name) (.variable name) (valid name member) assignment

theorem Rule.at_mem_atoms (rule : Rule) (coordinate : Coordinate) (atom : Atom)
    (found : rule.at? coordinate = some atom) : atom ∈ rule.atoms := by
  cases patternAt : rule.premises[coordinate.premise]? with
  | none => simp [at?, patternAt] at found
  | some pattern =>
      have atomAt : pattern.fields[coordinate.field]? = some atom := by
        simpa [at?, patternAt] using found
      exact List.mem_append_left _ (List.mem_flatMap.mpr
        ⟨pattern, List.mem_of_getElem? patternAt, List.mem_of_getElem? atomAt⟩)

theorem gather_sources (premises : List Tuple) (atoms : List Atom) (origins : Origins)
    (assignment : Assignment)
    (reads : ∀ atom ∈ atoms, (atom.source origins).read premises = some (atom.evaluate assignment)) :
    gather premises (atoms.map (Atom.source origins)) = some (atoms.map (Atom.evaluate assignment)) := by
  induction atoms with
  | nil => rfl
  | cons atom later ih =>
      simp only [List.map_cons, gather]
      rw [reads atom (List.mem_cons_self)]
      rw [ih (fun atom member => reads atom (List.mem_cons_of_mem _ member))]
      rfl

/-- Every declaratively instantiated premise list executes to its conclusion. -/
theorem Rule.compile_complete (rule : Rule) (origins : Origins)
    (valid : rule.ValidOrigins origins) (assignment : Assignment) :
    (rule.compile origins).run (rule.premises.map (Pattern.instantiate assignment)) =
      some (rule.conclusion.instantiate assignment) := by
  apply (Plan.run_eq_some_iff _ _ _).mpr
  refine ⟨?_, ?_, rfl, ?_⟩
  · simp [compile, Pattern.instantiate, Tuple.shape, Pattern.shape, List.map_map, Function.comp_def]
  · intro guard member
    obtain ⟨⟨coordinate, atom⟩, inEntries, rfl⟩ := List.mem_map.mp member
    have found := (rule.mem_entries_iff coordinate atom).mp inEntries
    apply (Guard.accepts_iff _ _).mpr
    exact ⟨atom.evaluate assignment, rule.read_instantiated coordinate atom found assignment,
      Atom.source_read_instantiated rule origins valid atom (rule.at_mem_atoms coordinate atom found) assignment⟩
  · apply gather_sources
    intro atom member
    exact Atom.source_read_instantiated rule origins valid atom
      (List.mem_append_right _ member) assignment

/-- Shape agreement guarantees a word at every coordinate used by a pattern. -/
theorem Rule.read_exists_of_shapes (rule : Rule) (premises : List Tuple)
    (shapes : premises.map Tuple.shape = rule.premises.map Pattern.shape)
    (coordinate : Coordinate) (atom : Atom) (found : rule.at? coordinate = some atom) :
    ∃ value, coordinate.read premises = some value := by
  cases patternAt : rule.premises[coordinate.premise]? with
  | none => simp [at?, patternAt] at found
  | some pattern =>
      have atomAt : pattern.fields[coordinate.field]? = some atom := by
        simpa [at?, patternAt] using found
      have atShape := congrArg (fun rows => rows[coordinate.premise]?) shapes
      simp only [List.getElem?_map, patternAt, Option.map_some] at atShape
      cases tupleAt : premises[coordinate.premise]? with
      | none => simp [tupleAt] at atShape
      | some tuple =>
          have same : tuple.shape = pattern.shape := by
            simpa [tupleAt] using atShape
          have lengths : tuple.fields.length = pattern.fields.length := congrArg Shape.arity same
          obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp atomAt
          have inTuple : coordinate.field < tuple.fields.length := lengths ▸ bound
          exact ⟨tuple.fields[coordinate.field], by simp [Coordinate.read, tupleAt, inTuple]⟩

def reconstruct (origins : Origins) (premises : List Tuple) : Assignment :=
  fun name => ((origins name).read premises).getD 0

theorem Atom.source_read_reconstructed (rule : Rule) (origins : Origins)
    (valid : rule.ValidOrigins origins) (premises : List Tuple)
    (shapes : premises.map Tuple.shape = rule.premises.map Pattern.shape)
    (atom : Atom) (member : atom ∈ rule.atoms) :
    (atom.source origins).read premises = some (atom.evaluate (reconstruct origins premises)) := by
  cases atom with
  | literal value => rfl
  | «variable» name =>
      obtain ⟨value, found⟩ := rule.read_exists_of_shapes premises shapes (origins name)
        (.variable name) (valid name member)
      change (origins name).read premises = some (((origins name).read premises).getD 0)
      rw [found]
      rfl

theorem Rule.premises_eq_of_reads (rule : Rule) (premises : List Tuple)
    (assignment : Assignment)
    (shapes : premises.map Tuple.shape = rule.premises.map Pattern.shape)
    (reads : ∀ coordinate atom, rule.at? coordinate = some atom →
      coordinate.read premises = some (atom.evaluate assignment)) :
    premises = rule.premises.map (Pattern.instantiate assignment) := by
  apply List.ext_getElem
  · simpa using congrArg List.length shapes
  · intro i actualBound instantiatedBound
    have patternBound : i < rule.premises.length := by simpa using instantiatedBound
    have atShape := congrArg (fun rows => rows[i]?) shapes
    have sameShape : premises[i].shape = rule.premises[i].shape := by
      simpa [actualBound, patternBound] using atShape
    simp only [List.getElem_map]
    change Tuple.mk premises[i].tag premises[i].fields =
      Tuple.mk rule.premises[i].tag (rule.premises[i].fields.map (Atom.evaluate assignment))
    apply (Tuple.mk.injEq _ _ _ _).mpr
    refine ⟨congrArg Shape.tag sameShape, ?_⟩
    apply List.ext_getElem
    · have lengths : premises[i].fields.length = rule.premises[i].fields.length :=
        congrArg Shape.arity sameShape
      simpa using lengths
    · intro j actualFieldBound outputFieldBound
      have patternFieldBound : j < rule.premises[i].fields.length := by
        simpa using outputFieldBound
      have found : rule.at? ⟨i, j⟩ = some rule.premises[i].fields[j] := by
        simp [at?, patternBound, patternFieldBound]
      have value := reads ⟨i, j⟩ rule.premises[i].fields[j] found
      have actual : Coordinate.read premises ⟨i, j⟩ = some premises[i].fields[j] := by
        simp [Coordinate.read, actualBound, actualFieldBound]
      rw [actual] at value
      simpa using Option.some.inj value

/-- Successful guard/gather execution reflects to a shared source assignment. -/
theorem Rule.compile_sound (rule : Rule) (origins : Origins)
    (valid : rule.ValidOrigins origins) (premises : List Tuple) (output : Tuple)
    (executes : (rule.compile origins).run premises = some output) :
    Derives rule premises output := by
  obtain ⟨shapes, guards, outputTag, outputFields⟩ := (Plan.run_eq_some_iff _ _ _).mp executes
  change premises.map Tuple.shape = rule.premises.map Pattern.shape at shapes
  let assignment := reconstruct origins premises
  have faithful : ∀ atom ∈ rule.atoms,
      (atom.source origins).read premises = some (atom.evaluate assignment) :=
    fun atom member => Atom.source_read_reconstructed rule origins valid premises shapes atom member
  have reads : ∀ coordinate atom, rule.at? coordinate = some atom →
      coordinate.read premises = some (atom.evaluate assignment) := by
    intro coordinate atom found
    have inGuards : Guard.mk (.field coordinate) (atom.source origins) ∈
        (rule.compile origins).guards := by
      apply List.mem_map.mpr
      exact ⟨(coordinate, atom), (rule.mem_entries_iff coordinate atom).mpr found, rfl⟩
    obtain ⟨value, left, right⟩ := (Guard.accepts_iff _ _).mp (guards _ inGuards)
    exact left.trans (right.symm.trans (faithful atom (rule.at_mem_atoms coordinate atom found)))
  refine ⟨assignment, rule.premises_eq_of_reads premises assignment shapes reads, ?_⟩
  have expected : gather premises (rule.conclusion.fields.map (Atom.source origins)) =
      some (rule.conclusion.fields.map (Atom.evaluate assignment)) :=
    gather_sources premises rule.conclusion.fields origins assignment
      (fun atom member => faithful atom (List.mem_append_right _ member))
  have fields : output.fields = rule.conclusion.fields.map (Atom.evaluate assignment) :=
    Option.some.inj (outputFields.symm.trans expected)
  change Tuple.mk output.tag output.fields =
    Tuple.mk rule.conclusion.tag (rule.conclusion.fields.map (Atom.evaluate assignment))
  exact (Tuple.mk.injEq _ _ _ _).mpr ⟨outputTag, fields⟩

theorem Rule.compile_iff (rule : Rule) (origins : Origins)
    (valid : rule.ValidOrigins origins) (premises : List Tuple) (output : Tuple) :
    (rule.compile origins).run premises = some output ↔ Derives rule premises output := by
  constructor
  · exact rule.compile_sound origins valid premises output
  · rintro ⟨assignment, rfl, rfl⟩
    exact rule.compile_complete origins valid assignment

def Plan.pruneSelfGuards (plan : Plan) : Plan :=
  { plan with guards := plan.guards.filter fun guard => guard.left != guard.right }

theorem Rule.self_guard_accepts (rule : Rule) (origins : Origins) (premises : List Tuple)
    (shapes : premises.map Tuple.shape = rule.premises.map Pattern.shape)
    (guard : Guard) (member : guard ∈ (rule.compile origins).guards)
    (same : guard.left = guard.right) : guard.accepts premises = true := by
  obtain ⟨⟨coordinate, atom⟩, inEntries, rfl⟩ := List.mem_map.mp member
  obtain ⟨value, read⟩ := rule.read_exists_of_shapes premises shapes coordinate atom
    ((rule.mem_entries_iff coordinate atom).mp inEntries)
  apply (Guard.accepts_iff _ _).mpr
  refine ⟨value, read, ?_⟩
  change (atom.source origins).read premises = some value
  change Source.field coordinate = atom.source origins at same
  rw [← same]
  exact read

/-- FL omits self-equalities. They are removable because input shapes first
establish that every tested coordinate exists. -/
theorem Rule.pruned_compile_iff (rule : Rule) (origins : Origins)
    (valid : rule.ValidOrigins origins) (premises : List Tuple) (output : Tuple) :
    (rule.compile origins).pruneSelfGuards.run premises = some output ↔
      Derives rule premises output := by
  rw [← rule.compile_iff origins valid premises output]
  rw [Plan.run_eq_some_iff, Plan.run_eq_some_iff]
  constructor
  · rintro ⟨shapes, guards, tag, fields⟩
    refine ⟨shapes, ?_, tag, fields⟩
    intro guard member
    by_cases same : guard.left = guard.right
    · exact rule.self_guard_accepts origins premises shapes guard member same
    · exact guards guard (List.mem_filter.mpr ⟨member, by simpa using same⟩)
  · rintro ⟨shapes, guards, tag, fields⟩
    exact ⟨shapes, fun guard member => guards guard (List.mem_filter.mp member).1, tag, fields⟩

def Rule.discoverOrigins (rule : Rule) : Origins := fun name =>
  match rule.entries.find? (fun entry => entry.2 == .variable name) with
  | some entry => entry.1
  | none => ⟨0, 0⟩

def Rule.validOrigins? (rule : Rule) (origins : Origins) : Bool :=
  rule.atoms.all fun atom => match atom with
    | .literal _ => true
    | .variable name => rule.at? (origins name) == some (.variable name)

theorem Rule.validOrigins?_iff (rule : Rule) (origins : Origins) :
    rule.validOrigins? origins = true ↔ rule.ValidOrigins origins := by
  simp only [validOrigins?, List.all_eq_true]
  constructor
  · intro checked name member
    have present := checked (.variable name) member
    exact beq_iff_eq.mp present
  · intro valid atom member
    cases atom with
    | literal value => rfl
    | «variable» name => exact beq_iff_eq.mpr (valid name member)

/-- This finite check compares both the guard program and gather coordinates. -/
def Rule.checkPlan (rule : Rule) (plan : Plan) : Bool :=
  rule.validOrigins? rule.discoverOrigins &&
    plan == (rule.compile rule.discoverOrigins).pruneSelfGuards

theorem Rule.checkPlan_correct (rule : Rule) (plan : Plan) (checked : rule.checkPlan plan = true)
    (premises : List Tuple) (output : Tuple) :
    plan.run premises = some output ↔ Derives rule premises output := by
  have both : rule.validOrigins? rule.discoverOrigins = true ∧
      (plan == (rule.compile rule.discoverOrigins).pruneSelfGuards) = true := by
    simpa only [checkPlan, Bool.and_eq_true] using checked
  obtain ⟨valid, same⟩ := both
  have samePlan : plan = (rule.compile rule.discoverOrigins).pruneSelfGuards := beq_iff_eq.mp same
  rw [samePlan]
  exact rule.pruned_compile_iff rule.discoverOrigins
    ((rule.validOrigins?_iff rule.discoverOrigins).mp valid) premises output

end Mettapedia.Machines.TIsa.RuleTable
