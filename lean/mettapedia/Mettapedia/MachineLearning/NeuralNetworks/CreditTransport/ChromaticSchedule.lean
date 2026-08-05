import Mathlib.Tactic

/-!
# Chromatic schedules for local credit dynamics

Chromatic Gauss--Seidel sweeps: group
noninterfering graph coordinates by color, update one color at a time, and
parallelize all coordinates within a color.

This file states the missing semantic condition.  A local rule declares the
coordinates read by every write and proves that its proposed value depends
only on those coordinates.  Two coordinate updates commute when they write
distinct coordinates and neither reads the other's write.  Consequently, a
proper color class is invariant under every permutation of its update order.

The result is deliberately weaker than finite-step equivalence between
Jacobi and Gauss--Seidel.  Every schedule preserves a common coordinate fixed
point, but dependent coordinate orders can have different finite trajectories.
An executable two-coordinate fixture records that boundary and refutes the
use of graph coloring without the read/write condition.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace ChromaticSchedule

noncomputable section

universe u v

variable {Vertex : Type u} [DecidableEq Vertex]

abbrev CoordinateState (Vertex : Type u) :=
  Vertex → ℝ

/-- One local coordinate rule, including an extensional certificate that the
new value reads only the declared finite support. -/
structure LocalRule (Vertex : Type u) [DecidableEq Vertex] where
  reads : Vertex → Finset Vertex
  value : Vertex → CoordinateState Vertex → ℝ
  locality :
    ∀ vertex left right,
      (∀ coordinate, coordinate ∈ reads vertex →
        left coordinate = right coordinate) →
      value vertex left = value vertex right

/-- Update one coordinate in place using the rule's value computed from the
input state. -/
def coordinateStep
    (rule : LocalRule Vertex)
    (vertex : Vertex)
    (state : CoordinateState Vertex) :
    CoordinateState Vertex :=
  fun coordinate =>
    if coordinate = vertex then rule.value vertex state
    else state coordinate

@[simp] theorem coordinateStep_same
    (rule : LocalRule Vertex)
    (vertex : Vertex)
    (state : CoordinateState Vertex) :
    coordinateStep rule vertex state vertex = rule.value vertex state := by
  simp [coordinateStep]

theorem coordinateStep_other
    (rule : LocalRule Vertex)
    (vertex coordinate : Vertex)
    (state : CoordinateState Vertex)
    (different : coordinate ≠ vertex) :
    coordinateStep rule vertex state coordinate = state coordinate := by
  simp [coordinateStep, different]

/-- Updating a coordinate outside one local rule's read support cannot change
the value proposed by that rule. -/
theorem value_coordinateStep_of_not_mem_reads
    (rule : LocalRule Vertex)
    (written reader : Vertex)
    (state : CoordinateState Vertex)
    (notRead : written ∉ rule.reads reader) :
    rule.value reader (coordinateStep rule written state) =
      rule.value reader state := by
  apply rule.locality
  intro coordinate member
  by_cases same : coordinate = written
  · subst coordinate
    exact False.elim (notRead member)
  · exact coordinateStep_other rule written coordinate state same

/-- Symmetric read/write independence for two coordinate updates. -/
def Noninterfering
    (rule : LocalRule Vertex)
    (left right : Vertex) : Prop :=
  left ≠ right ∧
    left ∉ rule.reads right ∧
    right ∉ rule.reads left

theorem noninterfering_symm
    (rule : LocalRule Vertex)
    {left right : Vertex}
    (independent : Noninterfering rule left right) :
    Noninterfering rule right left :=
  ⟨independent.1.symm, independent.2.2, independent.2.1⟩

/-- Independent local writes commute exactly. -/
theorem coordinateStep_commute
    (rule : LocalRule Vertex)
    (state : CoordinateState Vertex)
    {left right : Vertex}
    (independent : Noninterfering rule left right) :
    coordinateStep rule left (coordinateStep rule right state) =
      coordinateStep rule right (coordinateStep rule left state) := by
  rcases independent with
    ⟨different, leftNotReadByRight, rightNotReadByLeft⟩
  funext coordinate
  by_cases coordinateLeft : coordinate = left
  · subst coordinate
    rw [coordinateStep_same]
    rw [value_coordinateStep_of_not_mem_reads
      rule right left state rightNotReadByLeft]
    rw [coordinateStep_other rule right left
      (coordinateStep rule left state) different]
    rw [coordinateStep_same]
  · by_cases coordinateRight : coordinate = right
    · subst coordinate
      rw [coordinateStep_other rule left right
        (coordinateStep rule right state) different.symm]
      rw [coordinateStep_same]
      rw [coordinateStep_same]
      rw [value_coordinateStep_of_not_mem_reads
        rule left right state leftNotReadByRight]
    · rw [coordinateStep_other rule left coordinate
        (coordinateStep rule right state) coordinateLeft]
      rw [coordinateStep_other rule right coordinate state coordinateRight]
      rw [coordinateStep_other rule right coordinate
        (coordinateStep rule left state) coordinateRight]
      rw [coordinateStep_other rule left coordinate state coordinateLeft]

/-- A coloring is proper for a local rule when distinct same-color writes are
noninterfering.  This is stronger and more operational than coloring only an
informal architecture diagram. -/
def ProperColoring
    {Color : Type v}
    (rule : LocalRule Vertex)
    (color : Vertex → Color) : Prop :=
  ∀ {left right},
    left ≠ right →
    color left = color right →
    Noninterfering rule left right

abbrev ColorClass
    {Color : Type v}
    (color : Vertex → Color)
    (selected : Color) :=
  {vertex : Vertex // color vertex = selected}

/-- Execute a finite list of vertices belonging to one color. -/
def runColorClass
    {Color : Type v}
    (rule : LocalRule Vertex)
    (color : Vertex → Color)
    (selected : Color)
    (vertices : List (ColorClass color selected))
    (state : CoordinateState Vertex) :
    CoordinateState Vertex :=
  vertices.foldl
    (fun current vertex => coordinateStep rule vertex.1 current)
    state

/-- The order inside a proper color class is semantically irrelevant. -/
theorem runColorClass_eq_of_perm
    {Color : Type v}
    (rule : LocalRule Vertex)
    (color : Vertex → Color)
    (selected : Color)
    (proper : ProperColoring rule color)
    {left right : List (ColorClass color selected)}
    (permutation : left.Perm right)
    (state : CoordinateState Vertex) :
    runColorClass rule color selected left state =
      runColorClass rule color selected right state := by
  let operation :
      CoordinateState Vertex →
        ColorClass color selected →
        CoordinateState Vertex :=
    fun current vertex => coordinateStep rule vertex.1 current
  letI : RightCommutative operation := ⟨by
    intro current first second
    by_cases same : first = second
    · subst second
      rfl
    · have different : first.1 ≠ second.1 := by
        intro equalValues
        exact same (Subtype.ext equalValues)
      have sameColor : color first.1 = color second.1 :=
        first.property.trans second.property.symm
      exact
        (coordinateStep_commute rule current
          (proper different sameColor)).symm⟩
  exact permutation.foldl_eq state

/-! ## Common fixed points and finite-schedule boundaries -/

/-- Every coordinate proposes its current value. -/
def IsCommonFixedPoint
    (rule : LocalRule Vertex)
    (state : CoordinateState Vertex) : Prop :=
  ∀ vertex, rule.value vertex state = state vertex

theorem coordinateStep_eq_of_commonFixedPoint
    (rule : LocalRule Vertex)
    (state : CoordinateState Vertex)
    (fixed : IsCommonFixedPoint rule state)
    (vertex : Vertex) :
    coordinateStep rule vertex state = state := by
  funext coordinate
  by_cases same : coordinate = vertex
  · subst coordinate
    rw [coordinateStep_same, fixed vertex]
  · simp [coordinateStep, same]

/-- Execute arbitrary coordinate updates in their recorded order. -/
def runCoordinates
    (rule : LocalRule Vertex)
    (vertices : List Vertex)
    (state : CoordinateState Vertex) :
    CoordinateState Vertex :=
  vertices.foldl (fun current vertex => coordinateStep rule vertex current) state

/-- Every finite coordinate schedule preserves a common fixed point. -/
theorem runCoordinates_eq_of_commonFixedPoint
    (rule : LocalRule Vertex)
    (vertices : List Vertex)
    (state : CoordinateState Vertex)
    (fixed : IsCommonFixedPoint rule state) :
    runCoordinates rule vertices state = state := by
  induction vertices generalizing state with
  | nil =>
      rfl
  | cons vertex rest inductionHypothesis =>
      change
        runCoordinates rule rest (coordinateStep rule vertex state) =
          state
      rw [coordinateStep_eq_of_commonFixedPoint rule state fixed vertex]
      exact inductionHypothesis state fixed

/-- Simultaneous Jacobi sweep from one immutable snapshot. -/
def jacobiSweep
    (rule : LocalRule Vertex)
    (state : CoordinateState Vertex) :
    CoordinateState Vertex :=
  fun vertex => rule.value vertex state

theorem jacobiSweep_eq_of_commonFixedPoint
    (rule : LocalRule Vertex)
    (state : CoordinateState Vertex)
    (fixed : IsCommonFixedPoint rule state) :
    jacobiSweep rule state = state := by
  funext vertex
  exact fixed vertex

/-! ## Executable dependent-coordinate counterexample -/

abbrev TwoVertices := Fin 2

def otherVertex (vertex : TwoVertices) : TwoVertices :=
  if vertex = 0 then 1 else 0

/-- Each coordinate reads the other and replaces itself by half of that
value. -/
def coupledHalfRule : LocalRule TwoVertices where
  reads vertex := {otherVertex vertex}
  value vertex state := state (otherVertex vertex) / 2
  locality := by
    intro vertex left right agree
    rw [agree (otherVertex vertex) (by simp)]

def coupledInitialState : CoordinateState TwoVertices :=
  fun vertex => if vertex = 0 then 2 else 0

/-- Jacobi and Gauss--Seidel share the zero fixed point but have different
finite trajectories from the same nonfixed state. -/
theorem coupled_jacobi_and_sequential_differ :
    jacobiSweep coupledHalfRule coupledInitialState 1 = 1 ∧
      runCoordinates coupledHalfRule [0, 1] coupledInitialState 1 = 0 := by
  norm_num [jacobiSweep, coupledHalfRule, otherVertex,
    coupledInitialState, runCoordinates, coordinateStep]

/-- Reversing two dependent writes changes the finite Gauss--Seidel result. -/
theorem coupled_coordinate_order_matters :
    runCoordinates coupledHalfRule [0, 1] coupledInitialState 1 = 0 ∧
      runCoordinates coupledHalfRule [1, 0] coupledInitialState 1 = 1 := by
  norm_num [coupledHalfRule, otherVertex, coupledInitialState,
    runCoordinates, coordinateStep]

def oneColor (_vertex : TwoVertices) : Unit :=
  ()

/-- The one-color assignment is invalid because the two same-color
coordinates read one another. -/
theorem coupled_oneColor_not_proper :
    ¬ ProperColoring coupledHalfRule oneColor := by
  intro proper
  have independent :
      Noninterfering coupledHalfRule (0 : TwoVertices) 1 :=
    proper (by decide) rfl
  exact independent.2.1 (by simp [coupledHalfRule, otherVertex])

/-- The zero state is a common fixed point of the coupled fixture, confirming
that schedule-level fixed-point agreement does not imply finite-step
agreement. -/
theorem coupled_zero_commonFixedPoint :
    IsCommonFixedPoint coupledHalfRule (fun _vertex => 0) := by
  intro vertex
  simp [coupledHalfRule]

#print axioms coordinateStep_commute
#print axioms runColorClass_eq_of_perm
#print axioms runCoordinates_eq_of_commonFixedPoint
#print axioms coupled_jacobi_and_sequential_differ
#print axioms coupled_oneColor_not_proper

end

end ChromaticSchedule

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
