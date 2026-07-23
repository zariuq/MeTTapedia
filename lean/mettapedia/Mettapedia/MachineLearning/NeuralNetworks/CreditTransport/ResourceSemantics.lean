import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Core

/-!
# Resource semantics for credit transport

Resource vectors compose differently for sequential and independent parallel
execution.  Work and call counts add in both cases.  Sequential spans add while
parallel spans take a maximum.  Sequential phases reuse peak storage by a
maximum; concurrently live storage adds.

This is an abstract accounting model.  It does not identify any coordinate with
wall time, device occupancy, or energy without an implementation refinement.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace ResourceVector

/-- Sequential composition: time-like coordinates add and reusable storage
takes the maximum footprint. -/
def sequential (first second : ResourceVector) : ResourceVector where
  scalarWork := first.scalarWork + second.scalarWork
  criticalPathSpan := first.criticalPathSpan + second.criticalPathSpan
  persistentMemory := max first.persistentMemory second.persistentMemory
  peakTemporaryMemory := max first.peakTemporaryMemory second.peakTemporaryMemory
  bytesCommunicated := first.bytesCommunicated + second.bytesCommunicated
  synchronizationRounds := first.synchronizationRounds + second.synchronizationRounds
  exactReverseCalls := first.exactReverseCalls + second.exactReverseCalls
  localDerivativeCalls := first.localDerivativeCalls + second.localDerivativeCalls
  functionEvaluations := first.functionEvaluations + second.functionEvaluations
  checkerEvaluations := first.checkerEvaluations + second.checkerEvaluations

/-- Independent parallel composition: work and simultaneously live storage add,
while span and synchronization depth take the larger branch. -/
def parallel (left right : ResourceVector) : ResourceVector where
  scalarWork := left.scalarWork + right.scalarWork
  criticalPathSpan := max left.criticalPathSpan right.criticalPathSpan
  persistentMemory := left.persistentMemory + right.persistentMemory
  peakTemporaryMemory := left.peakTemporaryMemory + right.peakTemporaryMemory
  bytesCommunicated := left.bytesCommunicated + right.bytesCommunicated
  synchronizationRounds := max left.synchronizationRounds right.synchronizationRounds
  exactReverseCalls := left.exactReverseCalls + right.exactReverseCalls
  localDerivativeCalls := left.localDerivativeCalls + right.localDerivativeCalls
  functionEvaluations := left.functionEvaluations + right.functionEvaluations
  checkerEvaluations := left.checkerEvaluations + right.checkerEvaluations

/-- Coordinatewise resource comparison. -/
def CoordinatewiseLE (left right : ResourceVector) : Prop :=
  left.scalarWork ≤ right.scalarWork ∧
  left.criticalPathSpan ≤ right.criticalPathSpan ∧
  left.persistentMemory ≤ right.persistentMemory ∧
  left.peakTemporaryMemory ≤ right.peakTemporaryMemory ∧
  left.bytesCommunicated ≤ right.bytesCommunicated ∧
  left.synchronizationRounds ≤ right.synchronizationRounds ∧
  left.exactReverseCalls ≤ right.exactReverseCalls ∧
  left.localDerivativeCalls ≤ right.localDerivativeCalls ∧
  left.functionEvaluations ≤ right.functionEvaluations ∧
  left.checkerEvaluations ≤ right.checkerEvaluations

theorem coordinatewiseLE_refl (resource : ResourceVector) :
    resource.CoordinatewiseLE resource := by
  exact ⟨le_rfl, le_rfl, le_rfl, le_rfl, le_rfl,
    le_rfl, le_rfl, le_rfl, le_rfl, le_rfl⟩

theorem coordinatewiseLE_trans {first second third : ResourceVector}
    (h₁₂ : first.CoordinatewiseLE second)
    (h₂₃ : second.CoordinatewiseLE third) :
    first.CoordinatewiseLE third := by
  rcases h₁₂ with ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀⟩
  rcases h₂₃ with ⟨k₁, k₂, k₃, k₄, k₅, k₆, k₇, k₈, k₉, k₁₀⟩
  exact ⟨h₁.trans k₁, h₂.trans k₂, h₃.trans k₃, h₄.trans k₄,
    h₅.trans k₅, h₆.trans k₆, h₇.trans k₇, h₈.trans k₈,
    h₉.trans k₉, h₁₀.trans k₁₀⟩

@[simp] theorem sequential_zero_left (resource : ResourceVector) :
    sequential 0 resource = resource := by
  ext <;> simp [sequential]

@[simp] theorem sequential_zero_right (resource : ResourceVector) :
    sequential resource 0 = resource := by
  ext <;> simp [sequential]

theorem sequential_assoc (first second third : ResourceVector) :
    sequential (sequential first second) third =
      sequential first (sequential second third) := by
  ext <;> simp [sequential, Nat.add_assoc, Nat.max_assoc]

@[simp] theorem parallel_zero_left (resource : ResourceVector) :
    parallel 0 resource = resource := by
  ext <;> simp [parallel]

@[simp] theorem parallel_zero_right (resource : ResourceVector) :
    parallel resource 0 = resource := by
  ext <;> simp [parallel]

theorem parallel_assoc (first second third : ResourceVector) :
    parallel (parallel first second) third =
      parallel first (parallel second third) := by
  ext <;> simp [parallel, Nat.add_assoc, Nat.max_assoc]

theorem parallel_comm (left right : ResourceVector) :
    parallel left right = parallel right left := by
  ext <;> simp [parallel, Nat.add_comm, Nat.max_comm]

/-- Fold a family of independent branches into one abstract parallel round. -/
def parallelMany : List ResourceVector → ResourceVector
  | [] => 0
  | resource :: resources => parallel resource (parallelMany resources)

@[simp] theorem parallelMany_nil : parallelMany [] = 0 := rfl

@[simp] theorem parallelMany_cons (resource : ResourceVector)
    (resources : List ResourceVector) :
    parallelMany (resource :: resources) =
      parallel resource (parallelMany resources) :=
  rfl

end ResourceVector

namespace CreditTransportSystem

variable {Problem Parameter LocalState Event Signal Update : Type*}
variable (system : CreditTransportSystem
  Problem Parameter LocalState Event Signal Update)

/-- State-sensitive cost of a sequential event schedule. -/
def scheduleCostFrom (problem : Problem) (parameter : Parameter) :
    LocalState → List Event → ResourceVector
  | _, [] => 0
  | state, event :: events =>
      ResourceVector.sequential
        (system.eventCost problem parameter state event)
        (scheduleCostFrom problem parameter
          (system.transition problem parameter event state) events)

/-- Cost from the declared initializer. -/
def scheduleCost (problem : Problem) (parameter : Parameter)
    (events : List Event) : ResourceVector :=
  system.scheduleCostFrom problem parameter
    (system.initialState problem parameter) events

@[simp] theorem scheduleCostFrom_nil (problem : Problem) (parameter : Parameter)
    (state : LocalState) :
    system.scheduleCostFrom problem parameter state [] = 0 :=
  rfl

@[simp] theorem scheduleCostFrom_cons (problem : Problem) (parameter : Parameter)
    (state : LocalState) (event : Event) (events : List Event) :
    system.scheduleCostFrom problem parameter state (event :: events) =
      ResourceVector.sequential
        (system.eventCost problem parameter state event)
        (system.scheduleCostFrom problem parameter
          (system.transition problem parameter event state) events) :=
  rfl

theorem scheduleCostFrom_append (problem : Problem) (parameter : Parameter)
    (state : LocalState) (events₁ events₂ : List Event) :
    system.scheduleCostFrom problem parameter state (events₁ ++ events₂) =
      ResourceVector.sequential
        (system.scheduleCostFrom problem parameter state events₁)
        (system.scheduleCostFrom problem parameter
          (system.runFrom problem parameter state events₁) events₂) := by
  induction events₁ generalizing state with
  | nil => simp [scheduleCostFrom]
  | cons event events₁ ih =>
      simp only [List.cons_append, scheduleCostFrom_cons, runFrom_cons]
      rw [ih]
      exact (ResourceVector.sequential_assoc _ _ _).symm

theorem scheduleCost_append (problem : Problem) (parameter : Parameter)
    (events₁ events₂ : List Event) :
    system.scheduleCost problem parameter (events₁ ++ events₂) =
      ResourceVector.sequential
        (system.scheduleCost problem parameter events₁)
        (system.scheduleCostFrom problem parameter
          (system.run problem parameter events₁) events₂) :=
  system.scheduleCostFrom_append problem parameter
    (system.initialState problem parameter) events₁ events₂

end CreditTransportSystem

#print axioms ResourceVector.sequential_assoc
#print axioms ResourceVector.parallel_assoc
#print axioms ResourceVector.parallel_comm
#print axioms CreditTransportSystem.scheduleCostFrom_append

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
