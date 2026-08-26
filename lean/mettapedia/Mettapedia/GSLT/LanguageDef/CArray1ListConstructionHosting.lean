import Mettapedia.GSLT.LanguageDef.CArray0SequenceHosting

/-!
# List construction hosted by an allocating C-like array machine

This is the construction rung above `CArray0SequenceHosting`.  The authored
source contains empty, prepend, append, and reverse over finite lists.  The
target has an independent array program and an explicit allocation relation.
Only allocators satisfying completeness and soundness may realize the source:
the target cannot silently return a differently populated buffer.

The target still abstracts from bytes, ownership transfer, allocation failure,
and deallocation.  Those belong to the next memory rung.  In particular, this
module does not claim that a live C allocator is infallible; it isolates the
successful-allocation fibre that a later outcome-aware target must embed.
-/

namespace Mettapedia.GSLT.LanguageDef.CArray1ListConstructionHosting

open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.Ultrainfinite
open Mettapedia.GSLT.LanguageDef.NIKRouteAdmission
open Mettapedia.GSLT.LanguageDef.NIKObservedRefinement
open Mettapedia.GSLT.LanguageDef.AuthoredGSLTHosting
open Mettapedia.GSLT.LanguageDef.CArray0SequenceHosting

/-! ## Authored finite-list construction -/

inductive ListConstruction (α : Type) where
  | empty
  | prepend (head : α) (tail : List α)
  | append (left right : List α)
  | reverse (values : List α)

def listConstructionSem : ListConstruction α → List α
  | .empty => []
  | .prepend head tail => head :: tail
  | .append left right => left ++ right
  | .reverse values => values.reverse

inductive SourceTerm (α : Type) where
  | request (program : ListConstruction α)
  | done (program : ListConstruction α)

inductive SourceStep : SourceTerm α → SourceTerm α → Prop
  | run (program : ListConstruction α) :
      SourceStep (.request program) (.done program)

inductive SourceMeaning : SourceTerm α → Prop
  | request (program : ListConstruction α) : SourceMeaning (.request program)
  | done (program : ListConstruction α) : SourceMeaning (.done program)

private def eqSetoid (β : Type) : Setoid β :=
  ⟨Eq, ⟨fun _ => rfl, Eq.symm, Eq.trans⟩⟩

def sourceGSLT (α : Type) : GSLT where
  Term := SourceTerm α
  equations := eqSetoid (SourceTerm α)
  rewrites := SourceStep
  rewrites_resp_left := by
    intro first first' last equal step
    cases equal
    exact ⟨last, step, rfl⟩
  rewrites_resp_right := by
    intro first last last' step equal
    cases equal
    exact step

def sourceObserve : SourceTerm α → Option (List α)
  | .request _ => none
  | .done program => some (listConstructionSem program)

def sourceObject (α : Type) : ObservedOperationalObject (List α) where
  operational := ⟨sourceGSLT α, SourceMeaning⟩
  observe := fun {_ last} _ => sourceObserve last

/-! ## Independent array construction and allocation boundary -/

inductive ArrayConstruction (α : Type) where
  | empty
  | prepend (head : α) (tail : Array α)
  | append (left right : Array α)
  | reverse (values : Array α)

def arrayConstructionSem : ArrayConstruction α → Array α
  | .empty => #[]
  | .prepend head tail => #[head] ++ tail
  | .append left right => left ++ right
  | .reverse values => values.reverse

def compileProgram : ListConstruction α → ArrayConstruction α
  | .empty => .empty
  | .prepend head tail => .prepend head tail.toArray
  | .append left right => .append left.toArray right.toArray
  | .reverse values => .reverse values.toArray

/-- The array program has the same sequence denotation, but computes through
array constructors rather than invoking the list source semantics. -/
theorem arrayConstructionSem_compile (program : ListConstruction α) :
    (arrayConstructionSem (compileProgram program)).toList =
      listConstructionSem program := by
  cases program <;> simp [arrayConstructionSem, compileProgram,
    listConstructionSem]

/-- An allocator relates one requested array image to the bounded slice it
returns.  This is a relation so different live allocation strategies can be
admitted without changing the array calculus. -/
abbrev AllocatorSpec (α : Type) := Array α → StackSlice α → Prop

structure AllocatorAdequacy (allocator : AllocatorSpec α) : Prop where
  complete : ∀ requested, allocator requested (StackSlice.ofArray requested)
  sound : ∀ {requested returned}, allocator requested returned →
    returned.toArray = requested

def referenceAllocator : AllocatorSpec α :=
  fun requested returned => returned.toArray = requested

def referenceAllocatorAdequacy : AllocatorAdequacy (referenceAllocator :
    AllocatorSpec α) where
  complete := by intro requested; simp [referenceAllocator]
  sound := fun returned => returned

/-- A degenerate allocator that always claims an empty returned buffer cannot
realize nonempty list construction. -/
def emptyAllocator : AllocatorSpec α :=
  fun _ returned => returned.toArray = #[]

theorem emptyAllocator_not_adequate (value : α) :
    ¬ AllocatorAdequacy (emptyAllocator : AllocatorSpec α) := by
  intro adequate
  have completed := adequate.complete #[value]
  simp [emptyAllocator] at completed

inductive TargetTerm (α : Type) where
  | start (program : ArrayConstruction α)
  | allocate (program : ArrayConstruction α)
  | halted (program : ArrayConstruction α) (result : StackSlice α)

inductive TargetStep (allocator : AllocatorSpec α) :
    TargetTerm α → TargetTerm α → Prop
  | request (program : ArrayConstruction α) :
      TargetStep allocator (.start program) (.allocate program)
  | returnBuffer {program : ArrayConstruction α} {result : StackSlice α}
      (returned : allocator (arrayConstructionSem program) result) :
      TargetStep allocator (.allocate program) (.halted program result)

inductive TargetMeaning (allocator : AllocatorSpec α) : TargetTerm α → Prop
  | start (program : ArrayConstruction α) : TargetMeaning allocator (.start program)
  | allocate (program : ArrayConstruction α) :
      TargetMeaning allocator (.allocate program)
  | halted {program : ArrayConstruction α} {result : StackSlice α}
      (returned : allocator (arrayConstructionSem program) result) :
      TargetMeaning allocator (.halted program result)

def targetGSLT (α : Type) (allocator : AllocatorSpec α) : GSLT where
  Term := TargetTerm α
  equations := eqSetoid (TargetTerm α)
  rewrites := TargetStep allocator
  rewrites_resp_left := by
    intro first first' last equal step
    cases equal
    exact ⟨last, step, rfl⟩
  rewrites_resp_right := by
    intro first last last' step equal
    cases equal
    exact step

def targetObserve : TargetTerm α → Option (List α)
  | .start _ => none
  | .allocate _ => none
  | .halted _ result => some result.toList

def targetObject (α : Type) (allocator : AllocatorSpec α) :
    ObservedOperationalObject (List α) where
  operational := ⟨targetGSLT α allocator, TargetMeaning allocator⟩
  observe := fun {_ last} _ => targetObserve last

/-! ## Compilation and two-sided hosting -/

def compileTerm : SourceTerm α → TargetTerm α
  | .request program => .start (compileProgram program)
  | .done program =>
      let targetProgram := compileProgram program
      .halted targetProgram
        (StackSlice.ofArray (arrayConstructionSem targetProgram))

private def one {allocator : AllocatorSpec α} {source target : TargetTerm α}
    (step : TargetStep allocator source target) :
    ExecutionPath (targetGSLT α allocator) source target :=
  .cons ⟨step⟩ (.refl _)

private def two {allocator : AllocatorSpec α}
    {first middle last : TargetTerm α}
    (firstStep : TargetStep allocator first middle)
    (secondStep : TargetStep allocator middle last) :
    ExecutionPath (targetGSLT α allocator) first last :=
  .cons ⟨firstStep⟩ (.cons ⟨secondStep⟩ (.refl _))

theorem no_source_step_from_done {program : ListConstruction α}
    {target : SourceTerm α} (step : SourceStep (.done program) target) : False := by
  cases step

theorem source_step_from_request {program : ListConstruction α}
    {target : SourceTerm α} (step : SourceStep (.request program) target) :
    target = .done program := by
  cases step
  rfl

def compileStep {allocator : AllocatorSpec α}
    (adequate : AllocatorAdequacy allocator)
    {source target : SourceTerm α} (step : SourceStep source target) :
    ExecutionPath (targetGSLT α allocator)
      (compileTerm source) (compileTerm target) := by
  cases source with
  | done program => exact (no_source_step_from_done step).elim
  | request program =>
      have targetEq := source_step_from_request step
      subst targetEq
      exact two (TargetStep.request _)
        (TargetStep.returnBuffer (adequate.complete _))

def preservesMeaning {allocator : AllocatorSpec α}
    (adequate : AllocatorAdequacy allocator) {term : SourceTerm α}
    (meaning : SourceMeaning term) :
    TargetMeaning allocator (compileTerm term) := by
  cases meaning with
  | request program => exact .start _
  | done program => exact .halted (adequate.complete _)

def realization {allocator : AllocatorSpec α}
    (adequate : AllocatorAdequacy allocator) :
    OperationalRealization (sourceGSLT α) (targetGSLT α allocator) where
  mapTerm := compileTerm
  mapEquiv := by intro left right equal; cases equal; rfl
  mapStep := compileStep adequate

def refinement {allocator : AllocatorSpec α}
    (adequate : AllocatorAdequacy allocator) :
    Refinement (sourceObject α).operational (targetObject α allocator).operational where
  realization := realization adequate
  preservesMeaning := fun _ => preservesMeaning adequate

theorem observation_compiles (term : SourceTerm α) :
    targetObserve (compileTerm term) = sourceObserve term := by
  cases term with
  | request program => rfl
  | done program =>
      change
        some (StackSlice.ofArray
          (arrayConstructionSem (compileProgram program))).toList =
            some (listConstructionSem program)
      simp only [StackSlice.toList_ofArray]
      exact congrArg some (arrayConstructionSem_compile program)

def forward {allocator : AllocatorSpec α}
    (adequate : AllocatorAdequacy allocator) :
    ObservedRefinement (sourceObject α) (targetObject α allocator) where
  refinement := refinement adequate
  commutes := by
    intro first last path
    simpa only [targetObject, sourceObject, refinement, realization] using
      observation_compiles last

theorem no_step_from_halted {allocator : AllocatorSpec α}
    {program : ArrayConstruction α} {result : StackSlice α}
    {target : TargetTerm α}
    (step : TargetStep allocator (.halted program result) target) : False := by
  cases step

theorem path_from_halted {allocator : AllocatorSpec α}
    {program : ArrayConstruction α} {result : StackSlice α}
    {target : TargetTerm α}
    (path : ExecutionPath (targetGSLT α allocator)
      (.halted program result) target) : target = .halted program result := by
  cases path with
  | refl => rfl
  | cons head _ => exact False.elim (no_step_from_halted head.down)

theorem target_observation_forces_source {allocator : AllocatorSpec α}
    (adequate : AllocatorAdequacy allocator)
    {program : ListConstruction α} {target : TargetTerm α}
    {observation : List α}
    (path : ExecutionPath (targetGSLT α allocator)
      (.start (compileProgram program)) target)
    (observed : targetObserve target = some observation) :
    observation = listConstructionSem program := by
  cases path with
  | refl => simp [targetObserve] at observed
  | cons head rest =>
      cases head.down with
      | request targetProgram =>
          cases rest with
          | refl => simp [targetObserve] at observed
          | cons returned restAfter =>
              cases returned.down with
              | returnBuffer allocationEvidence =>
                  have finalEq := path_from_halted restAfter
                  subst finalEq
                  simp [targetObserve] at observed
                  have exactArray := adequate.sound allocationEvidence
                  have exactList := congrArg Array.toList exactArray
                  rw [arrayConstructionSem_compile program] at exactList
                  exact observed.symm.trans exactList

def listConstructionHostedByCArray1 {allocator : AllocatorSpec α}
    (adequate : AllocatorAdequacy allocator) :
    BehavioralHosting (sourceObject α) (targetObject α allocator) where
  forward := forward adequate
  noInvention := by
    intro initial observation produced
    obtain ⟨⟨final, path, observed⟩⟩ := produced
    cases initial with
    | request program =>
        have exactObservation :=
          target_observation_forces_source adequate path observed
        subst exactObservation
        exact ⟨⟨SourceTerm.done program,
          ⟨Route.cons ⟨SourceStep.run program⟩ (Route.refl _), rfl⟩⟩⟩
    | done program =>
        have finalEq := path_from_halted path
        subst finalEq
        change
          some (StackSlice.ofArray
            (arrayConstructionSem (compileProgram program))).toList =
              some observation at observed
        simp only [StackSlice.toList_ofArray] at observed
        rw [arrayConstructionSem_compile program] at observed
        exact ⟨⟨SourceTerm.done program, ⟨Route.refl _, observed⟩⟩⟩

theorem hosting_exact {allocator : AllocatorSpec α}
    (adequate : AllocatorAdequacy allocator)
    (initial : SourceTerm α) (observation : List α) :
    ProducesObservation (targetObject α allocator) (compileTerm initial) observation ↔
      ProducesObservation (sourceObject α) initial observation :=
  (listConstructionHostedByCArray1 adequate).produces_iff initial observation

/-! ## Concrete positive controls -/

example :
    (arrayConstructionSem (compileProgram
      (ListConstruction.prepend 1 [2, 3]))).toList = [1, 2, 3] := by
  simp [arrayConstructionSem, compileProgram]

example :
    (arrayConstructionSem (compileProgram
      (ListConstruction.append [1, 2] [3, 4]))).toList = [1, 2, 3, 4] := by
  simp [arrayConstructionSem, compileProgram]

example :
    (arrayConstructionSem (compileProgram
      (ListConstruction.reverse [1, 2, 3]))).toList = [3, 2, 1] := by
  simp [arrayConstructionSem, compileProgram]

end Mettapedia.GSLT.LanguageDef.CArray1ListConstructionHosting
