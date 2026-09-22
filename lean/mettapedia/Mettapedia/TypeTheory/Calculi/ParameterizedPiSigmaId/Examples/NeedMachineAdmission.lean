import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Computation.ScopedNeedMachineAdmission
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.NeedTyping
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Computation.ScopedNeedMachineTyping
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveDependentComputation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.DependentComputation

/-! # Finite execution and admission controls -/

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace ScopedNeedMachine
open Mettapedia.Machines.BranchLocalNeed
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
set_option autoImplicit false
open NeedReference
open ScopedComputation (OperationSignature)
variable {Head Operation Effect StableFault NativeFault : Type} {n m k : Nat}
  {R : Rules Head} {signature : OperationSignature Head Operation} {Δ : Ctx Head m}

namespace AdmissionExamples

open ScopedNeedComputation.Examples

abbrev ExampleMachine := NeedMachine Tower.Head Empty Bool Empty Empty 1

def primitive : Empty → Tower.Tm 1 → Produced (Tower.Tm 1) Empty Empty :=
  fun operation => nomatch operation

def machineSpec : NeedSpec Tower.Head Empty Bool Empty Empty 1 := spec primitive

def initial : ExampleMachine where
  world :=
    { lineage := 0, path := [], heap := .empty, receipts := .empty,
      nextCell := 0, nextEvaluator := 0 }
  control := .run (.evaluate ⟨1, 0, source, ids, Fin.elim0⟩ .done) []

/-- The source is admitted before execution; its result type depends on the
first selected native value through both endpoints of an identity type. -/
theorem initial_source_typed :
    ClosureTyping Tower.rules operationSignature context (fun _ => none)
      (⟨1, 0, source, ids, Fin.elim0⟩ : Closure Tower.Head Empty Bool 1)
      (.sigma ground identityFamily) := by
  have typed : ClosureTyping Tower.rules operationSignature context (fun _ => none)
      (⟨1, 0, source, ids, Fin.elim0⟩ : Closure Tower.Head Empty Bool 1)
      (subst ids (.sigma ground identityFamily)) :=
    .captured source_typing (fun index => by simpa only [subst_ids, ids] using
      (FormationSensitive.Typing.var (R := Tower.rules) (Γ := context) index))
      (fun index => Fin.elim0 index)
  simpa only [subst_ids] using typed

def effects (machine : ExampleMachine) : List Bool :=
  machine.world.receipts.nodes.reverse.filterMap fun node =>
    match node.payload with
    | .effect effect => some effect
    | _ => none

def observe (machine : ExampleMachine) : Option (Outcome Tower.Head Empty Empty 1) × List Bool :=
  (haltedOutcome machine, effects machine)

/-- Two force sites share the one effectful producer, including the force
below a native binder. The retained result is a native dependent pair. -/
theorem shared_dependent_run :
    (runFrontier machineSpec 64 [initial]).map observe =
      [(some (.value (.pair (.var 0) (.refl (.var 0)))), [true])] := by
  rfl

theorem dependent_result_admitted :
    FormationSensitive.Judgment Tower.rules context
      (.pair (.var 0) (.refl (.var 0))) (.sigma ground identityFamily) :=
  ⟨source_judgment.context,
    .pairIntro sigma_formed (.sort _) (.var 0) (.reflIntro (.var 0))⟩

/-- This bounded execution's actual value results have native judgments.
The proof uses its computed frontier and independent native pair admission,
not a claim of preservation for arbitrary machine stacks. -/
theorem shared_returned_judgment {machine : ExampleMachine} {value : Tower.Tm 1}
    (member : machine ∈ runFrontier machineSpec 64 [initial])
    (returned : haltedOutcome machine = some (.value value)) :
    FormationSensitive.Judgment Tower.rules context value (.sigma ground identityFamily) := by
  have observed : observe machine ∈ (runFrontier machineSpec 64 [initial]).map observe :=
    List.mem_map.mpr ⟨machine, member, rfl⟩
  rw [shared_dependent_run, List.mem_singleton] at observed
  have equal := congrArg Prod.fst observed
  change haltedOutcome machine = _ at equal
  rw [returned] at equal
  cases equal
  exact dependent_result_admitted

end AdmissionExamples

namespace CacheExamples

open FormationSensitive.DependentComputation.Examples
open ScopedNeedComputation.Examples (operationSignature)

abbrev ExampleMachine := NeedMachine Tower.Head Empty Bool Empty Empty 2

def primitive : Empty → Tower.Tm 2 → Produced (Tower.Tm 2) Empty Empty :=
  fun operation => nomatch operation

def cell : CellId := ⟨0, [], 0, 0⟩

def producer : Closure Tower.Head Empty Bool 2 :=
  ⟨2, 0, .returnValue (.refl older.val), ids, Fin.elim0⟩

def suspendedHeap : Heap (Closure Tower.Head Empty Bool 2) (Tower.Tm 2) Empty where
  current := Function.update (fun _ => none) cell (some ⟨producer, .suspended⟩)
  spine := [.allocate cell producer]

/-- The fixture's allocation is an actual successful heap operation. -/
theorem suspendedHeap_allocated :
    Heap.empty.allocate? cell producer = some suspendedHeap := rfl

def completedHeap : Heap (Closure Tower.Head Empty Bool 2) (Tower.Tm 2) Empty :=
  suspendedHeap.setKnownCache cell ⟨producer, .suspended⟩ (.value (.refl older.val))

def cellTypes : CellTypes Tower.Head 2 :=
  Function.update (fun _ => none) cell (some (inst0 older.val family))

private theorem environment : FormationSensitive.CtxMor Tower.rules context context ids := by
  intro index
  simpa only [subst_ids, ids] using
    (FormationSensitive.Typing.var (R := Tower.rules) (Γ := context) index)

theorem producer_typed :
    ClosureTyping Tower.rules operationSignature context cellTypes producer
      (inst0 older.val family) := by
  have typed : ClosureTyping Tower.rules operationSignature context cellTypes producer
      (subst ids (inst0 older.val family)) :=
    .captured (needTypes := Fin.elim0)
      (.returnValue (reflexivity older).property.typing) environment
      (fun index => Fin.elim0 index)
  simpa only [subst_ids] using typed

theorem suspendedHeap_typed :
    HeapTyping Tower.rules operationSignature context cellTypes suspendedHeap := by
  constructor
  · intro key record lookup
    by_cases equal : key = cell
    · subst key
      have same : record = ⟨producer, .suspended⟩ := by
        simpa [Heap.lookup, suspendedHeap] using lookup.symm
      subst record
      exact ⟨inst0 older.val family, by simp [cellTypes], producer_typed, .suspended⟩
    · simp only [Heap.lookup, suspendedHeap, Function.update_of_ne equal] at lookup
      cases lookup
  · intro key A declared
    by_cases equal : key = cell
    · subst key
      exact ⟨⟨producer, .suspended⟩, by simp [Heap.lookup, suspendedHeap]⟩
    · simp only [cellTypes, Function.update_of_ne equal] at declared
      cases declared

/-- The cache write is qualified by independent native reflexivity typing. -/
theorem completedHeap_typed :
    HeapTyping Tower.rules operationSignature context cellTypes completedHeap :=
  suspendedHeap_typed.setKnownCache (by simp [Heap.lookup, suspendedHeap])
    (by simp [cellTypes]) (.value (reflexivity older).property.typing)

def forceClosure : Closure Tower.Head Empty Bool 2 :=
  ⟨2, 1, .force 0, ids, fun _ => cell⟩

theorem force_typed :
    ClosureTyping Tower.rules operationSignature context cellTypes forceClosure
      (inst0 older.val family) := by
  have typed : ClosureTyping Tower.rules operationSignature context cellTypes forceClosure
      (subst ids (inst0 older.val family)) := by
    apply ClosureTyping.captured
      (needTypes := fun _ => inst0 older.val family) (.force 0) environment
    intro index
    simp [cellTypes]
  simpa only [subst_ids] using typed

def pairKont : Kont Tower.Head 2 := .pair older.val .done

theorem pairKont_typed : KontTyping Tower.rules context pairKont
    (inst0 older.val family) (.sigma ground family) :=
  .pair sigma_formed.typing (.sort _) older.property.typing (.done _)

/-- This actual cache consumer returns the dependent pair at the selected
older value; its second component is admitted in that exact identity fibre. -/
theorem actual_cached_pair_judgment :
    FormationSensitive.Judgment Tower.rules context
      (.pair older.val (.refl older.val)) (.sigma ground family) :=
  cached_force_consumer_judgment (NativeFault := Empty) (origin := producer)
    force_typed context_formed
    completedHeap_typed (by simp [completedHeap, Heap.setKnownCache_lookup_same])
    pairKont_typed rfl

def cachedMachine : ExampleMachine where
  world :=
    { lineage := 0, path := [], heap := completedHeap, receipts := .empty,
      nextCell := 1, nextEvaluator := 0 }
  control := .force cell [.resume (.finish pairKont)]

theorem actual_cached_pair_run :
    answers (spec primitive) 8 cachedMachine =
      [.value (.pair older.val (.refl older.val))] := rfl

def wrongCellTypes : CellTypes Tower.Head 2 :=
  Function.update (fun _ => none) cell (some (inst0 newer.val family))

/-- The same raw cached term cannot acquire the other selected value's fibre.
This refutes the independently stated heap invariant, not machine execution. -/
theorem wrong_fibre_cache_not_typed :
    ¬ HeapTyping Tower.rules operationSignature context wrongCellTypes completedHeap := by
  intro typed
  exact wrong_selected_index_not_admitted
    (typed.cached_judgment (cell := cell) (origin := producer)
      context_formed (by simp [wrongCellTypes])
      (by simp [completedHeap, Heap.setKnownCache_lookup_same]))

/-- With no proof-side cell-type assignment consulted, the raw machine still
returns an injected value even when it violates the declared native fibre. -/
def wrongMachine : ExampleMachine :=
  { cachedMachine with control := .force cell [] }

theorem wrong_fibre_still_returned :
    answers (spec primitive) 4 wrongMachine = [.value (.refl older.val)] := rfl

theorem wrong_return_has_no_requested_judgment :
    ¬ FormationSensitive.Judgment Tower.rules context
      (.refl older.val) (inst0 newer.val family) := wrong_selected_index_not_admitted

end CacheExamples

#print axioms AdmissionExamples.initial_source_typed

#print axioms AdmissionExamples.shared_dependent_run

#print axioms AdmissionExamples.shared_returned_judgment

#print axioms CacheExamples.suspendedHeap_allocated

#print axioms CacheExamples.completedHeap_typed

#print axioms CacheExamples.actual_cached_pair_judgment

#print axioms CacheExamples.actual_cached_pair_run

#print axioms CacheExamples.wrong_fibre_cache_not_typed

#print axioms CacheExamples.wrong_fibre_still_returned

#print axioms CacheExamples.wrong_return_has_no_requested_judgment

end ScopedNeedMachine
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
