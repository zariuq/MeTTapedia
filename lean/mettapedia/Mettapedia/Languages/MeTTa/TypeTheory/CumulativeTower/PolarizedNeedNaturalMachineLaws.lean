import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.PolarizedNeedNaturalSemantics
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.PolarizedNeedMachineRunSegments

/-!
# Exact source selection and owned finalization for first-class Need

Source selection identifies an actual successor occurrence at the same list
position, retaining its world, control and work. Source finalization agrees
with the actual commit step for arbitrary rich cached answers, including
missing cells, lost ownership and receipt-preserving retry reset.

These are local protocol boundary laws. No source evaluation derivation,
typing invariant, or source-to-machine adequacy premise is used. Arbitrary
outer stacks are retained; ordinary thunk or function evaluation is not
replaced by Need allocation here.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
namespace PolarizedNeedNaturalSemantics

open PrimeNeedReference PolarizedNeedMachine

variable {Head Operation Effect StableFault NativeFault : Type} {m : Nat}

theorem Selection.alternativeAt {origin selected : Closure Head Operation Effect m}
    {position : Nat} {rule : PolarizedNeedMachine.Rule}
    (selection : Selection origin position rule selected) :
    getElem? (alternatives (StableFault := StableFault) (NativeFault := NativeFault) origin) position =
      some (rule, .evaluate selected .done) := by
  cases selection with
  | @entry n v k code native values needs notChoice =>
      cases code <;> simp_all [alternatives]
  | left => rfl
  | right => rfl

theorem Selection.alternative_mem {origin selected : Closure Head Operation Effect m}
    {position : Nat} {rule : PolarizedNeedMachine.Rule}
    (selection : Selection origin position rule selected) :
    (rule, .evaluate selected .done) ∈
      alternatives (StableFault := StableFault) (NativeFault := NativeFault) origin :=
  List.mem_of_getElem? selection.alternativeAt

/-- The source's occurrence index selects the exact rich-machine successor,
including the owner, branch path, receipts and updated work counters. -/
theorem Selection.force_entry_at
    (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)
    (world : NeedWorld Head Operation Effect StableFault NativeFault m)
    (stack : List (Frame (Resume Head Operation Effect m)))
    {cell : CellId} {origin selected : Closure Head Operation Effect m}
    {position : Nat} {rule : PolarizedNeedMachine.Rule}
    (selection : Selection origin position rule selected)
    (suspended : world.heap.lookup cell = some ⟨origin, .suspended⟩) (work : Work) :
    getElem? (PrimeNeedLocalSteps.step (extension primitive) ⟨world, .force cell stack, work⟩) position =
      some ⟨enterWorld world cell origin position rule,
        .run (.evaluate selected .done) (.commit cell world.nextEvaluator :: stack),
        work.bump 1 1 2 0⟩ := by
  cases selection with
  | @entry n v k code native values needs notChoice =>
      cases code <;>
        simp_all [PrimeNeedLocalSteps.step, PrimeNeedReference.step, extension, reference,
          alternatives, branchAlternatives, enterWorld, finished, recorded]
  | left =>
      simp only [PrimeNeedLocalSteps.step, PrimeNeedReference.step, suspended,
        extension, reference, alternatives, branchAlternatives,
        List.getElem?_cons_zero, enterWorld, finished, recorded]
  | right =>
      simp only [PrimeNeedLocalSteps.step, PrimeNeedReference.step, suspended,
        extension, reference, alternatives, branchAlternatives,
        List.getElem?_cons_succ, List.getElem?_cons_zero, enterWorld, finished, recorded]

theorem Selection.force_entry
    (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)
    (world : NeedWorld Head Operation Effect StableFault NativeFault m)
    (stack : List (Frame (Resume Head Operation Effect m)))
    {cell : CellId} {origin selected : Closure Head Operation Effect m}
    {position : Nat} {rule : PolarizedNeedMachine.Rule}
    (selection : Selection origin position rule selected)
    (suspended : world.heap.lookup cell = some ⟨origin, .suspended⟩) :
    RunSegment primitive world (.force cell stack)
      (enterWorld world cell origin position rule)
      (.run (.evaluate selected .done) (.commit cell world.nextEvaluator :: stack)) := by
  apply RunSegment.of_step
  intro work
  exact ⟨work.bump 1 1 2 0, ⟨⟨position, selection.force_entry_at primitive world stack suspended work⟩⟩⟩

/-- Reverse extraction retains the supplied occurrence index, even when the
two chosen source bodies are identical. -/
theorem force_suspended_successorAt
    (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)
    {machine next : NeedMachine Head Operation Effect StableFault NativeFault m}
    {cell : CellId} {stack : List (Frame (Resume Head Operation Effect m))}
    {origin : Closure Head Operation Effect m} (position : Nat)
    (control : machine.control = .force cell stack)
    (suspended : machine.world.heap.lookup cell = some ⟨origin, .suspended⟩)
    (selected : getElem? (PrimeNeedLocalSteps.step (extension primitive) machine) position = some next) :
    ∃ rule source, Nonempty (Selection origin position rule source) ∧
      next.world = enterWorld machine.world cell origin position rule ∧
      next.control = .run (.evaluate source .done) (.commit cell machine.world.nextEvaluator :: stack) ∧
      next.work = machine.work.bump 1 1 2 0 := by
  rcases origin with ⟨n, v, k, code, native, values, needs⟩
  simp only [PrimeNeedLocalSteps.step, control, PrimeNeedReference.step, suspended,
    extension, reference] at selected
  cases code with
  | choose left right =>
      cases position with
      | zero =>
          simp only [alternatives, branchAlternatives, List.getElem?_cons_zero, Option.some.injEq] at selected
          subst next
          exact ⟨.left, _, ⟨.left left right native values needs⟩, rfl, rfl, rfl⟩
      | succ position =>
          cases position with
          | zero =>
              simp only [alternatives, branchAlternatives, List.getElem?_cons_succ,
                List.getElem?_cons_zero, Option.some.injEq] at selected
              subst next
              exact ⟨.right, _, ⟨.right left right native values needs⟩, rfl, rfl, rfl⟩
          | succ position =>
              simp only [alternatives, branchAlternatives, List.getElem?_cons_succ,
                List.getElem?_nil, reduceCtorEq] at selected
  | _ =>
      cases position with
      | zero =>
          simp only [alternatives, branchAlternatives, List.getElem?_cons_zero, Option.some.injEq] at selected
          subst next
          exact ⟨.entry, _, ⟨.entry (by intro left right impossible; cases impossible)⟩, rfl, rfl, rfl⟩
      | succ position =>
          simp only [alternatives, branchAlternatives, List.getElem?_cons_succ,
            List.getElem?_nil, reduceCtorEq] at selected

theorem force_suspended_successor
    (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)
    {machine next : NeedMachine Head Operation Effect StableFault NativeFault m}
    {cell : CellId} {stack : List (Frame (Resume Head Operation Effect m))}
    {origin : Closure Head Operation Effect m}
    (control : machine.control = .force cell stack)
    (suspended : machine.world.heap.lookup cell = some ⟨origin, .suspended⟩)
    (member : next ∈ PrimeNeedLocalSteps.step (extension primitive) machine) :
    ∃ position rule selected, Nonempty (Selection origin position rule selected) ∧
      next.world = enterWorld machine.world cell origin position rule ∧
      next.control = .run (.evaluate selected .done) (.commit cell machine.world.nextEvaluator :: stack) := by
  obtain ⟨position, bounded, selected⟩ := List.mem_iff_getElem.mp member
  obtain ⟨rule, source, selection, world, control, _⟩ := force_suspended_successorAt primitive position
    control suspended (List.getElem?_eq_some_iff.mpr ⟨bounded, selected⟩)
  exact ⟨position, rule, source, selection, world, control⟩

/-- Source finalization agrees with the actual commit transition, rather
than being defined by that transition. No owned-cache premise is needed. -/
theorem finalize_commit
    (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)
    (world : NeedWorld Head Operation Effect StableFault NativeFault m)
    (stack : List (Frame (Resume Head Operation Effect m)))
    (cell : CellId) (owner : EvaluatorId) (outcome : Outcome Head Operation Effect StableFault NativeFault m) :
    RunSegment primitive world (.returned outcome (.commit cell owner :: stack))
      (finalize world cell owner outcome).2
      (.returned (finalize world cell owner outcome).1 stack) := by
  cases present : world.heap.lookup cell with
  | none =>
      apply RunSegment.of_singleton (lookups := 1) (updates := 0) (receipts := 1) (allocations := 0)
      intro work
      simp only [PrimeNeedLocalSteps.step, PrimeNeedReference.step, present, finalize,
        retryResult, retryMachine, finished, recorded]
  | some record =>
      cases cached : record.cache with
      | evaluating actual =>
          by_cases same : actual = owner
          · cases outcome <;>
              apply RunSegment.of_singleton (lookups := 1) (updates := 1) (receipts := 1) (allocations := 0) <;>
              intro work <;>
              simp only [PrimeNeedLocalSteps.step, PrimeNeedReference.step, present, cached,
                dif_pos same, finalize, if_pos same, retryResult, retryMachine, finished, recorded]
          · apply RunSegment.of_singleton (lookups := 1) (updates := 0) (receipts := 1) (allocations := 0)
            intro work
            simp only [PrimeNeedLocalSteps.step, PrimeNeedReference.step, present, cached,
              dif_neg same, finalize, if_neg same, retryResult, retryMachine, finished, recorded]
      | suspended | value _ | stableFault _ =>
          apply RunSegment.of_singleton (lookups := 1) (updates := 0) (receipts := 1) (allocations := 0)
          intro work
          simp only [PrimeNeedLocalSteps.step, PrimeNeedReference.step, present, cached, finalize,
            retryResult, retryMachine, finished, recorded]

theorem finalize_successor
    (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)
    {machine next : NeedMachine Head Operation Effect StableFault NativeFault m}
    {cell : CellId} {owner : EvaluatorId} {outcome : Outcome Head Operation Effect StableFault NativeFault m}
    {stack : List (Frame (Resume Head Operation Effect m))}
    (control : machine.control = .returned outcome (.commit cell owner :: stack))
    (member : next ∈ PrimeNeedLocalSteps.step (extension primitive) machine) :
    next.world = (finalize machine.world cell owner outcome).2 ∧
      next.control = .returned (finalize machine.world cell owner outcome).1 stack := by
  cases present : machine.world.heap.lookup cell with
  | none =>
      simp only [PrimeNeedLocalSteps.step, control, PrimeNeedReference.step, present, List.mem_singleton] at member
      subst next
      simp only [finalize, present, retryResult, retryMachine, finished, recorded, and_self]
  | some record =>
      cases cached : record.cache with
      | evaluating actual =>
          by_cases same : actual = owner
          · cases outcome <;>
              simp only [PrimeNeedLocalSteps.step, control, PrimeNeedReference.step, present, cached,
                dif_pos same, List.mem_singleton] at member <;>
              subst next <;>
              simp only [finalize, present, cached, if_pos same, retryResult, retryMachine, finished,
                recorded, and_self]
          · simp only [PrimeNeedLocalSteps.step, control, PrimeNeedReference.step, present, cached,
              dif_neg same, List.mem_singleton] at member
            subst next
            simp only [finalize, present, cached, if_neg same, retryResult, retryMachine, finished,
              recorded, and_self]
      | suspended | value _ | stableFault _ =>
          simp only [PrimeNeedLocalSteps.step, control, PrimeNeedReference.step, present, cached,
            List.mem_singleton] at member
          subst next
          simp only [finalize, present, cached, retryResult, retryMachine, finished, recorded, and_self]

/-- Equal branch bodies do not identify their selected occurrence worlds. -/
theorem choice_entry_worlds_ne
    (world : NeedWorld Head Operation Effect StableFault NativeFault m)
    (cell : CellId) (origin : Closure Head Operation Effect m) :
    enterWorld world cell origin 0 .left ≠ enterWorld world cell origin 1 .right := by
  intro equal
  have paths : world.path ++ [0] = world.path ++ [1] := congrArg World.path equal
  have different : [0] = ([1] : WorldPath) := List.append_cancel_left paths
  cases different

/-- An actual wrong-owner commit produces the ownership fault and retains
the heap; an independently supplied value does not bypass the owner check. -/
theorem wrong_owner_successor
    (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)
    {machine next : NeedMachine Head Operation Effect StableFault NativeFault m}
    {cell : CellId} {owner actual : EvaluatorId}
    {origin : Closure Head Operation Effect m} {outcome : Outcome Head Operation Effect StableFault NativeFault m}
    {stack : List (Frame (Resume Head Operation Effect m))}
    (control : machine.control = .returned outcome (.commit cell owner :: stack))
    (present : machine.world.heap.lookup cell = some ⟨origin, .evaluating actual⟩)
    (different : actual ≠ owner)
    (member : next ∈ PrimeNeedLocalSteps.step (extension primitive) machine) :
    next.world.heap = machine.world.heap ∧
      next.control = .returned (.retryableFault (.ownershipLost cell owner actual)) stack := by
  obtain ⟨world, control⟩ := finalize_successor primitive control member
  constructor
  · rw [world]
    simp only [finalize, present, if_neg different, retryResult, World.record]
  · simpa only [finalize, present, if_neg different, retryResult] using control

#print axioms Selection.alternativeAt
#print axioms Selection.alternative_mem
#print axioms Selection.force_entry_at
#print axioms Selection.force_entry
#print axioms force_suspended_successorAt
#print axioms force_suspended_successor
#print axioms finalize_commit
#print axioms finalize_successor
#print axioms choice_entry_worlds_ne
#print axioms wrong_owner_successor

end PolarizedNeedNaturalSemantics
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
