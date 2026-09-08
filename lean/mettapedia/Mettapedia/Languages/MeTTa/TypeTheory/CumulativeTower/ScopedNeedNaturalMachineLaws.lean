import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.ScopedNeedNaturalSemantics
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.ScopedNeedMachineRunSegments

/-!
# Source selection and finalization at exact machine boundaries

An independently selected source occurrence is at its stated position in the
machine's alternative list. Forcing a suspended cell enters that exact world,
including singleton branch paths and the owned commit frame. The source's
finalization operation agrees with the actual commit transition, including
missing cells, lost ownership and retry restoration.

These are boundary laws, not evaluation adequacy assumed as a premise. They
use no source evaluation derivation and retain arbitrary outer consumer stacks.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
namespace ScopedNeedNaturalSemantics

open PrimeNeedReference ScopedNeedMachine

variable {Head Operation Effect StableFault NativeFault : Type} {m : Nat}

theorem Selection.alternativeAt {origin selected : Closure Head Operation Effect m}
    {position : Nat} {rule : ScopedNeedMachine.Rule}
    (selection : Selection origin position rule selected) :
    (alternatives (StableFault := StableFault) (NativeFault := NativeFault) origin)[position]? =
      some (rule, .evaluate selected .done) := by
  cases selection with
  | @entry n k code values needs notChoice =>
      cases code <;> simp_all [alternatives]
  | left => rfl
  | right => rfl

theorem Selection.alternative_mem {origin selected : Closure Head Operation Effect m}
    {position : Nat} {rule : ScopedNeedMachine.Rule}
    (selection : Selection origin position rule selected) :
    (rule, .evaluate selected .done) ∈
      alternatives (StableFault := StableFault) (NativeFault := NativeFault) origin := by
  exact List.mem_of_getElem? selection.alternativeAt

/-- Source selection retains the actual successor position, not only the
possibility of reaching an equal branch value. -/
theorem Selection.force_entry
    (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)
    (world : NeedWorld Head Operation Effect StableFault NativeFault m)
    (stack : List (Frame (Resume Head Operation Effect m)))
    {cell : CellId} {origin selected : Closure Head Operation Effect m}
    {position : Nat} {rule : ScopedNeedMachine.Rule}
    (selection : Selection origin position rule selected)
    (suspended : world.heap.lookup cell = some ⟨origin, .suspended⟩) :
    RunSegment primitive world (.force cell stack)
      (enterWorld world cell origin position rule)
      (.run (.evaluate selected .done) (.commit cell world.nextEvaluator :: stack)) := by
  apply RunSegment.of_step
  intro work
  refine ⟨work.bump 1 1 2 0, ⟨⟨position, ?_⟩⟩⟩
  cases selection with
  | @entry n k code values needs notChoice =>
      cases code <;>
        simp_all [step, spec, alternatives, branchAlternatives, enterWorld, finished, recorded]
  | left =>
      simp only [step, suspended, spec, alternatives, branchAlternatives,
        List.getElem?_cons_zero, enterWorld, finished, recorded]
  | right =>
      simp only [step, suspended, spec, alternatives, branchAlternatives,
        List.getElem?_cons_succ, List.getElem?_cons_zero, enterWorld, finished, recorded]

/-- Every actual suspended-force successor supplies independent source
selection evidence and the exact entered world and commit control. -/
theorem force_suspended_successor
    (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)
    {machine next : NeedMachine Head Operation Effect StableFault NativeFault m}
    {cell : CellId} {stack : List (Frame (Resume Head Operation Effect m))}
    {origin : Closure Head Operation Effect m}
    (control : machine.control = .force cell stack)
    (suspended : machine.world.heap.lookup cell = some ⟨origin, .suspended⟩)
    (member : next ∈ step (spec primitive) machine) :
    ∃ position rule selected, Nonempty (Selection origin position rule selected) ∧
      next.world = enterWorld machine.world cell origin position rule ∧
      next.control = .run (.evaluate selected .done) (.commit cell machine.world.nextEvaluator :: stack) := by
  rcases origin with ⟨n, k, code, values, needs⟩
  simp only [step, control, suspended, spec] at member
  cases code with
  | choose left right =>
      simp only [alternatives, branchAlternatives, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact ⟨0, .left, _, ⟨.left left right values needs⟩, rfl, rfl⟩
      · exact ⟨1, .right, _, ⟨.right left right values needs⟩, rfl, rfl⟩
  | _ =>
      simp only [alternatives, branchAlternatives, List.mem_singleton] at member
      subst next
      exact ⟨0, .entry, _, ⟨.entry (by intro left right impossible; cases impossible)⟩, rfl, rfl⟩

/-- Actual commit and source finalization agree even when ownership is lost.
The outcome and world are computed independently by `finalize`. -/
theorem finalize_commit
    (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)
    (world : NeedWorld Head Operation Effect StableFault NativeFault m)
    (stack : List (Frame (Resume Head Operation Effect m)))
    (cell : CellId) (owner : EvaluatorId) (outcome : Outcome Head StableFault NativeFault m) :
    RunSegment primitive world (.returned outcome (.commit cell owner :: stack))
      (finalize world cell owner outcome).2
      (.returned (finalize world cell owner outcome).1 stack) := by
  cases present : world.heap.lookup cell with
  | none =>
      apply RunSegment.of_singleton (lookups := 1) (updates := 0) (receipts := 1) (allocations := 0)
      intro work
      simp only [step, present, finalize, retryResult, retryMachine, finished, recorded]
  | some record =>
      cases cached : record.cache with
      | evaluating actual =>
          by_cases same : actual = owner
          · cases outcome <;>
              apply RunSegment.of_singleton (lookups := 1) (updates := 1) (receipts := 1) (allocations := 0) <;>
              intro work <;>
              simp only [step, present, cached, dif_pos same, finalize, if_pos same,
                retryResult, retryMachine, finished, recorded]
          · apply RunSegment.of_singleton (lookups := 1) (updates := 0) (receipts := 1) (allocations := 0)
            intro work
            simp only [step, present, cached, dif_neg same, finalize, if_neg same,
              retryResult, retryMachine, finished, recorded]
      | suspended | value _ | stableFault _ =>
          apply RunSegment.of_singleton (lookups := 1) (updates := 0) (receipts := 1) (allocations := 0)
          intro work
          simp only [step, present, cached, finalize, retryResult, retryMachine, finished, recorded]

/-- Conversely, an actual commit step cannot invent a different source
finalization outcome or erase its receipt-bearing final world. -/
theorem finalize_successor
    (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)
    {machine next : NeedMachine Head Operation Effect StableFault NativeFault m}
    {cell : CellId} {owner : EvaluatorId} {outcome : Outcome Head StableFault NativeFault m}
    {stack : List (Frame (Resume Head Operation Effect m))}
    (control : machine.control = .returned outcome (.commit cell owner :: stack))
    (member : next ∈ step (spec primitive) machine) :
    next.world = (finalize machine.world cell owner outcome).2 ∧
      next.control = .returned (finalize machine.world cell owner outcome).1 stack := by
  cases present : machine.world.heap.lookup cell with
  | none =>
      simp only [step, control, present, List.mem_singleton] at member
      subst next
      simp only [finalize, present, retryResult, retryMachine, finished, recorded, and_self]
  | some record =>
      cases cached : record.cache with
      | evaluating actual =>
          by_cases same : actual = owner
          · cases outcome <;>
              simp only [step, control, present, cached, dif_pos same, List.mem_singleton] at member <;>
              subst next <;>
              simp only [finalize, present, cached, if_pos same, retryResult, retryMachine, finished, recorded,
                and_self]
          · simp only [step, control, present, cached, dif_neg same, List.mem_singleton] at member
            subst next
            simp only [finalize, present, cached, if_neg same, retryResult, retryMachine, finished, recorded,
              and_self]
      | suspended | value _ | stableFault _ =>
          simp only [step, control, present, cached, List.mem_singleton] at member
          subst next
          simp only [finalize, present, cached, retryResult, retryMachine, finished, recorded, and_self]

#print axioms Selection.alternativeAt
#print axioms Selection.alternative_mem
#print axioms Selection.force_entry
#print axioms force_suspended_successor
#print axioms finalize_commit
#print axioms finalize_successor

end ScopedNeedNaturalSemantics
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
