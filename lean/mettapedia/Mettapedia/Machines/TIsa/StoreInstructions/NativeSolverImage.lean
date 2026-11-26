import Mettapedia.Machines.TIsa.StoreInstructions.NativeBindingStep
import Mettapedia.Machines.TIsa.StoreInstructions.NativeBindingRoots
import Mettapedia.Machines.TIsa.StoreInstructions.NativeDecompose
import Mettapedia.Machines.TIsa.StoreInstructions.NativeDiscardRun

/-!
# The emitted finite unifier

The decoder, discard edge, decomposition path and two
directions of binding form one image. The three terminal
outcomes of finite unification (solved, head conflict, cyclic
binding) have distinct continuations. Exhaustion and malformed
packing are not logical conflicts.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeSolverImage

open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedScalar (Code)
open NativeTermDispatch (Targets)
open NativeBindEntry (Side)

structure Exits where
  solved : ℕ
  heads : ℕ
  cycle : ℕ
  exhausted : ℕ
  malformed : ℕ

def Exits.inImage (exits : Exits) (image : NativeImage.View) : Prop :=
  exits.solved ≤ image.size ∧ exits.heads ≤ image.size ∧ exits.cycle ≤ image.size ∧
    exits.exhausted ≤ image.size ∧ exits.malformed ≤ image.size

def entrySize : ℕ := 137 + NativeDecisionTargets.width NativeUnifierHeaders.tree
def expandAt (start : ℕ) : ℕ := start + entrySize
def bindAt (start : ℕ) (side : Side) : ℕ := expandAt start + (if side = .left then 200 else 211)
def shared (start : ℕ) : ℕ := expandAt start + 222
def bindingAt (start : ℕ) : ℕ := shared start + 273
def finish (start : ℕ) : ℕ := bindingAt start + 1051

def targets (start : ℕ) (exits : Exits) : Targets :=
  ⟨exits.malformed, start, bindAt start .left, bindAt start .right, expandAt start, exits.heads⟩

@[simp] theorem bind_target (start : ℕ) (exits : Exits) (side : Side) :
    (targets start exits).at side.exiting = bindAt start side := by cases side <;> rfl

def emitPrefix (start : ℕ) (exits : Exits) : List ℕ :=
  NativeAgendaDispatch.emit start exits.solved (targets start exits) ++
    (NativeDecompose.emit (expandAt start) start exits.malformed exits.exhausted ++
      (NativeBindEntry.entryCode .left (bindAt start .left) (shared start) ++
        (NativeBindEntry.entryCode .right (bindAt start .right) (shared start) ++
          NativeBindingGate.emit (shared start) exits.cycle exits.exhausted exits.malformed)))

def emit (start : ℕ) (exits : Exits) : List ℕ :=
  emitPrefix start exits ++ NativeBindingStep.emit (bindingAt start) start exits.exhausted exits.malformed

def finishRooted (start : ℕ) : ℕ := NativeBindingRoots.endAt (bindingAt start)

def emitRooted (start : ℕ) (exits : Exits) : List ℕ :=
  emitPrefix start exits ++ NativeBindingRoots.emit (bindingAt start) start exits.exhausted exits.malformed

theorem entry_size (start : ℕ) (exits : Exits) :
    (NativeAgendaDispatch.emit start exits.solved (targets start exits)).length = entrySize := by
  simp [NativeAgendaDispatch.emit, NativeTermDispatch.emit_size, NativeAgendaRead.emit_size, entrySize]
  omega

theorem prefix_size (start : ℕ) (exits : Exits) : start + (emitPrefix start exits).length = bindingAt start := by
  simp only [emitPrefix, List.length_append, entry_size, NativeDecompose.emit_size, NativeBindEntry.entry_size,
    NativeBindingGate.emit_size, bindingAt, shared, expandAt]
  omega

theorem emit_size (start : ℕ) (exits : Exits) : start + (emit start exits).length = finish start := by
  simp only [emit, List.length_append, ← Nat.add_assoc, prefix_size, NativeBindingStep.emit_size, finish]

theorem emitRooted_size (start : ℕ) (exits : Exits) : start + (emitRooted start exits).length = finishRooted start := by
  simp only [emitRooted, List.length_append, ← Nat.add_assoc, prefix_size, NativeBindingRoots.emit_size, finishRooted]

structure CorePlaced (image : NativeImage.View) (start : ℕ) (exits : Exits) : Prop where
  dispatch : NativeAgendaDispatch.Placed image start exits.solved (targets start exits)
  expand : NativeDecompose.Placed image (expandAt start) start exits.malformed exits.exhausted
  bind : ∀ side, NativeBindEntry.EntryPlaced image side (bindAt start side) (shared start)
  gate : NativeBindingGate.Placed image (shared start) exits.cycle exits.exhausted exits.malformed

structure Placed (image : NativeImage.View) (start : ℕ) (exits : Exits) : Prop extends CorePlaced image start exits where
  binding : NativeBindingStep.Placed image (bindingAt start) start exits.exhausted exits.malformed

structure RootedPlaced (image : NativeImage.View) (start : ℕ) (exits : Exits) : Prop extends CorePlaced image start exits where
  binding : NativeBindingRoots.Placed image (bindingAt start) start exits.exhausted exits.malformed

theorem placed_prefix (image : NativeImage.View) (start : ℕ) (exits : Exits)
    (extent : bindingAt start ≤ image.size) (ends : exits.inImage image) (short : image.size < 2 ^ 31)
    (code : Code image start (emitPrefix start exits)) : CorePlaced image start exits := by
  obtain ⟨dispatch, rest⟩ := NativeWords.code_append
    (show Code image start (NativeAgendaDispatch.emit start exits.solved (targets start exits) ++ _) from code)
  rw [entry_size] at rest
  obtain ⟨expand, rest⟩ := NativeWords.code_append rest
  rw [NativeDecompose.emit_size] at rest
  obtain ⟨bindLeft, rest⟩ := NativeWords.code_append rest
  rw [NativeBindEntry.entry_size] at rest
  obtain ⟨bindRight, gate⟩ := NativeWords.code_append rest
  rw [NativeBindEntry.entry_size] at gate
  have limits := extent
  unfold bindingAt shared expandAt at limits
  have ready : (targets start exits).inImage image := by
    intro exit
    cases exit <;> simp [NativeTermDispatch.Targets.at, targets, bindAt, expandAt]
    all_goals first | exact ends.2.2.2.2 | exact ends.2.1 | omega
  refine ⟨NativeAgendaDispatch.placed_of_emitted image _ _ _ (by rw [entry_size]; omega) ends.1 ready short dispatch,
    NativeDecompose.placed_of_emitted image _ _ _ _ (by unfold expandAt; omega) (by omega)
      ends.2.2.2.2 ends.2.2.2.1 short expand, ?_,
    NativeBindingGate.placed_of_emitted image _ _ _ _ (by unfold shared expandAt; omega)
      ends.2.2.1 ends.2.2.2.1 ends.2.2.2.2 short gate⟩
  intro side
  cases side
  · exact NativeBindEntry.entry_placed image _ _ _ (by simp [bindAt, expandAt]; omega)
      (by unfold shared expandAt; omega) short bindLeft
  · exact NativeBindEntry.entry_placed image _ _ _ (by simp [bindAt, expandAt]; omega)
      (by unfold shared expandAt; omega) short bindRight

theorem placed_of_emitted (image : NativeImage.View) (start : ℕ) (exits : Exits)
    (extent : finish start ≤ image.size) (ends : exits.inImage image) (short : image.size < 2 ^ 31)
    (code : Code image start (emit start exits)) : Placed image start exits := by
  obtain ⟨core, binding⟩ := NativeWords.code_append (show Code image start (emitPrefix start exits ++ _) from code)
  rw [prefix_size] at binding
  have fits := extent
  unfold finish bindingAt shared expandAt at fits
  refine ⟨placed_prefix image start exits ?_ ends short core, NativeBindingStep.placed_of_emitted image _ _ _ _
    extent ?_ ends.2.2.2.1 ends.2.2.2.2 short binding⟩
  · unfold bindingAt shared expandAt
    omega
  · omega

theorem rooted_placed_of_emitted (image : NativeImage.View) (start : ℕ) (exits : Exits)
    (extent : finishRooted start ≤ image.size) (ends : exits.inImage image) (short : image.size < 2 ^ 31)
    (code : Code image start (emitRooted start exits)) : RootedPlaced image start exits := by
  obtain ⟨core, binding⟩ := NativeWords.code_append (show Code image start (emitPrefix start exits ++ _) from code)
  rw [prefix_size] at binding
  have fits := extent
  unfold finishRooted NativeBindingRoots.endAt NativeBindingRoots.atTail NativeBindingRoots.atLoop
    NativeBindingRoots.atRoots bindingAt shared expandAt at fits
  refine ⟨placed_prefix image start exits ?_ ends short core, NativeBindingRoots.placed_of_emitted image _ _ _ _
    extent ?_ ends.2.2.2.1 ends.2.2.2.2 short binding⟩
  · unfold bindingAt shared expandAt
    omega
  · omega

namespace Examples

theorem both_binding_edges_are_distinct (start : ℕ) (exits : Exits) :
    (targets start exits).bindLeft ≠ (targets start exits).bindRight := by
  simp [targets, bindAt]

end Examples

end Mettapedia.Machines.TIsa.StoreInstructions.NativeSolverImage
