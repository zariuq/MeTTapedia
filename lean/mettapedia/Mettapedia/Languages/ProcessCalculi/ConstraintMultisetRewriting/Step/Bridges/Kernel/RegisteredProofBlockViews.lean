import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.RegisteredProofBlocksControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.ReplayCacheViews

/-!
# Shared Array views feed the existing registered block checker

Parent selection through a sized view agrees exactly with the original
Array lookup. A balanced representation of the resulting cache is accepted
only with equality to the actual ordered cache extension. The original
formation, primitive replay, declaration context and command receipts are
retained. No alternative proof checker or native receiver is introduced.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.RegisteredProofBlockViews

open Mettapedia.Logic Mettapedia.Languages.OpenTheory Mettapedia.Languages.HOLLight
open ProofExecution ReplayCacheViews

universe u

theorem select_lookup {α : Type u} {size : Nat} (view : View α size) (roots : List Nat) :
    view.select? roots = DerivationGraph.lookupPremises view.values roots := by
  induction roots with
  | nil => rfl
  | cons index later ih =>
      simp only [View.select?, DerivationGraph.lookupPremises, View.read_values, ih]

def finishView (before : Registered.State) (instances : SignatureFormation.InstanceWitnesses)
    (nodes : List Receipt) {size : Nat} (view : View Theorem size) : Registered.State :=
  ⟨before.context, view.values, before.receipts ++ (RegisteredProofBlocks.receipts instances nodes).toArray⟩

theorem finishView_eq (before : Registered.State) (instances : SignatureFormation.InstanceWitnesses)
    (nodes : List Receipt) {size : Nat} (view : View Theorem size)
    (extension : view.values = before.cache ++ (nodes.map (·.conclusion)).toArray) :
    finishView before instances nodes view = RegisteredProofBlocks.finish before instances nodes := by
  simp only [finishView, RegisteredProofBlocks.finish, extension]

theorem extension_size (before : Registered.State) (nodes : List Receipt)
    {size : Nat} (view : View Theorem size)
    (extension : view.values = before.cache ++ (nodes.map (·.conclusion)).toArray) :
    size = before.cache.size + nodes.length := by
  have counted := congrArg Array.size extension
  simpa only [View.values_size, Array.size_append, List.size_toArray, List.length_map] using counted

theorem relocated_replay_view (policy : AxiomPolicy) [DecidablePred policy]
    (before : Registered.State) (instances : SignatureFormation.InstanceWitnesses)
    {beforeSize afterSize : Nat} (beforeView : View Theorem beforeSize) (afterView : View Theorem afterSize)
    (beforeExact : before.cache = beforeView.values)
    (roots : List Nat) (premises : List Theorem) (conclusion : Theorem) (block : ProofSystem.Certificate)
    (selected : beforeView.select? roots = some premises)
    (checked : GraphExpansion.BlockChecked policy premises conclusion block)
    (formed : RegisteredProofBlocks.Formed before instances block.1)
    (extension : afterView.values = before.cache ++
      ((GraphExpansion.expandBlock roots before.cache.size block).1.map (·.conclusion)).toArray) :
    Registered.replayFrom policy before
        (RegisteredProofBlocks.commands instances (GraphExpansion.expandBlock roots before.cache.size block).1) =
      some (finishView before instances (GraphExpansion.expandBlock roots before.cache.size block).1 afterView) := by
  have actual : DerivationGraph.lookupPremises before.cache roots = some premises := by
    rw [beforeExact]
    exact (select_lookup beforeView roots).symm.trans selected
  rw [finishView_eq before instances _ afterView extension]
  exact RegisteredProofBlocks.relocated_replay policy before instances roots premises conclusion block
    actual checked formed

theorem relocated_root_view (policy : AxiomPolicy) [DecidablePred policy]
    (before : Registered.State) (instances : SignatureFormation.InstanceWitnesses)
    {beforeSize afterSize : Nat} (beforeView : View Theorem beforeSize) (afterView : View Theorem afterSize)
    (beforeExact : before.cache = beforeView.values)
    (roots : List Nat) (premises : List Theorem) (conclusion : Theorem) (block : ProofSystem.Certificate)
    (selected : beforeView.select? roots = some premises)
    (checked : GraphExpansion.BlockChecked policy premises conclusion block)
    (extension : afterView.values = before.cache ++
      ((GraphExpansion.expandBlock roots before.cache.size block).1.map (·.conclusion)).toArray) :
    (finishView before instances (GraphExpansion.expandBlock roots before.cache.size block).1 afterView).cache[
      (GraphExpansion.expandBlock roots before.cache.size block).2]? = some conclusion := by
  have actual : DerivationGraph.lookupPremises before.cache roots = some premises := by
    rw [beforeExact]
    exact (select_lookup beforeView roots).symm.trans selected
  rw [finishView_eq before instances _ afterView extension]
  exact RegisteredProofBlocks.relocated_root policy before instances roots premises conclusion block actual checked

namespace Controls

open RegisteredProofBlocks.Controls
local instance : DecidablePred emptyAxiomPolicy := fun _ => isFalse id

def beforeBlocks : List (Block Theorem) :=
  [Block.ofArray #[fact], Block.ofArray
    #[Registered.Controls.definedType.output.abstractionRepresentationTheorem,
      Registered.Controls.definedType.output.representationAbstractionTheorem]]

def beforeView : Packed Theorem := build beforeBlocks
def afterView : Packed Theorem :=
  build (beforeBlocks ++ [Block.ofArray (expanded.map (·.conclusion)).toArray])

theorem before_exact : before.cache = beforeView.2.values := by
  change before.cache = (build beforeBlocks).2.values
  rw [build_values]
  rfl

theorem after_extension : afterView.2.values = before.cache ++ (expanded.map (·.conclusion)).toArray := by
  change (build (beforeBlocks ++ [Block.ofArray (expanded.map (·.conclusion)).toArray])).2.values = _
  rw [build_append_values]
  exact congrArg (fun cache => cache ++ (expanded.map (·.conclusion)).toArray) before_exact.symm

theorem selected_view : beforeView.2.select? [0, 0] = some [fact, fact] := by
  rw [select_lookup, ← before_exact]
  exact RegisteredProofBlocks.Controls.selected

theorem actual_registered_replay :
    Registered.replayFrom emptyAxiomPolicy before (RegisteredProofBlocks.commands instances expanded) =
      some (finishView before instances expanded afterView.2) :=
  relocated_replay_view emptyAxiomPolicy before instances beforeView.2 afterView.2 before_exact
    [0, 0] [fact, fact] fact block selected_view block_checked formed after_extension

theorem actual_registered_root :
    (finishView before instances expanded afterView.2).cache[4]? = some fact := by
  have actual := relocated_root_view emptyAxiomPolicy before instances beforeView.2 afterView.2 before_exact
    [0, 0] [fact, fact] fact block selected_view block_checked after_extension
  exact actual

theorem exact_two_output_definition :
    (finishView before instances expanded afterView.2).cache[1]? =
        some Registered.Controls.definedType.output.abstractionRepresentationTheorem ∧
      (finishView before instances expanded afterView.2).cache[2]? =
        some Registered.Controls.definedType.output.representationAbstractionTheorem := by
  rw [finishView_eq before instances expanded afterView.2 after_extension]
  exact ⟨definition_first_retained, definition_second_retained⟩

theorem wrong_address_is_still_refused :
    Registered.replayFrom emptyAxiomPolicy before
      (RegisteredProofBlocks.commands instances wrongIndexNodes) = none :=
  wrong_index_refused

end Controls

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.RegisteredProofBlockViews

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.RegisteredProofBlockViews.relocated_replay_view
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.RegisteredProofBlockViews.Controls.actual_registered_replay
