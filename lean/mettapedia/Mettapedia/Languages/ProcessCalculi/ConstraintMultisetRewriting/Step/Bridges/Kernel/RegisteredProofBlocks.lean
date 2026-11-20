import Mettapedia.Languages.HOLLight.RegisteredProofGraph
import Mettapedia.Languages.HOLLight.RegisteredReplayComposition
import Mettapedia.Languages.HOLLight.GraphExpansion
import Mettapedia.Logic.DerivationGraph.CheckedMaterialization

/-!
# Exact registered reception of checked local proof blocks

The original primitive graph checker validates a block over its compact
external-premise vector. Existing relocation transports that check to the
actual receiving cache. Request and result formation are checked in the
actual receiving signature. The resulting registered execution retains
exactly the relocated commands, their ordered receipts and their outputs.

Declaration commands remain separate registered commands. These lemmas do
not quote a native receiver run or supply an accepted history for a source
packet whose individual blocks have not been checked.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.RegisteredProofBlocks

open Mettapedia.Logic Mettapedia.Languages.OpenTheory Mettapedia.Languages.HOLLight
open ProofExecution

def commands (instances : SignatureFormation.InstanceWitnesses) (nodes : List Receipt) :
    List Registered.Command :=
  nodes.map (fun node => .proof node instances)

def receipts (instances : SignatureFormation.InstanceWitnesses) (nodes : List Receipt) :
    List Registered.CommandReceipt :=
  nodes.map (fun node => ⟨.proof node instances, [node.conclusion]⟩)

def finish (before : Registered.State) (instances : SignatureFormation.InstanceWitnesses)
    (nodes : List Receipt) : Registered.State :=
  ⟨before.context, before.cache ++ (nodes.map (·.conclusion)).toArray,
    before.receipts ++ (receipts instances nodes).toArray⟩

def Formed (before : Registered.State) (instances : SignatureFormation.InstanceWitnesses)
    (nodes : List Receipt) : Prop :=
  ∀ node ∈ nodes,
    Registered.requestFormedB before.context.signature instances node.witness = true ∧
      DefinitionAdapters.theoremFormedB before.context.signature instances node.conclusion = true

theorem materialize_eq_append (cache : Array Theorem) (nodes : List Receipt) :
    DerivationGraph.materialize cache nodes = cache ++ (nodes.map (·.conclusion)).toArray := by
  induction nodes generalizing cache with
  | nil => simp [DerivationGraph.materialize]
  | cons node nodes ih =>
      change DerivationGraph.materialize (cache.push node.conclusion) nodes =
        cache ++ ((node :: nodes).map (·.conclusion)).toArray
      rw [ih, List.map_cons, List.toArray_cons, Array.push_eq_append, Array.append_assoc]

theorem apply_proof_receipt (policy : AxiomPolicy) [DecidablePred policy]
    {before after : Registered.State} {node : Receipt}
    {instances : SignatureFormation.InstanceWitnesses}
    (accepted : Registered.apply policy before (.proof node instances) = some after) :
    after.receipts = before.receipts.push ⟨.proof node instances, [node.conclusion]⟩ := by
  obtain ⟨_, native, arguments, output⟩ := Registered.proof_apply_replay policy accepted
  have actual : (Registered.Command.proof node instances).check policy
      before.context before.cache = some ⟨before.context, [node.conclusion]⟩ := by
    simp [Registered.Command.check, native, arguments, output]
  obtain ⟨result, checked, _, _, retained⟩ := Registered.apply_result policy accepted
  have same := Option.some.inj (checked.symm.trans actual)
  simpa only [same] using retained

theorem replay_proof_receipts (policy : AxiomPolicy) [DecidablePred policy]
    (before : Registered.State) (instances : SignatureFormation.InstanceWitnesses)
    (nodes : List Receipt) {after : Registered.State}
    (accepted : Registered.replayFrom policy before (commands instances nodes) = some after) :
    after.receipts = before.receipts ++ (receipts instances nodes).toArray := by
  induction nodes generalizing before with
  | nil =>
      have same : before = after := Option.some.inj accepted
      simp [same, receipts]
  | cons node nodes ih =>
      cases first : Registered.apply policy before (.proof node instances) with
      | none => simp [commands, Registered.replayFrom, first] at accepted
      | some middle =>
          have tail : Registered.replayFrom policy middle (commands instances nodes) = some after := by
            simpa [commands, Registered.replayFrom, first] using accepted
          rw [ih middle tail, apply_proof_receipt policy first]
          change before.receipts.push _ ++ (receipts instances nodes).toArray =
            before.receipts ++ (_ :: receipts instances nodes).toArray
          rw [List.toArray_cons, Array.push_eq_append, Array.append_assoc]

theorem replayProofs_exact (policy : AxiomPolicy) [DecidablePred policy]
    (before : Registered.State) (instances : SignatureFormation.InstanceWitnesses)
    (nodes : List Receipt) (out : Array Theorem)
    (formed : Formed before instances nodes)
    (checked : DerivationGraph.replayFrom (ruleWitness policy) before.cache nodes = some out) :
    Registered.replayFrom policy before (commands instances nodes) =
      some (finish before instances nodes) := by
  obtain ⟨after, accepted, context, cache⟩ :=
    Registered.replayProofs_available policy before nodes instances out formed checked
  have kept := replay_proof_receipts policy before instances nodes accepted
  have materialized := (DerivationGraph.replayFrom_eq_materialize (ruleWitness policy) checked).trans
    (materialize_eq_append before.cache nodes)
  have same : after = finish before instances nodes := by
    cases after
    simp_all only [finish]
  exact accepted.trans (congrArg some same)

theorem relocated_formed (before : Registered.State)
    (instances : SignatureFormation.InstanceWitnesses) (roots : List Nat)
    (block : ProofSystem.Certificate) (formed : Formed before instances block.1) :
    Formed before instances (GraphExpansion.expandBlock roots before.cache.size block).1 := by
  intro node member
  obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
  simpa only [DerivationGraph.Node.relocate] using formed original present

theorem relocated_replay (policy : AxiomPolicy) [DecidablePred policy]
    (before : Registered.State) (instances : SignatureFormation.InstanceWitnesses)
    (roots : List Nat) (premises : List Theorem) (conclusion : Theorem)
    (block : ProofSystem.Certificate)
    (selected : DerivationGraph.lookupPremises before.cache roots = some premises)
    (checked : GraphExpansion.BlockChecked policy premises conclusion block)
    (formed : Formed before instances block.1) :
    Registered.replayFrom policy before
        (commands instances (GraphExpansion.expandBlock roots before.cache.size block).1) =
      some (finish before instances (GraphExpansion.expandBlock roots before.cache.size block).1) := by
  obtain ⟨out, replayed, _⟩ := GraphExpansion.expandBlock_checked selected checked
  exact replayProofs_exact policy before instances _ out
    (relocated_formed before instances roots block formed) replayed

theorem relocated_root (policy : AxiomPolicy) [DecidablePred policy]
    (before : Registered.State) (instances : SignatureFormation.InstanceWitnesses)
    (roots : List Nat) (premises : List Theorem) (conclusion : Theorem)
    (block : ProofSystem.Certificate)
    (selected : DerivationGraph.lookupPremises before.cache roots = some premises)
    (checked : GraphExpansion.BlockChecked policy premises conclusion block) :
    (finish before instances (GraphExpansion.expandBlock roots before.cache.size block).1).cache[(GraphExpansion.expandBlock roots before.cache.size block).2]? = some conclusion := by
  obtain ⟨out, replayed, found⟩ := GraphExpansion.expandBlock_checked selected checked
  have same : out =
      (finish before instances (GraphExpansion.expandBlock roots before.cache.size block).1).cache :=
    (DerivationGraph.replayFrom_eq_materialize (ruleWitness policy) replayed).trans
      (materialize_eq_append before.cache _)
  rw [same] at found
  exact found

theorem relocated_preserves_lookup (policy : AxiomPolicy) [DecidablePred policy]
    (before : Registered.State) (instances : SignatureFormation.InstanceWitnesses)
    (roots : List Nat) (premises : List Theorem) (conclusion : Theorem)
    (block : ProofSystem.Certificate)
    (selected : DerivationGraph.lookupPremises before.cache roots = some premises)
    (checked : GraphExpansion.BlockChecked policy premises conclusion block)
    (formed : Formed before instances block.1)
    {index : Nat} {fact : Theorem} (found : before.cache[index]? = some fact) :
    (finish before instances (GraphExpansion.expandBlock roots before.cache.size block).1).cache[index]? =
      some fact :=
  Registered.replayFrom_preserves_lookup policy before _ _
    (relocated_replay policy before instances roots premises conclusion block selected checked formed) found

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.RegisteredProofBlocks
