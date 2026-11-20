import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.RegisteredProofBlocks
import Mettapedia.Languages.HOLLight.SourceProfileModels
import Mettapedia.Languages.HOLLight.ExactFormulaReadback
import Mettapedia.Languages.HOLLight.ReferenceBooleanSemantics

/-!
# One selected source interpretation through registered proof suffixes

The input interpretation is carried through the actual proof commands.
New cache evidence and the reference invariant are retained while its model
stays fixed. A source-profile axiom request uses the existing interpreted
adjoin operation; declaration commands are outside this proof-only suffix.
No equality between independently selected replay frames is required.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.SourceProofSuffix

open Mettapedia.Logic Mettapedia.Languages.OpenTheory Mettapedia.Languages.HOLLight
open ProofExecution DefinitionAdapters SignatureFormation RegisteredReplayModels TypeFamilySemantics ModelInstanceCoherence DefinitionModelFamily
open SourceProfileModels

universe w

theorem apply_proof_model {initial : TheoryContext} {policy : AxiomPolicy} [DecidablePred policy]
    (primitives : Primitives initial) {before after : Registered.State}
    (frame : Frame.{w} initial policy before.context before.cache)
    (node : Receipt) (instances : InstanceWitnesses)
    (accepted : Registered.apply policy before (.proof node instances) = some after)
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    (Frame.apply primitives before after frame (.proof node instances) accepted).model other assignment =
      frame.model other assignment := by
  unfold Frame.apply
  simp only [Frame.model, Frame.transfer_model, Frame.command]
  all_goals rfl

theorem receive_proof_model {before after : Registered.State} (profile : ProfileFrame.{w} before)
    (node : Receipt) (instances : InstanceWitnesses)
    (accepted : @Registered.apply profile.current profile.decision before (.proof node instances) = some after)
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    (profile.receive (.proof node instances) accepted).frame.model other assignment =
      profile.frame.model other assignment := by
  exact @apply_proof_model _ profile.current profile.decision SourceProfileModels.primitives _ _
    profile.frame node instances accepted other assignment

theorem adjoin_model {before : Registered.State} (profile : ProfileFrame.{w} before)
    (sentence : SourceSentence) (member : sentence ∈ sentences)
    (formed : AnnotationsFormed before.context.signature sentence.canonical.term)
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    (profile.adjoin sentence member formed).frame.model other assignment =
      profile.frame.model other assignment := by
  rfl

def advance {before after : Registered.State} (profile : ProfileFrame.{w} before)
    (node : Receipt) (instances : InstanceWitnesses)
    (accepted : Registered.apply SourceProfileModels.policy before (.proof node instances) = some after) :
    ProfileFrame.{w} after := by
  letI := profile.decision
  let command := Registered.Command.proof node instances
  cases witness : node.witness with
  | inference request =>
      apply profile.receive command
      rw [Registered.apply_policy_congr profile.current SourceProfileModels.policy before command]
      · exact accepted
      · intro sequent asked
        simp only [command, Registered.Command.requestedAxiom, witness, RuleRequest.requestedAxiom] at asked
        cases asked
  | «axiom» sequent =>
      have requested : command.requestedAxiom = some sequent := by
        simp only [command, Registered.Command.requestedAxiom, witness, RuleRequest.requestedAxiom]
      have checked := (Registered.apply_check_exists accepted).choose_spec
      have facts := Registered.requested_axiom_formed requested checked
      have allowed : sequent ∈ sentences.map SourceSentence.sequent := facts.1
      let sentence := (List.mem_map.mp allowed).choose
      have member := (List.mem_map.mp allowed).choose_spec.1
      have same := (List.mem_map.mp allowed).choose_spec.2
      have formed : AnnotationsFormed before.context.signature sentence.canonical.term := by
        change AnnotationsFormed before.context.signature sentence.sequent.concl.term
        rw [same]
        exact facts.2
      let next := profile.adjoin sentence member formed
      letI := next.decision
      apply next.receive command
      rw [Registered.apply_policy_congr next.current SourceProfileModels.policy before command]
      · exact accepted
      · intro candidate asked
        have target : candidate = sentence.sequent :=
          (Option.some.inj (asked.symm.trans requested)).trans same.symm
        constructor
        · intro _
          change candidate ∈ sentences.map SourceSentence.sequent
          exact List.mem_map.mpr ⟨sentence, member, target.symm⟩
        · intro _
          exact Or.inr target

theorem advance_proof_model {before after : Registered.State} (profile : ProfileFrame.{w} before)
    (node : Receipt) (instances : InstanceWitnesses)
    (accepted : Registered.apply SourceProfileModels.policy before (.proof node instances) = some after)
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    (advance profile node instances accepted).frame.model other assignment =
      profile.frame.model other assignment := by
  rcases node with ⟨conclusion, witness, parents, origin⟩
  cases witness with
  | inference request =>
      simp only [advance]
      exact receive_proof_model profile _ instances _ other assignment
  | «axiom» sequent =>
      simp only [advance]
      rw [receive_proof_model]
      exact adjoin_model profile _ _ _ other assignment

theorem replay_head {before after : Registered.State} (node : Receipt)
    (instances : InstanceWitnesses) (later : List Receipt)
    (accepted : Registered.replayFrom SourceProfileModels.policy before
      (RegisteredProofBlocks.commands instances (node :: later)) = some after) :
    ∃ middle,
      Registered.apply SourceProfileModels.policy before (.proof node instances) = some middle ∧
      Registered.replayFrom SourceProfileModels.policy middle
        (RegisteredProofBlocks.commands instances later) = some after := by
  cases first : Registered.apply SourceProfileModels.policy before (.proof node instances) with
  | none => simp [RegisteredProofBlocks.commands, Registered.replayFrom, first] at accepted
  | some middle =>
      exact ⟨middle, rfl, by
        simpa only [RegisteredProofBlocks.commands, List.map_cons, Registered.replayFrom,
          first, bind, Option.bind] using accepted⟩

def carry {before after : Registered.State} (profile : ProfileFrame.{w} before)
    (instances : InstanceWitnesses) (nodes : List Receipt)
    (accepted : Registered.replayFrom SourceProfileModels.policy before
      (RegisteredProofBlocks.commands instances nodes) = some after) : ProfileFrame.{w} after :=
  match nodes with
  | [] => (Option.some.inj accepted) ▸ profile
  | node :: later =>
      let facts := (replay_head node instances later accepted).choose_spec
      carry (advance profile node instances facts.1) instances later facts.2
termination_by nodes

theorem carry_model {before after : Registered.State} (profile : ProfileFrame.{w} before)
    (instances : InstanceWitnesses) (nodes : List Receipt)
    (accepted : Registered.replayFrom SourceProfileModels.policy before
      (RegisteredProofBlocks.commands instances nodes) = some after)
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    (carry profile instances nodes accepted).frame.model other assignment = profile.frame.model other assignment := by
  induction nodes generalizing before with
  | nil =>
      have same : before = after := Option.some.inj accepted
      subst after
      rw [carry]
  | cons node later ih =>
      rw [carry]
      exact (ih _ _).trans (advance_proof_model profile node instances _ other assignment)

def retain_read {before after : Registered.State} (instances : InstanceWitnesses) (nodes : List Receipt)
    (accepted : Registered.replayFrom SourceProfileModels.policy before
      (RegisteredProofBlocks.commands instances nodes) = some after)
    {formula : HOL.ClosedFormula Symbol} (read : ExactFormulaReadback.ReadFact before formula) :
    ExactFormulaReadback.ReadFact after formula where
  fact := read.fact
  known := by
    obtain ⟨index, found⟩ := Array.mem_iff_getElem?.mp read.known
    exact Array.mem_of_getElem? (Registered.replayFrom_preserves_lookup SourceProfileModels.policy
      before _ after accepted found)
  closed := read.closed
  translated := read.translated

/-- A newly earned suffix fact holds in the actual chosen prefix model. -/
theorem read_in_prefix_model {before after : Registered.State} (profile : ProfileFrame.{w} before)
    (instances : InstanceWitnesses) (nodes : List Receipt)
    (accepted : Registered.replayFrom SourceProfileModels.policy before
      (RegisteredProofBlocks.commands instances nodes) = some after)
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w})
    (formula : HOL.ClosedFormula Symbol) (read : ExactFormulaReadback.ReadFact after formula) :
    (profile.frame.model other assignment).models formula := by
  rw [← carry_model profile instances nodes accepted other assignment]
  exact ExactFormulaReadback.read_models (carry profile instances nodes accepted).frame other assignment formula read

theorem context_eq {before after : Registered.State} (instances : InstanceWitnesses) (nodes : List Receipt)
    (accepted : Registered.replayFrom SourceProfileModels.policy before
      (RegisteredProofBlocks.commands instances nodes) = some after) :
    after.context = before.context :=
  (Registered.replayProofs_primitive SourceProfileModels.policy before nodes instances accepted).1

theorem old_lookup {before after : Registered.State} (instances : InstanceWitnesses) (nodes : List Receipt)
    (accepted : Registered.replayFrom SourceProfileModels.policy before
      (RegisteredProofBlocks.commands instances nodes) = some after)
    {index : Nat} {fact : Theorem} (found : before.cache[index]? = some fact) :
    after.cache[index]? = some fact :=
  Registered.replayFrom_preserves_lookup SourceProfileModels.policy before _ after accepted found

theorem carry_meanings {before after : Registered.State} (profile : ProfileFrame.{w} before)
    (instances : InstanceWitnesses) (nodes : List Receipt)
    (accepted : Registered.replayFrom SourceProfileModels.policy before
      (RegisteredProofBlocks.commands instances nodes) = some after)
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    ReferenceBooleanSemantics.Meanings ((carry profile instances nodes accepted).frame.model other assignment) :=
  ReferenceBooleanSemantics.meanings_of_invariant _ (carry profile instances nodes accepted).invariant other assignment

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.SourceProofSuffix

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.SourceProofSuffix.carry_model
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.SourceProofSuffix.read_in_prefix_model
