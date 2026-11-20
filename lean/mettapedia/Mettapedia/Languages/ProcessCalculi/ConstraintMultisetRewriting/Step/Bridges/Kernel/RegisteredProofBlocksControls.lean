import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.RegisteredProofBlocks
import Mettapedia.Languages.HOLLight.EqualityExpansion
import Mettapedia.Languages.HOLLight.SourceProfileModels

/-! Registered block controls with a real preceding type definition,
duplicate external premises and relocated internal references. -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.RegisteredProofBlocks.Controls

open Mettapedia.Logic Mettapedia.Languages.OpenTheory Mettapedia.Languages.HOLLight
open ProofExecution DefinitionAdapters

local instance : DecidablePred emptyAxiomPolicy := fun _ => isFalse id

def fact : Theorem := ContextControls.identityExistence
def instances : SignatureFormation.InstanceWitnesses := Registered.Controls.certificates
def before : Registered.State := Registered.Controls.withDefinedType

def first : Receipt :=
  ⟨fact, .inference (.trans fact fact), [0, 1], ("registered-block", 0)⟩

def second : Receipt :=
  ⟨fact, .inference (.trans fact fact), [2, 0], ("registered-block", 1)⟩

def block : ProofSystem.Certificate := ([first, second], 3)

theorem trans_checked : (RuleRequest.inference (.trans fact fact)).check emptyAxiomPolicy = some fact := by
  change checkTrans fact fact = some fact
  simpa [EqualityExpansion.transResult, fact, ContextControls.identityExistence,
    Theorem.unionResult, Theorem.emptyResult] using
    EqualityExpansion.transResult_checked fact fact DefinitionAdapters.Controls.identityTerm
      DefinitionAdapters.Controls.identityTerm DefinitionAdapters.Controls.identityTerm rfl
      (EqualityExpansion.equality_view _ _ rfl) (EqualityExpansion.equality_view _ _ rfl)

theorem block_checked : GraphExpansion.BlockChecked emptyAxiomPolicy [fact, fact] fact block := by
  have firstReplay : first.replay (ruleWitness emptyAxiomPolicy) #[fact, fact] =
      some #[fact, fact, fact] := by
    apply (ProofSystem.node_replay_iff emptyAxiomPolicy _ _ _).mpr
    exact ⟨rfl, trans_checked, rfl⟩
  have secondReplay : second.replay (ruleWitness emptyAxiomPolicy) #[fact, fact, fact] =
      some #[fact, fact, fact, fact] := by
    apply (ProofSystem.node_replay_iff emptyAxiomPolicy _ _ _).mpr
    exact ⟨rfl, trans_checked, rfl⟩
  exact ⟨#[fact, fact, fact, fact], by
    simp only [block, DerivationGraph.replayFrom, firstReplay, secondReplay,
      bind, Option.bind], rfl⟩

theorem selected : DerivationGraph.lookupPremises before.cache [0, 0] = some [fact, fact] := rfl

theorem formed : Formed before instances block.1 := by
  intro node member
  have shape : node = first ∨ node = second := by simpa [block] using member
  rcases shape with rfl | rfl
  all_goals constructor <;> decide +kernel

def expanded : List Receipt := (GraphExpansion.expandBlock [0, 0] before.cache.size block).1
def after : Registered.State := finish before instances expanded

theorem block_received : Registered.replayFrom emptyAxiomPolicy before (commands instances expanded) =
    some after :=
  relocated_replay emptyAxiomPolicy before instances [0, 0] [fact, fact] fact block selected block_checked formed

theorem relocated_parents : expanded.map (·.parents) = [[0, 0], [3, 0]] := rfl
theorem after_cache : after.cache = before.cache ++ #[fact, fact] := rfl
theorem physical_counts : after.cache.size = 5 ∧ after.receipts.size = 4 := by decide +kernel
theorem root : after.cache[4]? = some fact :=
  relocated_root emptyAxiomPolicy before instances [0, 0] [fact, fact] fact block selected block_checked

def literalCommands : List Registered.Command :=
  [Registered.Controls.existenceCommand, Registered.Controls.typeCommand] ++ commands instances expanded

theorem literal_history : Registered.replayFrom emptyAxiomPolicy
    (Registered.empty ContextControls.coreContext) literalCommands = some after :=
  Registered.replayFrom_append_accepted emptyAxiomPolicy
    Registered.Controls.definition_history_replayed block_received

theorem definition_first_retained : after.cache[1]? =
    some Registered.Controls.definedType.output.abstractionRepresentationTheorem :=
  relocated_preserves_lookup emptyAxiomPolicy before instances [0, 0] [fact, fact] fact block
    selected block_checked formed rfl

theorem definition_second_retained : after.cache[2]? =
    some Registered.Controls.definedType.output.representationAbstractionTheorem :=
  relocated_preserves_lookup emptyAxiomPolicy before instances [0, 0] [fact, fact] fact block
    selected block_checked formed rfl

theorem root_has_no_axioms : fact.axioms = ∅ := rfl

def wrongIndexNodes : List Receipt :=
  (GraphExpansion.expandBlock [before.cache.size, 0] before.cache.size block).1

theorem wrong_index_refused : Registered.replayFrom emptyAxiomPolicy before
    (commands instances wrongIndexNodes) = none := by
  decide +kernel

def forged : Receipt :=
  { first with
    parents := [0, 0]
    conclusion := Registered.Controls.definedType.output.abstractionRepresentationTheorem }

theorem forged_parents_match : DerivationGraph.lookupPremises before.cache forged.parents =
    some forged.witness.premises := rfl

theorem forged_request_checked : forged.witness.check emptyAxiomPolicy = some fact := trans_checked

theorem forged_conclusion_refused : Registered.replayFrom emptyAxiomPolicy before
    (commands instances [forged]) = none := by
  decide +kernel

theorem existence_not_invented : Registered.apply emptyAxiomPolicy
    (Registered.empty ContextControls.coreContext) Registered.Controls.typeCommand = none :=
  Registered.Controls.unproved_existence_refused

theorem formation_not_optional : Registered.replayFrom emptyAxiomPolicy
    (Registered.empty ContextControls.coreContext)
    [Registered.Command.proof Registered.GraphControls.unregisteredNode Registered.GraphControls.instances] = none :=
  Registered.GraphControls.unregistered_reception_refused

theorem unregistered_primitive_passes : DerivationGraph.replayFrom (ruleWitness emptyAxiomPolicy)
    #[] [Registered.GraphControls.unregisteredNode] = some #[Registered.Controls.undeclaredReflexivity] :=
  Registered.GraphControls.unregistered_primitive_replay

namespace SourcePrefix

/-! The first two canonical commands of the numbered source export:
admit T = ((lambda p. p) = (lambda p. p)), then REFL of that identity.
The source constructors below are independent inputs to the actual checks.
No equality with the numbered JSON decoder is asserted. -/

def identitySource : SourceTerm := .abs (.global "p") Ty.bool (.var (.global "p") Ty.bool)
def body : SourceTerm :=
  .app (.app (.const Const.equality (Ty.equality (.function Ty.bool Ty.bool))) identitySource) identitySource

theorem body_agrees_with_source : body = StandardTheoryInterpretation.Source.truthBody := by
  unfold StandardTheoryInterpretation.Source.truthBody
  rfl

def instances : SignatureFormation.InstanceWitnesses :=
  ExportReplay.instanceCertificates StandardTheoryInterpretation.Source.truthResult.context.signature

theorem admission : (admitConstantInTheory SourceProfile.primitiveContext instances (.global "T") body).isSome = true := by
  decide +kernel

def defined : ContextConstantDefinitionResult :=
  (admitConstantInTheory SourceProfile.primitiveContext instances (.global "T") body).get admission

theorem admitted : admitConstantInTheory SourceProfile.primitiveContext instances (.global "T") body =
    some defined := (Option.some_get admission).symm

theorem output_formed : theoremFormedB defined.context.signature instances defined.output.definitionTheorem = true := by
  decide +kernel

def truthCommand : Registered.Command :=
  .constant ("indexed-hol-source-export", 0) (.global "T") body instances

def withTruth : Registered.State :=
  ⟨defined.context, #[defined.output.definitionTheorem],
    #[⟨truthCommand, [defined.output.definitionTheorem]⟩]⟩

theorem truth_checked : truthCommand.check SourceProfileModels.policy SourceProfile.primitiveContext #[] =
    some ⟨defined.context, [defined.output.definitionTheorem]⟩ := by
  simp [truthCommand, Registered.Command.check, admitted, output_formed]

theorem truth_applied : Registered.apply SourceProfileModels.policy
    (Registered.empty SourceProfile.primitiveContext) truthCommand = some withTruth := by
  simp only [Registered.apply, Registered.empty, truth_checked, bind, Option.bind]
  rfl

def identity : CanonicalTerm :=
  ⟨.abs Ty.bool (.bound 0), .function Ty.bool Ty.bool, by simp [DBTerm.inferType]⟩
def reflexivity : Theorem := EqualityExpansion.reflexivity identity
def reflBlock : ProofSystem.Certificate := GraphExpansion.primitiveBlock
  (.inference (.refl identity)) reflexivity ("indexed-hol-source-export", 1)

theorem refl_block_checked : GraphExpansion.BlockChecked SourceProfileModels.policy [] reflexivity reflBlock :=
  GraphExpansion.primitiveBlock_checked (.inference (.refl identity)) reflexivity
    ("indexed-hol-source-export", 1) (EqualityExpansion.reflexivity_checked identity)

theorem refl_formed : Formed withTruth instances reflBlock.1 := by
  intro node member
  simp only [reflBlock, GraphExpansion.primitiveBlock, List.mem_singleton] at member
  subst node
  constructor <;> decide +kernel

def packetCommands : List Registered.Command := [truthCommand] ++
  commands instances (GraphExpansion.expandBlock [] withTruth.cache.size reflBlock).1
def received : Registered.State :=
  finish withTruth instances (GraphExpansion.expandBlock [] withTruth.cache.size reflBlock).1

theorem prefix_replayed : Registered.replayFrom SourceProfileModels.policy
    (Registered.empty SourceProfile.primitiveContext) packetCommands = some received := by
  apply Registered.replayFrom_append_accepted SourceProfileModels.policy
  · simpa [Registered.replayFrom] using truth_applied
  · exact relocated_replay SourceProfileModels.policy withTruth instances [] [] reflexivity reflBlock
      rfl refl_block_checked refl_formed

theorem prefix_root : received.cache[1]? = some reflexivity :=
  relocated_root SourceProfileModels.policy withTruth instances [] [] reflexivity reflBlock rfl refl_block_checked

theorem prefix_sizes : packetCommands.length = 2 ∧ received.cache.size = 2 ∧ received.receipts.size = 2 := by
  decide +kernel

end SourcePrefix

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.RegisteredProofBlocks.Controls
