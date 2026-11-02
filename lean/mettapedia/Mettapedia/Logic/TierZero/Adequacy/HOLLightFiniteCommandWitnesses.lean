import Mettapedia.Logic.TierZero.Adequacy.HOLLightFiniteWitnessLocalChecks

/-!
# Every accepted original command has an exact finite witness observation

Replacing only the certificate provider preserves origin, ordered premise
addresses and every accepted original output. The graph is sampled at the
command's actual input annotations and its finite output theorems, including
all hypotheses and axiom commitments. No equality between arbitrary function
providers is needed, and no proof history is interpreted during checking.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.HOLLightFiniteCommandWitnesses

open Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.OpenTheory.SignatureFormation
open Mettapedia.Languages.HOLLight
open Mettapedia.Languages.HOLLight.DefinitionAdapters
open Mettapedia.Languages.HOLLight.ProofExecution.Registered
open HOLLightFiniteWitnesses HOLLightFiniteWitnessLocalChecks

local instance : DecidableEq Const := SyntaxEncoding.constantCodec.decEq
local instance : DecidableEq Ty := SyntaxEncoding.tyCodec.decEq

def provider : Command → InstanceWitnesses
  | .proof _ certificates | .constant _ _ _ certificates | .typeDefinition _ _ _ certificates => certificates

def withWitnesses : Command → InstanceWitnesses → Command
  | .proof node _, certificates => .proof node certificates
  | .constant origin name body _, certificates => .constant origin name body certificates
  | .typeDefinition origin request index _, certificates => .typeDefinition origin request index certificates

def inputKeys : Command → Finset Key
  | .proof node _ => requestKeys node.witness ∪ theoremKeys node.conclusion
  | .constant _ _ body _ => sourceKeys body
  | .typeDefinition _ request _ _ => typeInputKeys request

def outputKeys (output : Output) : Finset Key := unionKeys theoremKeys output.theorems

theorem origin_preserved (command : Command) (certificates : InstanceWitnesses) :
    (withWitnesses command certificates).origin = command.origin := by cases command <;> rfl

theorem parents_preserved (command : Command) (certificates : InstanceWitnesses) :
    (withWitnesses command certificates).parents = command.parents := by cases command <;> rfl

theorem input_keys_preserved (command : Command) (certificates : InstanceWitnesses) :
    inputKeys (withWitnesses command certificates) = inputKeys command := by cases command <;> rfl

theorem accepted_check_agree (policy : AxiomPolicy) [DecidablePred policy]
    (context : TheoryContext) (cache : Array Theorem) (command : Command) (certificates : InstanceWitnesses)
    (inputsAgree : Agree (inputKeys command) (provider command) certificates)
    {output : Output} (outputsAgree : Agree (outputKeys output) (provider command) certificates)
    (accepted : command.check policy context cache = some output) :
    (withWitnesses command certificates).check policy context cache = some output := by
  cases command with
  | proof node original =>
      cases replayed : node.replay (ruleWitness policy) cache with
      | none => simp [Command.check, replayed] at accepted
      | some result =>
          simp only [Command.check, replayed, Bind.bind, Option.bind] at accepted
          split at accepted
          · rename_i formation
            cases Option.some.inj accepted
            have requestSame := request_check_agree context.signature original certificates node.witness
              (inputsAgree.mono Finset.subset_union_left)
            have theoremSame := theorem_agree context.signature original certificates node.conclusion
              (inputsAgree.mono Finset.subset_union_right)
            have checked : requestFormedB context.signature certificates node.witness = true ∧
                theoremFormedB context.signature certificates node.conclusion = true :=
              ⟨requestSame ▸ formation.1, theoremSame ▸ formation.2⟩
            simp only [withWitnesses, Command.check, replayed, Bind.bind, Option.bind, if_pos checked]
            rfl
          · contradiction
  | constant origin name body original =>
      cases admitted : admitConstantInTheory context original name body with
      | none => simp [Command.check, admitted] at accepted
      | some defined =>
          simp only [Command.check, admitted, Bind.bind, Option.bind] at accepted
          split at accepted
          · rename_i formation
            cases Option.some.inj accepted
            have admissionSame := constant_admission_agree context original certificates name body inputsAgree
            have definedAgain := admissionSame.symm.trans admitted
            have theoremSame := theorem_agree defined.context.signature original certificates defined.output.definitionTheorem
              (outputsAgree.mono (key_member_subset theoremKeys (List.mem_cons_self ..)))
            have checked : theoremFormedB defined.context.signature certificates defined.output.definitionTheorem = true := theoremSame ▸ formation
            simp only [withWitnesses, Command.check, definedAgain, Bind.bind, Option.bind, if_pos checked]
            rfl
          · contradiction
  | typeDefinition origin request index original =>
      cases found : cache[index]? with
      | none => simp [Command.check, found] at accepted
      | some existence =>
          simp only [Command.check, found, Bind.bind, Option.bind] at accepted
          split at accepted
          · rename_i sameExistence
            cases admitted : admitSourceTypeInTheory context original request with
            | none => simp [admitted] at accepted
            | some defined =>
                simp only [admitted] at accepted
                split at accepted
                · rename_i formation
                  cases Option.some.inj accepted
                  have admissionSame := type_admission_agree context original certificates request inputsAgree
                  have definedAgain := admissionSame.symm.trans admitted
                  have firstSame := theorem_agree defined.context.signature original certificates defined.output.abstractionRepresentationTheorem
                    (outputsAgree.mono (key_member_subset theoremKeys (List.mem_cons_self ..)))
                  have secondSame := theorem_agree defined.context.signature original certificates defined.output.representationAbstractionTheorem
                    (outputsAgree.mono (key_member_subset theoremKeys (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
                  have checked : theoremFormedB defined.context.signature certificates defined.output.abstractionRepresentationTheorem = true ∧
                      theoremFormedB defined.context.signature certificates defined.output.representationAbstractionTheorem = true :=
                    ⟨firstSame ▸ formation.1, secondSame ▸ formation.2⟩
                  simp only [withWitnesses, Command.check, found, Bind.bind, Option.bind, if_pos sameExistence,
                    definedAgain, if_pos checked]
                  rfl
                · contradiction
          · contradiction

def sampleCommand (command : Command) (output : Output) : Graph :=
  sample (inputKeys command ∪ outputKeys output) (provider command)

theorem accepted_finite_observation (policy : AxiomPolicy) [DecidablePred policy]
    (context : TheoryContext) (cache : Array Theorem) (command : Command) {output : Output}
    (accepted : command.check policy context cache = some output) :
    (withWitnesses command (witnesses (sampleCommand command output))).check policy context cache = some output := by
  apply accepted_check_agree policy context cache command
  · exact (sample_agrees (inputKeys command ∪ outputKeys output) (provider command)).mono Finset.subset_union_left
  · exact (sample_agrees (inputKeys command ∪ outputKeys output) (provider command)).mono Finset.subset_union_right
  · exact accepted

end Mettapedia.Logic.TierZero.Adequacy.HOLLightFiniteCommandWitnesses
