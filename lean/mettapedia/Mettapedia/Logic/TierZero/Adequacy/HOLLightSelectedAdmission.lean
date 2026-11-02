import Mettapedia.Languages.HOLLight.ProofExecution
import Mettapedia.Logic.DerivationGraph.SelectedPremises

/-!
# Exact-context HOL declaration admission from actual selected proof addresses

The original local command checker retains all ten inference operations,
authorized axioms, constant definitions, and both type-definition outputs.
Only its actual selected cache addresses supply proof authority. Context
inclusion, all theorem hypotheses, axiom dependencies, and the type-definition
existence premise remain those of the independent original source judgment.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.HOLLightSelectedAdmission

open Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight
open Mettapedia.Languages.HOLLight.DefinitionAdapters
open Mettapedia.Languages.HOLLight.ProofExecution
open Mettapedia.Languages.HOLLight.ProofExecution.Registered
open Mettapedia.Logic

theorem check_sound_selected (policy : AxiomPolicy) [DecidablePred policy]
    (context : TheoryContext) (cache : Array Theorem) (command : Command)
    (earlier : ∀ index ∈ command.parents, ∀ fact,
      cache[index]? = some fact → TheoryDerives policy context fact)
    {result : Output} (accepted : command.check policy context cache = some result) :
    context.signature.Includes result.context.signature ∧
      ∀ fact ∈ result.theorems, TheoryDerives policy result.context fact := by
  cases command with
  | proof node witnesses =>
      simp only [Command.check] at accepted
      cases replayed : node.replay (ruleWitness policy) cache with
      | none => simp [replayed] at accepted
      | some next =>
          simp only [replayed] at accepted
          split at accepted
          · rename_i formation
            cases Option.some.inj accepted
            obtain ⟨premises, found, checked, _⟩ :=
              (node.replay_eq_some_iff (ruleWitness policy) cache next).mp replayed
            have sourceCheck : node.witness.isInstance policy premises node.conclusion = true := checked
            obtain ⟨samePremises, sourceStep⟩ :=
              (RuleRequest.isInstance_eq_true_iff policy _ _ _).mp sourceCheck
            have outputFormed := theoremFormedB_sound context.signature witnesses formation.2
            have proof : TheoryDerives policy context node.conclusion := by
              cases source : node.witness with
              | inference request =>
                  rw [source] at samePremises sourceStep formation
                  refine .inference sourceStep
                    (InferenceFormation.check_sound _ _ _ formation.1) ?_ outputFormed
                  intro premise member
                  obtain ⟨index, selected, lookup⟩ :=
                    DerivationGraph.lookupPremises_selected cache found premise (samePremises ▸ member)
                  exact earlier index selected premise lookup
              | «axiom» sequent =>
                  rw [source] at sourceStep
                  exact .axiom sourceStep.1 sourceStep.2.1 sourceStep.2.2 outputFormed
            exact ⟨.refl _, fun fact member => by simpa using (List.mem_singleton.mp member) ▸ proof⟩
          · contradiction
  | constant origin name body witnesses =>
      have emptyChecked : (Command.constant origin name body witnesses).check policy context #[] = some result := by
        simpa only [Command.check] using accepted
      exact Command.check_sound policy context #[] (by simp) emptyChecked
  | typeDefinition origin request index witnesses =>
      simp only [Command.check] at accepted
      cases found : cache[index]? with
      | none => simp [found] at accepted
      | some existence =>
          rw [found] at accepted
          change (if existence.structuralSame request.existence then do
            let defined ← admitSourceTypeInTheory context witnesses request
            if theoremFormedB defined.context.signature witnesses
                defined.output.abstractionRepresentationTheorem = true ∧
                theoremFormedB defined.context.signature witnesses
                  defined.output.representationAbstractionTheorem = true then
              pure (⟨defined.context, [defined.output.abstractionRepresentationTheorem,
                defined.output.representationAbstractionTheorem]⟩ : Output)
            else none
          else none) = some result at accepted
          split at accepted
          · rename_i sameExistence
            have actual : existence = request.existence :=
              (Theorem.structuralSame_eq_true_iff _ _).mp sameExistence
            have existenceProof := earlier index (by simp [Command.parents]) request.existence (found.trans (congrArg some actual))
            cases admitted : admitSourceTypeInTheory context witnesses request with
            | none => simp [admitted] at accepted
            | some defined =>
                rw [admitted] at accepted
                change (if theoremFormedB defined.context.signature witnesses
                    defined.output.abstractionRepresentationTheorem = true ∧
                    theoremFormedB defined.context.signature witnesses
                      defined.output.representationAbstractionTheorem = true then
                  some (⟨defined.context, [defined.output.abstractionRepresentationTheorem,
                    defined.output.representationAbstractionTheorem]⟩ : Output)
                else none) = some result at accepted
                split at accepted
                · rename_i formation
                  cases Option.some.inj accepted
                  refine ⟨(admitSourceTypeInTheory_result admitted).1, ?_⟩
                  intro fact member
                  rcases List.mem_cons.mp member with rfl | member
                  · exact .typeAbstractionDefinition admitted existenceProof
                      (theoremFormedB_sound _ _ formation.1)
                  · have equal := List.mem_singleton.mp member
                    subst fact
                    exact .typeRepresentationDefinition admitted existenceProof
                      (theoremFormedB_sound _ _ formation.2)
                · contradiction
          · contradiction

end Mettapedia.Logic.TierZero.Adequacy.HOLLightSelectedAdmission
