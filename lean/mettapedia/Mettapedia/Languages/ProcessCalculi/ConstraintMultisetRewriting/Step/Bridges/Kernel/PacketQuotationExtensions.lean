import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.PacketQuotation

/-!
# Policy and two-output declaration evidence for packet quotation

Object-theory axioms retain their actual policy and dependency tags. Type
definitions retain a cache-selected existence theorem and both ordered
source outputs. A replay from an empty registered state must establish the
earlier derivation of that cached theorem; isolated cache membership alone
is not such a history.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.PacketQuotationExtensions

open Mettapedia.Logic Mettapedia.Languages.OpenTheory Mettapedia.Languages.HOLLight
open ProofExecution DefinitionAdapters SignatureFormation

theorem axiom_request_checked (policy : AxiomPolicy) [DecidablePred policy]
    (sequent : Sequent) (empty : sequent.hyp = ∅) (allowed : policy sequent)
    (bool : sequent.IsBool) :
    (RuleRequest.axiom sequent).check policy = some (Theorem.axiomResult sequent bool) := by
  apply (RuleRequest.check_eq_some_iff policy _ _).mpr
  exact ⟨empty, allowed, bool, rfl, rfl, rfl⟩

theorem type_definition_checked (policy : AxiomPolicy) [DecidablePred policy]
    (before : Registered.State) (oldInstances : InstanceWitnesses)
    (request : TypeOperatorDefinitionRequest) (result : SourceTypeDefinitionResult)
    (index : Nat) (origin : Origin)
    (admitted : admitSourceTypeInTheory before.context oldInstances request = some result)
    (available : (admitSourceTypeInTheory before.context
      (ExportReplay.instanceCertificates result.context.signature) request).isSome = true)
    (found : before.cache[index]? = some request.existence)
    (formed : theoremFormedB result.context.signature
        (ExportReplay.instanceCertificates result.context.signature)
        result.output.abstractionRepresentationTheorem = true ∧
      theoremFormedB result.context.signature
        (ExportReplay.instanceCertificates result.context.signature)
        result.output.representationAbstractionTheorem = true) :
    (Registered.Command.typeDefinition origin request index
      (ExportReplay.instanceCertificates result.context.signature)).check policy before.context before.cache =
      some ⟨result.context, [result.output.abstractionRepresentationTheorem,
        result.output.representationAbstractionTheorem]⟩ := by
  obtain ⟨actual, received⟩ := Option.isSome_iff_exists.mp available
  have same := admitSourceTypeInTheory_unique before.context oldInstances
    (ExportReplay.instanceCertificates result.context.signature) request result actual admitted received
  rw [← same] at received
  have self : request.existence.structuralSame request.existence = true :=
    (Theorem.structuralSame_eq_true_iff _ _).mpr rfl
  simp only [Registered.Command.check, found, bind, Option.bind, self, if_true, received]
  change (if theoremFormedB result.context.signature
      (ExportReplay.instanceCertificates result.context.signature)
      result.output.abstractionRepresentationTheorem = true ∧
    theoremFormedB result.context.signature
      (ExportReplay.instanceCertificates result.context.signature)
      result.output.representationAbstractionTheorem = true then
    some (⟨result.context, [result.output.abstractionRepresentationTheorem,
      result.output.representationAbstractionTheorem]⟩ : Registered.Output) else none) = _
  rw [if_pos formed]

theorem type_definition_apply (policy : AxiomPolicy) [DecidablePred policy]
    (before : Registered.State) (oldInstances : InstanceWitnesses)
    (request : TypeOperatorDefinitionRequest) (result : SourceTypeDefinitionResult)
    (index : Nat) (origin : Origin) (target : Array Theorem)
    (admitted : admitSourceTypeInTheory before.context oldInstances request = some result)
    (available : (admitSourceTypeInTheory before.context
      (ExportReplay.instanceCertificates result.context.signature) request).isSome = true)
    (found : before.cache[index]? = some request.existence)
    (formed : theoremFormedB result.context.signature
        (ExportReplay.instanceCertificates result.context.signature)
        result.output.abstractionRepresentationTheorem = true ∧
      theoremFormedB result.context.signature
        (ExportReplay.instanceCertificates result.context.signature)
        result.output.representationAbstractionTheorem = true)
    (extension : target = before.cache ++ #[result.output.abstractionRepresentationTheorem,
      result.output.representationAbstractionTheorem]) :
    let command := Registered.Command.typeDefinition origin request index
      (ExportReplay.instanceCertificates result.context.signature)
    Registered.apply policy before command = some
      (⟨result.context, target, before.receipts.push
        ⟨command, [result.output.abstractionRepresentationTheorem,
          result.output.representationAbstractionTheorem]⟩⟩ : Registered.State) := by
  exact PacketQuotation.apply_checked_cache policy before _ _ target
    (type_definition_checked policy before oldInstances request result index origin
      admitted available found formed) extension

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.PacketQuotationExtensions
