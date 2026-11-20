import Mettapedia.Languages.HOLLight.SourceProfileModels
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.RegisteredProofBlocks

/-!
# Checked constructor quotations for registered source commands

Source annotations, binder-sensitive de Bruijn encodings and regenerated
typing evidence remain separate obligations. These lemmas compose the
existing source check equations; quoting an annotation or a symbol name
does not establish signature formation or a source derivation.

Definition reception uses the actual admitted provenance-bearing result.
Replacing a cache representation requires equality to the exact receiving
cache, retaining the command, declaration context and receipt unchanged.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.PacketQuotation

open Mettapedia.Logic Mettapedia.Languages.OpenTheory Mettapedia.Languages.HOLLight
open ProofExecution DefinitionAdapters SignatureFormation

theorem source_constant (constant : Const) (annotation : Ty) :
    (SourceTerm.const constant annotation).inferType = some annotation := by simp

theorem source_variable (name : Name) (annotation : Ty) :
    (SourceTerm.var name annotation).inferType = some annotation := by simp

theorem source_application (function argument : SourceTerm) (domain codomain : Ty)
    (functionTyped : function.inferType = some (.function domain codomain))
    (argumentTyped : argument.inferType = some domain) :
    (SourceTerm.app function argument).inferType = some codomain := by
  have same : Ty.same domain domain = true := (Ty.same_eq_true_iff _ _).mpr rfl
  simp [functionTyped, argumentTyped, same]

theorem source_abstraction (name : Name) (domain : Ty) (body : SourceTerm) (codomain : Ty)
    (bodyTyped : body.inferType = some codomain) :
    (SourceTerm.abs name domain body).inferType = some (.function domain codomain) := by
  simp [bodyTyped]

theorem encoding_constant (binders : List SourceVar) (constant : Const) (annotation : Ty) :
    (SourceTerm.const constant annotation).toDB binders = .const constant annotation := by simp

theorem encoding_application (binders : List SourceVar) (function argument : SourceTerm)
    (encodedFunction encodedArgument : DBTerm)
    (functionEncoding : function.toDB binders = encodedFunction)
    (argumentEncoding : argument.toDB binders = encodedArgument) :
    (SourceTerm.app function argument).toDB binders = .app encodedFunction encodedArgument := by
  simp only [SourceTerm.toDB, functionEncoding, argumentEncoding]

theorem encoding_abstraction (binders : List SourceVar) (name : Name) (domain : Ty)
    (body : SourceTerm) (encodedBody : DBTerm)
    (bodyEncoding : body.toDB (⟨name, domain⟩ :: binders) = encodedBody) :
    (SourceTerm.abs name domain body).toDB binders = .abs domain encodedBody := by
  simp only [SourceTerm.toDB, bodyEncoding]

theorem canonical_checked (source : SourceTerm) (encoded : DBTerm) (type : Ty)
    (typed : source.inferType = some type) (encoding : source.toDB [] = encoded) :
    encoded.inferType [] = some type := by
  rw [← encoding]
  exact (DBTerm.inferType_toDB [] source).trans typed

theorem canonical_from_source (source : SourceTerm) (encoded : DBTerm) (type : Ty)
    (typed : source.inferType = some type) (encoding : source.toDB [] = encoded) :
    source.check = some (⟨encoded, type, canonical_checked source encoded type typed encoding⟩ : CanonicalTerm) := by
  apply (SourceTerm.check_eq_some_iff source _).mpr
  exact encoding

theorem constant_checked (policy : AxiomPolicy) [DecidablePred policy]
    (context : TheoryContext) (oldInstances : InstanceWitnesses) (name : Name) (body : SourceTerm)
    (result : ContextConstantDefinitionResult) (origin : Origin)
    (admitted : admitConstantInTheory context oldInstances name body = some result)
    (available : (admitConstantInTheory context
      (ExportReplay.instanceCertificates result.context.signature) name body).isSome = true)
    (formed : theoremFormedB result.context.signature
      (ExportReplay.instanceCertificates result.context.signature) result.output.definitionTheorem = true)
    (cache : Array Theorem) :
    (Registered.Command.constant origin name body
      (ExportReplay.instanceCertificates result.context.signature)).check policy context cache =
      some ⟨result.context, [result.output.definitionTheorem]⟩ := by
  obtain ⟨actual, received⟩ := Option.isSome_iff_exists.mp available
  have same := admitConstantInTheory_unique admitted received
  rw [← same] at received
  change (do
    let defined ← admitConstantInTheory context
      (ExportReplay.instanceCertificates result.context.signature) name body
    if theoremFormedB defined.context.signature
      (ExportReplay.instanceCertificates result.context.signature) defined.output.definitionTheorem then
      pure (⟨defined.context, [defined.output.definitionTheorem]⟩ : Registered.Output)
    else none) = _
  rw [received]
  change (if theoremFormedB result.context.signature
      (ExportReplay.instanceCertificates result.context.signature) result.output.definitionTheorem then
    some (⟨result.context, [result.output.definitionTheorem]⟩ : Registered.Output) else none) = _
  rw [if_pos formed]

theorem apply_checked_cache (policy : AxiomPolicy) [DecidablePred policy]
    (before : Registered.State) (command : Registered.Command) (output : Registered.Output)
    (target : Array Theorem)
    (checked : command.check policy before.context before.cache = some output)
    (exactCache : target = before.cache ++ output.theorems.toArray) :
    Registered.apply policy before command =
      some (⟨output.context, target,
        before.receipts.push ⟨command, output.theorems⟩⟩ : Registered.State) := by
  simp only [Registered.apply, checked, bind, Option.bind]
  rw [exactCache]
  rfl

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.PacketQuotation
