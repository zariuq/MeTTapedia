import Mettapedia.Languages.HOLLight.SealedInference
import Mettapedia.Languages.HOLLight.ArgumentNamingMachine
import Mettapedia.Languages.HOLLight.QuantifierArgumentEmission
import Mettapedia.Languages.HOLLight.QuantifierArgumentProgram
import Mettapedia.Languages.HOLLight.MixedDefinitionModelFamily
import Mettapedia.Languages.HOLLight.MixedTypeDefinitionModels
import Mettapedia.Languages.HOLLight.MixedTypeDefinitionExtensions
import Mettapedia.Languages.HOLLight.MixedDefinitionModels
import Mettapedia.Languages.HOLLight.QuantifierEmission
import Mettapedia.Languages.HOLLight.SourceProfile
import Mettapedia.Languages.HOLLight.DefinitionSchemaClosure
import Mettapedia.Languages.HOLLight.DefinitionSchemaInstances
import Mettapedia.Languages.HOLLight.SourceQuantifierEmission
import Mettapedia.Languages.HOLLight.Rules
import Mettapedia.Languages.HOLLight.DefinitionAdapters
import Mettapedia.Languages.HOLLight.ExportReplay
import Mettapedia.Languages.HOLLight.HOLRDeliveries
import Mettapedia.Languages.HOLLight.RuleModulePrimitives
import Mettapedia.Languages.HOLLight.RuleModuleComparisonLaws
import Mettapedia.Languages.HOLLight.RuleModuleInterning
import Mettapedia.Languages.HOLLight.RuleModuleComponents
import Mettapedia.Languages.HOLLight.RuleModuleReader
import Mettapedia.Languages.HOLLight.RuleModuleHandles
import Mettapedia.Languages.HOLLight.RuleModuleFeed
import Mettapedia.Languages.HOLLight.RuleModuleCaches
import Mettapedia.Languages.HOLLight.IncrementalExecution
import Mettapedia.Languages.HOLLight.ModelInterpretation
import Mettapedia.Languages.HOLLight.StandardTheoryInterpretation
import Mettapedia.Languages.HOLLight.ProofSystem
import Mettapedia.Languages.HOLLight.FirstOrder.GraphSimulation
import Mettapedia.Languages.HOLLight.FirstOrder.Validation
import Mettapedia.Languages.HOLLight.FirstOrder.Multifunctor
import Mettapedia.Languages.HOLLight.FirstOrder.PortableKernel
import Mettapedia.Languages.HOLLight.InferenceCompiler
import Mettapedia.Languages.HOLLight.ChronologicalDriver
import Mettapedia.Languages.HOLLight.ChronologicalDriverCorrectness
import Mettapedia.Languages.HOLLight.ChronologicalTaskEncoding
import Mettapedia.Languages.HOLLight.ChronologicalInsertion
import Mettapedia.Languages.HOLLight.EmittedCertificateInsertion
import Mettapedia.Languages.HOLLight.RelocatedCertificateInsertion
import Mettapedia.Languages.HOLLight.SavedRootInsertion
import Mettapedia.Languages.HOLLight.EncodedTableInsertion
import Mettapedia.Languages.HOLLight.ChronologicalBlockCorrespondence
import Mettapedia.Languages.HOLLight.EffectiveEvidenceHosting
import Mettapedia.Languages.HOLLight.EffectiveEvidenceCompilation
import Mettapedia.Languages.HOLLight.EffectiveKernelSearchBridge
import Mettapedia.Languages.HOLLight.CheckingDiscipline
import Mettapedia.Languages.HOLLight.KernelAtlas
import Mettapedia.Languages.HOLLight.ChronologicalTaskExecution
import Mettapedia.Languages.HOLLight.ReturnedRootPrefixExtraction
import Mettapedia.Languages.HOLLight.DynamicModusPonensRelocation
import Mettapedia.Languages.HOLLight.ChronologicalInsertionProgram
import Mettapedia.Languages.HOLLight.EmittedCertificateInsertionProgram
import Mettapedia.Languages.HOLLight.SavedRootInsertionProgram
import Mettapedia.Languages.HOLLight.EncodedTableInsertionProgram
import Mettapedia.Languages.HOLLight.RelocatedCertificateInsertionProgram
import Mettapedia.Languages.HOLLight.InferenceCompilerControls
import Mettapedia.Languages.HOLLight.InferenceCompilerSize
import Mettapedia.Languages.HOLLight.TemplateInstantiationMachine
import Mettapedia.Languages.HOLLight.ArgumentRenderingMachine
import Mettapedia.Languages.HOLLight.AdmittedArgumentRendering
import Mettapedia.Languages.HOLLight.AdmittedArgumentProgram
import Mettapedia.Languages.HOLLight.ArgumentVectorRendering
import Mettapedia.Languages.HOLLight.ArgumentVectorProgram
import Mettapedia.Languages.HOLLight.ArgumentListRendering
import Mettapedia.Languages.HOLLight.ArgumentListProgram
import Mettapedia.Languages.HOLLight.RuleArgumentRendering
import Mettapedia.Languages.HOLLight.RuleArgumentProgram
import Mettapedia.Languages.HOLLight.RuleArgumentRetentionProgram
import Mettapedia.Languages.HOLLight.MM0Meaning
import Mettapedia.Languages.HOLLight.DefinitionHistoryModels
import Mettapedia.Languages.HOLLight.SourceTypeDefinitionTransport
import Mettapedia.Languages.HOLLight.ModelAssignmentSupport
import Mettapedia.Languages.HOLLight.ModelInstanceCoherence
import Mettapedia.Languages.HOLLight.ConstantHistoryInstanceCoherence
import Mettapedia.Languages.HOLLight.UniformTypeDefinitionFamily
import Mettapedia.Languages.HOLLight.UniformTypeDefinitionModels
import Mettapedia.Languages.HOLLight.UniformTypeDefinitionSupport
import Mettapedia.Languages.HOLLight.ConstantHistoryExpandedTypes
import Mettapedia.Languages.HOLLight.UniformTypeDefinitionInstances
import Mettapedia.Languages.HOLLight.UniformTypeDefinitionExtensions
import Mettapedia.Languages.HOLLight.MixedDefinitionHistory
import Mettapedia.Languages.HOLLight.DefinitionSchemaSubstitution
import Mettapedia.Languages.HOLLight.DefinitionHistorySchemas
/-!
# HOL Light: kernel, theories, replay and inference-presentation hosting

The pinned source kernel retains its ten inference operations and actual
substitution and beta-admission conventions. Axiom policies describe separate
object theories; the kernel's existing graph checker retains chronological
sharing and rejects forward references.

`FirstOrder.Validation` admits the kernel's first-order rendering for arbitrary
finite axiom lists. `PrimitiveTransport` connects the primitive checker to the
shared equational kernel without adding eta. `InferenceCompiler` generates a
finite schematic HOL theory from an admitted constructor-and-metavariable rule
presentation. Its concrete shared-certificate compiler emits actual AXIOM,
SPEC and MP expansions, retaining chronological lemma roots and proving the
generated graph is accepted by the original primitive checker. Physical node
growth is linear for each fixed finite source calculus. `InferenceCompilerSize`
proves a polynomial bound on the complete typed payload, copied theorem data,
UTF-8 names, binary parent references, origins and selected root, measured
against the actual finite-alphabet source encoding. The original independent
target checker accepts encoded claims exactly when the source derives them.
The serialized interface retains the complete original graph through the
lossless `ProofDataEncoding` codec, with polynomial physical output length.
Its `Serialization` stage executes receipt-list assembly and final binary-root
packing in the original format. `SharedReferenceExecution` executes full binary
root lookup and chronological table append; `InferenceCompilerSize` joins their
clocks to the checked builder's stored-root bounds. `InferenceRuleExpansion.Emission` also executes full original AXIOM
receipt generation with variable-size provenance and independently proves
original kernel replay. Whole-translator operational time remains a separate
proof obligation.

`TemplateInstantiationMachine` realizes original multivariable scoped
substitution for each fixed authored term by finite control and actual
encoded-argument copying. `ArgumentRenderingMachine` realizes opaque argument
rendering, nullary constructors, binary arity metadata and complete constructor
types, charging physical child occurrences for type growth. Recursive
constructor rendering and the whole chronological driver remain separate
operational joins.

`Logic.HOL.Embedding.InferenceRules` and `InferenceRuleInstances` supply the
independent finite-theory preservation and reflection laws. The source's
canonical argument values may contain binders; this is distinct from allowing
binders in the source rule schemas.

`FirstOrder.GraphSimulation` gives the reverse translation to MM0 with retained
saved proofs and polynomial certificate-size bounds. Its declared translation
clock is distinct from the execution-backed realizations formalized in
`GSLT.LanguageDef.ProofSystemExecution`.
-/
