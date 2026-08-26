import Mettapedia.GSLT.LanguageDef.Extension
import Mettapedia.GSLT.LanguageDef.InferenceExtension
import Mettapedia.GSLT.LanguageDef.ValidatedInferenceExtension
import Mettapedia.GSLT.LanguageDef.ExtensionComposition
import Mettapedia.GSLT.LanguageDef.ExtensionGluing
import Mettapedia.GSLT.LanguageDef.InferenceNewJudgmentConservativity
import Mettapedia.GSLT.LanguageDef.ExtendedLanguageDef
import Mettapedia.GSLT.LanguageDef.TotalGSLT
import Mettapedia.GSLT.LanguageDef.CalculusLanguageDef
import Mettapedia.GSLT.LanguageDef.GradedLanguageDef
import Mettapedia.GSLT.LanguageDef.CalculusAsLanguage
import Mettapedia.GSLT.LanguageDef.CalculusExtension
import Mettapedia.GSLT.LanguageDef.CertificateGSLT
import Mettapedia.GSLT.LanguageDef.RuleMachineCompilation
import Mettapedia.GSLT.LanguageDef.CompiledPlanWireFormat
import Mettapedia.GSLT.LanguageDef.CompiledPlanAdmission
import Mettapedia.GSLT.LanguageDef.CompiledPlanLowering
import Mettapedia.GSLT.LanguageDef.CompiledPlanOptimizationCertificate
import Mettapedia.GSLT.LanguageDef.InferenceCompiledPlanLowering
import Mettapedia.GSLT.LanguageDef.FiniteVariableFrameCompilation
import Mettapedia.GSLT.LanguageDef.FiniteRuleIndexCompilation
import Mettapedia.GSLT.LanguageDef.ExactRuleSelectorCompilation
import Mettapedia.GSLT.LanguageDef.ChronologicalArticleCompilation
import Mettapedia.GSLT.LanguageDef.ExactFrameProofCompilation
import Mettapedia.GSLT.LanguageDef.PreparedEquationCompilation
import Mettapedia.GSLT.LanguageDef.FiniteSupportBitVecCompilation
import Mettapedia.GSLT.LanguageDef.FiniteApartnessMatrixCompilation
import Mettapedia.GSLT.LanguageDef.FiniteSupportSummaryCacheCompilation
import Mettapedia.GSLT.LanguageDef.InferenceRuleIndexCompilation
import Mettapedia.GSLT.LanguageDef.GuardedRuleMaterialization
import Mettapedia.GSLT.LanguageDef.RigidHeadPrefilter
import Mettapedia.GSLT.LanguageDef.RigidCoordinateIndexCompilation
import Mettapedia.GSLT.LanguageDef.FixedHeadBucketCompilation
import Mettapedia.GSLT.LanguageDef.FlatVariableHeadCompilation
import Mettapedia.GSLT.LanguageDef.GroundLinearHeadCompilation
import Mettapedia.GSLT.LanguageDef.GroundDenseHeadCompilation
import Mettapedia.GSLT.LanguageDef.ConstructorGuidedUnificationCompilation
import Mettapedia.GSLT.LanguageDef.FiniteGroundFactIndexCompilation
import Mettapedia.GSLT.LanguageDef.GroundSubtermCacheCompilation
import Mettapedia.GSLT.LanguageDef.WorklistRegionCompilation
import Mettapedia.GSLT.LanguageDef.ReusableSlotBufferCompilation
import Mettapedia.GSLT.LanguageDef.EpochStampedSlotCompilation
import Mettapedia.GSLT.LanguageDef.AuthoritativeSlotTrailCompilation
import Mettapedia.GSLT.LanguageDef.ScopedAuthoritativeSlotCompilation
import Mettapedia.GSLT.LanguageDef.AuthoritativeMAMActivationProtocol
import Mettapedia.GSLT.LanguageDef.PreparedIndexedValueTableCompilation
import Mettapedia.GSLT.LanguageDef.MonotoneUniqueIndexCompilation
import Mettapedia.GSLT.LanguageDef.CanonicalValueIdQueryCompilation
import Mettapedia.GSLT.LanguageDef.DemandSynchronizedIndexCompilation
import Mettapedia.GSLT.LanguageDef.CheckedBindingCoordinateCompilation
import Mettapedia.GSLT.LanguageDef.LiteralHoleRunCompilation
import Mettapedia.GSLT.LanguageDef.LiteralHeadSeparationCompilation
import Mettapedia.GSLT.LanguageDef.TwoPhaseFrameCompilation
import Mettapedia.GSLT.LanguageDef.OptimizedFirstOrderFramePipeline
import Mettapedia.GSLT.LanguageDef.TwoPhaseFrameMachinePhysicalRefinement
import Mettapedia.GSLT.LanguageDef.IndexedCompressedProgramPlanCompilation
import Mettapedia.GSLT.LanguageDef.CompiledPlanOptimizationPipeline
import Mettapedia.GSLT.LanguageDef.CompiledPlanOpenActivationViewCompilation
import Mettapedia.GSLT.LanguageDef.LogicExtension
import Mettapedia.GSLT.LanguageDef.OracleExtension
import Mettapedia.GSLT.LanguageDef.ReflectionExtension
import Mettapedia.GSLT.LanguageDef.RuntimeProfileExtension
import Mettapedia.GSLT.LanguageDef.PresentationSensitiveTransformation

/-!
# Compositional language definitions

This is the canonical entry point for the five-field language-definition and
extension architecture.

An object language remains exactly `name`, `types`, `terms`, `equations`, and
`rewrites`.  Additional authored structures are dependent fibres over that
base.  Their authoring languages are GSLTs, their elaborators respect the
source equations and rewrites, and erasure recovers the exact base.

Primary human authoring has two direct forms.  `CalculusLanguageDef` is the
flat specialization with judgments and rules in the same record as the five
object-language fields.  `ExtendedLanguageDef layer`, together with
`extendedLanguageDef!`, handles any finite product of independently authored
layers without adding a universal optional field for every future extension.
The older nested `Presentation` remains a derived checker and transport type;
validators, generated projections, and focused checker fixtures may use it,
but it is not the primary authoring authority.

The reusable hierarchy is law-based:

1. `GSLT.Embedding` preserves and reflects `(E,R)`; `Embedding.Observed`
   additionally names the answer, trace, cost, or reflection observation that
   is preserved.
2. `CoGSLTLayer` is an exact dependent elaboration over an unchanged base.  It
   does not by itself claim that authored terms can be concatenated.
3. `GSLT.Compositional` supplies empty and concatenation inside `(T,E,R)`, and
   `GSLT.CompositionalElaboration` requires elaboration to preserve that
   concatenation.  The payload partial monoid is derived from this law rather
   than carried independently.
4. `GSLT.ContextualAdmission` separates total authored composition from an
   application-specific acceptance predicate and overlap law.  Compatible
   siblings glue; staged increments are admitted relative to an accumulated
   payload.
5. `GSLT.Realization` carries compilation together with an explicitly named
   conservation certificate.  Stages compose, independent realizations form
   products, and certified backends may be selected per source without changing
   their common observation.

`RuleMachineCompilation` supplies a nontrivial realization instance: it compiles
authored inference rules to register-machine blocks and proves that executing a
compiled block agrees with applying the authored rule.  Binary encoding and
search scheduling remain later realization stages rather than hidden parts of
that theorem.

`CompiledPlanWireFormat` closes the first physical part of that later stage for
the generic finite-Horn machine.  It specifies the exact `CGP1` byte carrier,
proves encode/decode round trips for every bounded NUL-free packet, and keeps
local record-shape admission distinct from the stronger node-forest and
rule-forest validator.  `CompiledPlanAdmission` supplies that stronger,
vocabulary-independent boundary in Lean: it reconstructs typed terms and
requires unique ownership of every node, child slot, and body slot together
with dense variables, postorder children, bounded depth, and unique rule names.
`CompiledPlanLowering` emits that physical forest from a typed finite-Horn rule
inventory, routes every result back through the independent admission pass, and
compares the reconstruction with the typed source meaning before emitting
bytes.  Nullary and binary canaries are byte-identical across Lean, the
stage-zero generator, and the generic C loader.

`InferenceCompiledPlanLowering` connects that physical seam to admitted
inference presentations.  It recognizes the local depth-zero, application-only
finite-Horn fragment, rejects binders and side conditions without assigning
them a fallback meaning, and proves that every emitted packet reconstructs the
recognized source presentation's typed meaning.

`FiniteVariableFrameCompilation` supplies a second composable realization.  A
decidable finite-support check resolves authored variable keys to bounded slots,
and the dense frame transformer is proved to have exactly the source frame's
observation.  The lowering depends only on a duplicate-free generated inventory
and complete support coverage, so it is reusable across rule and proof guests.

`FiniteRuleIndexCompilation` groups any fully classified rule inventory by a
generated dispatch key and proves exact equality with full-scan candidate
selection.  `FiniteSupportBitVecCompilation` lowers any admitted finite support
to an inventory-width bit vector, with exact membership, union, and disjointness
theorems.  Both reject unclassified source data rather than introducing a
fallback interpretation.

`GuardedRuleMaterialization` admits bodies through a local decidable
recognizer and proves that a rule machine may delay total body materialization
until after head matching.  Its cost refinement is non-increasing for every
candidate and strictly improving for rejected heads with positive body cost.
`RigidHeadPrefilter` proves that constructor-level incompatibility rules out
every common ground instance, licensing rejection before general unification,
freshening, or body materialization.
`RigidCoordinateIndexCompilation` turns one locally useful rigid head
coordinate into an ordered discrimination index.  Its bounded refinement
charges source-order fuel for skipped rules while avoiding their physical
inspection, and preserves both completed and exhausted observations.
`FixedHeadBucketCompilation` then consumes the relation-and-arity certificate
from the outer index, moves that discriminator out of the hot representation,
and proves that residual argument-only comparison is exact.
`GroundDenseHeadCompilation` combines the dynamic ground-input certificate
with the generated finite-variable inventory.  It resolves every variable to
a bounded slot and proves direct recursive matching equal to the independent
association-list matcher, including repeated-variable equality and rejection.
`FiniteGroundFactIndexCompilation` applies the same rigid-root theorem to
catalog-authorized finite ground providers.  It preserves exact row order and
multiplicity, while an open query falls back to the complete source bag.
`GroundSubtermCacheCompilation` structurally recognizes maximal
variable-free subtrees in an immutable generated plan and proves that their
cached values are independent of every execution environment.  The compiled
realization rebuilds only variable-bearing structure, with an exact semantic
and non-increasing constructor-cost refinement.
`ConstructorGuidedUnificationCompilation` recognizes equal rigid constructors
at the dynamic equation boundary and emits the ordered child equations that
the proved Martelli--Montanari machine would schedule next.  Its realization
preserves the complete returned substitution while eliminating the temporary
rule-side constructor node; variables and disagreements fail recognition.
`WorklistRegionCompilation` recognizes the value-owned transition boundary:
successors and persistent observations cross it as complete values, so a
consumed state cannot escape into the remaining frontier.  It proves that
reclaiming one state region at dequeue preserves every bounded residual queue
and observation, while retain-everything adds one dead state per step.
`ReusableSlotBufferCompilation` applies the same non-escape discipline inside
a transition.  A finite dense slot buffer is reset between transactions and
retains its physical capacity, while the published ordered snapshots remain
exactly those of fresh-per-transaction allocation.
`EpochStampedSlotCompilation` then removes width-proportional clearing from
that reusable buffer.  A finite scan certifies that the next epoch is absent;
stamped slots present exactly the same fresh logical view, with a mandatory
full stamp clear at physical epoch wraparound.
`PreparedIndexedValueTableCompilation` recognizes an immutable finite value
segment immediately before an indexed instruction stream.  It proves exact
ordered lookup after lowering the segment to a contiguous table, including
duplicate occurrences and failed bounds checks, and rejects ambiguous,
mutable, or escaping shapes.
`MonotoneUniqueIndexCompilation` handles the complementary associative case.
It recognizes a 32-bit table with only fresh-insert and lookup effects, checks
key uniqueness through the shared hash-indexed validator, and proves exact
association-list-to-hash-index lookup together with entry-count preservation.
Overwrite, deletion, duplicate keys, and unsupported carriers fail admission.
`LiteralHoleRunCompilation` recognizes flat persistent symbolic templates with
a call-local execution region.  It groups maximal adjacent literals into a
compact run program, proves its independent instantiation and fused matcher
exact, and proves non-increasing dispatch and descriptor-plus-pool word costs.
Nested, scoped, and escaping representations fail admission.
`LiteralHeadSeparationCompilation` then performs a value-local second pass.  A
leading literal is carried out of band while a leading hole or empty template
retains the preceding representation exactly; both dynamic tag dispatches and
physical words are non-increasing.  `TwoPhaseFrameCompilation` independently
proves the complete binder-collection then fused-match schedule, including
interleaved source frames whose stack positions must remain unchanged.
`OptimizedFirstOrderFramePipeline` composes these results into one certified
partial stack transformer and lifts both cost refinements across every
matching hypothesis and the conclusion.

`GSLT.Interaction` is the complementary construction for components that are
not independent: the component theories remain faithfully embedded while all
cross-rewrites are explicit authored data.  `GSLT.InteractionElaboration`
requires those crossings to preserve the common interpretation.  Together
they prevent a product construction from silently claiming that communicating
layers are disjoint.

Proof calculi use the complete path:

1. atomic judgment and rule declarations form a GSLT;
2. the free document construction supplies empty documents, concatenation,
   equations, and contextual rewrites;
3. elaboration produces a `ProofCalculus` in the fibre over one base;
4. admission validates that calculus against the unchanged base; and
5. proof search is a derived GSLT whose reachability agrees with derivability.

`ExtensionComposition` derives the payload partial monoid from authored
concatenation and its elaboration law, then combines independently authored
layers.  `ExtensionGluing` instantiates contextual admission for proof calculi.
Admission is deliberately separate: authored documents always compose, while
admitted payloads compose only when their overlap conditions hold.  Pairwise
gluing is not called descent: covers and coherent higher overlaps have not been
chosen here.

The strict `CertificateGSLT` nucleus is included here.  Stronger certificate-GSLT
interpretation, cyclic, and ultrainfinite modules have their own imports so
that this foundational entry point does not silently enlarge its authority.
-/
