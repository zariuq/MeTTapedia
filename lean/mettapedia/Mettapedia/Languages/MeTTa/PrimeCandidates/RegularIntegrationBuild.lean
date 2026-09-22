import Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Regular.Normalization
import Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Regular.SubjectReduction
import Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Regular.Bidirectional
import Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Regular.BidirectionalCompleteness
import Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Adapters.RegularPatternElaboration
import Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Regular.PresheafSemantics
import Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Regular.PresheafNormalization
import Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Regular.TypeConversionSemantics
import Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Regular.ContextNormalizationSemantics
import Mettapedia.Languages.MeTTa.PrimeCandidates.FiniteLanguageOperationSignature
import Mettapedia.Languages.MeTTa.PrimeCandidates.InternalDataTransport
import Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageOperationSyntax
import Mettapedia.Languages.MeTTa.PrimeCandidates.InternalAdmission
import Mettapedia.Languages.MeTTa.PrimeCandidates.SelfInstance
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveSimpleCwf
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.FormationSensitivePreservationExamples
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.TransparentRelatorExtension
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLImpredicativeRepresentation
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLDefinitionAdmission
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLImpredicativeProofCompilation
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLDependentProofExecution
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitivePresheafSemantics
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeFormedPresheafControls
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Checking.NativeJudgmentReplay
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Checking.NativeJudgmentReplayTransport
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Checking.NativeJudgmentReplayCoherence
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Checking.NativeJudgmentReplayFormation
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Contextual.NativeCheckedJudgmentPresheaf
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Checking.NativeCheckedContextConversion
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Checking.NativeIntroductionComputationReplay
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Checking.NativePrincipalComputationReplay
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Examples.NativeConvertedIntroductionControls
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Checking.NativeBranchReturnControls
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Examples.NativeDeclaredRootControls
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeContextualComputationCompleteness
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Examples.NativeContextualComputationControls
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Checking.NativeCheckedPathExecution
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Checking.NativeCheckedPathControls
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Conversion.NativeConversionPaths
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Conversion.NativeParallelReceiptSubstitution
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Conversion.NativeParallelReceiptControls
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Conversion.NativeParallelReceiptPaths
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Conversion.NativeParallelReceiptJoinControls
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Conversion.NativeConversionComponentsControls
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Checking.NativeCheckedBinderAlignment
import Mettapedia.Languages.Megalodon.TheoryAdmissionKernel
import Mettapedia.Languages.Megalodon.SourceTypeParameters
import Mettapedia.Languages.Megalodon.TheoryAdmissionSequence
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLNativeProofConsumption

/-!
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

# Formed-core and regular-fragment candidate integration build

This module declares nothing.  It is a focused integration gate that collects
the exact regular normalizer and bidirectional checker (the `TwoSortPiSigmaId`
`Regular*` development), strict Pattern elaboration, internal
language-operation transport, revision-scoped admission, and the level-raised
cumulative-tower candidate self-instance, so that they can be elaborated
together.  It belongs to the candidate integration layer, not to the
foundations of the regular calculus it imports.

The regular checker collected here is a concrete two-sort test instance:
ground `u0`, untyped formation marker `u1`, dependent Π/Σ, identity
formation and reflexivity, without J or a cumulative hierarchy. It is not
the Prime dependent core. Its exact-image relationship
to the staged-reflective presentation is a separate theorem boundary.
The regular source now supplies the shared structural CwF, and its represented
types have an exact source-term/natural-section equivalence with coherent
substitution and a connection to the existing checker. That representation
retains raw syntax rather than quotienting by beta conversion. Its type-map
action is fully faithful on represented types, and the substitution
comparisons satisfy identity, composition, and pairing laws. A separate
normal-form observation uses the existing executable normalizer, identifies
exactly convertible source terms, and commutes with substitution after
renormalization.
Conversion of independently formed source types gives represented family
isomorphisms coherent with substitution, composition, and the normalizer,
without reflecting conversion into raw syntax equality.

Separately, the formation-sensitive cumulative presentation now inhabits the
same structural CwF interface using its own judgments. Its erasure to the
permissive presentation is a strict morphism. The existing STT translation is
a strict morphism into this formed source, and its executable beta-conversion
decision recognizes equality of the actual conversion-valued term fibres on
the simple image. General represented source sections retain exact term code;
their conversion observation commutes with every admitted substitution. The
mixed HOL/wire projection has equal conversion observations and unequal raw
sections, while a polymorphic dependent identity is represented at each level.
These constructions do not extend the two-sort checker to the cumulative
core or normalize arbitrary declaration-specific computation.

Finite transparent declaration packages also have an executable expansion
qualifier. Its successful fixed-point check supplies the existing open-term
conversion equivalence and, with independently typed bodies, full contextual
subject preservation. The nonempty dependent-pair consumers now use the
computed qualification. A self-loop and an ill-typed body separate this check
from termination and body admission respectively.

The cumulative source has its own finite evidence replay: the shared checker
now includes conversion certificates at every recursive premise and a checked
ambient telescope. Soundness and certificate-existence completeness cover the
unchanged formation-sensitive judgment. The native List/identity/relator
instance uses its existing finite conversion checker and actual universe
decisions, and accepted replay supplies represented terms under every admitted
substitution. This is not a total type-inference or proof-search algorithm.
The native inventory includes full fixed-left-endpoint J as the declared
constant `CumulativeTower.Id.eliminate`, with endpoint-and-proof-dependent
motive and reflexivity computation. `NativeIndexedFamilySource` connects
the authored declarations to that signature; the structural `const` and
`appElim` rules check its applications. The fourteen typing-code constructors
are not the inventory of declared language constants.
The same finite certificates now transport executably: native conversion
codes admit coherent simultaneous substitution; typing trees admit coherent
renaming and checked substitution using certificates for the actual argument images.
The existing dependent telescope checker supplies those image obligations.
Checked telescope application reduces to the same substituted subject whose
computed certificate passes complete judgment replay. No proof search or
certificate-existence theorem is used to choose that output certificate.

The complete replay also computes result-type formation. The same
certificate-substitution operation transports bodies across convertible,
independently formed binders. These transformations supply actual arrows of
the checked-context category and commute with its semantic observation;
conversion there and back can retain casts despite erasing to identity.
Pointwise conversion of substitution images computes conversion evidence
under arbitrary further binders. The native introduction-root beta and pair
projection cases now compute accepted result certificates, with second
projection preserving its dependent annotation through an explicit cast.
Principal certificate generation now extracts arbitrary outer cumulative and
conversion wrappers and reconstructs the original tree exactly. The admitted
native executor replaces an introduction/elimination proof beneath those
wrappers and produces both a checked result and a checked directed step.
On accepted sources its success domain is exactly the recognized principal
introduction/elimination shapes, with no additional formation-extraction failure.
Its retained receipt changes while its conversion-class observation is
preserved. Component conversion and binder alignment are computed below.
Converted inner introduction evidence is handled by the computed views and
component alignment below. The selected declared roots and contextual steps
are handled below.

Declaration-spine recovery now computes checked argument certificates from
every accepted declaration-headed application whose instantiated declaration
exposes its Pi spine. It aligns supplied premise types by computed conversion
and preserves the final displayed type. Successful syntactic spine descriptions
commute with arbitrary simultaneous substitution. When the supplied and
declared Pi components are identical, the proved direct case reuses the
argument certificate instead of constructing redundant conversions.
List-nil, identity-reflexivity and relational List-nil contractions consume
these recovered branches. The admission-gated executor retains the selected
root, checks its exact source, computes an accepted target certificate, and
preserves conversion-class observation. Its success domain is exactly those
three roots on admitted matching sources. Kernel controls independently
check the source, every recovered argument, and the actual returned certificate;
outer conversions are retained and changed results, types, relations and
malformed source certificates are rejected.
Execution also commutes with every checked context substitution on its actual
result term and selected root, with equal semantic observations on the two
routes. This does not identify the resulting certificate trees. A non-variable
nil-branch substitution returns the actual substituted beta redex; a variable
certificate for that non-variable image is rejected.

The recursive List-cons and relational-cons contractions now instantiate
independently checked open schemas. A shared recovery operation takes the
actual outer eliminator and inner constructor arguments, preserves their
ordered certificates, and supplies all schema images to the existing checked
simultaneous substitution. NativePayloadSchemaCompilation now computes those
positional descriptors from the open declarations, with an exact acceptance
criterion and one execution theorem for every ambient substitution. Recompiling
positions after a noninjective substitution can change the selected occurrence,
so the compiled positions are retained. No target-typing
premise is supplied by the caller. The resulting all-root executor agrees
exactly with the branch executor on its three cases, and accepts every matching
source admitted by the checker for all five declared roots. It retains the
original displayed type, selected directed root, and semantic observation;
actual result terms and roots commute with checked context substitution.
Kernel controls exercise both recursive schemas, outer result conversions,
and missing-recursion or changed-witness rejections.

NativeContextualComputationReplay extends these same root executors through
all fifteen constructor positions. It computes casts for dependent argument,
pair, projection and identity indices, and transports a body certificate when
its binder's domain changes. Outer cumulative/conversion wrappers are retained.
The head case transports the displayed successor level when equal levels have
different syntactic expressions. NativeContextualComputationCompleteness proves
that every selected step decoding to an admitted source computes an accepted
result at the original displayed type. The public executor's exact domain is
successful step decoding, source matching and complete source admission: its
independent output replay introduces no additional rejection. Execution commutes
with every checked context substitution on actual result terms and selected
steps, with equal semantic observations, without identifying typing trees.
Controls cover every constructor position, nested binders, dependent indices,
equal but differently expressed levels, and rejected missing casts/capture.
NativeCheckedPathExecution extends this executor to supplied finite paths
using Mathlib's free path-category lift. Concatenation gives exactly sequential
certificate computation; semantic observation is preserved and commutes with
checked substitution. The generic Logic.Relation.DecodedPath codec admits
connected step lists and retains every supplied code in order, including
repeats. The public runCodes entry accepts exactly an admitted source plus a
decodable path. Its actual output certificate rechecks at the original type;
its endpoint agrees with term-only trace admission, which does not construct
intermediate typing trees. This separation does not reconstruct certificates
from an erased result or give a complexity bound. Controls include dependent
two-step execution, declared J, disconnected traces and malformed evidence.
Selecting a terminating normalization strategy and full-core normalization
remain open. CeTTa directly implements the shared contracts in C; automatic
translation or implementation-refinement proofs are not required by this gate.

The generic Logic.Relation.PathConfluence construction computes directed-path
and zigzag joins from a supplied one-step diamond operation, retaining both
output paths in Type. StructuralConversionPaths translates accepted finite
conversion codes into Mathlib symmetric paths and re-encodes those paths as
accepted conversion evidence. The native instance retains actual relational
roots and binder positions while explicitly forgetting reflexivity grouping.
Flattening preserves the exact number of selected step occurrences; a native
root step followed by its reverse remains distinct from the empty path.
The native receipt graph now instantiates this generic joining infrastructure.
Authored one-step reduction is not asserted to have the auxiliary parallel
diamond.

NativeParallelReceipt now retains every branch of the existing auxiliary
parallel relation, with checked finite codes for its metadata guards.
Its support is exactly that existing relation. NativeCompletedRootCertificate
replays all five completed root shapes through the original authored checker;
Receipt.toCertificate extends this to every parallel receipt. Renaming and
simultaneous parallel substitution compute on those receipts and their guard
codes. Controls develop relational payloads and branches together, instantiate
a native body with a reducing argument, verify the resulting beta/native
square, and reject capture and changed witnesses. Receipt distinctions can
survive when emitted authored conversions agree: contraction may discard an
argument whose selected development remains in the receipt.

NativeParallelReceiptInversion recovers ordered component receipt data from
rigid spines. NativeParallelReceiptJoin.localJoin computes a common successor
and both continuation receipts for every pair of native parallel developments,
recursing on their shared source syntax and transporting supplied guard codes.
NativeParallelReceiptPaths instantiates the shared quiver-path diamond to join
finite directed paths and symmetric paths, retaining both outputs, proving their
exact lengths, and rechecking their authored replay. Controls execute all five
native root cases, beta/native interaction, projections, binding and a two-step
commuting example; capture and changed relational witnesses are rejected.
NativeConversionReceiptIngress maps every accepted authored step, including
all native roots and congruence positions, into that parallel graph. The map
preserves path length and direction counts. checkedJoin accepts exactly the
original checker's inputs and computes recheckable continuations.
NativeConversionComponents then decomposes the actual joined continuations
of any Pi/Sigma conversion into accepted domain and codomain codes, keeping
the latter under its binder. Controls pass through a native List eliminator,
change both components, and reject capture and a changed constructor.
NativeCheckedBinderAlignment consumes those computed components to transport
a checked dependent body across independently formed binders and body types.
Both function and pair cases recheck, while an altered body and an unformed
destination context are rejected. NativeIntroductionView extracts the original
lambda/pair introduction and composes its actual conversion wrappers.
NativeConvertedIntroductionComputation uses component conversion and checked
substitution to execute arbitrary converted inner introduction evidence.
All three operations are consumed by the principal executor, whose direct
introduction outputs remain unchanged. Controls change both type components
via a List-eliminator detour, retain the dependent second projection's original
annotation, and independently check the actual computed output certificates.
Incorrect conversion, unformed destination evidence, and an altered result
are rejected.

The source-hosting boundary also includes Megalodon's ordered theory admission
kernel. Its axiom rule requires ordinary or prefix-polymorphic proposition
formation, while theorem admission requires formation and a proof in the exact
preceding environment. Checked sequence composition uses the same intermediate
environment for the admitted item and the remaining document. This is syntactic
admission with explicit assumptions, not validity of the full HOTG theory or
automatic compilation of every admitted theorem into a native dependent term.

Importing these components together proves neither joint semantic adequacy
nor correspondence with a CeTTa implementation, and selects no final MeTTa
type theory.

Quantitative scheduling, evidence weights, and cost semantics are deliberately
outside this boundary.
-/
