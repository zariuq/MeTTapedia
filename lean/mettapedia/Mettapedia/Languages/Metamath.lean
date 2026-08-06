import Mettapedia.Languages.Metamath.MMLean4Bridge
import Mettapedia.Languages.Metamath.GroundedSemantics
import Mettapedia.Languages.Metamath.LanguageDefDSL
import Mettapedia.Languages.Metamath.BridgeConformance
import Mettapedia.Languages.Metamath.Fixtures
import Mettapedia.Languages.Metamath.CommentConformance
import Mettapedia.Languages.Metamath.NTTDiagnostics
import Mettapedia.Languages.Metamath.InferenceGeneratedProvesExecution
import Mettapedia.Languages.Metamath.InferenceActiveHypothesisReflection
import Mettapedia.Languages.Metamath.InferenceAssertionRawApplicationShape
import Mettapedia.Languages.Metamath.InferenceAssertionRawCanonicalization
import Mettapedia.Languages.Metamath.InferenceAssertionLeadingProvesReflection
import Mettapedia.Languages.Metamath.InferenceAssertionSideReflection
import Mettapedia.Languages.Metamath.InferenceAssertionRootReflection
import Mettapedia.Languages.Metamath.InferenceGeneratedProvesReflection
import Mettapedia.Languages.Metamath.InferenceProjectionLookupCompleteness
import Mettapedia.Languages.Metamath.InferenceOperationalSpecStepSoundness
import Mettapedia.Languages.Metamath.InferenceOperationalSpecStepInversion
import Mettapedia.Languages.Metamath.InferenceOperationalExprReification
import Mettapedia.Languages.Metamath.InferenceOperationalSubstitutionReification
import Mettapedia.Languages.Metamath.InferenceOperationalProjectedImage
import Mettapedia.Languages.Metamath.InferenceNormalTraceReflection
import Mettapedia.Languages.Metamath.InferenceNormalByteLedger
import Mettapedia.Languages.Metamath.InferenceNormalByteReflection
import Mettapedia.Languages.Metamath.InferenceNormalProvabilitySoundness
import Mettapedia.Languages.Metamath.InferenceSourceAdmission
import Mettapedia.Languages.Metamath.SourceInferenceDeclarativeAdequacy
import Mettapedia.Languages.Metamath.SourceGSLTOperations
import Mettapedia.Languages.Metamath.SourceGSLTState
import Mettapedia.Languages.Metamath.SourceGSLTNormalTheorem
import Mettapedia.Languages.Metamath.SourceGSLTCompressedTheorem
import Mettapedia.Languages.Metamath.SourceGSLTCompressedMMLean4
import Mettapedia.Languages.Metamath.SourceGSLTCompressedExecutionMMLean4
import Mettapedia.Languages.Metamath.SourceGSLTCompressedParserMMLean4
import Mettapedia.Languages.Metamath.SourceGSLTRawByteLexical
import Mettapedia.Languages.Metamath.InferenceSupportedProvableBoundary
import Mettapedia.Languages.Metamath.InferenceSemanticFiniteSupport
import Mettapedia.Languages.Metamath.SourceGSLTSpecGrounding
import Mettapedia.Languages.Metamath.InferenceDummyAllocation
import Mettapedia.Languages.Metamath.InferenceSourceDummyRealization
import Mettapedia.Languages.Metamath.SourceGSLTStatementPlan
import Mettapedia.Languages.Metamath.SourceGSLTIncludeDAG
import Mettapedia.Languages.Metamath.SourceGSLTRawSourceComposition
import Mettapedia.Languages.Metamath.SourceGSLTLifecycleComposition
import Mettapedia.Languages.Metamath.SourceGSLTRuntimeStateAgreement
import Mettapedia.Languages.Metamath.SourceGSLTCompressedParserComposition
import Mettapedia.Languages.Metamath.SourceGSLTCompressedReflection
import Mettapedia.Languages.Metamath.SourceGSLTDerivationCorrespondence
import Mettapedia.Languages.Metamath.SourceGSLTLexicalClosure
import Mettapedia.Languages.Metamath.SourceGSLTRuntimeCoEvolution
import Mettapedia.Languages.Metamath.SourceGSLTParallelAcceptance
import Mettapedia.Languages.Metamath.SourceGSLTReaderTraceBinding
import Mettapedia.Languages.Metamath.SourceGSLTRuntimeProofTransport
import Mettapedia.Languages.Metamath.SourceGSLTRuntimeCompressedTransport
import Mettapedia.Languages.Metamath.SourceGSLTParserPrefixBisimulation
import Mettapedia.Languages.Metamath.SourceGSLTParserStatementTransitions
import Mettapedia.Languages.Metamath.SourceGSLTParserStatementOutcomes

/-!
# Metamath Bridge Surface

Positive example:
- this umbrella exposes the verified `mm-lean4` bridge layer used for rebuilding
  Metamath semantics in `mettapedia`
- it exposes source-pinned recursive native-proof execution and exhaustive raw
  root classification for successfully projected presentations, including
  exact reflection of active-hypothesis roots and the exact raw assertion-root
  normal form; explicit body-decoding evidence canonically reconstructs the
  corresponding Metamath hypothesis instances, substitution, premises, and
  conclusion, while a proof-relevant leading-child bridge retains each
  recursively reflected tree and its exact original raw artifact; the final
  `ApplySubst` child decodes the result while preserving every original side
  proof artifact, and these inputs reconstruct the exact canonical assertion
  tree with whole-root raw-erasure equality
- mutual structural reflection now constructs those leading-child witnesses
  for every arbitrary projected `Proves` derivation, yielding an exact decoded
  Metamath formula, source-pinned tree, and whole-proof raw-erasure equality
- successful prefix projection is extensionally complete for live assertion
  lookups: every assertion object in that supplied database has an exact
  projected view with the same label, formula, frame, and embedded label
- projected active hypotheses construct their exact singleton upstream
  `Metamath.Spec.ProofValidFrom` step; a proof-relevant generated assertion
  node does so when every actual formula respects the caller frame, and an
  exact runtime stack window plus the recursive stack invariant derives that
  condition while making the same node imply the exact live `stepNormal`
  transition; mandatory actuals retain authored order and are reversed exactly
  once for the top-first operational stack
- the upstream singleton relation itself is inverted exactly: hypothesis steps
  are characterized by caller-frame membership and their forced pushed value,
  while assertion steps expose the exact lookup, DV, typing, authored mandatory
  vector, one stack reversal, substituted result, and unchanged older suffix
- over an exact projected database image, every singleton hypothesis step has
  an existential retained source hypothesis and generated leaf, while every
  singleton step at a retained assertion label has a canonical generated node
  with exact frame-relative actuals, result, and authored finite substitution;
  for a fixed older suffix, existence of that canonical assertion node is
  equivalent to the exact upstream singleton step
- relative to supplied active variable names, every operational expression has
  a canonical frame-respecting tagged representative; erasing that
  representative returns the exact expression, and reification after erasure
  returns every already frame-respecting tagged formula exactly
- a total operational substitution now has a canonical authored-order finite
  image over projected floating hypotheses; totalizing that image with the
  original substitution as fallback returns the original function on every
  variable, while operational `applySubst` and `dvOK` construct the exact
  finite side semantics under their explicit classification, coverage,
  and uniqueness conditions
- proof-relevant normal-stack certificates retain the exact generated forest,
  submitted label order, complete runtime state, and original premise trees;
  on an empty stack, the real `stepNormal` fold reaches exactly the complete
  state obtained by pushing one formula when and only when those labels belong
  to a generated tree for that formula
- under a successful projection, matching validated presentation, and
  constant-headed target decoding, an accepted exact normal parser trace
  reflects through the same pre-insertion database to a generated tree and
  native `Proves` derivation with the exact submitted postfix labels, while
  retaining target freshness, the exact final insertion, and absence of target
  self-reference
- a proof-relevant normal token ledger retains ordinary data for the exact
  trimmed target frame, authored tokens, intermediate proof states, and fixed
  pre-insertion anchor; successful live proof-token observations safely rebase
  by database equality, structural erasure yields the exact parser trace, and
  native reflection additionally retains the live frame-trimming equation
- independently of source-trace provenance, inhabitation of the generated
  native `Proves` type executes an exact reflected normal-label fold and implies
  upstream `Metamath.Spec.Provable` in the exact operational image of the same
  runtime database and its ambient frame
- a validated source prefix now owns its operational assertion database,
  caller frame, and proof-occurrence trees directly; those trees are equivalent
  in both directions to source-derived operational provability and to the
  derivation-locally supported declarative semantics, with frame scope,
  declaration separation, floating uniqueness, and DV well-formedness all
  derived from source validation; existential exact-label acceptance by the
  verified `stepNormal` fold is equivalent to that same declarative relation
- the supported/active-frame semantic boundary is calibrated by a strongly
  well-formed counterexample: unrestricted declarative `var` is strictly
  stronger at a fixed frame; adjoining a genuinely fresh optional floating
  hypothesis preserves frame and DV well-formedness and monotonically
  transports every existing supported derivation
- every unrestricted semantic derivation whose conclusion is based in the
  active frame now constructs a finite, ordered semantic frame extension and
  an exact supported derivation of the original conclusion; this characterizes
  finite-extension closure without pretending the generated dummy names were
  already declared in a fixed source prefix
- canonical source admission takes exact bytes and an optional target rather
  than a caller-supplied rule table; database requests project the accepted
  reader database, theorem requests retain a target-absent proof-ingress
  boundary, and successful admission exposes exactly the presentation
  generated from that selected database
- global object-namespace agreement separately retains labels of hypotheses
  that have left the active frame; source theorem insertion therefore proves
  freshness for the live runtime database, the real `finishProof`/`DB.insert`
  branch succeeds, and the post-insertion runtime namespace agrees exactly
  with the extended source state
- the streaming statement plan is compiled fail-closed from the authored
  source productions; include expansion preserves file/offset provenance,
  accepted segmentation recovers the exact input span stream, and declaration
  folding carries every theorem occurrence into an exact normal or compressed
  lifecycle discharge rather than treating declaration success as proof
  success
- one shared runtime-prefix projector now separates raw optional `$d` storage
  from the active proof-facing frame; the two views are proved semantically
  equivalent for legal substitutions, while source/runtime agreement also
  records permanent object names, raw frame contents, and scope-stack order
- exact reader-call traces now reconstruct statement-local normal and
  compressed theorem outcomes at the real parser boundary.  Verified proofs
  produce source proof occurrences and the next agreed prefix; explicitly
  unknown normal or compressed proofs advance that same prefix without
  producing a verified theorem judgment

Negative example:
- this umbrella does not expose the legacy file-lowering/source-proof
  simulation and refined-trace claim class
- the whole byte-parser loop does not yet construct a complete theorem-event
  ledger or prove event completeness.  Statement-local normal and compressed
  traces now authenticate their actual reader transitions and proof outcomes,
  but those results are not yet threaded through the complete statement-prefix
  induction or lifted through include expansion and EOF
- include-aware admission currently exposes database projection only, and the
  large-input proof-ingress traversal is checked against the reader's complete
  logical database snapshot rather than related by a general chunking theorem
- canonical projected-image equivalence is local to the exact operational
  database/frame image and a known retained assertion label; it does not relate
  the arbitrary older operational-stack suffix to a runtime-stack prefix or
  manufacture recursive proofs of the leading `Proves` premises
- canonical reification does not recover an original malformed symbol tag,
  an erased source hypothesis label, or a prior finite representation distinct
  from the canonical authored one
- reverse formula substitution explicitly requires surviving source constants
  not to be caller-active names; the generic theorem does not silently derive
  that caller/callee classification boundary from unrelated local premises
- unrestricted declarative `Provable.var` admits semantic variables without a
  caller-frame witness; exact reflection therefore targets the supported
  active-frame relation.  Fixed-frame conservativity is formally refuted even
  under strong database/frame/DV well-formedness; the unrestricted relation is
  instead reconciled as finite semantic frame-extension closure
- proof-site monotonicity under optional `$f` extension is proved, and accepted
  optional `$f` and `$d` transitions leave the assertion's mandatory source
  projection exactly unchanged.  Every unrestricted declarative derivation
  now has finite typed support; fresh dummy variables and labels are
  constructed, admitted through the real source `$v`/`$f` gates, and yield a
  supported derivation over the accepted successor whenever the required
  typecodes are declared
- these remaining source-spec, parser, and compressed-proof boundaries prevent
  a claim of whole-source adequacy
-/
