import Mettapedia.GSLT.LanguageDef.ProofGSLTClone
import Mettapedia.GSLT.LanguageDef.ProofGSLTDAGSubstitution
import Mettapedia.GSLT.LanguageDef.ProofGSLTStepPresentability
import Mettapedia.GSLT.LanguageDef.ProofGSLTStepPresentation
import Mettapedia.GSLT.LanguageDef.ProofGSLTStepAdequacyGeneral
import Mettapedia.GSLT.LanguageDef.ProofGSLTWireFormat
import Mettapedia.GSLT.LanguageDef.ProofGSLTArticleIdentity
import Mettapedia.GSLT.LanguageDef.ProofGSLTConversionElimination
import Mettapedia.GSLT.LanguageDef.ProofGSLTConversionTier
import Mettapedia.GSLT.LanguageDef.ProofGSLTRelationalInterpretation
import Mettapedia.GSLT.LanguageDef.ProofGSLTAmbient
import Mettapedia.GSLT.LanguageDef.ProofGSLTCyclic
import Mettapedia.GSLT.LanguageDef.ProofGSLTNonFactorizationInstances
import Mettapedia.GSLT.Core.Ultrainfinite
import Mettapedia.GSLT.Core.UltrainfiniteTransport
import Mettapedia.GSLT.LanguageDef.ProofGSLTUltrainfiniteInstances
import Mettapedia.GSLT.LanguageDef.ProofGSLTSearchAuthority
import Mettapedia.GSLT.LanguageDef.ProofGSLTRuleJoin
import Mettapedia.GSLT.LanguageDef.ProofGSLTFeatureLinkage
import Mettapedia.GSLT.LanguageDef.ProofGSLTConstructibleDuality

/-!
# Proof-GSLT framework

This module is the canonical import for the proof-theoretic GSLT nucleus.  It
collects validated semantic presentations, strict refinement, open
derivations and their substitution calculus, derivation-valued
interpretations, set-valued models, indexed categories of derivations and
models, executable open-proof checking, chronological DAG evidence, exact DAG
transport under refinement, the multisorted-clone structure carried by each
presentation, and sharing-preserving substitution of checked chronological
artifacts with its exact expansion and cost laws.  It also exposes the
proof-carrying direct-trace generator, the collection-rest admission
boundary, general two-sided trace adequacy over the gated adequate
fragment of direct-trace languages, the versioned chronological-article
wire semantics with canonical encoding and exact checker correspondence.  The
ambient-first GSLT layer above this nucleus distinguishes filtered growth from
perspective projection and retains routes, two-cells, and bisimulation
witnesses as data; ProofGSLT supplies derivation/article, conversion-path, and
finite-support instances.  Carried bisimulations transport through locally
step-covered embeddings, and certified search pruning is stated against an
authority's semantic meaning rather than a producer score.  Authority-indexed finite certificates for
infinitary recurrence are one application, with an explicit
local-legality/global-progress boundary and checked native lowering.  The
framework also includes fixed-core binary coproducts of strict rule theories
and paired certificate verdicts with both Belnap orders.  Optional affine feature
linkage is kept as a separate interface algebra: it does not restrict the
general proof-GSLT category.

The ordinary interpretation category preserves the shared ground-judgment
representation.  The proof-relevant relational layer may instead select a
related target judgment, retains intermediate judgments under composition,
and supplies only the relation-fiber associator; no completed bicategory or
higher completion is claimed.  The OSLF adequacy fixture and executable
canaries remain separate imports so this canonical framework module does not
pull instance-specific operational semantics into every consumer.
-/
