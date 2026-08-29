import Mettapedia.GSLT.LanguageDef.CertificateGSLTClone
import Mettapedia.GSLT.LanguageDef.CertificateGSLTDAGSubstitution
import Mettapedia.GSLT.LanguageDef.CertificateGSLTTraceSchemaBoundary
import Mettapedia.GSLT.LanguageDef.CertificateGSLTStepTraceLanguage
import Mettapedia.GSLT.LanguageDef.CertificateGSLTStepAdequacyGeneral
import Mettapedia.GSLT.LanguageDef.CertificateGSLTWireFormat
import Mettapedia.GSLT.LanguageDef.CertificateGSLTArticleIdentity
import Mettapedia.GSLT.LanguageDef.CertificateGSLTConversionElimination
import Mettapedia.GSLT.LanguageDef.CertificateGSLTConversionTier
import Mettapedia.GSLT.LanguageDef.CertificateGSLTRelationalInterpretation
import Mettapedia.GSLT.LanguageDef.CertificateGSLTAmbient
import Mettapedia.GSLT.LanguageDef.CertificateGSLTCyclic
import Mettapedia.GSLT.LanguageDef.CertificateGSLTNonFactorizationInstances
import Mettapedia.GSLT.Core.Ultrainfinite
import Mettapedia.GSLT.Core.UltrainfiniteTransport
import Mettapedia.GSLT.LanguageDef.CertificateGSLTUltrainfiniteInstances
import Mettapedia.GSLT.LanguageDef.CertificateGSLTSearchAuthority
import Mettapedia.GSLT.LanguageDef.CertificateGSLTJudgmentAuthority
import Mettapedia.GSLT.LanguageDef.CertificateGSLTFiniteTraceAuthority
import Mettapedia.GSLT.LanguageDef.CertificateGSLTRecurrentTraceAuthority
import Mettapedia.GSLT.LanguageDef.CertificateGSLTRuleJoin
import Mettapedia.GSLT.LanguageDef.CertificateGSLTFeatureLinkage
import Mettapedia.GSLT.LanguageDef.CertificateGSLTConstructibleDuality

/-!
# Certificate-GSLT framework

This module is the canonical import for the proof-theoretic GSLT nucleus.  It
collects validated semantic definitions, strict refinement, open
derivations and their substitution calculus, derivation-valued
interpretations, set-valued models, indexed categories of derivations and
models, executable open-proof checking, chronological DAG evidence, exact DAG
transport under refinement, the multisorted-clone structure carried by each
definition, and sharing-preserving substitution of checked chronological
artifacts with its exact expansion and cost laws.  It also exposes the
proof-carrying direct-trace generator, the collection-rest admission
boundary, general two-sided trace adequacy over the gated adequate
fragment of direct-trace languages, the versioned chronological-article
wire semantics with canonical encoding and exact checker correspondence.  The
ambient-first GSLT layer above this nucleus distinguishes filtered growth from
perspective projection and retains routes, two-cells, and bisimulation
witnesses as data; CertificateGSLT supplies derivation/article, conversion-path, and
finite-support instances.  Carried bisimulations transport through locally
step-covered embeddings, and certified search pruning is stated against an
authority's semantic meaning rather than a producer score.  Authority-indexed finite certificates for
infinitary recurrence are one application, with an explicit
local-legality/global-progress boundary and checked native lowering.  The
same authority interface covers arbitrary semantic judgments and generates
finite reachability checking freely from any sound local OSLF edge checker;
open query, decomposition, substitution, and capability obligations remain
explicit premises until a separately sound discharger closes them.  For
infinite executions, the same checked edges combine with a separate Büchi
progress measure, yielding genuine GSLT execution plus recurrence rather than
mistaking a cyclic finite prefix for liveness.  The
framework also includes fixed-core binary coproducts of strict rule theories
and paired certificate verdicts with both Belnap orders.  Optional affine feature
linkage is kept as a separate interface algebra: it does not restrict the
general certificate-GSLT category.

The ordinary interpretation category preserves the shared ground-judgment
representation.  The proof-relevant relational layer may instead select a
related target judgment, retains intermediate judgments under composition,
and supplies only the relation-fiber associator; no completed bicategory or
higher completion is claimed.  The OSLF adequacy fixture and executable
canaries remain separate imports so this canonical framework module does not
pull instance-specific operational semantics into every consumer.
-/
