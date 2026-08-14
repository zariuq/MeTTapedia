import Mettapedia.GSLT.Core.LambdaTheoryCategory
import Mettapedia.GSLT.Core.BranchingTemporal
import Mettapedia.GSLT.Core.Web
import Mettapedia.GSLT.Core.ChangeOfBase
import Mettapedia.GSLT.Core.Composition
import Mettapedia.GSLT.Core.GSLTConstructions
import Mettapedia.GSLT.Core.CertifiedPlanning
import Mettapedia.GSLT.Core.ClosureCriteria
import Mettapedia.GSLT.Core.InteractionEvent
import Mettapedia.GSLT.Core.InteractionComposition
import Mettapedia.GSLT.Core.Ultrainfinite
import Mettapedia.GSLT.Core.UltrainfiniteTransport
import Mettapedia.GSLT.Core.IndexedOperational
import Mettapedia.GSLT.Core.IndexedOperationalCanary
import Mettapedia.GSLT.Core.WeightedMuScheduler
import Mettapedia.GSLT.Core.GradedSelectionIrreducibility
import Mettapedia.GSLT.Dynamics.QueryRevision
import Mettapedia.GSLT.Dynamics.InteractionEventValuation
import Mettapedia.GSLT.Dynamics.ProofRelevantNeed
import Mettapedia.GSLT.Dynamics.ProofRelevantNeedProfile
import Mettapedia.GSLT.Dynamics.ProofRelevantNeedDiagram
import Mettapedia.GSLT.Dynamics.ProofRelevantNeedSharing
import Mettapedia.GSLT.Dynamics.ProofRelevantNeedValuation
import Mettapedia.GSLT.Dynamics.ProofRelevantNeedOwnership
import Mettapedia.GSLT.Dynamics.ProofRelevantNeedOwnershipValuation
import Mettapedia.GSLT.Dynamics.ProofRelevantNeedNIK
import Mettapedia.GSLT.Dynamics.IndexedQueryRevision
import Mettapedia.GSLT.Dynamics.IndexedQueryRevisionCanary
import Mettapedia.GSLT.GraphTheory.Basic
import Mettapedia.GSLT.GraphTheory.BohmTree
import Mettapedia.GSLT.GraphTheory.WeakProduct
import Mettapedia.GSLT.GraphTheory.Substitution
import Mettapedia.GSLT.GraphTheory.ParallelReduction
import Mettapedia.GSLT.Topos.Yoneda
import Mettapedia.GSLT.Topos.SubobjectClassifier
import Mettapedia.GSLT.Topos.PredicateFibration
import Mettapedia.GSLT.Parsing.CompilerCorrespondence
import Mettapedia.GSLT.Parsing.GuardCorrespondence
import Mettapedia.GSLT.Parsing.HornCertificate
import Mettapedia.GSLT.Parsing.HornStream
import Mettapedia.GSLT.Parsing.HornSpecialization
import Mettapedia.GSLT.Parsing.HornCategoryTable
import Mettapedia.GSLT.Parsing.HornRootUniverse
import Mettapedia.GSLT.Parsing.HornChildDiscovery
import Mettapedia.GSLT.Parsing.HornReachableClosure
import Mettapedia.GSLT.Parsing.HornProgramChildren
import Mettapedia.GSLT.Parsing.HornSemanticChildren
import Mettapedia.GSLT.Parsing.HornSemanticAdequacy
import Mettapedia.GSLT.Parsing.HornSideAdmission
import Mettapedia.GSLT.Parsing.PackedForest
import Mettapedia.GSLT.Parsing.DynamicEnvironment
import Mettapedia.GSLT.Parsing.BoundedScheduler
import Mettapedia.GSLT.Parsing.FiniteHornSaturation
import Mettapedia.GSLT.Parsing.GroundedChart
import Mettapedia.GSLT.Parsing.BackendCorrespondence
import Mettapedia.GSLT.Parsing.HornPlan
import Mettapedia.GSLT.Parsing.HornUnification
import Mettapedia.GSLT.Parsing.HornHeadEnumeration
import Mettapedia.GSLT.Parsing.HornSpecializationHead
import Mettapedia.GSLT.Parsing.HornSpecializationBody
import Mettapedia.GSLT.Parsing.HornGuardedSpecialization
import Mettapedia.GSLT.Parsing.HornSemanticEnumeration
import Mettapedia.GSLT.Parsing.HornRequestDiscovery
import Mettapedia.GSLT.Parsing.HornSemanticPlan
import Mettapedia.GSLT.LanguageDef
import Mettapedia.GSLT.LanguageDef.KernelAuthority
import Mettapedia.GSLT.LanguageDef.CheckerAuthorityFamily
import Mettapedia.GSLT.LanguageDef.CompletenessSpectrum
import Mettapedia.GSLT.LanguageDef.CompletenessSpectrumSAT
import Mettapedia.GSLT.LanguageDef.SemanticProofGSLTCategory
import Mettapedia.GSLT.LanguageDef.NIKGSLT
import Mettapedia.GSLT.LanguageDef.NIKIndexedOperational
import Mettapedia.GSLT.LanguageDef.NIKMetalogic
import Mettapedia.GSLT.LanguageDef.DescentInterface
import Mettapedia.GSLT.LanguageDef.GSLTIL
import Mettapedia.GSLT.LanguageDef.GSLTILSyntax
import Mettapedia.GSLT.LanguageDef.GSLTILCanary
import Mettapedia.GSLT.LanguageDef.NIKDefaultProfile
import Mettapedia.GSLT.LanguageDef.NIKPolarizedAuthority
import Mettapedia.GSLT.LanguageDef.NIKCertifiedCompilation
import Mettapedia.GSLT.LanguageDef.NIKDefaultCertifiedCompilation
import Mettapedia.GSLT.LanguageDef.NIKCompilationAuthority
import Mettapedia.GSLT.LanguageDef.NIKStagedPipeline
import Mettapedia.GSLT.LanguageDef.InteractionEventAuthority
import Mettapedia.GSLT.LanguageDef.ProofGSLTCheckerCapabilities
import Mettapedia.GSLT.LanguageDef.ProofGSLTMuCalculusBoundary
import Mettapedia.GSLT.LanguageDef.ProofGSLTParityAuthority
import Mettapedia.GSLT.LanguageDef.ProofGSLTInferenceControl
import Mettapedia.GSLT.LanguageDef.OSLFCheckerCapabilities
import Mettapedia.GSLT.LanguageDef.TwoNTTCoherence
import Mettapedia.GSLT.LanguageDef.ReflectiveStructuralCategory
import Mettapedia.GSLT.LanguageDef.ReflectiveWellSorted
import Mettapedia.GSLT.LanguageDef.ReflectiveWellSortedChecker

/-!
# Graph-Structured Lambda Theories (GSLT)

This module formalizes the GSLT framework from Bucciarelli & Salibra's
"Graph Lambda Theories" (2008) and related work on lambda calculus semantics.

## Structure

* `Core/` - Basic infrastructure (lambda theories, webs, change of base)
* `GraphTheory/` - Graph models, Böhm trees, weak products
* `Topos/` - Presheaf topos construction (Yoneda, subobject classifier)

## Main Results

* Lambda theories form a category with CCCs
* Graph models provide semantics for lambda calculus
* Böhm theory B is the maximal sensible graph theory (Theorem 45)
* Presheaf categories have subobject classifiers

## References

- Bucciarelli & Salibra, "Graph Lambda Theories" (2008)
- Barendregt, "The Lambda Calculus", Chapters 8-10
- Mac Lane & Moerdijk, "Sheaves in Geometry and Logic"
-/
