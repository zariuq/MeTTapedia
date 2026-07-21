import Mettapedia.GSLT.Core.LambdaTheoryCategory
import Mettapedia.GSLT.Core.Web
import Mettapedia.GSLT.Core.ChangeOfBase
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
