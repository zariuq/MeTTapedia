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
