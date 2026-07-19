import Mettapedia.OSLF.Framework.TypeSynthesis
import Mettapedia.OSLF.Framework.KSUnificationSketch

/-!
# Bounded OSLF Image-Finiteness

Finite-branching lemmas for the explicitly bounded contextual compiler, plus
a direct HM-converse wrapper for that relation.

The unbounded least contextual relation is not image-finite for an arbitrary
`LanguageDef`: a recursive rule can repeatedly wrap the result of its own
congruence premise.  Recovering unbounded image-finiteness therefore requires
a separate guarded-context theorem for the particular language; it is not a
property of the shared `Pattern` representation.
-/

namespace Mettapedia.OSLF.Framework.ImageFinite

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Formula
open Mettapedia.OSLF.Framework.KSUnificationSketch

/-- At fixed contextual depth, successors are exactly members of one finite
compiler result list. -/
theorem imageFinite_langReducesAtUsing
    (relEnv : RelationEnv) (lang : LanguageDef) (contextFuel : Nat)
    (p : Pattern) :
    Set.Finite {q : Pattern |
      langReducesAtUsing relEnv lang contextFuel p q} := by
  apply Set.Finite.subset
    (List.finite_toSet
      (rewriteAt (engineBasePremises relEnv) lang contextFuel p))
  intro q step
  exact (mem_rewriteAt_iff_langReducesAtUsing
    relEnv lang contextFuel p q).2 step

/-- HM converse for the explicitly bounded contextual relation. -/
theorem hm_converse_langReducesAtUsing
    (relEnv : RelationEnv) (lang : LanguageDef) (contextFuel : Nat)
    (I : AtomSem)
    {p q : Pattern}
    (hobs : OSLFObsEq
      (langReducesAtUsing relEnv lang contextFuel) I p q) :
    Bisimilar (langReducesAtUsing relEnv lang contextFuel) p q := by
  exact
    hm_converse_schema
      (R := langReducesAtUsing relEnv lang contextFuel)
      (I := I)
      (hImageFinite := imageFinite_langReducesAtUsing
        relEnv lang contextFuel)
      hobs

end Mettapedia.OSLF.Framework.ImageFinite
