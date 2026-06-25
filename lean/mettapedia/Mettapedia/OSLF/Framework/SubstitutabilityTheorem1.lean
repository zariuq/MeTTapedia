import Mettapedia.OSLF.Framework.DistinctionGraph

/-!
# Theorem-1-Style Substitutability Endpoint

This file packages a paper-facing form of OSLF Theorem 1:

- behavioral equivalence side (bisimulation-flavored),
- native-type/logical equivalence side (formula indistinguishability),
- and the equivalence contract as one proposition.

The first nontrivial proved direction is exported here (`forward`), with an
image-finite scoped iff theorem as the first full equivalence instance.
-/

namespace Mettapedia.OSLF.Framework

open Mettapedia.OSLF.Framework.DistinctionGraph
open Mettapedia.OSLF.Framework.KSUnificationSketch

abbrev Pat := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern

/-- Theorem-1 behavioral side: full bisimulation-style equivalence. -/
abbrev theorem1_behaviorEq (R : Pat → Pat → Prop) (I : Mettapedia.OSLF.Formula.AtomSem)
    (p q : Pat) : Prop :=
  FullBisimilar R I p q

/-- Theorem-1 native-type side: formula indistinguishability (`same native types`). -/
abbrev theorem1_sameNativeTypes (R : Pat → Pat → Prop) (I : Mettapedia.OSLF.Formula.AtomSem)
    (p q : Pat) : Prop :=
  indistObs R I p q

/-- Theorem-1-style substitutability equivalence contract (skeleton endpoint). -/
def Theorem1SubstitutabilityEquiv (R : Pat → Pat → Prop)
    (I : Mettapedia.OSLF.Formula.AtomSem) : Prop :=
  ∀ p q, theorem1_behaviorEq R I p q ↔ theorem1_sameNativeTypes R I p q

/-- First nontrivial proved direction of Theorem-1-style substitutability:
full bisimilarity implies same native types (formula indistinguishability). -/
theorem theorem1_substitutability_forward
    {R : Pat → Pat → Prop}
    {I : Mettapedia.OSLF.Formula.AtomSem}
    {p q : Pat} :
    theorem1_behaviorEq R I p q →
      theorem1_sameNativeTypes R I p q :=
  fullBisim_implies_indist

/-- First scoped full equivalence instance for Theorem-1-style substitutability:
under forward/backward image-finiteness, behavioral and native-type sides coincide. -/
theorem theorem1_substitutability_imageFinite
    {R : Pat → Pat → Prop}
    {I : Mettapedia.OSLF.Formula.AtomSem}
    (hImageFinite : ∀ p : Pat, Set.Finite {q : Pat | R p q})
    (hPredFinite : ∀ p : Pat, Set.Finite {q : Pat | R q p}) :
    Theorem1SubstitutabilityEquiv R I := by
  intro p q
  simpa [theorem1_behaviorEq, theorem1_sameNativeTypes] using
    (indist_iff_fullBisim_imageFinite (R := R) (I := I) hImageFinite hPredFinite p q).symm

end Mettapedia.OSLF.Framework
