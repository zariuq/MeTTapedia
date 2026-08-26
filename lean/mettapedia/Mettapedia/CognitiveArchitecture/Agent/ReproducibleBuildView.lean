import Mettapedia.CognitiveArchitecture.Agent.OpenEndedContext
import Mettapedia.GSLT.Core.ReproducibleBuild

/-!
# Reproducible builds as sufficient agent views

The relational reproducible-build core is dependency-minimal and therefore
does not import cognitive architecture.  This bridge identifies its executable
reproducer with the existing open-ended-context refinement order.

For the state space of proof-relevant build occurrences, a declared input view
refines an artifact observation exactly when an executable reproducer computes
that observation from the declaration.  Fibrewise declaration sufficiency is
the weaker proposition obtained by forgetting the executable map.  The
distinction matters outside the realized declaration image.
-/

set_option autoImplicit false

namespace Mettapedia.CognitiveArchitecture.Agent.ReproducibleBuildView

open Mettapedia.CognitiveArchitecture.Agent.OpenEndedContext
open Mettapedia.GSLT.Core
open Mettapedia.GSLT.Core.ReproducibleBuild

universe u uDeclared uObserved

variable {Source Artifact : Type u}
  {build : RelationalBuild Source Artifact}
  {view : InputView.{u, uDeclared} Source}
  {observation : ArtifactObservation.{u, uObserved} Artifact}

/-- Open-ended-context refinement is definitionally the same executable
factorization used by the general non-factorization core. -/
theorem refines_iff_factors :
    Refines
        (declaredOccurrence build view)
        (observedOccurrence build observation) <->
      NonFactorization.Factors
        (declaredOccurrence build view)
        (observedOccurrence build observation) :=
  Iff.rfl

/-- An executable build reproducer exists exactly when the declared input view
refines the observed artifact view. -/
theorem nonempty_reproducer_iff_refines :
    Nonempty (Reproducer build view observation) <->
      Refines
        (declaredOccurrence build view)
        (observedOccurrence build observation) := by
  rw [Reproducer.nonempty_iff_factors]
  exact refines_iff_factors.symm

/-- Every executable reproducer supplies the corresponding agent-view
refinement witness. -/
theorem reproducer_refines
    (reproducer : Reproducer build view observation) :
    Refines
      (declaredOccurrence build view)
      (observedOccurrence build observation) :=
  refines_iff_factors.mpr reproducer.toFactors

/-- Executable refinement entails fibrewise declaration sufficiency.  No
surjectivity or default observation is required in this direction. -/
theorem declarationSufficient_of_refines
    (refines : Refines
      (declaredOccurrence build view)
      (observedOccurrence build observation)) :
    DeclarationSufficient build view observation :=
  refines.factorsThrough

/-- The executable bridge retains the same strict implication already exposed
by the core: refinement gives sufficiency, while the reverse requires a way to
totalize the reproducer outside the realized declaration image. -/
theorem reproducer_declarationSufficient_via_refines
    (reproducer : Reproducer build view observation) :
    DeclarationSufficient build view observation :=
  declarationSufficient_of_refines (reproducer_refines reproducer)

#print axioms nonempty_reproducer_iff_refines
#print axioms declarationSufficient_of_refines
#print axioms reproducer_declarationSufficient_via_refines

end Mettapedia.CognitiveArchitecture.Agent.ReproducibleBuildView
