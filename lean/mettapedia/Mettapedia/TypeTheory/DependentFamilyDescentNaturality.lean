import Mettapedia.TypeTheory.DependentFamilyObserverFactorization

/-!
# Reindexing dependent-family descent

Descent data for a dependent family is stable under a commuting square of
source and observation maps.  This is the basic substitution law needed by any
restricted doctrine of families that descend through an observer.

The theorem retains the factorization data itself.  It does not yet construct
context comprehension or claim a category-with-families structure.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.DependentFamilyDescentNaturality

open Mettapedia.TypeTheory.DependentFamilyObserverFactorization

universe uSource uTarget uSource' uTarget' uFibre

namespace Descent

/-- Reindex a factorizing family along a commuting square.

```
Source'  --sourceMap-->  Source
  |                       |
observe'                observe
  |                       |
  v                       v
Target'  --targetMap-->  Target
```

The source family is pulled back along `sourceMap`, while its descended target
family is pulled back along `targetMap`. -/
def reindexAlongSquare
    {Source : Type uSource} {Target : Type uTarget}
    {Source' : Type uSource'} {Target' : Type uTarget'}
    {observe : Source -> Target} {family : Source -> Type uFibre}
    (factorization : FamilyFactorization observe family)
    (sourceMap : Source' -> Source) (observe' : Source' -> Target')
    (targetMap : Target' -> Target)
    (commutes : forall source,
      observe (sourceMap source) = targetMap (observe' source)) :
    FamilyFactorization observe'
      (fun source => family (sourceMap source)) where
  targetFamily := fun target => factorization.targetFamily (targetMap target)
  identify source :=
    (factorization.identify (sourceMap source)).trans
      (Equiv.cast
        (congrArg factorization.targetFamily (commutes source)))

/-- Pullback along a source map is the identity-target special case. -/
def reindexSource
    {Source : Type uSource} {Target : Type uTarget}
    {Source' : Type uSource'}
    {observe : Source -> Target} {family : Source -> Type uFibre}
    (factorization : FamilyFactorization observe family)
    (sourceMap : Source' -> Source) :
    FamilyFactorization (fun source => observe (sourceMap source))
      (fun source => family (sourceMap source)) :=
  reindexAlongSquare factorization sourceMap
    (fun source => observe (sourceMap source)) id (fun _ => rfl)

end Descent

/-! ## Positive control -/

namespace Canary

/-- Reindexing the constant-family control along Boolean negation retains
actual factorization data. -/
def negationReindexesConstant :
    FamilyFactorization
      (fun value : Bool =>
        DependentFamilyObserverFactorization.Canary.coarseBool (Bool.not value))
      (fun _ => PUnit) :=
  Descent.reindexSource
    DependentFamilyObserverFactorization.Canary.constantFactors Bool.not

end Canary

#print axioms Descent.reindexAlongSquare
#print axioms Descent.reindexSource
#print axioms Canary.negationReindexesConstant

end Mettapedia.TypeTheory.DependentFamilyDescentNaturality
