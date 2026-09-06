import Mettapedia.Logic.TheorySimulation
import Mettapedia.UniversalAlgebra.NIK.ConsequenceInvariance

/-!
# Simulation of NIK equational theories

Generated-consequence equivalence supplies conservative semantic simulations
in both directions between the corresponding NIK theory objects.  This is an
instance of the morphism-class-indexed simulation order; it does not identify
the occurrence-bearing equation systems or their concrete certificate types.
-/

set_option autoImplicit false

namespace Mettapedia.UniversalAlgebra.NIK

open Mettapedia.GSLT.LanguageDef.CertifiedTheoryCategory
open Mettapedia.Logic.TheorySimulation

universe u

variable {S : Signature.{u}} [DecidableEq S.Operation]

/-- Bundle one equational NIK theory as a heterogeneous semantic theory
object. -/
def theoryObject (system : EquationSystem S) :
    TheoryObject.{0, 0, u} where
  Kind := Unit
  family := theory system

/-- Consequence equivalence gives a conservative simulation in the forward
direction. -/
theorem conservativelySimulates_of_sameConsequences
    {left right : EquationSystem S}
    (equivalent : EquationSystem.SameConsequences left right) :
    ConservativelySimulates (theoryObject right) (theoryObject left) :=
  ⟨identityOnEquationsTranslation equivalent,
    identityOnEquationsTranslation_conservative equivalent⟩

/-- Consequence-equivalent systems mutually simulate one another through
conservative semantic translations. -/
theorem mutuallyConservativelySimulates_of_sameConsequences
    {left right : EquationSystem S}
    (equivalent : EquationSystem.SameConsequences left right) :
    MutuallyConservativelySimulates (theoryObject left) (theoryObject right) :=
  ⟨conservativelySimulates_of_sameConsequences equivalent.symm,
    conservativelySimulates_of_sameConsequences equivalent⟩

end Mettapedia.UniversalAlgebra.NIK

