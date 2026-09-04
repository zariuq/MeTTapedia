import Mettapedia.UniversalAlgebra.NIK.Authority

/-!
# Canonically rejected equational certificates

A malformed symmetry node with no premise is rejected by equational replay
for every proposed conclusion.  Retaining the proposed equation at the root
makes this a reusable sentinel when a total certificate transformation must
preserve both rejection and the physical conclusion.
-/

set_option autoImplicit false

namespace Mettapedia.UniversalAlgebra.NIK

open Mettapedia.Logic

universe u

variable {S : Signature.{u}} [DecidableEq S.Operation]

/-- A malformed symmetry node with no premise is rejected for every proposed
equation while retaining that equation as its physical conclusion. -/
def rejectedCertificate (system : EquationSystem S) (equation : Equation S) :
    Derivation (Equation S) (EquationalRuleWitness system) :=
  .node equation (.symm equation.1 equation.2) 0 Fin.elim0

omit [DecidableEq S.Operation] in
@[simp] theorem rejectedCertificate_concl
    (system : EquationSystem S) (equation : Equation S) :
    (rejectedCertificate system equation).concl = equation :=
  rfl

@[simp] theorem rejectedCertificate_valid
    (system : EquationSystem S) (equation : Equation S) :
    (rejectedCertificate system equation).valid
      (equationalRuleInterface system) = false := by
  simp [rejectedCertificate, Derivation.valid, equationalRuleInterface,
    EquationalRuleWitness.isInstance]

end Mettapedia.UniversalAlgebra.NIK
