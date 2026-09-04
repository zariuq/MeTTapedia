import Mettapedia.UniversalAlgebra.Instances.Monoid
import Mettapedia.UniversalAlgebra.Ultrapower

/-!
# Monoid equations in constant ultrapowers

This file is a concrete positive control for the generic ultrapower theorems.
It transports both the defining monoid equation system and one nontrivial
derived equation to every constant ultrapower of a Mathlib monoid model.
-/

set_option autoImplicit false

namespace Mettapedia.UniversalAlgebra.Monoid

open Filter
open Mettapedia.UniversalAlgebra

universe u

/-- Every constant ultrapower of a Mathlib monoid model still satisfies the
three defining monoid equations. -/
theorem ultrapower_satisfies_equationSystem (Carrier : Type) [Monoid Carrier]
    {Index : Type u} (ultrafilter : Ultrafilter Index) :
    ((mathlibModel Carrier).ultrapower ultrafilter).Satisfies equationSystem :=
  (Model.satisfies_ultrapower_iff
    (mathlibModel Carrier) ultrafilter equationSystem).mpr
      (mathlibModel_satisfies Carrier)

/-- Positive canary: the derived equation `(1 * x) * 1 = x` remains true for
arbitrary valuations taking values in the ultrapower. -/
theorem one_mul_mul_one_holds_in_ultrapower (Carrier : Type) [Monoid Carrier]
    {Index : Type} (ultrafilter : Ultrafilter Index) :
    Equation.Holds ((mathlibModel Carrier).ultrapower ultrafilter)
      (mul (mul one x) one, x) :=
  equationalConsequence_sound one_mul_mul_one
    (Model.UltrapowerCarrier Carrier ultrafilter)
    ((mathlibModel Carrier).ultrapower ultrafilter)
    (ultrapower_satisfies_equationSystem Carrier ultrafilter)

end Mettapedia.UniversalAlgebra.Monoid
