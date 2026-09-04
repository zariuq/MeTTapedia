import Mathlib.Analysis.Real.Hyperreal
import Mettapedia.TypeTheory.FamilyEnclosingUniverse
import Mettapedia.UniversalAlgebra.PrincipalUltrapower

/-!
# Ultrafilter-indexed carriers inside family-enclosing universes

This module connects two independent constructions:

* a family-enclosing predicative Tarski-universe model; and
* ultrapowers selected by ultrafilter perspectives.

Every principal perspective collapses to its selected ordinary coordinate.
The free hyperfilter perspective has a carrier element outside the diagonal
image, and the standard hyperreal construction has an element `omega` larger
than every embedded real.  These are genuine nonstandard-model separation
theorems.  They do not by themselves construct a non-well-founded universe or
promote an ultrapower to a new proof-theoretic foundation.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.UltrafilterUniverseModel

open Filter
open Mettapedia.TypeTheory.FamilyEnclosingUniverse
open Mettapedia.UniversalAlgebra

/-- The natural-number ultrapower carrier selected by one ultrafilter
perspective. -/
abbrev PerspectiveCarrier (view : Ultrafilter Nat) : Type :=
  Model.UltrapowerCarrier Nat view

/-- Every selected perspective carrier is contained in a closed Tarski
universe together with its constant unit evidence family. -/
noncomputable def perspectiveEnvelope (view : Ultrafilter Nat) :
    ClosedTarskiUniverseOver (PerspectiveCarrier view) (fun _ => PUnit) :=
  ambientOperator.enclose (PerspectiveCarrier view) (fun _ => PUnit)

/-- At a principal perspective the enclosed carrier is equivalent to the
ordinary natural numbers. -/
def principalCarrierEquiv (point : Nat) :
    PerspectiveCarrier (pure point) ≃ Nat :=
  Model.principalUltrapowerEquiv point

/-- Every principal perspective has a surjective diagonal embedding. -/
theorem principalDiagonal_surjective (point : Nat) :
    Function.Surjective
      (Model.diagonal (pure point : Ultrafilter Nat) :
        Nat → PerspectiveCarrier (pure point)) :=
  (Model.diagonal_bijective_principal point).2

/-- The free hyperfilter carrier contains the growing element outside the
entire standard diagonal image. -/
theorem freeDiagonal_not_surjective :
    ¬ Function.Surjective
      (Model.diagonal (Filter.hyperfilter Nat) :
        Nat → PerspectiveCarrier (Filter.hyperfilter Nat)) :=
  UltrapowerBoundary.diagonal_not_surjective

/-- Principal collapse and free non-collapse coexist in one
ultrafilter-indexed carrier family. -/
theorem principal_free_boundary :
    (∀ point : Nat,
      Function.Surjective
        (Model.diagonal (pure point : Ultrafilter Nat) :
          Nat → PerspectiveCarrier (pure point))) ∧
      ¬ Function.Surjective
        (Model.diagonal (Filter.hyperfilter Nat) :
          Nat → PerspectiveCarrier (Filter.hyperfilter Nat)) :=
  ⟨principalDiagonal_surjective, freeDiagonal_not_surjective⟩

/-! ## A magnitude-separating nonstandard model -/

/-- The ordinary Mathlib hyperreal carrier and a varying sign-indexed family
fit inside the same closed Tarski-universe interface. -/
noncomputable def hyperrealEnvelope :
    ClosedTarskiUniverseOver Hyperreal
      (fun value => if value < 0 then PUnit else Bool) :=
  ambientOperator.enclose Hyperreal
    (fun value => if value < 0 then PUnit else Bool)

/-- The canonical hyperreal `omega` is an inhabitant of the enclosed base
carrier. -/
noncomputable def enclosedOmega :
    hyperrealEnvelope.El hyperrealEnvelope.baseCode :=
  Hyperreal.omega

/-- The free-ultrafilter construction contains a magnitude larger than every
standard embedded real. -/
theorem every_standard_real_below_omega (value : Real) :
    (value : Hyperreal) < Hyperreal.omega :=
  Hyperreal.coe_lt_omega value

/-- Hence `omega` is not the image of any standard real. -/
theorem omega_not_standard (value : Real) :
    (value : Hyperreal) ≠ Hyperreal.omega :=
  (every_standard_real_below_omega value).ne

/-- The hyperreal embedding is not surjective. -/
theorem real_embedding_not_surjective :
    ¬ Function.Surjective (Hyperreal.ofReal : Real → Hyperreal) := by
  intro surjective
  obtain ⟨value, valueMaps⟩ := surjective Hyperreal.omega
  exact omega_not_standard value valueMaps

#print axioms principalCarrierEquiv
#print axioms principalDiagonal_surjective
#print axioms freeDiagonal_not_surjective
#print axioms principal_free_boundary
#print axioms enclosedOmega
#print axioms every_standard_real_below_omega
#print axioms omega_not_standard
#print axioms real_embedding_not_surjective

end Mettapedia.TypeTheory.UltrafilterUniverseModel
