import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentNormalSupport
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentCheckingReplay

/-!
# An equality forces normal scope recoverability

In the rigid-constant profile, a normal term equal to a normal image of an
injective variable map uses only variables in that map's image. Thus the
actual inverse must succeed. With an exact typed context inclusion, normal
typing replay supplies the recovered body's typing as well.

This is a consequence at each witnessed equality, not permission to reject
an open unification problem from an earlier syntactic occurrence check.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentScopeConsequence

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentNormalChecking ContextualDependentNormalObservations
open ContextualDependentSupport ContextualDependentTypedInversion

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable (rigid : ∀ name, S.roles name = .rigid) (complete : AlgorithmicComplete S.R S.roles)

/-- Retain precisely those parameters whose ambient image occurs on the
other side. The finite lookup is shared with the existing inverter. -/
def commonMask {n k m : Nat} (left : Ren n m) (right : Ren k m) (index : Fin k) : Bool :=
  (ContextualDependentInversion.lookup left (right index)).isSome

theorem commonMask_iff {n k m : Nat} (left : Ren n m) (right : Ren k m) (index : Fin k) :
    commonMask left right index = true ↔ ∃ other, left other = right index := by
  constructor
  · intro found
    obtain ⟨other, found⟩ := Option.isSome_iff_exists.mp found
    exact ⟨other, ContextualDependentInversion.lookup_sound left found⟩
  · rintro ⟨other, image⟩
    cases found : ContextualDependentInversion.lookup left (right index) with
    | some result => simp only [commonMask, found, Option.isSome_some]
    | none =>
        have missing := (List.find?_eq_none.mp found) other (List.mem_finRange other)
        simp [image] at missing

include rigid complete in
theorem common_parameters_forced {n k m : Nat} (left : Ren n m) (right : Ren k m)
    {Γ : Ctx Head m} (formed : CtxFormed S.R Γ) (first : Tm Head n) (second : Tm Head k)
    (type : Tm Head m)
    (same : Equal S.R Γ (Presentation.rename left first) (Presentation.rename right second) type)
    (firstNormal : Normal (S := S) first) (secondNormal : Normal (S := S) second) :
    ∀ index ∈ second.support, commonMask left right index = true := by
  have support := ContextualDependentNormalSupport.equal_support rigid complete formed same
    (normal_rename rigid left firstNormal) (normal_rename rigid right secondNormal)
  rw [support_rename, support_rename] at support
  intro index present
  apply (commonMask_iff left right index).mpr
  have imagePresent : right index ∈ second.support.image right :=
    Finset.mem_image.mpr ⟨index, present, rfl⟩
  rw [← support] at imagePresent
  obtain ⟨other, _, image⟩ := Finset.mem_image.mp imagePresent
  exact ⟨other, image⟩

include rigid complete in
theorem inversion_forced {n m : Nat} (rho : Ren n m) (injective : Function.Injective rho)
    {Γ : Ctx Head m} (formed : CtxFormed S.R Γ) (body : Tm Head n) (right type : Tm Head m)
    (same : Equal S.R Γ (Presentation.rename rho body) right type)
    (bodyNormal : Normal (S := S) body) (rightNormal : Normal (S := S) right) :
    (ContextualDependentInversion.invert (ContextualDependentInversion.lookup rho) right).isSome = true := by
  apply (invert_lookup_defined_iff rho injective right).mpr
  have support := ContextualDependentNormalSupport.equal_support rigid complete formed same
    (normal_rename rigid rho bodyNormal) rightNormal
  rw [support_rename] at support
  intro index present
  rw [← support] at present
  obtain ⟨original, _, image⟩ := Finset.mem_image.mp present
  exact ⟨original, image⟩

include rigid in
theorem root_reflection : ContextualDependentReductionReflection.RootReflectsInjections S.R.computation := by
  intro n m rho injective term result step
  exact False.elim (no_root rigid step)

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R)
  (heads : HeadPreserving S.R) (algebra : CumulativeAlgebra S.R)
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)
  (declared : DeclaredTypesFormed S.R)

include rigid complete facts roots heads algebra headTypingUnique declared in
theorem typed_recovery_forced {source target : Context S.R} (inclusion : Inclusion source target)
    (compatible : CtxRen source.raw target.raw inclusion.forward) (type : TypeOver source)
    (body : Tm Head source.arity) (right : Term target (type.reindex inclusion.hom))
    (same : Equal S.R target.raw (Presentation.rename inclusion.forward body) right.code
      (type.reindex inclusion.hom).code)
    (bodyNormal : Normal (S := S) body) (rightNormal : Normal (S := S) right.code) :
    ∃ recovered : Recovery inclusion type right.code,
      ContextualDependentCheckingReplay.recover_normal facts algebra headTypingUnique complete roots heads declared
        (root_reflection rigid) inclusion compatible type right rightNormal = some recovered := by
  have invertible := inversion_forced rigid complete inclusion.forward inclusion.injective target.formed
    body right.code (type.reindex inclusion.hom).code same bodyNormal rightNormal
  obtain ⟨candidate, found⟩ := Option.isSome_iff_exists.mp invertible
  have recovered := ContextualDependentCheckingReplay.recover_normal_code facts algebra headTypingUnique complete
    roots heads declared (root_reflection rigid) inclusion compatible type right rightNormal found
  obtain ⟨result, accepted, _⟩ := Option.map_eq_some_iff.mp recovered
  exact ⟨result, accepted⟩

end ContextualDependentScopeConsequence
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
