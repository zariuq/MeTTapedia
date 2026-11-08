import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentInversion
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentEta
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.ExecutableChecking

/-!
# Checked typed inversion along a dependent context inclusion

A variable selection must itself be a typed substitution. The inverse
traversal recovers the proposed body, then the existing executable checker
checks it at the metavariable's declared type in its smaller context.
Successful results reconstruct the original syntax and retain an actual
typed derivation. Failure leaves a solver obligation; it is not a negative
typing or unification judgment.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentTypedInversion

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual

variable {Head : Type} {rules : Rules Head}

/-- No prefix or ordering requirement is imposed. The typing certificate
accounts for the dependencies of every selected variable. -/
structure Inclusion (source target : Context rules) where
  forward : Ren source.arity target.arity
  injective : Function.Injective forward
  typed : SubstMor rules source.raw target.raw (renSub forward)

def Inclusion.hom {Γ Δ : Context rules} (inclusion : Inclusion Γ Δ) : Δ ⟶ Γ :=
  ⟨renSub inclusion.forward, inclusion.typed⟩

structure Recovery {Γ Δ : Context rules} (inclusion : Inclusion Γ Δ) (type : TypeOver Γ)
    (target : Tm Head Δ.arity) where
  body : Term Γ type
  recovers : rename inclusion.forward body.code = target

theorem Recovery.unique {Γ Δ : Context rules} {inclusion : Inclusion Γ Δ} {type : TypeOver Γ}
    {target : Tm Head Δ.arity} (first second : Recovery inclusion type target) : first = second := by
  have firstInverse := ContextualDependentInversion.invert_rename first.body.code inclusion.forward
    (ContextualDependentInversion.lookup inclusion.forward)
    (ContextualDependentInversion.lookup_exact inclusion.forward inclusion.injective)
  have secondInverse := ContextualDependentInversion.invert_rename second.body.code inclusion.forward
    (ContextualDependentInversion.lookup inclusion.forward)
    (ContextualDependentInversion.lookup_exact inclusion.forward inclusion.injective)
  rw [first.recovers] at firstInverse
  rw [second.recovers] at secondInverse
  have codes := Option.some.inj (firstInverse.symm.trans secondInverse)
  have bodies := Term.ext codes
  cases first
  cases second
  cases bodies
  rfl

variable {L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable [DecidableEq Head] [DecidableRel S.R.headEq]
  [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R)
  (heads : HeadPreserving S.R) (algebra : CumulativeAlgebra S.R) (declared : DeclaredTypesFormed S.R)
variable (choices : ExecutableChecking.HeadChoices S.R) (reducer : ExecutableReduction.Reducer S.R)

def recover (fuel : Nat) {Γ Δ : Context S.R} (inclusion : Inclusion Γ Δ)
    (type : TypeOver Γ) (target : Tm Head Δ.arity) : Option (Recovery inclusion type target) :=
  match found : ContextualDependentInversion.invert
      (ContextualDependentInversion.lookup inclusion.forward) target with
  | none => none
  | some body => do
      let checked ← ExecutableChecking.check S.R choices reducer fuel Γ.raw body type.code
      return ⟨⟨body, CheckingAlgorithm.sound (S := S) facts roots heads algebra declared
          checked.down Γ.formed type.isType⟩,
        ContextualDependentInversion.invert_sound target inclusion.forward _
          (ContextualDependentInversion.lookup_exact inclusion.forward inclusion.injective) body found⟩

omit [DecidableEq Head] [DecidableRel S.R.headEq]
  [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative] in
/-- The recovered body really solves the original homogeneous equation at
the typed eta frame, including its dependent annotation. -/
theorem Recovery.solves {Γ Δ : Context S.R} {inclusion : Inclusion Γ Δ} {type : TypeOver Γ}
    (target : Term Δ (type.reindex inclusion.hom)) (recovered : Recovery inclusion type target.code) :
    (ContextualDependentEta.frames S.levels).E
      (TotalTerm.reindex ⟨type, recovered.body⟩ inclusion.hom)
      (⟨type.reindex inclusion.hom, target⟩ : TotalTerm Δ) := by
  refine ⟨(type.reindex inclusion.hom).isType.refl, ?_⟩
  change Equal S.R Δ.raw (subst (renSub inclusion.forward) recovered.body.code) target.code
    (type.reindex inclusion.hom).code
  rw [subst_renSub, recovered.recovers]
  exact .refl target.typed

end ContextualDependentTypedInversion
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
