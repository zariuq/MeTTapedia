import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualResidual
import Mettapedia.OSLF.Syntax.BindingRenamingInverse
import Mettapedia.OSLF.Syntax.ContextualFamilyDeclarations
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Solving a contextual hole against an object variable

The common finite inverse search finds the formal parameter of an ambient
variable. A successful search gives an ordinary contextual assignment into
the remaining declaration family. For injective spines every solution
factors through that assignment; refusing an out-of-scope variable refutes
the equation. Other queued equations are instantiated and retained.

Repeated spines remain valid application syntax, but the factorization
theorem requires injectivity. No new term representation or binding
interpreter is introduced.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualVariableBinding

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open scoped BigOperators

variable {S : Signature} [DecidableEq S.Srt] {Other Variables : Type}
  {next : Variables → MetaArity S}

abbrev declarations (parameters : Ctx S) (result : S.Srt) (others : Other → MetaArity S) :
    Unit ⊕ Other → MetaArity S := sumDeclarations (fun _ => (parameters, result)) others

def answer (parameters : Ctx S) {result : S.Srt} (others : Other → MetaArity S)
    (position : Var parameters result) : Assignment (declarations parameters result others) others
  | .inl () => .var position
  | .inr identity => generator others identity

def remainingAssignment (parameters : Ctx S) (result : S.Srt) (others : Other → MetaArity S)
    (candidate : Assignment (declarations parameters result others) next) : Assignment others next :=
  fun identity => candidate (.inr identity)

def solve? (parameters : Ctx S) {result : S.Srt} (others : Other → MetaArity S)
    {Γ : Ctx S} (rho : Ren S parameters Γ) (position : Var Γ result) :
    Option (Assignment (declarations parameters result others) others) :=
  (RenamingInverse.inverse rho result position).map (answer parameters others)

theorem image_of_solution (parameters : Ctx S) {result : S.Srt} (others : Other → MetaArity S)
    {Γ : Ctx S} (rho : Ren S parameters Γ) (injective : ∀ sort, Function.Injective (rho sort))
    (position : Var Γ result) (formal : Var parameters result)
    (found : RenamingInverse.inverse rho result position = some formal)
    (candidate : Assignment (declarations parameters result others) next)
    (solved : rename (S := signature S next) rho (candidate (.inl ())) = .var position) :
    candidate (.inl ()) = .var formal := by
  apply rename_injective (RenamingInverse.strengthener (S := signature S next) rho injective)
  exact solved.trans (congrArg Term.var (RenamingInverse.inverse_sound rho result position formal found).symm)

omit [DecidableEq S.Srt] in
theorem factors_of_image (parameters : Ctx S) {result : S.Srt} (others : Other → MetaArity S)
    (formal : Var parameters result) (candidate : Assignment (declarations parameters result others) next)
    (image : candidate (.inl ()) = .var formal) :
    ∀ identity, candidate identity =
      instantiate (remainingAssignment parameters result others candidate) (answer parameters others formal identity)
  | .inl () => image
  | .inr identity => by
      change candidate (.inr identity) =
        instantiate (remainingAssignment parameters result others candidate) (generator others identity)
      exact (instantiate_generator (remainingAssignment parameters result others candidate) identity).symm

theorem reduction (parameters : Ctx S) {result : S.Srt} (others : Other → MetaArity S)
    {Γ : Ctx S} (rho : Ren S parameters Γ) (injective : ∀ sort, Function.Injective (rho sort))
    (position : Var Γ result) (formal : Var parameters result)
    (found : RenamingInverse.inverse rho result position = some formal)
    (problem : ContextualResidual.Problem (declarations parameters result others))
    (selected :
      (observe (rename (S := signature S (declarations parameters result others)) rho
        (generator (declarations parameters result others) (.inl ()))),
       observe (Term.var (S := signature S (declarations parameters result others)) position)) ∈ problem) :
    ContextualResidual.Reduction problem (answer parameters others formal)
      (ContextualResidual.mapProblem (answer parameters others formal) problem) := by
  constructor
  · intro Next declaration candidate solved
    exact (ContextualResidual.models_mapProblem _ _ _).mp solved
  · intro Next declaration candidate solved
    have same := observe_injective (solved _ selected)
    rw [ContextualFamily.instantiate_rename, instantiate_generator] at same
    have image := image_of_solution parameters others rho injective position formal found candidate same
    have factors := factors_of_image parameters others formal candidate image
    exact ⟨remainingAssignment parameters result others candidate,
      (ContextualResidual.models_of_components candidate _ _ factors problem).mp solved, factors⟩

theorem refused_has_no_solution (parameters : Ctx S) {result : S.Srt} (others : Other → MetaArity S)
    {Γ : Ctx S} (rho : Ren S parameters Γ) (injective : ∀ sort, Function.Injective (rho sort))
    (position : Var Γ result) (refused : RenamingInverse.inverse rho result position = none)
    (candidate : Assignment (declarations parameters result others) next) :
    rename (S := signature S next) rho (candidate (.inl ())) ≠ .var position := by
  intro solved
  let inverse : Strengthener (S := signature S next) rho :=
    ⟨RenamingInverse.inverse (S := S) rho,
      RenamingInverse.inverse_complete (S := S) rho injective,
      RenamingInverse.inverse_sound (S := S) rho⟩
  have recovered := strengthenT_rename inverse (candidate (.inl ()))
  rw [solved] at recovered
  change (RenamingInverse.inverse (S := S) rho result position).map
    (Term.var (S := signature S next) (Γ := parameters)) =
    some (candidate (.inl ())) at recovered
  rw [refused] at recovered
  cases recovered

def sourcePotential (parameters : Ctx S) (result : S.Srt) (others : Other → MetaArity S)
    (candidate : Assignment (declarations parameters result others) next) (active : Finset Other) : Nat :=
  termSize (candidate (.inl ())) + ∑ identity ∈ active, termSize (candidate (.inr identity))

def targetPotential (others : Other → MetaArity S) (candidate : Assignment others next)
    (active : Finset Other) : Nat := ∑ identity ∈ active, termSize (candidate identity)

omit [DecidableEq S.Srt] in
theorem removes_one_model_node (parameters : Ctx S) {result : S.Srt} (others : Other → MetaArity S)
    (formal : Var parameters result) (candidate : Assignment (declarations parameters result others) next)
    (image : candidate (.inl ()) = .var formal) (active : Finset Other) :
    targetPotential others (remainingAssignment parameters result others candidate) active + 1 =
      sourcePotential parameters result others candidate active := by
  unfold sourcePotential targetPotential remainingAssignment
  rw [image]
  simp only [termSize]
  omega

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualVariableBinding
