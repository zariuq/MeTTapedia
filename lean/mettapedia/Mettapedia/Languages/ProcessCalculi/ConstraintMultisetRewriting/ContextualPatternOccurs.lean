import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPatternPreservation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualResidual
import Mettapedia.OSLF.Syntax.ContextualFamilySupport

/-!
# A finite occurs obstruction for the declared contextual pattern fragment

In a structural pattern, a mentioned hole's instantiated image survives:
variable-only occurrence arguments rename that image and preserve its size.
Under a rigid constructor the resulting tree is strictly larger. A flexible
image therefore cannot equal such a tree containing itself.

The pattern hypothesis is essential. A general application can erase an
argument containing the selected hole. This obstruction is a solver case,
not a global restriction on application or on other declared term theories.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPatternOccurs

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualPatternFragment

variable {S : Signature} {V W : Type} {source : V → MetaArity S} {target : W → MetaArity S}

theorem variable_spine_has_no_hole_support : ∀ (parameters : Ctx S) {Γ : Ctx S}
    (arguments : Args (signature S source) (parameters.map fun sort => ([], sort)) Γ)
    (rho : Ren S parameters Γ),
    (∀ sort position, argsToSub arguments sort position = .var (rho sort position)) → supportArgs arguments = []
  | [], _, .nil, _, _ => rfl
  | first :: rest, _, .cons head tail, rho, spine => by
      have headImage : head = .var (rho first .zero) := spine first .zero
      rw [headImage, supportArgs, support, List.nil_append]
      exact variable_spine_has_no_hole_support rest tail (fun sort position => rho sort (.succ position))
        (fun sort position => spine sort (.succ position))

theorem image_size_le (assignment : Assignment source target) {Γ : Ctx S} {sort : S.Srt}
    (term : Term (signature S source) Γ sort) (proof : Pattern S source term)
    (identity : V) (present : identity ∈ support term) :
    termSize (assignment identity) ≤ termSize (instantiate assignment term) := by
  refine Pattern.rec
    (motive_1 := fun value _ => ∀ identity ∈ support value,
      termSize (assignment identity) ≤ termSize (instantiate assignment value))
    (motive_2 := fun values _ => ∀ identity ∈ supportArgs values,
      termSize (assignment identity) ≤ argsSize (instantiateArgs assignment values))
    ?_ ?_ ?_ ?_ ?_ proof identity present
  · intro context result position name member
    cases member
  · intro context result operator arguments fields bounded name member
    have child := bounded name member
    rw [ContextualFamily.instantiate, termSize]
    omega
  · intro context selected arguments rho spine _ name member
    have absent := variable_spine_has_no_hole_support _ arguments rho spine
    simp only [support, absent, List.mem_cons, List.not_mem_nil, or_false] at member
    subst name
    rw [instantiate_spine assignment selected arguments rho spine, termSize_rename]
  · intro context name member
    cases member
  · intro arities context binders result head tail first rest boundedHead boundedTail name member
    have alternative := List.mem_append.mp member
    change termSize (assignment name) ≤
      termSize (instantiate assignment head) + argsSize (instantiateArgs assignment tail)
    cases alternative with
    | inl headMember => have := boundedHead name headMember; omega
    | inr tailMember => have := boundedTail name tailMember; omega

theorem argument_image_size_le (assignment : Assignment source target) :
    ∀ {arities : List (MetaArity S)} {Γ : Ctx S}
      (arguments : Args (signature S source) arities Γ) (_proof : PatternArgs S source arguments)
      (identity : V), identity ∈ supportArgs arguments →
        termSize (assignment identity) ≤ argsSize (instantiateArgs assignment arguments)
  | _, _, .nil, .nil, _, member => by cases member
  | _, _, .cons head tail, .cons _ _ first rest, identity, member => by
      have alternative := List.mem_append.mp member
      change termSize (assignment identity) ≤
        termSize (instantiate assignment head) + argsSize (instantiateArgs assignment tail)
      cases alternative with
      | inl headMember => have := image_size_le assignment head first identity headMember; omega
      | inr tailMember => have := argument_image_size_le assignment tail rest identity tailMember; omega

theorem strict_under_rigid (assignment : Assignment source target) {Γ : Ctx S} {sort : S.Srt}
    (operator : S.Op sort) (arguments : Args (signature S source) (S.arity operator) Γ)
    (fields : PatternArgs S source arguments) (identity : V) (present : identity ∈ supportArgs arguments) :
    termSize (assignment identity) <
      termSize (instantiate assignment (Term.op (.inl operator) arguments)) := by
  have bound := argument_image_size_le assignment arguments fields identity present
  rw [ContextualFamily.instantiate, termSize]
  omega

theorem no_finite_solution (assignment : Assignment source target) (identity : V) {Γ : Ctx S}
    (rho : Ren S (source identity).1 Γ) (operator : S.Op (source identity).2)
    (arguments : Args (signature S source) (S.arity operator) Γ)
    (fields : PatternArgs S source arguments) (present : identity ∈ supportArgs arguments) :
    instantiate assignment (rename (S := signature S source) rho (generator source identity)) ≠
      instantiate assignment (Term.op (.inl operator) arguments) := by
  intro same
  have strict := strict_under_rigid assignment operator arguments fields identity present
  have sizes := congrArg termSize same
  rw [ContextualFamily.instantiate_rename, instantiate_generator, termSize_rename] at sizes
  omega

theorem selected_occurs_equation_refutes_models (assignment : Assignment source target) (identity : V)
    {Γ : Ctx S} (rho : Ren S (source identity).1 Γ) (operator : S.Op (source identity).2)
    (arguments : Args (signature S source) (S.arity operator) Γ)
    (fields : PatternArgs S source arguments) (present : identity ∈ supportArgs arguments)
    (problem : ContextualResidual.Problem source)
    (selected :
      (observe (rename (S := signature S source) rho (generator source identity)),
       observe (Term.op (.inl operator) arguments)) ∈ problem) : ¬ ContextualResidual.Models assignment problem := by
  intro solved
  exact no_finite_solution assignment identity rho operator arguments fields present
    (observe_injective (solved _ selected))

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPatternOccurs
