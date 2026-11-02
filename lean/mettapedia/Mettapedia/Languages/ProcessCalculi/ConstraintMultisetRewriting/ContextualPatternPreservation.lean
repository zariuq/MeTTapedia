import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPatternFragment

/-!
# Permitted contextual instantiation preserves structural patterns

Injective object renamings preserve the distinct-variable fragment beneath
every binder. Replacing holes by pattern images preserves it too: at a
flexible occurrence, contextual instantiation is exactly renaming the chosen
image along the existing argument spine. This law states the actual
restriction on solver substitutions; arbitrary applications remain available
outside the fragment.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPatternFragment

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily

variable {S : Signature} {V W : Type} {source : V → MetaArity S} {target : W → MetaArity S}

theorem rename_preserves {Γ : Ctx S} {sort : S.Srt} (term : Term (signature S source) Γ sort)
    (proof : Pattern S source term) {Δ : Ctx S} (rho : Ren S Γ Δ)
    (injective : ∀ sort, Function.Injective (rho sort)) : Pattern S source (rename rho term) := by
  refine Pattern.rec
    (motive_1 := fun {context} _ value _ =>
      ∀ {next : Ctx S} (mapping : Ren S context next),
        (∀ sort, Function.Injective (mapping sort)) → Pattern S source (rename mapping value))
    (motive_2 := fun {_} {context} values _ =>
      ∀ {next : Ctx S} (mapping : Ren S context next),
        (∀ sort, Function.Injective (mapping sort)) → PatternArgs S source (renameArgs mapping values))
    ?_ ?_ ?_ ?_ ?_ proof rho injective
  · intro context result position next mapping _
    exact Pattern.object (S := S) (declaration := source) (mapping result position)
  · intro context result operator arguments fields checked next mapping oneToOne
    exact Pattern.rigid operator _ (checked mapping oneToOne)
  · intro context identity arguments spineMap spine distinct next mapping oneToOne
    refine Pattern.hole identity (renameArgs mapping arguments)
      (fun sort position => mapping sort (spineMap sort position)) ?_
      (RenamingSlots.compose_injective spineMap mapping distinct oneToOne)
    intro result position
    rw [argsToSub_renameArgs, spine]
    rfl
  · intro context next mapping _
    exact .nil
  · intro arities context binders result head tail first rest checkedHead checkedTail next mapping oneToOne
    exact .cons _ _ (checkedHead (liftRen mapping binders)
      (RenamingSlots.lift_injective mapping oneToOne binders)) (checkedTail mapping oneToOne)

theorem instantiate_spine (assignment : Assignment source target) (identity : V) {Γ : Ctx S}
    (arguments : Args (signature S source) ((source identity).1.map fun sort => ([], sort)) Γ)
    (rho : Ren S (source identity).1 Γ)
    (spine : ∀ sort index, argsToSub arguments sort index = .var (rho sort index)) :
    instantiate assignment (Term.op (.inr (.mk identity)) arguments) =
      rename (S := signature S target) rho (assignment identity) := by
  change bind (argsToSub (instantiateArgs assignment arguments)) (assignment identity) = _
  have spineSubstitution : argsToSub (instantiateArgs assignment arguments) =
      fun sort index => Term.var (S := signature S target) (rho sort index) := by
    funext sort index
    rw [argsToSub_instantiateArgs, spine]
    rfl
  rw [spineSubstitution, bind_var_eq_rename]

theorem instantiate_preserves (assignment : Assignment source target)
    (images : ∀ identity, Pattern S target (assignment identity))
    {Γ : Ctx S} {sort : S.Srt} (term : Term (signature S source) Γ sort)
    (proof : Pattern S source term) : Pattern S target (instantiate assignment term) := by
  refine Pattern.rec
    (motive_1 := fun value _ => Pattern S target (instantiate assignment value))
    (motive_2 := fun values _ => PatternArgs S target (instantiateArgs assignment values))
    ?_ ?_ ?_ ?_ ?_ proof
  · intro context result position
    exact Pattern.object (S := S) (declaration := target) position
  · intro context result operator arguments fields checked
    exact .rigid operator _ checked
  · intro context identity arguments rho spine distinct
    rw [instantiate_spine assignment identity arguments rho spine]
    exact rename_preserves (assignment identity) (images identity) rho distinct
  · intro context
    exact .nil
  · intro arities context binders result head tail first rest checkedHead checkedTail
    exact .cons _ _ checkedHead checkedTail

theorem checked_instantiation_stays_in_fragment (assignment : Assignment source target)
    (images : ∀ identity, check (assignment identity) = true)
    {Γ : Ctx S} {sort : S.Srt} (term : Term (signature S source) Γ sort)
    (checked : check term = true) : check (instantiate assignment term) = true :=
  check_complete _ (instantiate_preserves assignment (fun identity => check_sound _ (images identity)) term
    (check_sound term checked))

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPatternFragment
