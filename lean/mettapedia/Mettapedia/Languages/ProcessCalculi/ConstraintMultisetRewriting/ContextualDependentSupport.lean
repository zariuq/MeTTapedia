import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentInversion
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.PartialSubstitution

/-!
# Native support, variable maps, and scope inversion

The native finite support inventory and partial substitution are reused.
The unifier's variable inverse is the variable-valued case of that partial
substitution. Its exact support criterion includes every binder and every
annotation constructor; no arbitrary value is supplied for a missing slot.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentSupport

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation

variable {Head : Type}

theorem outer_image_lift {n m : Nat} (rho : Ren n m) (slots : Finset (Fin (n + 1))) :
    outerSupport (slots.image (liftRen rho)) = (outerSupport slots).image rho := by
  ext index
  simp only [mem_outerSupport, Finset.mem_image]
  constructor
  · rintro ⟨position, present, same⟩
    revert present same
    refine Fin.cases ?_ (fun position => ?_) position
    · intro _ impossible
      exact False.elim (Fin.succ_ne_zero _ impossible.symm)
    · intro present same
      exact ⟨position, present, Fin.succ_injective _ same⟩
  · rintro ⟨position, present, same⟩
    exact ⟨position.succ, present, congrArg Fin.succ same⟩

theorem support_rename {n : Nat} (term : Tm Head n) :
    ∀ {m : Nat} (rho : Ren n m), (Presentation.rename rho term).support = term.support.image rho := by
  induction term with
  | var index => intro m rho; simp [Presentation.rename, Tm.support]
  | head head => intro m rho; simp [Presentation.rename, Tm.support]
  | const name => intro m rho; simp [Presentation.rename, Tm.support]
  | pi domain body ihDomain ihBody =>
      intro m rho
      simp only [Presentation.rename, Tm.support, ihDomain, ihBody, outer_image_lift, Finset.image_union]
  | sigma domain body ihDomain ihBody =>
      intro m rho
      simp only [Presentation.rename, Tm.support, ihDomain, ihBody, outer_image_lift, Finset.image_union]
  | id carrier first second ihCarrier ihFirst ihSecond =>
      intro m rho
      simp only [Presentation.rename, Tm.support, ihCarrier, ihFirst, ihSecond, Finset.image_union]
  | lam body ih => intro m rho; simp only [Presentation.rename, Tm.support, ih, outer_image_lift]
  | app first second ihFirst ihSecond =>
      intro m rho; simp only [Presentation.rename, Tm.support, ihFirst, ihSecond, Finset.image_union]
  | pair first second ihFirst ihSecond =>
      intro m rho; simp only [Presentation.rename, Tm.support, ihFirst, ihSecond, Finset.image_union]
  | fst value ih => intro m rho; exact ih rho
  | snd value ih => intro m rho; exact ih rho
  | refl value ih => intro m rho; exact ih rho

def variableEnvironment {n m : Nat} (inverse : ContextualDependentInversion.Partial n m) :
    PartialSub Head m n := fun index => (inverse index).map Tm.var

theorem variableEnvironment_lift {n m : Nat} (inverse : ContextualDependentInversion.Partial n m) :
    variableEnvironment (Head := Head) (ContextualDependentInversion.lift inverse) =
      liftPartialSub (variableEnvironment inverse) := by
  funext index
  refine Fin.cases rfl (fun index => ?_) index
  cases found : inverse index <;>
    simp [variableEnvironment, ContextualDependentInversion.lift, liftPartialSub, found, Presentation.rename, wk]

theorem invert_eq_partial {m : Nat} (term : Tm Head m) :
    ∀ {n : Nat} (inverse : ContextualDependentInversion.Partial n m),
      ContextualDependentInversion.invert inverse term = substPartial (variableEnvironment inverse) term := by
  induction term with
  | var index => intros; rfl
  | head head => intros; rfl
  | const name => intros; rfl
  | pi domain body ihDomain ihBody =>
      intro n inverse
      simp only [ContextualDependentInversion.invert, substPartial, ihDomain, ihBody, variableEnvironment_lift]
  | sigma domain body ihDomain ihBody =>
      intro n inverse
      simp only [ContextualDependentInversion.invert, substPartial, ihDomain, ihBody, variableEnvironment_lift]
  | id carrier first second ihCarrier ihFirst ihSecond =>
      intro n inverse
      simp only [ContextualDependentInversion.invert, substPartial, ihCarrier, ihFirst, ihSecond]
  | lam body ih =>
      intro n inverse
      simp only [ContextualDependentInversion.invert, substPartial, ih, variableEnvironment_lift]
      cases substPartial (liftPartialSub (variableEnvironment inverse)) body <;> rfl
  | app first second ihFirst ihSecond =>
      intro n inverse
      simp only [ContextualDependentInversion.invert, substPartial, ihFirst, ihSecond]
  | pair first second ihFirst ihSecond =>
      intro n inverse
      simp only [ContextualDependentInversion.invert, substPartial, ihFirst, ihSecond]
  | fst value ih =>
      intro n inverse; simp only [ContextualDependentInversion.invert, substPartial, ih]
      cases substPartial (variableEnvironment inverse) value <;> rfl
  | snd value ih =>
      intro n inverse; simp only [ContextualDependentInversion.invert, substPartial, ih]
      cases substPartial (variableEnvironment inverse) value <;> rfl
  | refl value ih =>
      intro n inverse; simp only [ContextualDependentInversion.invert, substPartial, ih]
      cases substPartial (variableEnvironment inverse) value <;> rfl

theorem invert_defined_iff {n m : Nat} (inverse : ContextualDependentInversion.Partial n m)
    (term : Tm Head m) :
    (ContextualDependentInversion.invert inverse term).isSome = true ↔
      ∀ index ∈ term.support, (inverse index).isSome = true := by
  rw [invert_eq_partial, substPartial_defined]
  simp only [variableEnvironment, Option.isSome_map]

theorem invert_lookup_defined_iff {n m : Nat} (rho : Ren n m) (injective : Function.Injective rho)
    (term : Tm Head m) :
    (ContextualDependentInversion.invert (ContextualDependentInversion.lookup rho) term).isSome = true ↔
      ∀ index ∈ term.support, ∃ original, rho original = index := by
  rw [invert_defined_iff]
  apply forall_congr'
  intro index
  apply forall_congr'
  intro _
  constructor
  · intro found
    obtain ⟨original, selected⟩ := Option.isSome_iff_exists.mp found
    exact ⟨original, ContextualDependentInversion.lookup_sound rho selected⟩
  · rintro ⟨original, rfl⟩
    rw [ContextualDependentInversion.lookup_complete rho injective original]
    rfl

end ContextualDependentSupport
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
