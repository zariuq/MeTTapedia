import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualBindingPermissions
import Mettapedia.Logic.ProjectedObservations

/-! Joint caller observation preservation has a semantic converse. The
existing dependency permission analysis supplies this criterion, but the
criterion itself refers only to solutions and their complete observation
vectors. Private helper representations are not observable coordinates. -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualBindingPermissions

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Logic

variable {S : Signature} {V W : Type} {declarations : V → MetaArity S}
  {future : W → MetaArity S} {Γ : Ctx S} {sort : S.Srt}

theorem joint_projection_iff_possible
    (before after : EquationStore (Term (signature S declarations) Γ sort))
    (observed : List (Observation S declarations)) :
    (fun candidate : Assignment declarations future => jointView candidate observed) ''
        {candidate | ContextualFrameUnifier.Models candidate before} =
      (fun candidate : Assignment declarations future => jointView candidate observed) ''
        {candidate | ContextualFrameUnifier.Models candidate after} ↔
      ∀ question : List (Observation S future) → Prop,
        (∃ candidate : Assignment declarations future,
          ContextualFrameUnifier.Models candidate before ∧ question (jointView candidate observed)) ↔
        (∃ candidate : Assignment declarations future,
          ContextualFrameUnifier.Models candidate after ∧ question (jointView candidate observed)) :=
  ProjectedObservations.image_eq_iff_possible _ _ _ _

theorem joint_projection_iff_necessary
    (before after : EquationStore (Term (signature S declarations) Γ sort))
    (observed : List (Observation S declarations)) :
    (fun candidate : Assignment declarations future => jointView candidate observed) ''
        {candidate | ContextualFrameUnifier.Models candidate before} =
      (fun candidate : Assignment declarations future => jointView candidate observed) ''
        {candidate | ContextualFrameUnifier.Models candidate after} ↔
      ∀ question : List (Observation S future) → Prop,
        (∀ candidate : Assignment declarations future,
          ContextualFrameUnifier.Models candidate before → question (jointView candidate observed)) ↔
        (∀ candidate : Assignment declarations future,
          ContextualFrameUnifier.Models candidate after → question (jointView candidate observed)) :=
  ProjectedObservations.image_eq_iff_necessary _ _ _ _

theorem Permitted.joint_projection_eq {granted : Set V}
    {old added : EquationStore (Term (signature S declarations) Γ sort)}
    {observed : List (Observation S declarations)} (permission : Permitted granted old added observed)
    (consistent : (ContextualFamilies.action declarations Γ sort).Consistent (old ++ added)) :
    (fun candidate : Assignment declarations future => jointView candidate observed) ''
        {candidate | ContextualFrameUnifier.Models candidate (old ++ added)} =
      (fun candidate : Assignment declarations future => jointView candidate observed) ''
        {candidate | ContextualFrameUnifier.Models candidate old} :=
  (joint_projection_iff_possible (old ++ added) old observed).mpr
    (fun question => permission.joint_possible_iff consistent question)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualBindingPermissions
