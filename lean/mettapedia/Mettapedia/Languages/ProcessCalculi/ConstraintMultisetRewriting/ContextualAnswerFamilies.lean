import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPublication

/-!
# Separate answer families share a private bank without sharing variables

An answer's helper names are tagged by its answer index. Packing preserves
the complete instance set of that answer, including in later declaration
frames. Unused arities of other answers receive fresh formal generators in
an extension; no arbitrary inhabitant of their interfaces is assumed.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualAnswerFamilies

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualGuardMatching

variable {S : Signature} {Index : Type} (Variables : Index → Type)
    (declarations : ∀ index, Variables index → MetaArity S)

abbrev Names := (index : Index) × Variables index
abbrev family : Names Variables → MetaArity S := fun name => declarations name.1 name.2

def inclusion (index : Index) : Assignment (declarations index) (family Variables declarations) :=
  fun name => generator (family Variables declarations) ⟨index, name⟩

def pack (index : Index) {Γ : Ctx S} {sort : S.Srt}
    (value : Term (signature S (declarations index)) Γ sort) :=
  instantiate (inclusion Variables declarations index) value

theorem instantiate_pack {Future : Type} {future : Future → MetaArity S}
    (images : Assignment (family Variables declarations) future) (index : Index)
    {Γ : Ctx S} {sort : S.Srt} (value : Term (signature S (declarations index)) Γ sort) :
    instantiate images (pack Variables declarations index value) =
      instantiate (fun name => images ⟨index, name⟩) value := by
  rw [pack, instantiate_comp]
  apply congrArg (fun assignment => instantiate assignment value)
  funext name
  exact instantiate_generator images ⟨index, name⟩

variable [DecidableEq Index]

theorem instances_pack_iff {Next : Type} (next : Next → MetaArity S) (index : Index)
    {Γ : Ctx S} {sort : S.Srt} (value : Term (signature S (declarations index)) Γ sort)
    (pattern : Term (signature S next) Γ sort) :
    ContextualPublication.Instances (family Variables declarations) (pack Variables declarations index value) next pattern ↔
      ContextualPublication.Instances (declarations index) value next pattern := by
  constructor
  · rintro ⟨extension, images, same⟩
    refine ⟨extension, (fun name => images ⟨index, name⟩), ?_⟩
    exact (instantiate_pack Variables declarations images index value).symm.trans same
  · rintro ⟨extension, images, same⟩
    let added := Extension.withLocals (family Variables declarations) extension.declarations
    let images' : Assignment (family Variables declarations) added.declarations := fun ⟨origin, name⟩ =>
      if equal : origin = index then by
        subst origin
        exact instantiate added.assignment (images name)
      else generator added.declarations (.inl ⟨origin, name⟩)
    refine ⟨extension.trans added, images', ?_⟩
    erw [instantiate_pack]
    have mapped := congrArg (instantiate added.assignment) same
    have imageEq : (fun name => images' ⟨index, name⟩) = Assignment.compose added.assignment images := by
      funext name
      dsimp only [images', Assignment.compose]
      exact if_pos rfl
    rw [imageEq]
    exact (Assignment.instantiate_compose added.assignment images value).trans
      (mapped.trans (by
        rw [Extension.trans_assignment]
        exact (Assignment.instantiate_compose added.assignment extension.assignment pattern).symm))

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualAnswerFamilies
