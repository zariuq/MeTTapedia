import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualRowOrigins

/-!
# Pure stored outputs do not automatically export returned declarations

Including a source term references only source names, also beneath binders
and in metavariable argument spines. Actual endpoint transport preserves
that origin. This concerns the stored payload before applying an answer;
resolution may reference declarations used by that answer.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualFrameUpdate

namespace ContextualComputedFreshFrame

variable {S : Signature} {V : Type} {source : V → MetaArity S}

theorem included_support_has_source_origin {problem : ContextualResidual.Problem source} (update : Update problem)
    {Γ : Ctx S} {sort : S.Srt} (value : Term (signature S source) Γ sort)
    (name : V ⊕ (update.Variables ⊕ Empty))
    (present : name ∈ support (instantiate (includeSource update) value)) :
    ∃ original : V, name = .inl original := by
  have bounded : Bounded (fun name : V ⊕ (update.Variables ⊕ Empty) => ∃ original : V, name = .inl original)
      (instantiate (includeSource update) value) := by
    apply bounded_instantiate
    intro original _member name member
    rw [ContextualFreshFrameScopeLedger.includeSource_image, support_generator] at member
    exact ⟨original, List.mem_singleton.mp member⟩
  exact bounded name present

theorem returned_name_not_in_included_support {problem : ContextualResidual.Problem source} (update : Update problem)
    {Γ : Ctx S} {sort : S.Srt} (value : Term (signature S source) Γ sort) (name : update.Variables) :
    Sum.inr (Sum.inl name) ∉ support (instantiate (includeSource update) value) := by
  intro present
  obtain ⟨original, impossible⟩ := included_support_has_source_origin update value _ present
  cases impossible

end ContextualComputedFreshFrame

namespace ContextualExecution.Firing

variable {S : Signature} {Local O : Type} {locals : Local → MetaArity S}
  [DecidableEq O] [DecidableEq Local] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]
  {Γ : Ctx S} {sort : S.Srt} {before after : Endpoint locals O Γ sort}

omit [DecidableEq O] [DecidableEq Local] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
private theorem bounded_castMetaBody {V : Type} {declaration : V → MetaArity S}
    (allowed : V → Prop) {first second : MetaArity S} (same : first = second)
    (body : Term (signature S declaration) first.1 first.2) (bounded : Bounded allowed body) :
    Bounded allowed (castMetaBody (V := signature S declaration) same body) := by
  cases same
  exact bounded

theorem output_support_has_source_origin (firing : Firing locals before after)
    (value : Term (signature S (ContextualActivatedStep.target locals before.declarations)) Γ sort)
    (name : after.Names) (present : name ∈ support (instantiate firing.outputAssignment value)) :
    ∃ original : Mettapedia.Logic.LP.ScopedVar Local ⊕ before.Names,
      name = Endpoint.namesEquiv firing.destination.symm (Sum.inl original) := by
  let allowed : after.Names → Prop := fun name =>
    ∃ original : Mettapedia.Logic.LP.ScopedVar Local ⊕ before.Names,
      name = Endpoint.namesEquiv firing.destination.symm (Sum.inl original)
  let relocation : Assignment
      (ContextualComputedFreshFrame.active (ContextualActivatedStep.target locals before.declarations)
        firing.update.declaration) after.declarations :=
    (Endpoint.equalityExtension firing.destination.symm).assignment
  have bounded : Bounded allowed (instantiate firing.outputAssignment value) := by
    change Bounded allowed
      (instantiate (Assignment.compose relocation (ContextualComputedFreshFrame.includeSource firing.update)) value)
    rw [Assignment.instantiate_compose]
    apply bounded_instantiate
    intro intermediate member
    obtain ⟨original, rfl⟩ := ContextualComputedFreshFrame.included_support_has_source_origin firing.update value intermediate member
    change Bounded allowed (castMetaBody (V := signature S after.declarations)
      (Endpoint.namesEquiv_preserves firing.destination.symm (Sum.inl original))
      (generator after.declarations (Endpoint.namesEquiv firing.destination.symm (Sum.inl original))))
    apply bounded_castMetaBody
    intro name member
    rw [support_generator] at member
    obtain rfl := List.mem_singleton.mp member
    exact ⟨original, rfl⟩
  exact bounded name present

theorem returned_name_not_in_stored_output_support (firing : Firing locals before after)
    (value : Term (signature S (ContextualActivatedStep.target locals before.declarations)) Γ sort)
    (name : firing.update.Variables) :
    Endpoint.namesEquiv firing.destination.symm (Sum.inr (Sum.inl name)) ∉
      support (instantiate firing.outputAssignment value) := by
  intro present
  obtain ⟨original, same⟩ := firing.output_support_has_source_origin value _ present
  have impossible := (Endpoint.namesEquiv firing.destination.symm).injective same
  cases impossible

end ContextualExecution.Firing
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
