import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSchematicStorageControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NamedSpacesAuthority

/-!
# Private schema variables and explicit shared references

Ordinary storage and shared storage give different variable identities even
when their displayed variable numbers coincide. In the existing named-space
authority model, passing the same shared reference passes a channel through
which a later binding can communicate a name. Binding a fresh private copy
does not communicate that name to the holder of another reference.

The authority results concern reference identity and possession. They use
no resolved-location admission rule.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSchematicStorage

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Logic.LP (ScopedVar)

namespace Controls

theorem an_ordinary_schema_variable_is_not_the_callers_shared_reference (scope : Nat) :
    ContextualStoredRows.viewAt locals captures scope
        (ContextualStoredRows.store locals captures (generator locals 0)) ≠
      ContextualStoredRows.viewAt locals captures scope (.shared (generator captures 0)) := by
  rw [ContextualStoredRows.view_store,instantiate_generator]
  change generator active (.inl (ScopedVar.at scope 0)) ≠
    instantiate (ContextualSelectionViews.capturedTarget locals captures) (generator captures 0)
  rw [instantiate_generator]
  intro same
  have operators := (Term.op.inj same).1
  cases operators

end Controls

namespace Authority

open NamedSpaces
open NamedSpaces.Controls (Tm names spaces)

/-- A deliberately shared variable can carry any space name when bound. -/
theorem passing_a_shared_reference_passes_a_name_channel (reference name : Nat) :
    NoNameFor names [] {.var reference} name ∧
      Possesses names [(.var reference,.nm name)] {.var reference} name := by
  constructor
  · refine ⟨name + 1, by omega, indistinguishable_of_invariant ?_ ?_⟩
    · intro t member
      simp only [Set.mem_singleton_iff] at member
      subst t
      rfl
    · simp
  · refine resolved_name_possessed (s := .var reference) ⟨fun _ => .nm name, ?_⟩ (by simp) ?_
    · simp [SubstitutionAction.Solves,Tm.subst]
    · intro candidate solved
      simpa [SubstitutionAction.Solves,spaces,Tm.subst] using solved

/-- Binding the reader's private instance cannot send the name through a
different shared reference retained by the owner. -/
theorem binding_a_private_copy_gives_the_owner_no_name (privateReference ownerReference name : Nat)
    (apart : privateReference ≠ ownerReference) :
    NoNameFor names [(.var privateReference,.nm name)] {.var ownerReference} name := by
  refine ⟨name + 1, by omega, ?_⟩
  intro candidate solved
  refine ⟨fun i => if i = ownerReference then (candidate ownerReference).swap name (name + 1) else candidate i,
    ?_, ?_⟩
  · intro e member
    have same := List.mem_singleton.mp member
    subst e
    have prior := solved _ List.mem_cons_self
    simpa [SubstitutionAction.Solves,Tm.subst,apart] using prior
  · intro t member
    simp only [Set.mem_singleton_iff] at member
    subst t
    simp [Tm.subst,names]

end Authority
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSchematicStorage
