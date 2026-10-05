import Mettapedia.Languages.MM0.Kernel.AdmissibleSubstitution

/-!
# Typing under MM0 simultaneous substitution

Argument typing suffices to preserve expression sorts and residual argument
lists. The stronger dependency admission is required by theorem application;
it must not be inferred merely from this typing theorem.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Kernel

theorem Substitution.typed_lookup {signature : TermSignature} {formal target : Context}
    {expressions : List Preterm}
    (typed : List.Forall₂ (Preterm.FitsBinder signature target) expressions formal)
    {index : Nat} {binder : Binder} {expression : Preterm}
    (formalLookup : formal[index]? = some binder)
    (imageLookup : expressions[index]? = some expression) :
    Preterm.FitsBinder signature target expression binder := by
  apply List.forall₂_zip typed
  exact List.mem_of_getElem? (List.getElem?_zip_eq_some.mpr ⟨imageLookup, formalLookup⟩)

namespace Preterm

theorem FitsBinder.hasType {signature : TermSignature} {context : Context}
    {expression : Preterm} {binder : Binder} (fits : FitsBinder signature context expression binder) :
    HasType signature context expression [] binder.sort := by
  cases fits with
  | bound lookup => exact .var lookup
  | regular typing => exact typing

theorem HasType.substitute {signature : TermSignature} {formal target remaining : Context}
    {expressions : List Preterm} {source result : Preterm} {sort : Nat}
    (typing : HasType signature formal source remaining sort)
    (typed : List.Forall₂ (FitsBinder signature target) expressions formal)
    (substituted : Substitutes (Substitution.ofList expressions) source result) :
    HasType signature target result remaining sort := by
  induction typing generalizing result with
  | var lookup =>
      cases substituted with
      | var image => exact (Substitution.typed_lookup typed lookup image).hasType
  | term lookup =>
      cases substituted
      exact .term lookup
  | bound _ lookup ih =>
      cases substituted with
      | app functionSubstitution argumentSubstitution =>
          cases argumentSubstitution with
          | var image =>
              have fits := Substitution.typed_lookup typed lookup image
              cases fits with
              | bound targetLookup => exact .bound (ih functionSubstitution) targetLookup
  | regular _ _ ihFunction ihArgument =>
      cases substituted with
      | app functionSubstitution argumentSubstitution =>
          exact .regular (ihFunction functionSubstitution) (ihArgument argumentSubstitution)

end Preterm

namespace Substitution

theorem instantiate_preserves_type {signature : TermSignature} {formal target remaining : Context}
    {expressions : List Preterm} {body result : Preterm} {sort : Nat}
    (typing : Preterm.HasType signature formal body remaining sort)
    (computed : instantiate signature formal target expressions body = some result) :
    Preterm.HasType signature target result remaining sort := by
  obtain ⟨admitted, substituted⟩ := (instantiate_eq_some_iff _ _ _ _ _ _).mp computed
  exact typing.substitute admitted.typed substituted

theorem Admissible.instantiate_typed {signature : TermSignature} {formal target remaining : Context}
    {expressions : List Preterm} (admitted : Admissible signature formal target expressions)
    {body : Preterm} {sort : Nat} (typing : Preterm.HasType signature formal body remaining sort) :
    ∃ result, instantiate signature formal target expressions body = some result ∧
      Preterm.HasType signature target result remaining sort := by
  obtain ⟨result, computed⟩ := admitted.instantiate_defined typing
  exact ⟨result, computed, instantiate_preserves_type typing computed⟩

end Substitution

end Mettapedia.Languages.MM0.Kernel
