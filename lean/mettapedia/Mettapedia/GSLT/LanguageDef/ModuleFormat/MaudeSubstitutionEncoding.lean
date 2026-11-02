import Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeSortedBindings

/-! Instantiating a source term commutes with its compilation. Coverage is
explicit: the finite binding map must contain every variable of the term.
The statement permits open values and repeated source variables. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax Match

theorem encode_substitute_of_variables (bindings : Bindings) (assignment : Maude.Valuation)
    (term : Maude.Term)
    (agrees : ∀ name ∈ term.variables, applyBindings bindings (.fvar name) = encode (assignment name)) :
    applyBindings bindings (encode term) =
      encode (term.substitute assignment) := by
  revert agrees
  refine Maude.Term.rec
    (motive_1 := fun term =>
      (∀ name ∈ term.variables, applyBindings bindings (.fvar name) = encode (assignment name)) →
      applyBindings bindings (encode term) =
        encode (term.substitute assignment))
    (motive_2 := fun terms =>
      (∀ name ∈ terms.flatMap Maude.Term.variables, applyBindings bindings (.fvar name) = encode (assignment name)) →
      (terms.map encode).map (applyBindings bindings) =
        (terms.map (Maude.Term.substitute assignment)).map encode)
    ?_ ?_ ?_ ?_ term
  · intro name agrees
    simpa only [encode, Maude.Term.substitute] using
      agrees name (by simp [Maude.Term.variables])
  · intro id arguments ih agrees
    simp only [encode, applyBindings, Maude.Term.substitute]
    rw [ih (by simpa [Maude.Term.variables] using agrees)]
  · intro _
    rfl
  · intro first rest firstIH restIH agrees
    simp only [List.map_cons]
    rw [firstIH (fun name member => agrees name (List.mem_append_left _ member)),
      restIH (fun name member => agrees name (List.mem_append_right _ member))]

theorem encode_substitute (names : List String) (assignment : Maude.Valuation)
    (term : Maude.Term) (covered : ∀ name ∈ term.variables, name ∈ names) :
    applyBindings (assignmentBindings names assignment) (encode term) =
      encode (term.substitute assignment) :=
  encode_substitute_of_variables _ assignment term (fun name member =>
    assignmentBindings_apply names assignment (covered name member))

theorem typed_variables {signature : Maude.Signature} {declarations : Maude.VariableContext}
    {term : Maude.Term} {sort : String} (typed : Maude.HasSort signature declarations term sort) :
    ∀ name ∈ term.variables, name ∈ declarations.map Prod.fst := by
  refine Maude.HasSort.rec
    (motive_1 := fun term _ _ => ∀ name ∈ term.variables, name ∈ declarations.map Prod.fst)
    (motive_2 := fun terms _ _ =>
      ∀ name ∈ terms.flatMap Maude.Term.variables, name ∈ declarations.map Prod.fst)
    ?_ ?_ ?_ ?_ typed
  · intro name sort found used member
    have same : used = name := by simpa [Maude.Term.variables] using member
    subst used
    obtain ⟨before, after, shape, _⟩ := List.lookup_eq_some_iff.mp found
    simp [shape]
  · intro declaration arguments _ _ ih
    simpa only [Maude.Term.variables] using ih
  · intro name member
    cases member
  · intro first sort rest sorts _ _ firstIH restIH name member
    simp only [List.flatMap_cons, List.mem_append] at member
    exact member.elim (firstIH name) (restIH name)

theorem typed_instantiation_exact (prepared : Prepared)
    (ambient declarations : Maude.VariableContext) (assignment : Maude.Valuation)
    {term : Maude.Term} {sort : String}
    (schema : Maude.HasSort prepared.source.signature declarations term sort)
    (typed : Maude.TypedValuation prepared.source.signature ambient declarations assignment) :
    applyBindings (assignmentBindings (declarations.map Prod.fst) assignment) (encode term) =
        encode (term.substitute assignment) ∧
      WellSorted.HasType prepared.language (freeContext ambient) []
        (applyBindings (assignmentBindings (declarations.map Prod.fst) assignment) (encode term))
        (.base sort) := by
  have exactTerm := encode_substitute (declarations.map Prod.fst) assignment term (typed_variables schema)
  refine ⟨exactTerm, ?_⟩
  rw [exactTerm]
  exact (prepared_typing_iff prepared ambient _ sort).mpr
    (Maude.substitute_preserves_sort assignment typed schema)

end Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeCompilation
