import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.Substitution

/-!
# Stored data viewed after a change of source frame

The view lists actual present occurrences and transports only their ambient
parts. Private schema code is unchanged. The reading equivalence preserves the
caller point explicitly; the list is not a set or a deduplication operation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows

open Interface (Frames)

universe uO uT uH uOcc
variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}

theorem Row.readsAt_identity_view (X : Frames Tm Hom) {a b : Obj} (row : Row Tm a)
    (point : Hom a b) (value : Tm b) :
    (row.act X point).ReadsAt X (X.id b) value ↔ row.ReadsAt X point value := by
  refine (Row.readsAt_act_iff X point (X.id b) value row).trans ?_
  apply Row.readsAt_source_congr
  intro term _
  rw [X.act_comp, X.act_id]
  exact (X.equivalence b).refl _

namespace State

variable {O : Type uOcc}

noncomputable def dataAt (X : Frames Tm Hom) {b : Obj} (s : State Tm O) (point : Hom s.frame b) :
    List (Row Tm b) := s.present.toList.map (fun o => (s.label o).act X point)

theorem mem_dataAt (X : Frames Tm Hom) {b : Obj} (s : State Tm O) (point : Hom s.frame b)
    (row : Row Tm b) : row ∈ s.dataAt X point ↔ ∃ o ∈ s.present, row = (s.label o).act X point := by
  classical
  simp only [dataAt, List.mem_map, Finset.mem_toList]
  exact exists_congr fun o => and_congr_right fun _ => eq_comm

theorem dataAt_reading_iff (X : Frames Tm Hom) {b : Obj} (s : State Tm O)
    (point : Hom s.frame b) (value : Tm b) :
    (∃ row ∈ s.dataAt X point, row.ReadsAt X (X.id b) value) ↔
      ∃ o ∈ s.present, (s.label o).ReadsAt X point value := by
  constructor
  · rintro ⟨row, member, reading⟩
    obtain ⟨o, present, rfl⟩ := (mem_dataAt X s point row).mp member
    exact ⟨o, present, (Row.readsAt_identity_view X (s.label o) point value).mp reading⟩
  · rintro ⟨o, present, reading⟩
    exact ⟨(s.label o).act X point, (mem_dataAt X s point _).mpr ⟨o, present, rfl⟩,
      (Row.readsAt_identity_view X (s.label o) point value).mpr reading⟩

theorem dataAt_term (X : Frames Tm Hom) {b : Obj} (s : State Tm O) (point : Hom s.frame b)
    (row : Row Tm b) (member : row ∈ s.dataAt X point) (term : Tm b)
    (inside : term ∈ row.ambientTerms) : term ∈ s.ambientTerms.map (X.act point) := by
  classical
  obtain ⟨o, present, rfl⟩ := (mem_dataAt X s point row).mp member
  rw [Row.ambientTerms_act] at inside
  obtain ⟨original, argument, rfl⟩ := List.mem_map.mp inside
  exact List.mem_map_of_mem (List.mem_flatMap.mpr
    ⟨o, Finset.mem_toList.mpr present, argument⟩)

end State

#print axioms Row.readsAt_identity_view
#print axioms State.mem_dataAt
#print axioms State.dataAt_reading_iff
#print axioms State.dataAt_term

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows
