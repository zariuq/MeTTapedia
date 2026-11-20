import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.DataViews

/-! # Caller models compose with actual stored-data views -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.State

open Interface (Frames)

universe uO uT uH uOcc
variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH} {O : Type uOcc}

theorem dataAt_model_reading_iff (X : Frames Tm Hom) {b c : Obj} (s : State Tm O)
    (point : Hom s.frame b) (source : Hom b c) (value : Tm c) :
    (∃ row ∈ s.dataAt X point, row.ReadsAt X source value) ↔
      ∃ o ∈ s.present, (s.label o).ReadsAt X (X.comp source point) value := by
  constructor
  · rintro ⟨row, member, reading⟩
    obtain ⟨o, present, rfl⟩ := (mem_dataAt X s point row).mp member
    exact ⟨o, present, (Row.readsAt_act_iff X point source value (s.label o)).mp reading⟩
  · rintro ⟨o, present, reading⟩
    exact ⟨(s.label o).act X point, (mem_dataAt X s point _).mpr ⟨o, present, rfl⟩,
      (Row.readsAt_act_iff X point source value (s.label o)).mpr reading⟩

#print axioms dataAt_model_reading_iff

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.State
