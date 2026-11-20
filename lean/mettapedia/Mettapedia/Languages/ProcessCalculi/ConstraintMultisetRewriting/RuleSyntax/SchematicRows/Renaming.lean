import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.Schema

/-!
# Local renaming and directed schematic subsumption

Local renaming acts on a schema's value, parameters and local equations together;
ambient arguments are unchanged. A one-way instance map need not be invertible
and therefore gives inclusion of readings, not equality. These are syntactic
instance witnesses, not arbitrary behavioural equivalence or equality obtained
only after solving the caller's knowledge.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.Renaming

open Interface (Frames)

universe uO uT uH
variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  (X : Frames Tm Hom)

theorem schema_instantiate_id (row : Schema Tm) :
    row.instantiate X (X.id row.locals) = row := by
  cases row with
  | mk frame knowledge params value =>
    have identity : X.act (X.id frame) = id := funext fun term => X.act_id term
    simp [Schema.instantiate, Frames.applyStore_id, identity, X.act_id]

theorem readsAt_rename_iff {a middle target : Obj} (row : Closure Tm a)
    (forward : Hom row.schema.locals middle) (backward : Hom middle row.schema.locals)
    (undo : ∀ term, X.act backward (X.act forward term) = term)
    (σ : Hom a target) (value : Tm target) :
    (row.instantiate X forward).ReadsAt X σ value ↔ row.ReadsAt X σ value := by
  constructor
  · exact Closure.readsAt_of_instance X row forward σ value
  · rintro ⟨h, known, captures, output⟩
    dsimp only [Closure.ReadsAt, Closure.instantiate, Schema.instantiate]
    refine ⟨X.comp h backward, ?_, ?_, ?_⟩
    · apply (Frames.models_applyStore forward (X.comp h backward) row.schema.knowledge).mpr
      have same : ∀ term,
          X.act (X.comp (X.comp h backward) forward) term = X.act h term := by
        intro term
        rw [X.act_comp, X.act_comp, undo]
      exact (Frames.models_congr same row.schema.knowledge).mpr known
    · rw [List.forall₂_map_left_iff]
      simpa only [X.act_comp, undo] using captures
    · simpa only [X.act_comp, undo] using output

/-- One-way matching of the whole schema, with the captured interface fixed. -/
def Subsumes {a : Obj} (general specific : Closure Tm a) : Prop :=
  ∃ j : Hom general.schema.locals specific.schema.locals,
    specific.schema = general.schema.instantiate X j ∧ specific.args = general.args

theorem subsumes_refl {a : Obj} (row : Closure Tm a) : Subsumes X row row :=
  ⟨X.id row.schema.locals, (schema_instantiate_id X row.schema).symm, rfl⟩

theorem subsumes_reading {a target : Obj} {general specific : Closure Tm a}
    (subsumes : Subsumes X general specific) (σ : Hom a target) (value : Tm target)
    (reading : specific.ReadsAt X σ value) : general.ReadsAt X σ value := by
  obtain ⟨j, schema, arguments⟩ := subsumes
  have same : specific = general.instantiate X j :=
    congrArg₂ (fun body args => (⟨body, args⟩ : Closure Tm a)) schema arguments
  exact Closure.readsAt_of_instance X general j σ value (same ▸ reading)

#print axioms schema_instantiate_id
#print axioms readsAt_rename_iff
#print axioms subsumes_refl
#print axioms subsumes_reading

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.Renaming
