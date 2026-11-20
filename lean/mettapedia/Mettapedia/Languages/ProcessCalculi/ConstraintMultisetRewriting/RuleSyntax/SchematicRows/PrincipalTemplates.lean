import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.Schema

/-!
# Principal preparation of a schema's private equations

A principal solution can be computed before activating a stored schema.
Preparation transports its value and the entire parameter vector together,
keeps ambient arguments unchanged, and removes the solved private equations.
Every reading at every caller point is preserved.

The statement concerns a prepared view. It does not identify raw code keys,
origins, occurrence identities or fixed-extension freshness requirements.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.PrincipalTemplates

open Interface (Frames)

universe uO uT uH
variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}

def prepare (X : Frames Tm Hom) {a m : Obj} (row : Closure Tm a)
    (answer : Hom row.schema.locals m) : Closure Tm a :=
  ⟨⟨m, [], row.schema.params.map (X.act answer), X.act answer row.schema.value⟩, row.args⟩

theorem wellFormed_iff (X : Frames Tm Hom) {a m : Obj} (row : Closure Tm a)
    (answer : Hom row.schema.locals m) : (prepare X row answer).WellFormed ↔ row.WellFormed := by
  simp only [prepare, Closure.WellFormed, List.length_map]

theorem readsAt_iff (X : Frames Tm Hom) {a m b : Obj} (row : Closure Tm a)
    (answer : Hom row.schema.locals m) (principal : X.Principal row.schema.knowledge answer)
    (source : Hom a b) (value : Tm b) :
    (prepare X row answer).ReadsAt X source value ↔ row.ReadsAt X source value := by
  constructor
  · intro reading
    dsimp only [prepare, Closure.ReadsAt] at reading
    obtain ⟨residual, _, captures, output⟩ := reading
    refine ⟨X.comp residual answer, Frames.models_comp principal.sound residual, ?_, ?_⟩
    · rw [List.forall₂_map_left_iff] at captures
      simpa only [X.act_comp] using captures
    · simpa only [X.act_comp] using output
  · rintro ⟨locals, solved, captures, output⟩
    obtain ⟨residual, factors⟩ := principal.factors b locals solved
    dsimp only [prepare, Closure.ReadsAt]
    refine ⟨residual, Frames.models_nil _, ?_, ?_⟩
    · apply List.forall₂_map_left_iff.mpr
      apply captures.imp
      intro parameter argument same
      have factor : X.E (X.act locals parameter) (X.act residual (X.act answer parameter)) := by
        simpa only [X.act_comp] using factors parameter
      exact (X.equivalence b).trans ((X.equivalence b).symm factor) same
    · have factor : X.E (X.act locals row.schema.value)
          (X.act residual (X.act answer row.schema.value)) := by
        simpa only [X.act_comp] using factors row.schema.value
      exact (X.equivalence b).trans ((X.equivalence b).symm factor) output

theorem arguments_unchanged (X : Frames Tm Hom) {a m : Obj} (row : Closure Tm a)
    (answer : Hom row.schema.locals m) : (prepare X row answer).args = row.args := rfl

theorem private_knowledge_empty (X : Frames Tm Hom) {a m : Obj} (row : Closure Tm a)
    (answer : Hom row.schema.locals m) : (prepare X row answer).schema.knowledge = [] := rfl

#print axioms wellFormed_iff
#print axioms readsAt_iff
#print axioms arguments_unchanged
#print axioms private_knowledge_empty

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.PrincipalTemplates
