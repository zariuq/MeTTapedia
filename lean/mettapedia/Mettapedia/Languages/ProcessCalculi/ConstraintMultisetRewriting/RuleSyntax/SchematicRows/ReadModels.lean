import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.Step

/-!
# Actual selected row openings denote valid readings

A model of a firing's information supplies the private model and all capture
equations of each selected schematic datum. Reading soundness is proved from
these equations, not assumed as part of admission. Freshness remains the
separate condition needed for the converse realization of independent uses.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows

open Interface (Frames)

universe uO uT uH uE uOcc
variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}

namespace RowUse

theorem reading_of_models (X : Frames Tm Hom) {a target b : Obj} (weaken : Hom a target)
    {row : Row Tm a} (use : RowUse Tm Hom target row) (wellFormed : row.WellFormed)
    (σ : Hom target b) (solved : X.Models σ (use.information X weaken)) :
    Row.ReadsAt X (X.comp σ weaken) (X.act σ (use.value X weaken)) row := by
  cases use with
  | shared term =>
    change X.E (X.act (X.comp σ weaken) term) (X.act σ (X.act weaken term))
    rw [X.act_comp]
    exact (X.equivalence b).refl _
  | schematic closure opening =>
    change closure.schema.params.length = closure.args.length at wellFormed
    obtain ⟨localKnowledge, captureEquations⟩ := (Frames.models_append _ _ _).mp solved
    refine ⟨X.comp σ opening,
      (Frames.models_applyStore opening σ closure.schema.knowledge).mp localKnowledge, ?_, ?_⟩
    · have captures : List.Forall₂ (fun parameter argument => X.E (X.act σ parameter) (X.act σ argument))
          (closure.schema.params.map (X.act opening)) (closure.args.map (X.act weaken)) := by
        apply List.forall₂_iff_zip.mpr
        refine ⟨?_, ?_⟩
        · simpa only [List.length_map] using wellFormed
        · intro parameter argument member
          exact captureEquations (parameter, argument) member
      rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff] at captures
      simpa only [X.act_comp] using captures
    · rw [X.act_comp]
      exact (X.equivalence b).refl _

end RowUse

namespace Firing

variable (X : Frames Tm Hom) {O : Type uOcc} {E : Extensions.{uO, uH, uE} Hom}
  {P : Set (Rule Tm)} {s : State Tm O} (f : Firing O E P s)

theorem selected_information_models {b : Obj} (σ : Hom (E.target f.ext) b)
    (solved : X.Models σ (f.information X))
    (selected : PackedUse Tm Hom s.frame (E.target f.ext)) (member : selected ∈ f.uses) :
    X.Models σ (selected.2.information X (E.weaken f.ext)) := by
  intro equation inside
  have selectedEquation : equation ∈ f.uses.flatMap
      (fun use => RowUse.information X (E.weaken f.ext) use.2) :=
    List.mem_flatMap.mpr ⟨selected, member, inside⟩
  exact solved equation (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_append_right _ selectedEquation))))

theorem selected_reading {b : Obj} (σ : Hom (E.target f.ext) b)
    (solved : X.Models σ (f.information X)) (shapes : f.Shapes X)
    (selected : PackedUse Tm Hom s.frame (E.target f.ext)) (member : selected ∈ f.uses) :
    Row.ReadsAt X (X.comp σ (E.weaken f.ext))
      (X.act σ (selected.2.value X (E.weaken f.ext))) selected.1 :=
  RowUse.reading_of_models X (E.weaken f.ext) selected.2
    (shapes.2.2.2.2.2.2.2.1 selected member) σ
    (f.selected_information_models X σ solved selected member)

end Firing

#print axioms RowUse.reading_of_models
#print axioms Firing.selected_information_models
#print axioms Firing.selected_reading

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows
