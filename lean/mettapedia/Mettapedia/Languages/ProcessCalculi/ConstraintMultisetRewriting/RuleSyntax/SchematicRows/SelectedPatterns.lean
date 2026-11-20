import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ReadModels

/-!
# Actual read patterns have the selected schema readings

The matching equations in a firing's information identify each opened pattern
with its selected value. Together with local-opening soundness, this gives
the reading of the original pattern, preserving shared captures. It does not
infer admission or query truth from a successful local match.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows

open Interface (Frames)

universe uO uT uH uE uOcc
variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}

theorem Row.readsAt_value_trans (X : Frames Tm Hom) {a b : Obj} (row : Row Tm a)
    (source : Hom a b) {first second : Tm b} (reading : row.ReadsAt X source first)
    (same : X.E first second) : row.ReadsAt X source second := by
  cases row with
  | shared term => exact (X.equivalence b).trans reading same
  | schematic closure =>
    obtain ⟨locals, known, captures, output⟩ := reading
    exact ⟨locals, known, captures, (X.equivalence b).trans output same⟩

namespace Firing

variable (X : Frames Tm Hom) {O : Type uOcc} {E : Extensions.{uO, uH, uE} Hom}
  {P : Set (Rule Tm)} {s : State Tm O} (f : Firing O E P s)

theorem read_pattern_readings {b : Obj} (assignment : Hom (E.target f.ext) b)
    (solved : X.Models assignment (f.information X)) (shapes : f.Shapes X) :
    List.Forall₂ (fun pattern selected =>
      Row.ReadsAt X (X.comp assignment (E.weaken f.ext))
        (X.act assignment (X.act f.opening pattern)) selected.1)
      f.rule.basic.body.read f.readUses := by
  apply List.forall₂_iff_zip.mpr
  refine ⟨?_, ?_⟩
  · simpa only [readUses, List.length_ofFn] using shapes.2.2.2.2.1
  · intro pattern selected member
    have equationMember : (X.act f.opening pattern, RowUse.value X (E.weaken f.ext) selected.2) ∈
        (f.rule.basic.body.read.map (X.act f.opening)).zip (f.readValues X) := by
      change _ ∈ (f.rule.basic.body.read.map (X.act f.opening)).zip
        (f.readUses.map (fun use => RowUse.value X (E.weaken f.ext) use.2))
      rw [List.zip_map]
      exact List.mem_map_of_mem member
    have equation := solved _ (List.mem_append_left _ (List.mem_append_right _ equationMember))
    have selectedMember : selected ∈ f.uses :=
      List.mem_append_right _ (List.of_mem_zip member).2
    exact Row.readsAt_value_trans X selected.1 (X.comp assignment (E.weaken f.ext))
      (f.selected_reading X assignment solved shapes selected selectedMember) ((X.equivalence b).symm equation)

end Firing

#print axioms Row.readsAt_value_trans
#print axioms Firing.read_pattern_readings

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows
