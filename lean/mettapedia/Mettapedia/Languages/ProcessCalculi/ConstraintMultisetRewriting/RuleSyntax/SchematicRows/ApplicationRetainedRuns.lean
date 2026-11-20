import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationStoreLaws
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationSupport

/-!
# Earlier data remain available through actual application runs

Occurrences are retained, their readings commute with the composed settlement,
and every transported source-context term remains protected. Consequently a
run preserving the entry interpretation also preserves all its hypotheses.
These are the transport laws needed to join separately derived premises in
one execution, rather than pretending that unrelated singleton runs compose.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationMachine

open Mettapedia.Logic.LP
open Presentation.Schematic (Tm rowSig)
open ApplicationSemantics (hypotheses)

universe uOcc
variable {judgmentTag arrowTag : Nat} {O : Type uOcc} [DecidableEq O] {s : Store O}

theorem run_present_mono (run : (machine judgmentTag arrowTag O).Run s) :
    s.present ⊆ run.last.present := by
  induction run with
  | nil _ => exact fun _ present => present
  | cons f admitted rest ih => exact (f.present_mono admitted).trans ih

theorem run_context_transport (run : (machine judgmentTag arrowTag O).Run s) :
    ∀ term ∈ context s, run.toLast.applyTerm term ∈ context run.last := by
  induction run with
  | nil source =>
    intro term inside
    change (Subst.id rowSig).applyTerm term ∈ context source
    rwa [Subst.applyTerm_id]
  | cons f admitted rest ih =>
    intro term inside
    have later := ih (f.answer.applyTerm term) (f.context_transport admitted term inside)
    change (rest.toLast.comp f.answer).applyTerm term ∈ context rest.last
    rw [Subst.applyTerm_comp]
    exact later

theorem run_retained_reading_iff (run : (machine judgmentTag arrowTag O).Run s) :
    ∀ o ∈ s.present, ∀ source : Subst rowSig, ∀ value : Tm,
      (run.last.label o).ReadsAt X (b := PUnit.unit) source value ↔
        (s.label o).ReadsAt X (b := PUnit.unit) (source.comp run.toLast) value := by
  induction run with
  | nil initial =>
    intro o _ source value
    change (initial.label o).ReadsAt X (b := PUnit.unit) source value ↔
      (initial.label o).ReadsAt X (b := PUnit.unit) (source.comp (Subst.id rowSig)) value
    rw [Subst.comp_id_right]
  | @cons initial f admitted rest ih =>
    intro o present source value
    have later := ih o (f.present_mono admitted present) source value
    have first := f.retained_reading_iff admitted o present (source.comp rest.toLast) value
    change (rest.last.label o).ReadsAt X (b := PUnit.unit) source value ↔
      (f.result.label o).ReadsAt X (b := PUnit.unit) (source.comp rest.toLast) value at later
    change (rest.last.label o).ReadsAt X (b := PUnit.unit) source value ↔
      (initial.label o).ReadsAt X (b := PUnit.unit) (source.comp (rest.toLast.comp f.answer)) value
    rw [Subst.comp_assoc] at first
    exact later.trans first

theorem run_preserves_hypotheses (run : (machine judgmentTag arrowTag O).Run s)
    (caller source : Subst rowSig)
    (agrees : ∀ term ∈ context s, source.applyTerm (run.toLast.applyTerm term) = caller.applyTerm term)
    (value : Tm)
    (assumed : value ∈ hypotheses (s.dataAt X (b := PUnit.unit) (Subst.id rowSig)) caller) :
    value ∈ hypotheses (run.last.dataAt X (b := PUnit.unit) (Subst.id rowSig)) source := by
  obtain ⟨o, present, reading⟩ := (State.dataAt_model_reading_iff X
    (b := PUnit.unit) (c := PUnit.unit) s (Subst.id rowSig) caller value).mp assumed
  change (s.label o).ReadsAt X (b := PUnit.unit) (caller.comp (Subst.id rowSig)) value at reading
  rw [Subst.comp_id_right] at reading
  have same : ∀ term ∈ (s.label o).ambientTerms,
      caller.applyTerm term = (source.comp run.toLast).applyTerm term := by
    intro term inside
    rw [Subst.applyTerm_comp]
    exact (agrees term (ambient_in_context s o present term inside)).symm
  have changed := (Row.readsAt_source_congr X (a := s.frame) (b := PUnit.unit) (s.label o)
    caller (source.comp run.toLast) same value).mp reading
  apply (State.dataAt_model_reading_iff X (b := PUnit.unit) (c := PUnit.unit)
    run.last (Subst.id rowSig) source value).mpr
  refine ⟨o, run_present_mono run present, ?_⟩
  change (run.last.label o).ReadsAt X (b := PUnit.unit) (source.comp (Subst.id rowSig)) value
  rw [Subst.comp_id_right]
  exact (run_retained_reading_iff run o present source value).mpr changed

#print axioms run_present_mono
#print axioms run_context_transport
#print axioms run_retained_reading_iff
#print axioms run_preserves_hypotheses

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationMachine
