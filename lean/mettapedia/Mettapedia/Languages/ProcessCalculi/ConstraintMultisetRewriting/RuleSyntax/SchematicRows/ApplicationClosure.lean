import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationCompleteness

/-!
# Actual application closure equals DTL derivability

The operational observer collects readings from finite actual runs preserving
the entry interpretation. This is not a terminal-state, chronological or
multiplicity observer. Derivation completeness constructs the run; run
soundness and source-interface transport prove the converse.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationMachine

open Mettapedia.Logic.LP
open Presentation.Schematic (Tm rowSig)
open ApplicationSemantics (Derives)

universe uOcc
variable {judgmentTag arrowTag : Nat} {O : Type uOcc} [DecidableEq O]

def operationalClosure (judgmentTag arrowTag : Nat) (s : Store O) (caller : Subst rowSig) : Set Tm :=
  {value | ∃ execution : ProtectedRun judgmentTag arrowTag s caller,
    ∃ o ∈ execution.run.last.present,
      (execution.run.last.label o).ReadsAt X (b := PUnit.unit) execution.source value}

theorem operational_closure_sound (s : Store O) (caller : Subst rowSig) (value : Tm)
    (member : value ∈ operationalClosure judgmentTag arrowTag s caller) :
    Derives judgmentTag arrowTag (s.dataAt X (b := PUnit.unit) (Subst.id rowSig)) caller value := by
  obtain ⟨execution, o, present, reading⟩ := member
  have derived := run_reading_sound execution.run execution.source o present value reading
  apply Derives.source_congr judgmentTag arrowTag
    (s.dataAt X (b := PUnit.unit) (Subst.id rowSig)) (execution.source.comp execution.run.toLast) caller ?_ derived
  intro row inside term mentioned
  obtain ⟨original, inContext, transformed⟩ := List.mem_map.mp
    (context_covers_data (s := s) (Subst.id rowSig) row inside term mentioned)
  have same : original = term := (Subst.applyTerm_id original).symm.trans transformed
  change (execution.source.comp execution.run.toLast).applyTerm term = caller.applyTerm term
  rw [← same, Subst.applyTerm_comp]
  exact execution.agrees original inContext

variable [Infinite O]

theorem operational_closure_iff_derives (s : Store O) (caller : Subst rowSig)
    (known : X.Models (a := PUnit.unit) (b := PUnit.unit) caller s.knowledge) (value : Tm) :
    value ∈ operationalClosure judgmentTag arrowTag s caller ↔
      Derives judgmentTag arrowTag (s.dataAt X (b := PUnit.unit) (Subst.id rowSig)) caller value :=
  ⟨operational_closure_sound s caller value, fun derivation => derives_realized s caller known derivation⟩

theorem operational_forward_closure (s : Store O) (caller : Subst rowSig)
    (known : X.Models (a := PUnit.unit) (b := PUnit.unit) caller s.knowledge) :
    operationalClosure judgmentTag arrowTag s caller = ApplicationSemantics.forwardClosure
      judgmentTag arrowTag (s.dataAt X (b := PUnit.unit) (Subst.id rowSig)) caller := by
  ext value
  exact (operational_closure_iff_derives s caller known value).trans
    (ApplicationSemantics.forward_closure_iff_derives judgmentTag arrowTag _ caller value).symm

theorem empty_knowledge_forward_closure (s : Store O) (empty : s.knowledge = []) (caller : Subst rowSig) :
    operationalClosure judgmentTag arrowTag s caller = ApplicationSemantics.forwardClosure
      judgmentTag arrowTag (s.dataAt X (b := PUnit.unit) (Subst.id rowSig)) caller := by
  apply operational_forward_closure s caller
  rw [empty]
  exact Interface.Frames.models_nil (X := X) (a := PUnit.unit) (b := PUnit.unit) caller

#print axioms operational_closure_sound
#print axioms operational_closure_iff_derives
#print axioms operational_forward_closure
#print axioms empty_knowledge_forward_closure

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationMachine
