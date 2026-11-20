import Mettapedia.Languages.MeTTa.PeTTa.AtomNegativeSchematicReads

/-!
# Independent captured readings construct the negative-frame protocol model

The caller and row assignments are supplied by the independent closure-reading
judgment. Constructed freshness combines them into a morphism satisfying the
actual direct firing's matching information. The existing two-event protocol
then executes that read while retaining the caller's negative frame.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.AtomNegativeSchematicReading

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open RuleSyntax SchematicRows HeldReadGenericSources
open AtomNegativeFreshNamespaces (Frame Hom X)
open AtomNegativeSchematicReads (Terms E closures bound opening direct direct_fresh consume)

variable {O R : Type*} (ordinary : RuleSyntax.State Terms O) (rows : Finset R)
  (data : R → AtomNegativeSchematicReads.RowData) (arguments : R → List Atom)

theorem direct_model_of_reading (selected : R) (output : O) {target : Frame}
    (caller : Hom ordinary.frame target) (present : selected ∈ rows)
    (known : X.Models caller ordinary.knowledge) (value : Atom)
    (reading : (closures ordinary data arguments selected).ReadsAt X caller value) :
    ∃ assignment : Hom ordinary.frame target,
      X.Models assignment ((direct ordinary rows data arguments selected output).information X) ∧
      (∀ term, (mixed ordinary rows (closures ordinary data arguments)).scope.Mentions term →
        X.act assignment term = X.act caller term) ∧
      X.act assignment (X.act (opening ordinary.frame (bound ordinary rows data arguments) 0)
        (closures ordinary data arguments selected).schema.value) = value := by
  obtain ⟨localAssignment, localKnown, captures, result⟩ := reading
  have independent := direct_fresh ordinary rows data arguments selected output target caller
  obtain ⟨assignment, together⟩ := independent localAssignment localAssignment
  change Hom ordinary.frame target at assignment
  have kept (term : Atom)
      (mentioned : (mixed ordinary rows (closures ordinary data arguments)).scope.Mentions term) :
      X.act assignment term = X.act caller term := by
    have actual := together.1.1 term mentioned
    change X.act assignment (X.act (X.id ordinary.frame) term) = X.act caller term at actual
    simpa only [X.act_id] using actual
  have copied := together.1.2 (closures ordinary data arguments selected).schema.value
    (by
      change (closures ordinary data arguments selected).schema.value ∈
        (HeldReadGenericFirings.copyRule (closures ordinary data arguments selected).schema).terms
      simp [HeldReadGenericFirings.copyRule, Rule.terms])
  have materialized := together.2 (closures ordinary data arguments selected).schema.value
    (by simp [RowUse.scopeRule, Rule.terms])
  refine ⟨assignment, ?_, kept, copied.trans result⟩
  unfold direct
  rw [HeldReadGenericFirings.direct_information (E := E) ordinary rows
      (closures ordinary data arguments) selected PUnit.unit
      (opening ordinary.frame (bound ordinary rows data arguments) 0)
      (opening ordinary.frame (bound ordinary rows data arguments) 1) X output,
    Interface.Frames.models_append]
  refine ⟨?_, ?_⟩
  · unfold HeldReadGenericFirings.datumInformation
    rw [Interface.Frames.models_append, Interface.Frames.models_append]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro equation inside
      obtain ⟨original, member, rfl⟩ := List.mem_map.mp inside
      have left := kept original.1 (Or.inl (List.mem_map_of_mem member))
      have right := kept original.2 (Or.inr (Or.inl (List.mem_map_of_mem member)))
      change X.act assignment (X.act (X.id ordinary.frame) original.1) =
        X.act assignment (X.act (X.id ordinary.frame) original.2)
      rw [X.act_id, X.act_id, left, right]
      exact known original member
    · intro equation inside
      obtain ⟨original, member, rfl⟩ := List.mem_map.mp inside
      have left := together.2 original.1
        (by simp [RowUse.scopeRule, Rule.terms, List.mem_map_of_mem member])
      have right := together.2 original.2
        (by simp [RowUse.scopeRule, Rule.terms, List.mem_map_of_mem member])
      exact left.trans ((localKnown original member).trans right.symm)
    · intro equation inside
      have aligned : List.Forall₂
          (fun parameter argument => X.E (a := target) (X.act assignment parameter) (X.act assignment argument))
          ((closures ordinary data arguments selected).schema.params.map
            (X.act (opening ordinary.frame (bound ordinary rows data arguments) 1)))
          ((closures ordinary data arguments selected).args.map (X.act (X.id ordinary.frame))) := by
        rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
        apply List.forall₂_iff_zip.mpr
        refine ⟨captures.length_eq, ?_⟩
        intro parameter argument paired
        have parameterInside := (List.of_mem_zip paired).1
        have argumentInside := (List.of_mem_zip paired).2
        have parameterRead := together.2 parameter
          (by simp [RowUse.scopeRule, Rule.terms, parameterInside])
        have argumentRead := kept argument
          ((HeldReadGenericSources.scope_mentions_iff ordinary rows
            (closures ordinary data arguments) argument).mpr
              (Or.inr ⟨selected, present, argumentInside⟩))
        have capture := List.forall₂_zip captures paired
        change X.act assignment
            (X.act (opening ordinary.frame (bound ordinary rows data arguments) 1) parameter) =
          X.act assignment (X.act (X.id ordinary.frame) argument)
        rw [X.act_id]
        exact parameterRead.trans (capture.trans argumentRead.symm)
      exact List.forall₂_zip aligned inside
  · intro equation inside
    obtain rfl := List.mem_singleton.mp inside
    exact copied.trans materialized.symm

variable [DecidableEq O] [DecidableEq R]

/-- The independently given reading constructs both the matching model and
the two protocol events. A resulting frame morphism interprets the final
knowledge and value; no admitted execution is supplied as a premise. -/
theorem execution_of_reading (selected : R) (temporary output : O) {target : Frame}
    (ambient : Set (HeldReadEncoding.Code Terms))
    (available : Sum.inr (HeldReadGenericFirings.consumeRule
      (closures ordinary data arguments selected).schema) ∈ ambient)
    (present : selected ∈ rows) (outputFresh : output ∉ ordinary.present)
    (temporaryFresh : temporary ∉ ordinary.present) (different : temporary ≠ output)
    (caller : Hom ordinary.frame target) (known : X.Models caller ordinary.knowledge) (value : Atom)
    (reading : (closures ordinary data arguments selected).ReadsAt X caller value) :
    ∃ run : (HeldReadGenericFirings.protocolMachine (E := E) (O := O) (R := R) X ambient).Run
        (hosted ordinary rows (closures ordinary data arguments)),
      run.word.length = 2 ∧ ∃ assignment : Hom run.last.frame target,
        X.Models assignment run.last.knowledge ∧ X.act assignment (run.last.label output) = value ∧
        run.last.present = ordinary.present ∪ {output} ∧ run.last.rules = rows ∧
          temporary ∉ run.last.present := by
  obtain ⟨assignment, solved, _, outputValue⟩ := direct_model_of_reading ordinary rows data arguments
    selected output caller present known value reading
  obtain ⟨run, length, last, presentAfter, rulesAfter, privateAbsent⟩ :=
    AtomNegativeSchematicReads.execution_of_solvable ordinary rows data arguments
      selected temporary output ambient available (Closure.wellFormed_of_readsAt X _ caller reading)
      present outputFresh temporaryFresh different ⟨target, assignment, solved⟩
  have finalModels : X.Models assignment
      ((consume ordinary rows data arguments selected temporary output).result X).knowledge := by
    change X.Models assignment
      ((consume ordinary rows data arguments selected temporary output).information X)
    unfold consume
    rw [HeldReadGenericFirings.information_eq (E := E) X ordinary rows
      (closures ordinary data arguments) selected PUnit.unit
      (opening ordinary.frame (bound ordinary rows data arguments) 0)
      (opening ordinary.frame (bound ordinary rows data arguments) 1) temporary output]
    exact solved
  have finalValue : X.act assignment
      (((consume ordinary rows data arguments selected temporary output).result X).label output) = value := by
    unfold consume
    rw [HeldReadGenericFirings.consumer_output_label (E := E) X ordinary rows
      (closures ordinary data arguments) selected PUnit.unit
      (opening ordinary.frame (bound ordinary rows data arguments) 0)
      (opening ordinary.frame (bound ordinary rows data arguments) 1) temporary output]
    exact outputValue
  refine ⟨run, length, ?_⟩
  rw [last] at presentAfter rulesAfter privateAbsent ⊢
  exact ⟨assignment, finalModels, finalValue, presentAfter, rulesAfter, privateAbsent⟩

end Mettapedia.Languages.MeTTa.PeTTa.AtomNegativeSchematicReading
