import Mettapedia.Languages.MeTTa.PeTTa.MachineNegativeHeadExecution

/-!
# Actual query-read admission is computed negative-frame matching

The direct firing's information contains the incoming bindings, the opened
stored row equated with the ambient query, and the copy equality. A model of
that information yields an independent separating source reading. Conversely,
the reading constructs the actual matching model through fresh openings.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.MachineNegativeHeadAdmission

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.Languages.MeTTa.SubstitutionAlgebra (subst)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MetaMeTTaComparison (atomAction)
open Mettapedia.Languages.MeTTa.PeTTa.UnifyingConstraintPresentation (presentation)
open RuleSyntax SchematicRows
open AtomNegativeFreshNamespaces (Frame Hom X)
open AtomNegativeSchematicReads (Terms E closures bound opening)
open MachineNegativeHeadExecution (data arguments state)

variable {O R : Type*} (frame : Frame) (bindings : Subst) (present : Finset O) (label : O → Atom)
  (rows : Finset R) (sources : R → Atom) (selected : R) (output : O) (query : Atom)

noncomputable def direct := AtomNegativeSchematicReads.direct (state frame bindings present label)
  rows (data sources) (arguments query) selected output

noncomputable def rowOpening (index : Nat) := opening frame
  (bound (state frame bindings present label) rows (data sources) (arguments query)) index

theorem information :
    (direct frame bindings present label rows sources selected output query).information X =
      presentation bindings ++
        [(X.act (rowOpening frame bindings present label rows sources query 1) (sources selected), query)] ++
        [(X.act (rowOpening frame bindings present label rows sources query 0) (sources selected),
          X.act (rowOpening frame bindings present label rows sources query 1) (sources selected))] := by
  have layout := HeldReadGenericFirings.direct_information (E := E) (state frame bindings present label) rows
    (closures (state frame bindings present label) (data sources) (arguments query)) selected PUnit.unit
    (rowOpening frame bindings present label rows sources query 0)
    (rowOpening frame bindings present label rows sources query 1) X output
  refine layout.trans ?_
  change (X.applyStore (X.id frame) (presentation bindings) ++ [] ++
      [(X.act (rowOpening frame bindings present label rows sources query 1) (sources selected),
        X.act (X.id frame) query)]) ++ _ = _
  rw [Interface.Frames.applyStore_id, X.act_id]
  simp only [List.append_nil]
  rfl

theorem reading_of_model {target : Frame} (point : Hom frame target)
    (solved : X.Models point
      ((direct frame bindings present label rows sources selected output query).information X)) :
    MachineHeadSelectionApart.Reading frame bindings (sources selected) query := by
  rw [information] at solved
  obtain ⟨first, _⟩ := (Interface.Frames.models_append point _ _).mp solved
  obtain ⟨known, matched⟩ := (Interface.Frames.models_append point _ _).mp first
  have rowMatch := matched _ (List.mem_singleton_self _)
  let localAssignment := atomAction.compose point.1
    (rowOpening frame bindings present label rows sources query 1).1
  refine ⟨point.1, known, Disequality.separates_hom point, localAssignment, ?_, ?_, ?_⟩
  · intro _ absent
    cases absent
  · exact .nil
  · change atomAction.apply localAssignment (sources selected) = atomAction.apply point.1 query
    rw [atomAction.apply_compose]
    exact rowMatch

theorem solvable_iff_reading (selectedPresent : selected ∈ rows) :
    X.Solvable (a := frame)
        ((direct frame bindings present label rows sources selected output query).information X) ↔
      MachineHeadSelectionApart.Reading frame bindings (sources selected) query := by
  constructor
  · rintro ⟨target, point, solved⟩
    exact reading_of_model frame bindings present label rows sources selected output query point solved
  · rintro ⟨callerAssignment, known, separated, localAssignment, _, _, value⟩
    let target := Disequality.image callerAssignment frame.1 separated
    let caller : Hom frame target := Disequality.toImage frame callerAssignment separated
    let localPoint : Hom AtomNegativeSchematicReads.emptyFrame target :=
      ⟨localAssignment, by intro _ _ _ absent; cases absent⟩
    have reading : (closures (state frame bindings present label) (data sources) (arguments query) selected).ReadsAt
        X caller (subst callerAssignment query) := by
      refine ⟨localPoint, ?_, .cons value .nil, value⟩
      intro _ absent
      cases absent
    obtain ⟨point, model, _, _⟩ := AtomNegativeSchematicReading.direct_model_of_reading
      (state frame bindings present label) rows (data sources) (arguments query)
      selected output caller selectedPresent known _ reading
    exact ⟨target, point, model⟩

variable [DecidableEq O] [DecidableEq R]

/-- With an available row and a fresh result occurrence, the actual firing
admits exactly the computed source matches, including retained disequations. -/
theorem admits_iff_computed (selectedPresent : selected ∈ rows) (outputFresh : output ∉ present)
    (valid : Unifying.Idempotent bindings) :
    (direct frame bindings present label rows sources selected output query).Admits X ↔
      MachineHeadSelection.accepted
        (MachineNegativeHeadExecution.probe frame bindings present label (sources selected) query) = true := by
  rw [MachineNegativeHeadExecution.probe,
    MachineHeadSelectionApart.probe_iff_reading frame bindings _ query valid
      (AtomFreshNamespaces.sourceTerms (presentation bindings) present label),
    ← solvable_iff_reading frame bindings present label rows sources selected output query selectedPresent]
  constructor
  · intro admitted
    exact admitted.2.2.1
  · intro solvable
    refine ⟨HeldReadGenericFirings.direct_shapes (E := E) X (state frame bindings present label) rows
        (closures (state frame bindings present label) (data sources) (arguments query)) selected PUnit.unit
        (rowOpening frame bindings present label rows sources query 0)
        (rowOpening frame bindings present label rows sources query 1) output
        (AtomNegativeSchematicReads.direct_fresh (state frame bindings present label) rows
          (data sources) (arguments query) selected output) rfl,
      HeldReadGenericFirings.direct_enabled (E := E) (state frame bindings present label) rows
        (closures (state frame bindings present label) (data sources) (arguments query)) selected PUnit.unit
        (rowOpening frame bindings present label rows sources query 0)
        (rowOpening frame bindings present label rows sources query 1) output selectedPresent outputFresh,
      solvable, ?_⟩
    intro target assignment _
    exact HeldReadGenericFirings.direct_holds (E := E) X (state frame bindings present label) rows
      (closures (state frame bindings present label) (data sources) (arguments query)) selected PUnit.unit
      (rowOpening frame bindings present label rows sources query 0)
      (rowOpening frame bindings present label rows sources query 1) output assignment

end Mettapedia.Languages.MeTTa.PeTTa.MachineNegativeHeadAdmission
