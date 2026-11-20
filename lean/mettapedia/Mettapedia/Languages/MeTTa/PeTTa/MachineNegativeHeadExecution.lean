import Mettapedia.Languages.MeTTa.PeTTa.MachineHeadSelectionApart
import Mettapedia.Languages.MeTTa.PeTTa.AtomNegativeSchematicReading

/-!
# Computed negative-frame head matches execute through the existing protocol

The complete stored row is one parameter of the read interface and the query
is its ambient argument. Head, body and repeated variables therefore remain
one correlated packet. The actual computed answer constructs the caller and
local reading; neither matching information solvability nor an admitted run
is supplied as a premise.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.MachineNegativeHeadExecution

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.Languages.MeTTa.SubstitutionAlgebra (subst)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MetaMeTTaComparison (atomAction)
open Mettapedia.Languages.MeTTa.PeTTa.UnifyingConstraintPresentation (presentation)
open RuleSyntax SchematicRows
open ListView
open Unifying (Idempotent)
open UnifyingDisequality (solved)
open AtomNegativeFreshNamespaces (Frame Hom X)
open AtomNegativeSchematicReads (Terms E closures)

theorem probe_ok {frame : Frame} {bindings answer : Subst} {source query : Atom} {retained : List Atom}
    (computed : MachineHeadSelectionApart.probe frame bindings source query retained = .ok answer) :
    MachineHeadSelectionApart.raw frame bindings source query retained = .ok answer ∧
      MachineHeadSelectionApart.apart frame answer = true := by
  unfold MachineHeadSelectionApart.probe at computed
  cases raw : MachineHeadSelectionApart.raw frame bindings source query retained with
  | clash | exhausted => simp [raw] at computed
  | ok candidate =>
      simp only [raw] at computed
      split at computed
      · rename_i separated
        cases computed
        exact ⟨rfl, separated⟩
      · cases computed

def data {R : Type*} (sources : R → Atom) (selected : R) : AtomNegativeSchematicReads.RowData :=
  ⟨[], [sources selected], sources selected⟩

def arguments {R : Type*} (query : Atom) (_ : R) : List Atom := [query]

def state {O : Type*} (frame : Frame) (bindings : Subst) (present : Finset O) (label : O → Atom) :
    RuleSyntax.State Terms O := ⟨frame, presentation bindings, present, label⟩

/-- State-level probes protect all ordinary retained rows, as well as the
query, incoming bindings and negative frame protected by the core probe. -/
noncomputable def probe {O : Type*} (frame : Frame) (bindings : Subst)
    (present : Finset O) (label : O → Atom) (source query : Atom) : Unifying.Unified :=
  MachineHeadSelectionApart.probe frame bindings source query
    (AtomFreshNamespaces.sourceTerms (presentation bindings) present label)

theorem computed_reading {frame : Frame} {bindings answer : Subst} {source query : Atom}
    {retained : List Atom}
    (valid : Idempotent bindings)
    (computed : MachineHeadSelectionApart.probe frame bindings source query retained = .ok answer) :
    ∃ (target : Frame) (caller : Hom frame target),
      caller.1 = solved answer ∧ X.Models caller (presentation bindings) ∧
        ((⟨[], [source], source⟩ : AtomNegativeSchematicReads.RowData).close frame [query]).ReadsAt X
          caller (subst (solved answer) query) := by
  obtain ⟨raw, compatible⟩ := probe_ok computed
  let separated := (MachineHeadSelectionApart.apart_iff frame answer).mp compatible
  let target := Disequality.image (solved answer) frame.1 separated
  let caller : Hom frame target := Disequality.toImage frame (solved answer) separated
  have positive := MachineClauseActivation.computed_reading PUnit.unit valid raw
  obtain ⟨localAssignment, _, _, output⟩ := positive
  let localPoint : Hom AtomNegativeSchematicReads.emptyFrame target :=
    ⟨localAssignment, by intro _ _ _ absent; cases absent⟩
  refine ⟨target, caller, rfl, MachineClauseActivation.computed_initial_model valid raw, localPoint, ?_, ?_, ?_⟩
  · intro _ absent
    cases absent
  · exact .cons output .nil
  · exact output

variable {O R : Type*} [DecidableEq O] [DecidableEq R]

/-- Every successful computed probe supplies an actual two-event read with
the computed query instance, retaining physical occurrences and schemas. -/
theorem computed_execution (frame : Frame) (bindings answer : Subst)
    (present : Finset O) (label : O → Atom) (rows : Finset R) (sources : R → Atom)
    (selected : R) (temporary output : O) (query : Atom)
    (ambient : Set (HeldReadEncoding.Code Terms))
    (available : Sum.inr (HeldReadGenericFirings.consumeRule
      (closures (state frame bindings present label) (data sources) (arguments query) selected).schema) ∈ ambient)
    (selectedPresent : selected ∈ rows) (outputFresh : output ∉ present)
    (temporaryFresh : temporary ∉ present) (different : temporary ≠ output)
    (valid : Idempotent bindings)
    (computed : probe frame bindings present label (sources selected) query = .ok answer) :
    ∃ (target : Frame) (run : (HeldReadGenericFirings.protocolMachine (E := E) (O := O) (R := R) X ambient).Run
        (HeldReadGenericSources.hosted (state frame bindings present label) rows
          (closures (state frame bindings present label) (data sources) (arguments query)))),
      run.word.length = 2 ∧ ∃ assignment : Hom run.last.frame target,
        X.Models assignment run.last.knowledge ∧
        X.act assignment (run.last.label output) = subst (solved answer) query ∧
        run.last.present = present ∪ {output} ∧ run.last.rules = rows ∧ temporary ∉ run.last.present := by
  obtain ⟨target, caller, _, known, reading⟩ := computed_reading valid computed
  obtain ⟨run, properties⟩ := AtomNegativeSchematicReading.execution_of_reading
    (state frame bindings present label) rows (data sources) (arguments query)
    selected temporary output ambient available selectedPresent outputFresh temporaryFresh different
    caller known _ reading
  exact ⟨target, run, properties⟩

end Mettapedia.Languages.MeTTa.PeTTa.MachineNegativeHeadExecution
