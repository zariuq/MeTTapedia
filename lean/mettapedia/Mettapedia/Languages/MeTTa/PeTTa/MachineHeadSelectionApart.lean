import Mettapedia.Languages.MeTTa.PeTTa.MachineHeadSelection
import Mettapedia.Languages.MeTTa.PeTTa.AtomNegativeFreshNamespaces

/-!
# Snapshot probes retain negative information

Fresh support includes both sides of every retained disequation, even when
those names occur in neither the query nor its positive bindings. A successful
principal answer is checked against the whole negative frame before selection.
Exhaustion remains unfinished work. This module joins the computed probe to
the existing disequation-frame solvability law and captured-row reading.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.MachineHeadSelectionApart

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.Languages.MeTTa.SubstitutionAlgebra (subst)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MetaMeTTaComparison (atomAction)
open Mettapedia.Languages.MeTTa.PeTTa.UnifyingConstraintPresentation (presentation)
open RuleSyntax OneFrame SchematicRows
open ListView Unifying UnifyingDisequality
open AtomFreshNamespaces (X)
open MachineClauseActivation (packet closure)

def support (frame : Disequality.Frame atomAction) (bindings : Subst) (query : Atom)
    (retained : List Atom := []) : List Atom :=
  AtomNegativeFreshNamespaces.support frame (retained ++ MachineClauseActivation.support bindings query [])

def scope (frame : Disequality.Frame atomAction) (bindings : Subst) (query : Atom)
    (retained : List Atom := []) : Nat :=
  AtomNegativeFreshNamespaces.bound frame (retained ++ MachineClauseActivation.support bindings query [])

theorem query_bounded (frame : Disequality.Frame atomAction) (bindings : Subst) (query : Atom)
    (retained : List Atom := []) :
    AtomFreshNamespaces.Bounded (scope frame bindings query retained) (packet query []) := by
  apply AtomNegativeFreshNamespaces.protected_bounded
  exact List.mem_append_right _ (by simp [MachineClauseActivation.support])

theorem bindings_bounded (frame : Disequality.Frame atomAction) (bindings : Subst) (query : Atom)
    (equation : Atom × Atom) (member : equation ∈ presentation bindings) (retained : List Atom := []) :
    AtomFreshNamespaces.Bounded (scope frame bindings query retained) equation.1 ∧
      AtomFreshNamespaces.Bounded (scope frame bindings query retained) equation.2 := by
  constructor
  · apply AtomNegativeFreshNamespaces.protected_bounded
    exact List.mem_append_right _
      (List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_map_of_mem member)))
  · apply AtomNegativeFreshNamespaces.protected_bounded
    exact List.mem_append_right _
      (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_map_of_mem member)))

theorem frame_bounded (frame : Disequality.Frame atomAction) (bindings : Subst) (query : Atom)
    (equation : Atom × Atom) (member : equation ∈ frame.1) (retained : List Atom := []) :
    AtomFreshNamespaces.Bounded (scope frame bindings query retained) equation.1 ∧
      AtomFreshNamespaces.Bounded (scope frame bindings query retained) equation.2 :=
  AtomNegativeFreshNamespaces.frame_bounded frame _ equation member

theorem retained_bounded (frame : Disequality.Frame atomAction) (bindings : Subst) (query : Atom)
    (retained : List Atom) (term : Atom) (member : term ∈ retained) :
    AtomFreshNamespaces.Bounded (scope frame bindings query retained) term :=
  AtomNegativeFreshNamespaces.protected_bounded frame _ term (List.mem_append_left _ member)

def apart (frame : Disequality.Frame atomAction) (bindings : Subst) : Bool :=
  frame.1.all fun equation => decide (resolve bindings equation.1 ≠ resolve bindings equation.2)

theorem apart_iff (frame : Disequality.Frame atomAction) (bindings : Subst) :
    apart frame bindings = true ↔ Disequality.Separates atomAction (solved bindings) frame.1 := by
  simp only [apart, List.all_eq_true, decide_eq_true_eq, Disequality.Separates]
  constructor
  · intro separated equation member
    change atomAction.apply (solved bindings) equation.1 ≠
      atomAction.apply (solved bindings) equation.2
    rw [solved_apply, solved_apply]
    exact separated equation member
  · intro separated equation member
    have distinct := separated equation member
    change atomAction.apply (solved bindings) equation.1 ≠
      atomAction.apply (solved bindings) equation.2 at distinct
    simpa only [solved_apply] using distinct

def opened (frame : Disequality.Frame atomAction) (bindings : Subst) (source query : Atom)
    (retained : List Atom := []) : Atom :=
  LibTransformStep.rename (scope frame bindings query retained) (packet source [])

def raw (frame : Disequality.Frame atomAction) (bindings : Subst) (source query : Atom)
    (retained : List Atom := []) : Unified :=
  unifyBinding bindings (GSLTBindingPatterns.quoted (opened frame bindings source query retained))
    (packet query [])

def probe (frame : Disequality.Frame atomAction) (bindings : Subst) (source query : Atom)
    (retained : List Atom := []) : Unified :=
  match raw frame bindings source query retained with
  | .ok answer => if apart frame answer then .ok answer else .clash
  | .clash => .clash
  | .exhausted => .exhausted

theorem unfinished_preserved (frame : Disequality.Frame atomAction) (bindings : Subst)
    (source query : Atom) (retained : List Atom := []) :
    MachineHeadSelection.unfinished (probe frame bindings source query retained) =
      MachineHeadSelection.unfinished (raw frame bindings source query retained) := by
  cases computed : raw frame bindings source query retained with
  | clash | exhausted => simp [probe, computed, MachineHeadSelection.unfinished]
  | ok answer =>
      simp only [probe, computed]
      split <;> rfl

def Reading (frame : Disequality.Frame atomAction) (bindings : Subst) (source query : Atom) : Prop :=
  ∃ caller : StepSubstitution, atomAction.Models caller (presentation bindings) ∧
    Disequality.Separates atomAction caller frame.1 ∧
      (closure PUnit.unit source [] []).ReadsAt X (b := PUnit.unit) caller (subst caller query)

theorem raw_reading (frame : Disequality.Frame atomAction) {bindings answer : Subst}
    {source query : Atom} {retained : List Atom} (valid : Idempotent bindings)
    (computed : raw frame bindings source query retained = .ok answer)
    (separated : apart frame answer = true) : Reading frame bindings source query := by
  refine ⟨solved answer, MachineClauseActivation.computed_initial_model valid computed,
    (apart_iff frame answer).mp separated, ?_⟩
  exact MachineClauseActivation.computed_reading PUnit.unit valid computed

theorem reading_has_raw_answer (frame : Disequality.Frame atomAction) (bindings : Subst)
    (source query : Atom) (valid : Idempotent bindings) (reading : Reading frame bindings source query)
    (retained : List Atom := []) :
    ∃ answer, raw frame bindings source query retained = .ok answer := by
  obtain ⟨caller, known, _, closureReading⟩ := reading
  exact (MachineClauseActivation.accepts_iff_reading (scope := scope frame bindings query retained)
    (source := source) (query := query) (parameters := []) (arguments := []) PUnit.unit valid
      (fun equation member => bindings_bounded frame bindings query equation member retained)
      (query_bounded frame bindings query retained)).mpr
    ⟨caller, known, closureReading⟩

theorem reading_solvable (frame : Disequality.Frame atomAction) (bindings : Subst)
    (source query : Atom) (reading : Reading frame bindings source query) (retained : List Atom := []) :
    (Disequality.frames atomAction).Solvable (a := frame)
      (presentation bindings ++ [(opened frame bindings source query retained, packet query [])]) := by
  obtain ⟨caller, known, separated, localAssignment, _, _, output⟩ := reading
  let fresh := scope frame bindings query retained
  let combined := AtomNegativeFreshNamespaces.combine (retained ++ MachineClauseActivation.support bindings query [])
    (Disequality.toImage frame caller separated) (fun _ => localAssignment)
  let assignment := combined.1
  have keep (term : Atom) (bounded : AtomFreshNamespaces.Bounded fresh term) :
      subst assignment term = subst caller term :=
    AtomFreshNamespaces.source_agrees fresh caller (fun _ => localAssignment) term bounded
  apply (Disequality.solvable_iff _).mpr
  refine ⟨assignment, ?_, ?_⟩
  · apply (atomAction.models_append _ _ _).mpr
    constructor
    · intro equation member
      change subst assignment equation.1 = subst assignment equation.2
      rw [keep _ (bindings_bounded frame bindings query equation member retained).1,
        keep _ (bindings_bounded frame bindings query equation member retained).2]
      exact known equation member
    · intro equation member
      obtain rfl := List.mem_singleton.mp member
      change subst assignment (opened frame bindings source query retained) = subst assignment (packet query [])
      have instantiated := AtomNegativeFreshNamespaces.combine_opening
        (retained ++ MachineClauseActivation.support bindings query [])
        (Disequality.toImage frame caller separated) (fun _ => localAssignment) 0 (packet source [])
      change subst assignment (subst (AtomFreshNamespaces.opening fresh 0) (packet source [])) =
        subst localAssignment (packet source []) at instantiated
      simp only [AtomFreshNamespaces.opening, Nat.add_zero, LibTransformStep.subst_tagging] at instantiated
      rw [show opened frame bindings source query retained = LibTransformStep.rename fresh (packet source [])
          from rfl, instantiated, keep _ (query_bounded frame bindings query retained)]
      rw [MachineClauseActivation.subst_packet, MachineClauseActivation.subst_packet]
      exact congrArg (fun value => packet value []) output
  · exact Disequality.separates_hom combined

theorem probe_iff_reading (frame : Disequality.Frame atomAction) (bindings : Subst)
    (source query : Atom) (valid : Idempotent bindings) (retained : List Atom := []) :
    MachineHeadSelection.accepted (probe frame bindings source query retained) = true ↔
      Reading frame bindings source query := by
  constructor
  · intro accepted
    unfold probe at accepted
    cases computed : raw frame bindings source query retained with
    | clash | exhausted => simp [computed, MachineHeadSelection.accepted] at accepted
    | ok answer =>
        simp only [computed] at accepted
        split at accepted
        · rename_i separated
          exact raw_reading frame valid computed separated
        · simp [MachineHeadSelection.accepted] at accepted
  · intro reading
    obtain ⟨answer, computed⟩ := reading_has_raw_answer frame bindings source query valid reading retained
    have compatible := (quoted_frame_solvable frame valid computed).mp
      (reading_solvable frame bindings source query reading retained)
    have check := (apart_iff frame answer).mpr compatible
    simp [probe, computed, check, MachineHeadSelection.accepted]

def snapshot (frame : Disequality.Frame atomAction) (bindings : Subst) (query : Atom)
    (rows : List Atom) (retained : List Atom := []) : MachineHeadSelection.Scan rows.length :=
  MachineHeadSelection.scan (fun position => probe frame bindings rows[position] query retained)

theorem snapshot_pending_preserved (frame : Disequality.Frame atomAction) (bindings : Subst)
    (query : Atom) (rows : List Atom) (retained : List Atom := []) :
    (snapshot frame bindings query rows retained).pending =
      (MachineHeadSelection.scan (fun position : Fin rows.length =>
        raw frame bindings rows[position] query retained)).pending := by
  change (List.finRange rows.length).filter _ = (List.finRange rows.length).filter _
  congr 1
  funext position
  exact unfinished_preserved frame bindings rows[position] query retained

theorem snapshot_exact (frame : Disequality.Frame atomAction) (bindings : Subst) (query : Atom)
    (rows : List Atom) (valid : Idempotent bindings) (position : Fin rows.length) (retained : List Atom := []) :
    position ∈ (snapshot frame bindings query rows retained).matched ↔
      Reading frame bindings rows[position] query := by
  rw [snapshot, MachineHeadSelection.mem_matched, probe_iff_reading frame bindings _ query valid retained]

theorem snapshot_unique_iff (frame : Disequality.Frame atomAction) (bindings : Subst) (query : Atom)
    (rows : List Atom) (valid : Idempotent bindings) (position : Fin rows.length) {retained : List Atom}
    (settled : (snapshot frame bindings query rows retained).pending = []) :
    MachineHeadSelection.verdict (snapshot frame bindings query rows retained) = .unique position ↔
      Reading frame bindings rows[position] query ∧
        ∀ other : Fin rows.length, Reading frame bindings rows[other] query → other = position := by
  rw [snapshot, MachineHeadSelection.unique_iff_one_accepted _ position settled]
  simp only [probe_iff_reading frame bindings _ query valid retained]

end Mettapedia.Languages.MeTTa.PeTTa.MachineHeadSelectionApart
