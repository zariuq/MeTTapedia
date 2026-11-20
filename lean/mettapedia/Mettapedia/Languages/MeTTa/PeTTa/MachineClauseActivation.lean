import Mettapedia.Languages.MeTTa.PeTTa.MachineClauseReads
import Mettapedia.Languages.MeTTa.PeTTa.AtomSchematicReads

/-!
# Computed matching answers realize captured schematic rows

One joint Atom packet contains the row and every captured parameter. Successful
quoted matching supplies the actual solved substitution, including the incoming
bindings. That answer constructs a reading of the existing row closure and an
actual held-read execution. The packet's variable correlations and arity are
checked by the same unifier; independent field matches are not substituted.

This connects the model's computed unifier to the schematic read protocol. It
does not assert that the C runtime implements either side of that model.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.MachineClauseActivation

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.Languages.MeTTa.SubstitutionAlgebra (subst)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MetaMeTTaComparison (atomAction)
open Mettapedia.Languages.MeTTa.PeTTa.UnifyingConstraintPresentation (presentation)
open RuleSyntax OneFrame SchematicRows
open ListView Unifying UnifyingDisequality
open AtomFreshNamespaces (X E)

def packet (value : Atom) (parameters : List Atom) : Atom := .expression (value :: parameters)

theorem subst_list (assignment : StepSubstitution) : ∀ terms : List Atom,
    subst.substList assignment terms = terms.map (subst assignment)
  | [] => rfl
  | first :: rest => by simp only [subst.substList, List.map_cons, subst_list assignment rest]

theorem subst_packet (assignment : StepSubstitution) (value : Atom) (parameters : List Atom) :
    subst assignment (packet value parameters) =
      packet (subst assignment value) (parameters.map (subst assignment)) := by
  simp [packet, subst, subst.substList, subst_list]

theorem rename_packet (scope : Nat) (value : Atom) (parameters : List Atom) :
    LibTransformStep.rename scope (packet value parameters) =
      packet (LibTransformStep.rename scope value) (parameters.map (LibTransformStep.rename scope)) := by
  simp only [packet, LibTransformStep.rename, LibTransformStep.rename.renameList]
  congr 2
  induction parameters with
  | nil => rfl
  | cons first rest ih => simp only [LibTransformStep.rename.renameList, List.map_cons, ih]

/-- Parameters and ambient arguments have distinct scopes even if they use
the same written variable name. Their correspondence is supplied at activation. -/
def closure (ambient : PUnit.{1}) (value : Atom) (parameters arguments : List Atom) :
    Closure (Terms Atom) ambient :=
  ⟨⟨PUnit.unit, [], parameters, value⟩, arguments⟩

variable {bindings bound : Subst} {scope : Nat} {source query : Atom}
  {parameters arguments : List Atom}

theorem computed_reading (ambient : PUnit.{1}) (valid : Idempotent bindings)
    (unified : unifyBinding bindings
      (GSLTBindingPatterns.quoted (LibTransformStep.rename scope (packet source parameters)))
      (packet query arguments) = .ok bound) :
    (closure ambient source parameters arguments).ReadsAt X (b := PUnit.unit) (solved bound)
      (subst (solved bound) query) := by
  have principal := quoted_principal valid unified
  have equation := principal.sound
    (LibTransformStep.rename scope (packet source parameters), packet query arguments)
    (List.mem_append_right _ (List.mem_singleton_self _))
  change subst (solved bound) (LibTransformStep.rename scope (packet source parameters)) =
    subst (solved bound) (packet query arguments) at equation
  rw [rename_packet, subst_packet, subst_packet] at equation
  have fields := Atom.expression.inj equation
  have same := List.cons.inj fields
  let localAssignment := atomAction.compose (solved bound) (LibTransformStep.tagging scope)
  have local_apply (term : Atom) :
      subst localAssignment term = subst (solved bound) (LibTransformStep.rename scope term) := by
    change atomAction.apply (atomAction.compose (solved bound) (LibTransformStep.tagging scope)) term = _
    rw [atomAction.apply_compose]
    change subst (solved bound) (subst (LibTransformStep.tagging scope) term) = _
    rw [LibTransformStep.subst_tagging]
  refine ⟨localAssignment, ?_, ?_, ?_⟩
  · intro _ absent
    cases absent
  · change List.Forall₂ (fun parameter argument =>
      subst localAssignment parameter = subst (solved bound) argument) parameters arguments
    simp only [local_apply]
    have aligned : List.Forall₂ Eq
        ((parameters.map (LibTransformStep.rename scope)).map (subst (solved bound)))
        (arguments.map (subst (solved bound))) := by
      rw [List.forall₂_eq_eq_eq]
      exact same.2
    simpa only [List.forall₂_map_left_iff, List.forall₂_map_right_iff] using aligned
  · change subst localAssignment source = subst (solved bound) query
    exact (local_apply source).trans same.1

theorem computed_initial_model (valid : Idempotent bindings)
    (unified : unifyBinding bindings
      (GSLTBindingPatterns.quoted (LibTransformStep.rename scope (packet source parameters)))
      (packet query arguments) = .ok bound) :
    atomAction.Models (solved bound) (presentation bindings) :=
  ((atomAction.models_append _ _ _).mp (quoted_principal valid unified).sound).1

/-- The fresh joint packet loses no closure reading. Freshness is a finite
syntactic support condition, not an assumed successful solver result. -/
theorem accepts_iff_reading (ambient : PUnit.{1}) (valid : Idempotent bindings)
    (knownBelow : ∀ equation ∈ presentation bindings,
      AtomFreshNamespaces.Bounded scope equation.1 ∧ AtomFreshNamespaces.Bounded scope equation.2)
    (queryBelow : AtomFreshNamespaces.Bounded scope (packet query arguments)) :
    (∃ bound, unifyBinding bindings
      (GSLTBindingPatterns.quoted (LibTransformStep.rename scope (packet source parameters)))
      (packet query arguments) = .ok bound) ↔
    ∃ caller : StepSubstitution, atomAction.Models caller (presentation bindings) ∧
      (closure ambient source parameters arguments).ReadsAt X (b := PUnit.unit) caller
        (subst caller query) := by
  constructor
  · rintro ⟨bound, unified⟩
    exact ⟨solved bound, computed_initial_model valid unified, computed_reading ambient valid unified⟩
  · rintro ⟨caller, known, localAssignment, _, captures, output⟩
    let assignment := AtomFreshNamespaces.combine scope caller (fun _ => localAssignment)
    have keep (term : Atom) (below : AtomFreshNamespaces.Bounded scope term) :
        subst assignment term = subst caller term :=
      AtomFreshNamespaces.source_agrees scope caller (fun _ => localAssignment) term below
    have keptKnowledge : atomAction.Models assignment (presentation bindings) := by
      intro equation member
      change subst assignment equation.1 = subst assignment equation.2
      rw [keep _ (knownBelow equation member).1, keep _ (knownBelow equation member).2]
      exact known equation member
    have correlation :
        (parameters.map (subst localAssignment)) = arguments.map (subst caller) := by
      rw [← List.forall₂_eq_eq_eq, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
      exact captures
    have packetEquation : subst assignment (LibTransformStep.rename scope (packet source parameters)) =
        subst assignment (packet query arguments) := by
      have instantiated := AtomFreshNamespaces.combine_opening scope caller (fun _ => localAssignment)
        0 (packet source parameters)
      simp only [AtomFreshNamespaces.opening, Nat.add_zero, LibTransformStep.subst_tagging] at instantiated
      rw [instantiated, keep _ queryBelow, subst_packet, subst_packet]
      exact congrArg₂ packet output correlation
    apply (GSLTBindingPatterns.quoted_accepts_iff bindings _ _ valid).mpr
    refine ⟨valuation assignment, (models_iff assignment _).mp keptKnowledge, ?_⟩
    change PatternHolds (valuation assignment)
      (GSLTDataPatterns.encode "cons" (LibTransformStep.rename scope (packet source parameters)))
      (packet query arguments)
    rw [GSLTDataPatterns.patternHolds_iff]
    simpa only [← step_apply, atomAction] using packetEquation

def support (bindings : Subst) (query : Atom) (arguments : List Atom) : List Atom :=
  packet query arguments :: (presentation bindings).map Prod.fst ++ (presentation bindings).map Prod.snd

def freshScope (bindings : Subst) (query : Atom) (arguments : List Atom) : Nat :=
  AtomFreshNamespaces.supportBound (support bindings query arguments)

/-- The support bound computes the freshness side conditions. No name class,
groundness requirement or user-supplied solver certificate is imposed. -/
theorem fresh_accepts_iff_reading (ambient : PUnit.{1}) (valid : Idempotent bindings) :
    (∃ bound, unifyBinding bindings
      (GSLTBindingPatterns.quoted (LibTransformStep.rename (freshScope bindings query arguments)
        (packet source parameters))) (packet query arguments) = .ok bound) ↔
    ∃ caller : StepSubstitution, atomAction.Models caller (presentation bindings) ∧
      (closure ambient source parameters arguments).ReadsAt X (b := PUnit.unit) caller
        (subst caller query) := by
  apply accepts_iff_reading ambient valid
  · intro equation member
    constructor
    · apply AtomFreshNamespaces.bounded_of_mem (terms := support bindings query arguments)
      exact List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_map_of_mem member))
    · apply AtomFreshNamespaces.bounded_of_mem (terms := support bindings query arguments)
      exact List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_map_of_mem member))
  · exact AtomFreshNamespaces.bounded_of_mem (terms := support bindings query arguments)
      (List.mem_cons_self)

variable {O R : Type*} [DecidableEq O] [DecidableEq R]
  (ordinary : RuleSyntax.State (Terms Atom) O) (rows : Finset R)
  (closures : R → Closure (Terms Atom) ordinary.frame)

/-- A successful computed packet produces an actual execution, with no
pre-assumed closure-reading or admitted-run witness. -/
theorem computed_execution (selected : R) (temporary output : O)
    (ambient : Set (HeldReadEncoding.Code (Terms Atom)))
    (available : Sum.inr (HeldReadGenericFirings.consumeRule (closures selected).schema) ∈ ambient)
    (present : selected ∈ rows) (outputFresh : output ∉ ordinary.present)
    (temporaryFresh : temporary ∉ ordinary.present) (different : temporary ≠ output)
    (sourceKnowledge : ordinary.knowledge = presentation bindings)
    (selectedClosure : closures selected = closure ordinary.frame source parameters arguments)
    (valid : Idempotent bindings)
    (unified : unifyBinding bindings
      (GSLTBindingPatterns.quoted (LibTransformStep.rename scope (packet source parameters)))
      (packet query arguments) = .ok bound) :
    ∃ (run : (HeldReadGenericFirings.protocolMachine (E := E) (O := O) (R := R) X ambient).Run
        (HeldReadGenericSources.hosted ordinary rows closures)) (assignment : StepSubstitution),
      run.word.length = 2 ∧ X.Models (b := PUnit.unit) assignment run.last.knowledge ∧
      subst assignment (run.last.label output) = subst (solved bound) query ∧
      run.last.present = ordinary.present ∪ {output} ∧ run.last.rules = rows ∧
        temporary ∉ run.last.present := by
  apply AtomSchematicReads.execution_of_reading ordinary rows closures selected temporary output
    ambient available present outputFresh temporaryFresh different (solved bound)
  · rw [sourceKnowledge]
    exact computed_initial_model valid unified
  · rw [selectedClosure]
    exact computed_reading ordinary.frame valid unified

end Mettapedia.Languages.MeTTa.PeTTa.MachineClauseActivation
