import Mettapedia.Machines.TIsa.Derivation.SymbolicFiring
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.FirstOrderAskLicence

/-!
# Testing a batch at its declared observation boundary

A batch uses the same residual solver as a single selected firing.
Its observation boundary is not an implementation detail: joint
guards, guards proved by each member alone, snapshot resource reads,
and guards before the tells are different readings. Every reading
still needs one solution of the whole information before publication.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.Derivation.SymbolicBatch

open Mettapedia.Logic.LP
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open RuleSyntax (Program)
open RuleSyntax.OneFrame (Terms ext)
open RuleSyntax.JointFirings (Bag)
open RuleSyntax.JointFirings.FirstOrderAskLicence (checks checks_correct)
open RuleSyntax.FirstOrderLicence (firingChecks firingChecks_correct)
open SymbolicFiring (World act)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (Enabled)

variable {signature : LPSignature} {O : Type} [DecidableEq O]
  {program : Program (Terms (Term signature))}

inductive Reading where
  | joint
  | memberOwn
  | snapshot
  | beforeTells

structure Prepared (before : World signature O) where
  batch : Bag O (ext (FirstOrder.action signature)) program before.frame
  nonempty : batch.members ≠ []
  fits : batch.Fits (act signature) before

variable {before : World signature O}

def Admits (reading : Reading) (selection : Prepared (program := program) before) : Prop :=
  let batch := selection.batch
  match reading with
  | .joint => batch.Admits (act signature) before
  | .memberOwn => batch.AdmitsOwn (act signature) before
  | .snapshot => batch.AdmitsSnapshot (act signature) before
  | .beforeTells => batch.AdmitsBeforeTells (act signature) before

variable [DecidableEq signature.vars] [DecidableEq signature.constants] [DecidableEq signature.functionSymbols]

def permits (reading : Reading) (selection : Prepared (program := program) before) (full : Subst signature) : Bool :=
  let batch := selection.batch
  let together := decide (Enabled (fun _ : O => ()) before.present (batch.selection.commit (T := Unit)))
  match reading with
  | .joint => together && checks full before batch
  | .snapshot =>
    (batch.members.all fun member => decide
      (Enabled (fun _ : O => ()) before.present (member.selection.commit (T := Unit)))) &&
      checks full before batch
  | .memberOwn => together && batch.members.all fun member =>
    match unifyTotal (member.firing.information (act signature) before) with
    | none => false
    | some own => firingChecks own before member.firing
  | .beforeTells => together &&
    match unifyTotal (batch.askInformation (act signature) before) with
    | none => false
    | some early => checks early before batch

theorem permits_exact (reading : Reading) (selection : Prepared (program := program) before)
    (full : Subst signature) (solved : unifyTotal (selection.batch.information (act signature) before) = some full) :
    permits reading selection full = true ↔ Admits reading selection := by
  have model := unifyTotal_sound _ _ solved
  have consistent : (act signature).Solvable (selection.batch.information (act signature) before) :=
    ⟨PUnit.unit, full, model⟩
  cases reading with
  | joint =>
    simp only [permits, Bool.and_eq_true, decide_eq_true_eq, checks_correct _ _ _ _ solved, Admits, Bag.Admits]
    exact ⟨fun h => ⟨selection.fits, h.1, consistent, h.2⟩, fun h => ⟨h.2.1, h.2.2.2⟩⟩
  | snapshot =>
    simp only [permits, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, checks_correct _ _ _ _ solved,
      Admits, Bag.AdmitsSnapshot]
    exact ⟨fun h => ⟨selection.fits, h.1, consistent, h.2⟩, fun h => ⟨h.2.1, h.2.2.2⟩⟩
  | memberOwn =>
    simp only [permits, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Admits, Bag.AdmitsOwn]
    have atMember (member : RuleSyntax.JointFirings.Member O (ext (FirstOrder.action signature)) program
        selection.batch.ext) (inside : member ∈ selection.batch.members) :
        (match unifyTotal (member.firing.information (act signature) before) with
          | none => false
          | some own => firingChecks own before member.firing) = true ↔
        (act signature).Entails (member.firing.information (act signature) before)
          (fun b answer => member.firing.Holds (act signature) before (b := b) answer) := by
      have ownModel := Bag.models_member (act signature) inside (b := PUnit.unit) (σ := full) model
      obtain ⟨own, found⟩ := unifyTotal_complete ⟨full, ownModel⟩
      rw [found]
      exact firingChecks_correct before member.firing own found
    exact ⟨fun h => ⟨selection.fits, h.1, consistent, fun member inside =>
      (atMember member inside).mp (h.2 member inside)⟩,
      fun h => ⟨h.2.1, fun member inside => (atMember member inside).mpr (h.2.2.2 member inside)⟩⟩
  | beforeTells =>
    have earlyModel := selection.batch.models_ask (act signature) before (b := PUnit.unit) (σ := full) model
    obtain ⟨early, found⟩ := unifyTotal_complete ⟨full, earlyModel⟩
    simp only [permits, found, Bool.and_eq_true, decide_eq_true_eq, checks_correct _ _ _ _ found,
      Admits, Bag.AdmitsBeforeTells]
    exact ⟨fun h => ⟨selection.fits, h.1, consistent, h.2⟩, fun h => ⟨h.2.1, h.2.2.2⟩⟩

def evaluate (reading : Reading) (selection : Prepared (program := program) before) :
    Option (Subst signature × World signature O) := do
  let full ← unifyTotal (selection.batch.information (act signature) before)
  if permits reading selection full then some (full, selection.batch.result (act signature) before) else none

theorem evaluate_exact (reading : Reading) (selection : Prepared (program := program) before)
    (answer : Subst signature) (after : World signature O) :
    evaluate reading selection = some (answer, after) ↔
      unifyTotal (selection.batch.information (act signature) before) = some answer ∧
      Admits reading selection ∧ after = selection.batch.result (act signature) before := by
  constructor
  · intro computed
    unfold evaluate at computed
    obtain ⟨full, solved, published⟩ := Option.bind_eq_some_iff.mp computed
    by_cases accepted : permits reading selection full = true
    · simp only [if_pos accepted, Option.some.injEq, Prod.mk.injEq] at published
      obtain ⟨rfl, rfl⟩ := published
      exact ⟨solved, (permits_exact reading selection _ solved).mp accepted, rfl⟩
    · simp [accepted] at published
  · rintro ⟨solved, admitted, rfl⟩
    have accepted := (permits_exact reading selection _ solved).mpr admitted
    simp [evaluate, solved, accepted]

theorem admitted_has_result (reading : Reading) (selection : Prepared (program := program) before)
    (admitted : Admits reading selection) :
    ∃ answer, evaluate reading selection = some (answer, selection.batch.result (act signature) before) := by
  have solvable : (act signature).Solvable (selection.batch.information (act signature) before) := by
    cases reading <;> exact admitted.2.2.1
  obtain ⟨frame, solution, model⟩ := solvable
  cases frame
  obtain ⟨answer, found⟩ := unifyTotal_complete ⟨solution, model⟩
  exact ⟨answer, (evaluate_exact reading selection _ _).mpr ⟨found, admitted, rfl⟩⟩

theorem refuses_exactly_when_not_admitted (reading : Reading)
    (selection : Prepared (program := program) before) : evaluate reading selection = none ↔ ¬Admits reading selection := by
  constructor
  · intro stopped admits
    obtain ⟨answer, result⟩ := admitted_has_result reading selection admits
    rw [stopped] at result
    cases result
  · intro refuses
    cases found : evaluate reading selection with
    | none => rfl
    | some result => exact (refuses ((evaluate_exact reading selection result.1 result.2).mp found).2.1).elim

end Mettapedia.Machines.TIsa.Derivation.SymbolicBatch
