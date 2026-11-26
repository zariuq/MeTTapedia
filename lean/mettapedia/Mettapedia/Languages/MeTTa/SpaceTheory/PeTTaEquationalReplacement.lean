import Mettapedia.Languages.MeTTa.SpaceTheory.EvaluationObservations
import Mettapedia.Languages.MeTTa.SpaceTheory.EquationalLookupProtection
import Mettapedia.Languages.MeTTa.SpaceTheory.PeTTaImportProtection

/-!
# Snapshot replacement for an equation-aware PeTTa call

Preserve the class of the ready call and the ordered definitions for
heads that can be its representatives. No older answer, store or
continuation is installed. The fixed and live entry programs produce
the same sequence of alternatives and leave all later steps live.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.SpaceTheory.PeTTaEquationalReplacement

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.GSLT.Contracts.OccurrenceObservers (Demand Result)
open Mettapedia.GSLT.Contracts.OccurrenceExecution (completed completed_iff_chain readCompleted reports ofTerm reports_congr)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.Schematic (SState)
open PeTTaEquationalOnTheStep (State Request Transition source theory Shows)
open PeTTaExecution (programAt)
open PeTTaImportProtection (definitions arities_from_definitions clauses_from_definitions)
open EquationalLookupProtection (SameClass)
open EvaluationObservations (pettaEquationalView pettaEmit)

structure EntryAgreement (before snapshot : List Atom) (query : Atom) : Prop where
  sameClass : SameClass before snapshot query
  sameDefinitions : ∀ head values,
    AtomEquations.Equivalent before query (.expression (.symbol head :: values)) →
    definitions (programAt before) head = definitions (programAt snapshot) head

theorem EntryAgreement.symm {before snapshot : List Atom} {query : Atom}
    (same : EntryAgreement before snapshot query) : EntryAgreement snapshot before query where
  sameClass member := (same.sameClass member).symm
  sameDefinitions head values reached :=
    (same.sameDefinitions head values ((same.sameClass _).mpr reached)).symm

theorem select_unchanged {before snapshot : List Atom} {query representative : Atom}
    (agrees : EntryAgreement before snapshot query)
    (reachable : AtomEquations.Equivalent before query representative) :
    PeTTaEquationEntry.select before representative = PeTTaEquationEntry.select snapshot representative := by
  cases representative with
  | symbol | var | grounded => rfl
  | expression args =>
    cases args with
    | nil => rfl
    | cons head values =>
      cases head with
      | var | grounded | expression => rfl
      | symbol head =>
        have definitions := agrees.sameDefinitions head values reachable
        simp only [PeTTaEquationEntry.select, arities_from_definitions _ _ head definitions,
          clauses_from_definitions _ _ head definitions values]

theorem entry_iff {before snapshot : List Atom} {call : Atom} (same : EntryAgreement before snapshot call)
    (alternatives : List Eval.Control) :
    (PeTTaEquationEntry.theory before).Step (.inl call) (.inr alternatives) ↔
      (PeTTaEquationEntry.theory snapshot).Step (.inl call) (.inr alternatives) := by
  refine (PeTTaEquationEntry.entry_exact before call alternatives).trans
    (Iff.trans ?_ (PeTTaEquationEntry.entry_exact snapshot call alternatives).symm)
  constructor
  · rintro ⟨rep, eq, selected⟩
    exact ⟨rep, (same.sameClass rep).mp eq, (select_unchanged same eq).symm.trans selected⟩
  · rintro ⟨rep, eq, selected⟩
    have previous := (same.sameClass rep).mpr eq
    exact ⟨rep, previous, (select_unchanged same previous).trans selected⟩

/-- A useful case for library metadata and unrelated data: the new
atoms contribute neither an equation generator nor a function definition. -/
theorem inert_extension (before added : List Atom) (query : Atom)
    (noEquations : ∀ a b, ¬AtomEquations.Generator added a b)
    (noDefinitions : (programAt added).equations = []) :
    EntryAgreement before (before ++ added) query := by
  constructor
  · exact (EquationalLookupProtection.class_append_iff before added query).mpr
      (fun _ _ _ declared => (noEquations _ _ declared).elim)
  · intro head _ _
    rw [PeTTaExecution.declaration_contributions_compose]
    simp only [definitions, SpaceSemantics.Program.append, noDefinitions, List.append_nil]

inductive ProtectedAt (snapshot : List Atom) : State → Prop where
  | ready (request : Request) : EntryAgreement request.state.core snapshot request.call →
      ProtectedAt snapshot (.ready request)
  | running (configuration : Eval.Configuration) : ProtectedAt snapshot (.running configuration)

theorem protected_step {snapshot : List Atom} {before after : State} (held : ProtectedAt snapshot before) :
    Transition id before after ↔ Transition (fun _ => snapshot) before after := by
  cases held with
  | ready request agreement =>
    constructor
    · intro step
      cases step with
      | enter admitted => exact .enter ((entry_iff agreement _).mp admitted)
    · intro step
      cases step with
      | enter admitted => exact .enter ((entry_iff agreement _).mpr admitted)
  | running configuration =>
    constructor
    · intro step; cases step with | ordinary now => exact .ordinary now
    · intro step; cases step with | ordinary now => exact .ordinary now

private theorem successor_protected {snapshot : List Atom} {before after : State}
    (step : Transition (fun _ => snapshot) before after) : ProtectedAt snapshot after := by
  cases step <;> exact .running _

private theorem protected_chain {snapshot : List Atom} (before : State) (tail : List State)
    (held : ProtectedAt snapshot before) :
    (before :: tail).IsChain (Transition id) ↔
      (before :: tail).IsChain (Transition (fun _ => snapshot)) := by
  induction tail generalizing before with
  | nil => simp
  | cons next rest ih =>
    simp only [List.isChain_cons_cons]
    rw [protected_step held]
    apply and_congr_right
    intro advances
    exact ih next (successor_protected advances)

theorem protected_reports_on_transform {O : Type} [DecidableEq O] [Infinite O]
    (snapshot : List Atom) {before : State} {start : SState O} (shown : Shows before start)
    (held : ProtectedAt snapshot before) (demand : Demand) (answer : Result Atom demand) :
    reports (completed (sys := source) pettaEquationalView (·.isSome = true) pettaEmit before) demand answer ↔
    reports (readCompleted (sys := theory O (fun _ => snapshot)) (ofTerm Shows pettaEquationalView)
      (·.isSome = true) pettaEmit start) demand answer := by
  refine Iff.trans ?_ (EvaluationObservations.petta_equational_reports_iff shown demand answer (fun _ => snapshot))
  apply reports_congr
  intro trace
  refine (completed_iff_chain (sys := source) pettaEquationalView _ pettaEmit before trace).trans
    (Iff.trans ?_ (completed_iff_chain (sys := source (fun _ => snapshot))
      pettaEquationalView _ pettaEmit before trace).symm)
  constructor
  · rintro ⟨tail, finish, chain, last, ended, batches⟩
    exact ⟨tail, finish, (protected_chain before tail held).mp chain, last, ended, batches⟩
  · rintro ⟨tail, finish, chain, last, ended, batches⟩
    exact ⟨tail, finish, (protected_chain before tail held).mpr chain, last, ended, batches⟩

end Mettapedia.Languages.MeTTa.SpaceTheory.PeTTaEquationalReplacement
