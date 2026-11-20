import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.RowCompiler

/-! # Ordered occurrence correspondence of the actual compiled row lists -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.RowCompilation

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation
open SourceLanguage.Elaboration

abbrev Entry := Σ slots : Nat, Tower.Tm slots × Tower.Tm slots
abbrev Rule := ProgramBinders.Equation MSig [] ()

theorem paired {table : List Entry} {generated : List Rule}
    (compiled : RowCompiler.rows table = some generated) :
    List.Forall₂ (fun entry rule => RowCompiler.row entry = some rule) table generated := by
  induction table generalizing generated with
  | nil => cases compiled; exact .nil
  | cons entry rest ih =>
      simp only [RowCompiler.rows, List.mapM_cons] at compiled
      obtain ⟨first, firstCompiled, restCompiled⟩ := Option.bind_eq_some_iff.mp compiled
      obtain ⟨later, laterCompiled, same⟩ := Option.bind_eq_some_iff.mp restCompiled
      cases same
      exact .cons firstCompiled (ih laterCompiled)

theorem length {table : List Entry} {generated : List Rule}
    (compiled : RowCompiler.rows table = some generated) : generated.length = table.length :=
  (paired compiled).length_eq.symm

theorem member {table : List Entry} {generated : List Rule}
    (compiled : RowCompiler.rows table = some generated) {entry : Entry} (inside : entry ∈ table) :
    ∃ rule ∈ generated, RowCompiler.row entry = some rule := by
  have pairs := paired compiled
  clear compiled
  induction pairs with
  | nil => cases inside
  | @cons first rule rest later firstCompiled restCompiled ih =>
      rcases List.mem_cons.mp inside with rfl | inRest
      · exact ⟨rule, List.mem_cons_self, firstCompiled⟩
      · obtain ⟨found, member, compiled⟩ := ih inRest
        exact ⟨found, List.mem_cons_of_mem _ member, compiled⟩

theorem reflects_member {table : List Entry} {generated : List Rule}
    (compiled : RowCompiler.rows table = some generated) {rule : Rule} (inside : rule ∈ generated) :
    ∃ entry ∈ table, RowCompiler.row entry = some rule := by
  have pairs := paired compiled
  clear compiled
  induction pairs with
  | nil => cases inside
  | @cons first found rest later firstCompiled restCompiled ih =>
      rcases List.mem_cons.mp inside with rfl | inRest
      · exact ⟨first, List.mem_cons_self, firstCompiled⟩
      · obtain ⟨entry, member, compiled⟩ := ih inRest
        exact ⟨entry, List.mem_cons_of_mem _ member, compiled⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.RowCompilation
