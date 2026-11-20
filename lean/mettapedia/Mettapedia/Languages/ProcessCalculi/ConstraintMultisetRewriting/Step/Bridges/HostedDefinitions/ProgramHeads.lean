import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.ProgramLayout
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.RowCompiler
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.TerminalAnswers

/-! # Literal head certificates of the actual generated source rules -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.ProgramHeads

open SourceLanguage SourceLanguage.Elaboration

abbrev Rule := ProgramBinders.Equation MSig [] ()

def Active (rule : Rule) : Prop := literalHead rule.lhs = some activeTag ∧
  (literalHead rule.rhs = some activeTag ∨ literalHead rule.rhs = some doneTag)

instance (rule : Rule) : Decidable (Active rule) := inferInstanceAs (Decidable (_ ∧ _))

theorem fixed : ∀ rule ∈ ContextRules.fixed, Active rule := by
  have checked : ContextRules.fixed.all (fun rule => decide (Active rule)) = true := by decide
  intro rule member
  exact of_decide_eq_true (List.all_eq_true.mp checked rule member)

theorem row {entry : Σ slots : Nat,
      Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tower.Tm slots ×
      Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tower.Tm slots}
    {rule : Rule} (compiled : RowCompiler.row entry = some rule) : Active rule := by
  unfold RowCompiler.row at compiled
  split at compiled
  · split at compiled
    · cases compiled
    · cases compiled
      exact ⟨rfl, .inl rfl⟩
  · cases compiled

theorem rows {table : Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.AlgebraicSchema.SchemaTable
      Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tower.Head}
    {compiled : List Rule} (found : RowCompiler.rows table = some compiled) :
    ∀ rule ∈ compiled, Active rule := by
  induction table generalizing compiled with
  | nil => cases found; exact fun rule member => (List.not_mem_nil member).elim
  | cons entry rest ih =>
      simp only [RowCompiler.rows, List.mapM_cons] at found
      obtain ⟨first, firstFound, restFound⟩ := Option.bind_eq_some_iff.mp found
      obtain ⟨later, laterFound, same⟩ := Option.bind_eq_some_iff.mp restFound
      cases same
      intro rule member
      rcases List.mem_cons.mp member with rfl | inside
      · exact row firstFound
      · exact ih laterFound rule inside

theorem assembled (helpers authored : List Rule)
    (helperHeads : ∀ rule ∈ helpers, Active rule)
    (authoredHeads : ∀ rule ∈ authored, Active rule) :
    HeadSeparated (ProgramLayout.rows helpers authored) activeTag doneTag where
  distinct := active_done_distinct
  lhs index := by
    have member := List.get_mem (ProgramLayout.rows helpers authored) index
    rcases List.mem_append.mp member with earlier | last
    · rcases List.mem_append.mp earlier with first | middle
      · exact (fixed _ first).1
      · exact (helperHeads _ middle).1
    · exact (authoredHeads _ last).1
  rhs index := by
    have member := List.get_mem (ProgramLayout.rows helpers authored) index
    rcases List.mem_append.mp member with earlier | last
    · rcases List.mem_append.mp earlier with first | middle
      · exact (fixed _ first).2
      · exact (helperHeads _ middle).2
    · exact (authoredHeads _ last).2

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.ProgramHeads
