import Mettapedia.Languages.TransitionSystem.Runs

/-!
# Two terms with the same traces and different branching

A transition table of eight states.  `Early` moves to `Open`, which then
chooses between `Win` and `Lose`.  `Late` chooses at once, between `Left`,
which moves to `Win`, and `Right`, which moves to `Lose`.  `Win` makes one
more step and `Lose` none.

`Early` and `Late` can run for the same numbers of steps, so the probe that
sees reduction finds the same traces from both.  They are not bisimilar:
after `Late` has moved to `Right` it has lost, while `Early` after its only
first move can still win.

So trace equivalence as a probe sees it is strictly coarser than bisimilarity
as the same probe sees it.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Contexts.Controls.Branching

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.Contexts
open Mettapedia.Languages.TransitionSystem

/-- The branching table. -/
def table : Table where
  states := ["Early", "Open", "Late", "Left", "Right", "Win", "Lose", "Done"]
  moves :=
    [("EarlyOpen", "Early", "Open"), ("OpenWin", "Open", "Win"), ("OpenLose", "Open", "Lose"),
      ("LateLeft", "Late", "Left"), ("LateRight", "Late", "Right"), ("LeftWin", "Left", "Win"),
      ("RightLose", "Right", "Lose"), ("WinDone", "Win", "Done")]

theorem table_wellFormed : table.WellFormed := by decide

/-- The validated branching presentation. -/
abbrev branchingValidated : ValidatedLanguageDef := Table.validated table_wellFormed

/-- The branching theory through its contexts. -/
abbrev theory : ContextTheory.{0} := Table.theory table_wellFormed

/-- The interface of closed states. -/
def proc : Interface := ⟨.base "Proc", []⟩

/-- A listed state as a closed term. -/
def stateTerm (label : String) (listed : label ∈ table.states) : Term table.language proc :=
  Table.stateTerm (interface := proc) rfl listed

/-- The longest run of a state. -/
def depth : String → ℕ
  | "Early" => 3
  | "Open" => 2
  | "Late" => 3
  | "Left" => 2
  | "Right" => 1
  | "Win" => 1
  | _ => 0

theorem table_height : table.Height depth := ⟨by decide, by decide⟩

/-! ## Same traces, different branching -/

/-- The term that chooses after its first move. -/
def early : Term table.language proc := stateTerm "Early" (by decide)

/-- The term that chooses with its first move. -/
def late : Term table.language proc := stateTerm "Late" (by decide)

/-- **The two terms have the same traces**, as the probe that sees reduction
finds them: each runs for up to three steps. -/
theorem early_late_traceEquivalent :
    theory.reductionProbe.TraceEquivalent (index := proc) early late :=
  Table.traceEquivalent_of_height_eq table_wellFormed table_height (leftLabel := "Early")
    (rightLabel := "Late") rfl rfl (by decide)

theorem only_from_early : ∀ move ∈ table.moves, move.2.1 = "Early" → move.2.2 = "Open" := by
  decide

theorem only_from_right : ∀ move ∈ table.moves, move.2.1 = "Right" → move.2.2 = "Lose" := by
  decide

theorem none_from_lose : ∀ move ∈ table.moves, move.2.1 ≠ "Lose" := by decide

/-- **The two terms are not bisimilar.**  `Late` moves to `Right`, which has
lost; the only first move of `Early` reaches `Open`, which can still win. -/
theorem early_late_not_bisimilar :
    ¬ theory.reductionProbe.Bisimilar (index := proc) early late := by
  intro bisimilar
  obtain ⟨relation, ⟨forward, backward⟩, related⟩ :=
    ContextTheory.reductionProbe_bisimilar_iff.mp bisimilar
  have lateMoves : theory.rewrites late (stateTerm "Right" (by decide)) :=
    (Table.rewrites_iff table_wellFormed).mpr
      ⟨("LateRight", "Late", "Right"), by decide, rfl, rfl⟩
  obtain ⟨answer, answerStep, answerRelated⟩ := backward related lateMoves
  obtain ⟨move, moveMember, source, target⟩ :=
    (Table.rewrites_iff table_wellFormed).mp answerStep
  have answerShape : answer.1 = state "Open" := by
    rw [target, only_from_early move moveMember (state_injective source.symm)]
  have answerMoves : theory.rewrites answer (stateTerm "Win" (by decide)) :=
    (Table.rewrites_iff table_wellFormed).mpr
      ⟨("OpenWin", "Open", "Win"), by decide, answerShape, rfl⟩
  obtain ⟨reply, replyStep, replyRelated⟩ := forward answerRelated answerMoves
  obtain ⟨second, secondMember, secondSource, secondTarget⟩ :=
    (Table.rewrites_iff table_wellFormed).mp replyStep
  have replyShape : reply.1 = state "Lose" := by
    rw [secondTarget, only_from_right second secondMember (state_injective secondSource.symm)]
  have winMoves : theory.rewrites (stateTerm "Win" (by decide)) (stateTerm "Done" (by decide)) :=
    (Table.rewrites_iff table_wellFormed).mpr ⟨("WinDone", "Win", "Done"), by decide, rfl, rfl⟩
  obtain ⟨final, finalStep, -⟩ := forward replyRelated winMoves
  obtain ⟨third, thirdMember, thirdSource, -⟩ :=
    (Table.rewrites_iff table_wellFormed).mp finalStep
  exact none_from_lose third thirdMember (state_injective (thirdSource.symm.trans replyShape))

/-- The two terms are not bisimilar over all contexts either: the hole is one
of them. -/
theorem early_late_not_bisimilar_fullProbe :
    ¬ theory.fullProbe.Bisimilar (index := proc) early late :=
  fun bisimilar => early_late_not_bisimilar
    (ContextTheory.reductionProbe_bisimilar_iff.mpr (ContextTheory.bisimilar_toGSLT bisimilar))

/-- **Trace equivalence is strictly coarser than bisimilarity**, for one and
the same probe. -/
theorem traceEquivalent_not_bisimilar :
    theory.reductionProbe.TraceEquivalent (index := proc) early late ∧
      ¬ theory.reductionProbe.Bisimilar (index := proc) early late :=
  ⟨early_late_traceEquivalent, early_late_not_bisimilar⟩

end Mettapedia.GSLT.LanguageDef.Contexts.Controls.Branching
