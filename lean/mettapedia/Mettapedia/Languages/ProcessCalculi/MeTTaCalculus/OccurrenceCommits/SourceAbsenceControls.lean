import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.SourceAbsence
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.CommutativeMatching

/-! # Absence of a correlated query is not absence of each of its sources -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources.AbsenceControls

open Commutative

inductive Symbol where
  | message | acknowledgement | a | b | nil
  deriving DecidableEq

abbrev Value := Tm Symbol
abbrev Pattern := Pat ℕ Symbol
abbrev Occurrence := Value × ℕ

def noComm : Symbol → Bool := fun _ => false
abbrev layer : TermLayer ℕ Value Pattern := termLayer noComm
abbrev matcher : Matcher ℕ Value Pattern := cmatch noComm
def empty : Subst ℕ Value := fun _ => none
def label : Occurrence → Value := Prod.fst

def message (x : Symbol) : Value := .node .message (.leaf x) (.leaf .nil)
def acknowledgement (x : Symbol) : Value := .node .acknowledgement (.leaf x) (.leaf .nil)
def messagePattern : Pattern := .node .message (.var 0) (.leaf .nil)
def acknowledgementPattern : Pattern := .node .acknowledgement (.var 0) (.leaf .nil)

def joined : SourceList ℕ Value Pattern :=
  .cons (.read messagePattern) (.cons (.read acknowledgementPattern) .done)

def unrelated : Finset Occurrence := {(message .a, 0), (acknowledgement .b, 1)}
def related : Finset Occurrence := {(message .a, 0), (acknowledgement .a, 1)}

/-- Both component searches succeed, but their shared-variable join is absent. -/
theorem correlated_absence :
    (stepRows matcher label unrelated (.read messagePattern) empty).card = 1 ∧
      (stepRows matcher label unrelated (.read acknowledgementPattern) empty).card = 1 ∧
      (absenceRows layer matcher label unrelated joined empty).card = 1 := by
  decide +kernel

/-- A matching acknowledgement disables the absence result. -/
theorem matching_join_refuses_absence :
    (rows layer matcher label related [] joined empty).card = 1 ∧
      (absenceRows layer matcher label related joined empty).card = 0 := by
  decide +kernel

/-- The empty conjunction has one successful row; its absence is false. -/
theorem empty_conjunction_not_absent :
    (absenceRows layer matcher label (∅ : Finset Occurrence) .done empty).card = 0 := by
  decide +kernel

/-- An empty `every` still has its amalgamated row. It must not be mistaken
for no row by an enclosing absence query. -/
theorem vacuous_every_not_absent :
    (absenceRows layer matcher label (∅ : Finset Occurrence)
      (.every (.cons (.read messagePattern) .done)) empty).card = 0 := by
  decide +kernel

/-- Two same-valued messages are two distinct witnesses of the positive join. -/
theorem duplicate_witnesses_retained :
    (rows layer matcher label
      {(message .a, 0), (message .a, 2), (acknowledgement .a, 1)} [] joined empty).card = 2 := by
  decide +kernel

/-- A matcher that silently drops every answer would incorrectly report absence. -/
theorem incomplete_matcher_false_absence :
    (absenceRows layer (fun _ _ _ => []) label related joined empty).card = 1 ∧
      (absenceRows layer matcher label related joined empty).card = 0 := by
  decide +kernel

/-- The query is also part of the recursive source grammar. -/
theorem recursive_absence :
    (rows layer matcher label unrelated [] (.absent joined .done) empty).card = 1 ∧
      (rows layer matcher label related [] (.absent joined .done) empty).card = 0 := by
  decide +kernel

/-- Failed attempts to bind the inner variable do not capture the continuation. -/
theorem query_bindings_do_not_escape :
    ∀ row ∈ rows layer matcher label unrelated [.var 0]
      (.absent joined (.cons (.read acknowledgementPattern) .done)) empty,
      row.1 0 = some (.leaf .b) := by
  decide +kernel

/-- Nested absence observes whether its inner query actually has a row. -/
theorem nested_absence :
    (rows layer matcher label unrelated []
      (.absent (.absent joined .done) .done) empty).card = 0 ∧
      (rows layer matcher label related []
        (.absent (.absent joined .done) .done) empty).card = 1 := by
  decide +kernel

/-- A pure computation returning a value supplies a row, even in an empty store. -/
theorem computed_row_not_absent :
    (rows layer matcher label (∅ : Finset Occurrence) []
      (.absent (.cons (.letBind (.var 0) (fun _ => [.leaf .a])) .done) .done) empty).card = 0 := by
  decide +kernel

/-- Continued absence does not validate an old exact observation: even an
additional nonjoining acknowledgement changes the retained query snapshot. -/
theorem absence_can_hold_with_stale_evidence :
    let changed := insert (acknowledgement .b, 2) unrelated
    (absenceRows layer matcher label changed joined empty).card = 1 ∧
      ¬ (complQueries label unrelated (complRegions matcher joined empty)).Holds label changed := by
  dsimp only
  unfold Footprint.Holds
  decide +kernel

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources.AbsenceControls
