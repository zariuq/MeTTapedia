import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceTraceClassifying
import Mettapedia.GSLT.LanguageDef.CertificateGSLTOpenApplicationControls

/-!
# Controls for protected occurrence projection and real-trace cut

Equal judgments at distinct physical rows remain distinct assumption nodes.
Repeated reads of one row select one position, while one row cannot supply
two different source judgments. An actual client/server run followed by a
second client/server run composes the original source rules over the initial
protected assumption.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceProjectionControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker hiding RuleInstance
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open InferenceSchemaActivation (action judgment)
open InferenceSchemaKernel (Space Value locatedAction)
open InferenceRequestExecution (Occurrence label location payload system)
open InferenceSelectedFirings
open InferenceJudgmentBoards
open InferenceTraceClassifying
open _root_.CategoryTheory

namespace BoardControls

open CertificateGSLT.OpenApplicationControls (a b c definition)

def firstRow : Occurrence := (0, (.judgments, judgment a))
def secondRow : Occurrence := (1, (.judgments, judgment a))
def initial : Configuration Value Occurrence := ⟨[], {firstRow}⟩
def doubled : Configuration Value Occurrence := ⟨[], {firstRow, secondRow}⟩

def initialBoard : Board initial where
  entries := [(firstRow, a)]
  distinct := by simp
  occupied := by
    intro occurrence
    simp only [List.map_cons, List.map_nil, List.mem_singleton, initial, Finset.mem_singleton]
    constructor
    · rintro rfl
      exact ⟨rfl, rfl⟩
    · exact fun present => present.1
  readback := by intro entry member; obtain rfl := List.mem_singleton.mp member; rfl
  supported := by intro entry member; obtain rfl := List.mem_singleton.mp member; rfl

def doubledBoard : Board doubled where
  entries := [(firstRow, a), (secondRow, a)]
  distinct := by decide +kernel
  occupied := by
    intro occurrence
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
      doubled, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (rfl | rfl) <;> exact ⟨by simp, rfl⟩
    · exact fun present => present.1
  readback := by
    intro entry member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> rfl
  supported := by
    intro entry member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> rfl

def leftPosition : Fin doubledBoard.entries.length := ⟨0, by decide⟩
def rightPosition : Fin doubledBoard.entries.length := ⟨1, by decide⟩

theorem equal_judgments :
    doubledBoard.judgmentAt leftPosition = doubledBoard.judgmentAt rightPosition := rfl

theorem different_physical_rows :
    doubledBoard.occurrenceAt leftPosition ≠ doubledBoard.occurrenceAt rightPosition := by
  intro same
  have indexEq : (0 : Nat) = 1 := congrArg Prod.fst same
  cases indexEq

/-- A visible-value coincidence does not collapse premise occurrences. -/
theorem distinct_assumption_nodes :
    doubledBoard.assumption definition leftPosition ≠
      doubledBoard.assumption definition rightPosition := by
  intro same
  change OpenDerivation.assumption (definition := definition) (context := [a, a])
      ⟨0, by decide⟩ = OpenDerivation.assumption ⟨1, by decide⟩ at same
  cases same

theorem first_application : RuleApplication definition ⟨⟨"ab"⟩, []⟩ [a] b :=
  instantiateRule?_eq_some_iff_application.mp (by decide +kernel)

theorem second_application : RuleApplication definition ⟨⟨"bc"⟩, []⟩ [b] c :=
  instantiateRule?_eq_some_iff_application.mp (by decide +kernel)

theorem initial_consistent : locatedAction.Consistent initial.equations :=
  ⟨action.identity, locatedAction.models_nil _⟩

/-- Both rules execute through their installed IDs and consumed requests.
The final open proof is constructed from those actual selected firings. -/
theorem two_actual_applications :
    ∃ after, (system definition).Run payload initial [false, true, false, true] after ∧
      Nonempty (OpenDerivation definition [a] c) := by
  obtain ⟨middle, firstRun, retained, output, outputPresent, outputReadback⟩ :=
    InferenceRequestExecution.application_runs definition first_application initial initial_consistent
      (by
        intro premise member
        have same : premise = a := List.mem_singleton.mp member
        subst premise
        exact ⟨firstRow, by simp [initial], rfl⟩)
  have middleConsistent := SchemaPublicationAuthority.System.Run.consistent firstRun initial_consistent
  obtain ⟨after, secondRun, _, result, resultPresent, resultReadback⟩ :=
    InferenceRequestExecution.application_runs definition second_application middle middleConsistent
      (by
        intro premise member
        have same : premise = b := List.mem_singleton.mp member
        subst premise
        exact ⟨output, outputPresent, outputReadback⟩)
  have combined : (system definition).Run payload initial [false, true, false, true] after :=
    SchemaPublicationAuthority.System.Run.append firstRun secondRun
  refine ⟨after, combined, ?_⟩
  exact actual_run_has_open_derivation combined initialBoard result resultPresent
    (congrArg Prod.fst resultReadback) c resultReadback

end BoardControls

/-- Aliasing is permitted only when the two expected source judgments
agree; it cannot turn one physical row into arbitrary premise values. -/
theorem one_row_cannot_supply_distinct_judgments
    {definition : ValidatedCalculusLanguageDef}
    {before after : Configuration Value Occurrence}
    {firing : SelectedFiring definition true before after} (origin : firing.KernelOrigin)
    (board : Board before) (first second : Fin origin.premises.length)
    (sameRow : origin.readOccurrence first = origin.readOccurrence second) :
    origin.premises.get first = origin.premises.get second := by
  rw [← origin.read_judgment board first, ← origin.read_judgment board second,
    origin.repeated_read_position board first second sameRow]

/-- No public request row can be a protected premise position. -/
theorem public_row_not_in_board {state : Configuration Value Occurrence}
    (board : Board state) (occurrence : Occurrence)
    (publicHere : location occurrence = .requests) : occurrence ∉ board.occurrences := by
  intro member
  have protectedHere := ((board.occupied occurrence).mp member).2
  rw [publicHere] at protectedHere
  cases protectedHere

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceProjectionControls
