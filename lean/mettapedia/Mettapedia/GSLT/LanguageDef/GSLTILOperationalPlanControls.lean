import Mettapedia.GSLT.LanguageDef.GSLTILOperationalPlans

/-!
# Authored-event controls for operational plans

Two authored occurrences share visible endpoints but have distinct retained
receipts. A third authored rule supplies a typed suffix. The controls check
open reconstruction, filling, occurrence identity, and unauthorized events.
-/

namespace Mettapedia.GSLT.LanguageDef.GSLTIL.OperationalPlans.Controls

open Mettapedia.GSLT.Ultrainfinite
open Mettapedia.GSLT.LanguageDef.GSLTIL.Syntax
open Mettapedia.GSLT.LanguageDef.GSLTIL.FreePath
open Mettapedia.OSLF.MeTTaIL.Syntax

set_option autoImplicit false

def space : Pattern := symbol "method-space"
def input : Pattern := inSpace space (symbol "input")
def middle : Pattern := inSpace space (symbol "middle")
def output : Pattern := inSpace space (symbol "output")

def firstRule : SpaceRule :=
  ⟨symbol "first-occurrence", space, symbol "input", symbol "middle"⟩
def secondRule : SpaceRule :=
  ⟨symbol "second-occurrence", space, symbol "input", symbol "middle"⟩
def suffixRule : SpaceRule :=
  ⟨symbol "suffix-occurrence", space, symbol "middle", symbol "output"⟩

def program : Program := ⟨[firstRule, secondRule, suffixRule], [], []⟩

def firstEvent : ProgramEvent program input middle :=
  .inSpace firstRule (by simp [program])
def secondEvent : ProgramEvent program input middle :=
  .inSpace secondRule (by simp [program])
def suffixEvent : ProgramEvent program middle output :=
  .inSpace suffixRule (by simp [program])

def suffix : ProgramPath program middle output := .cons suffixEvent (.refl output)
def firstPath : ProgramPath program input output := .cons firstEvent suffix
def secondPath : ProgramPath program input output := .cons secondEvent suffix

def firstPlan : ClosedPlan program output input := encode firstPath
def secondPlan : ClosedPlan program output input := encode secondPath

theorem distinct_occurrences : occurrences (decode firstPlan) ≠ occurrences (decode secondPlan) := by
  simp only [firstPlan, secondPlan, decode_encode]
  decide

theorem distinct_plans : firstPlan ≠ secondPlan := by
  intro same
  exact distinct_occurrences (congrArg (fun p => occurrences (decode p)) same)

/-- Proposition-valued runs cannot distinguish the two actual histories. -/
theorem equal_erased_runs : firstPath.toRuns = secondPath.toRuns := Subsingleton.elim _ _

def receipt {source target : Pattern} (event : ProgramEvent program source target) : Nat :=
  if event.occurrence = firstRule.occurrence then 2 else 1

theorem different_costs :
    cost receipt (decode firstPlan) = 3 ∧ cost receipt (decode secondPlan) = 2 := by
  simp only [firstPlan, secondPlan, decode_encode]
  decide

/-- This obligation requires a path with these endpoints; it contains no path. -/
def SuffixHole (target source : Pattern) : Type := PLift (source = middle ∧ target = output)

def openPlan : Plan program SuffixHole output input :=
  step firstEvent (hole ⟨⟨rfl, rfl⟩⟩)

theorem open_hole_stays_unresolved :
    reconstruct? (fun _ _ _ => none) output input openPlan = none := rfl

def solveSuffix (target source : Pattern) (h : SuffixHole target source) :
    ProgramPath program source target := by
  rcases h with ⟨⟨rfl, rfl⟩⟩
  exact suffix

noncomputable def filledPlan : ClosedPlan program output input :=
  fill (fun target source h => encode (solveSuffix target source h)) output input openPlan

/-- Filling retains the first actual occurrence and the supplied actual suffix. -/
theorem filled_retains_path : decode filledPlan = firstPath := by
  calc
    decode filledPlan = reconstruct solveSuffix output input openPlan :=
      decode_fill_encode solveSuffix openPlan
    _ = firstPath := by
      change Route.cons firstEvent (solveSuffix output middle ⟨⟨rfl, rfl⟩⟩) = firstPath
      rfl

theorem filled_retains_occurrences :
    occurrences (decode filledPlan) =
      [firstRule.occurrence, suffixRule.occurrence] := by
  rw [filled_retains_path]
  rfl

theorem filled_retains_cost : cost receipt (decode filledPlan) = 3 := by
  rw [filled_retains_path]
  decide

theorem fill_cannot_replace_prefix : decode filledPlan ≠ secondPath := by
  rw [filled_retains_path]
  intro same
  have occurrenceEquality := congrArg occurrences same
  contradiction

def forgedOccurrence : Pattern := symbol "unauthorized-occurrence"

/-- Event authorization comes from this authored program, not from endpoints
alone or from a controller's proposed method label. -/
theorem no_unauthorized_event {source target : Pattern}
    (event : ProgramEvent program source target) : event.occurrence ≠ forgedOccurrence := by
  cases event with
  | inSpace rule member =>
    simp only [program, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;>
      simp only [ProgramEvent.occurrence] <;> decide
  | underRoute route rule routeMember _ _ =>
    simp [program] at routeMember
  | applyRoute route rule routeMember _ _ =>
    simp [program] at routeMember

theorem cannot_supply_forged_step :
    ¬ ∃ event : ProgramEvent program input middle, event.occurrence = forgedOccurrence := by
  rintro ⟨event, same⟩
  exact no_unauthorized_event event same

end Mettapedia.GSLT.LanguageDef.GSLTIL.OperationalPlans.Controls
