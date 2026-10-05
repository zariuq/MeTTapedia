import Mettapedia.Languages.TuringMachine.Bridges.GSLTIL
import Mettapedia.Languages.TuringMachine.ClassicMachines

/-!
# Controls for Turing execution in GSLT-IL

The controls retain returned tape contents and divergence, reject unsupported
stages, and separate finite control from a finite catalog of concrete edges.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.TuringMachine.Bridges.GSLTIL.Controls

open Mettapedia.GSLT
open Mettapedia.GSLT.Ultrainfinite
open Mettapedia.OSLF.MeTTaIL.Syntax

theorem busy_beaver_returns : Returns busyBeaver2 Configuration.blank busyBeaver2Final :=
  (returns_iff _ _ _).mpr busyBeaver2_run

theorem alternating_has_no_return : ¬ Halts alternating Configuration.blank.term :=
  fun halted => alternating_never_halts ((halts_iff _ _).mp halted)

theorem unsupported_stage_inert (machine : Machine) (state : Pattern) :
    (theory machine).IsNormalForm
      (Mettapedia.GSLT.LanguageDef.GSLTIL.atPattern (.apply "OtherStage" []) state) :=
  Mettapedia.GSLT.LanguageDef.GSLTIL.FibreExecution.other_stage_normal
    stage (.apply "OtherStage" []) (successors machine) (by decide) state

def longTape (length : Nat) : Configuration := ⟨0, List.replicate length 1, 0, []⟩

theorem longTape_injective : Function.Injective (fun length => (longTape length).term) := by
  intro first second same
  have configurations := Configuration.term_injective same
  have lengths := congrArg (fun configuration : Configuration => configuration.left.length) configurations
  simpa [longTape] using lengths

theorem longTape_enabled (length : Nat) :
    ∃ next, (configurationGSLT busyBeaver2).Step (longTape length) next := by
  refine ⟨(longTape length).after ⟨0, 0, 1, .right, 1⟩, ?_⟩
  exact step_term_iff.mpr ⟨_, by decide, ⟨rfl, rfl⟩, rfl⟩

/-- Even this two-state machine has infinitely many enabled complete tapes.
No finite list of concrete command edges covers its configuration GSLT. -/
theorem no_finite_catalog_cover
    (catalog : Mettapedia.GSLT.LanguageDef.GSLTIL.Catalog) :
    ¬ Nonempty (StepCover (configurationGSLT busyBeaver2)
      (Mettapedia.GSLT.LanguageDef.GSLTIL.totalTheory catalog)
      (fun state : Configuration => command state.term)) :=
  Mettapedia.GSLT.LanguageDef.GSLTIL.FibreExecution.finite_catalog_not_cover
    (configurationGSLT busyBeaver2) stage Configuration.term catalog
    longTape longTape_injective longTape_enabled

/-- The same infinite tape family is covered by the authored-query backend. -/
theorem query_covers_longTape :
    StepCover (configurationGSLT busyBeaver2) (theory busyBeaver2)
      (fun state : Configuration => command state.term) := stepCover busyBeaver2

end Mettapedia.Languages.TuringMachine.Bridges.GSLTIL.Controls
