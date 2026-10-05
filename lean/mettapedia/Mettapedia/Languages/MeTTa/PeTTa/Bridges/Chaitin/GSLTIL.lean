import Mettapedia.Languages.MeTTa.PeTTa.Bridges.Chaitin.IterationBisimulation
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.Chaitin.TablePrograms
import Mettapedia.Languages.TuringMachine.Bridges.GSLTIL

/-!
# Historical Lisp iteration blocks in GSLT-IL

The source edge is the existing complete execution of an ordinary historical
Lisp row-search and tape-motion program. The target edge executes the same
authored table through the shared GSLT-IL command rules. Deterministic tables
give a step cover on all outgoing target answers, with complete terminal
configurations as observations. Modal formulas and return-observing block
bisimilarity are preserved and reflected.

The independent full recursive Lisp interpreter and the command execution
also agree on returned configurations. This comparison selects table programs
and complete iteration boundaries; it does not equate elementary evaluator
steps, arbitrary ambient contexts, or implementations in C.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.Chaitin.GSLTIL

open Mettapedia.Languages
open TuringMachine
open Mettapedia.GSLT
open Mettapedia.GSLT.Ultrainfinite
open Mettapedia.GSLT.HennessyMilner
open Mettapedia.OSLF.MeTTaIL.Syntax

theorem iteration_step_iff (machine : Machine) (deterministic : machine.Deterministic)
    (source target : Configuration) :
    IterationBisimulation.IterationStep machine source target ↔
      (configurationGSLT machine).Step source target :=
  (IterationBisimulation.iterationStep_iff machine source target).trans
    (MathlibBridge.next_some_iff_step machine deterministic source target)

/-- The block boundary transports the source's actual generated executions,
while the intermediate object is the existing table-configuration GSLT. -/
theorem tableCover (machine : Machine) (deterministic : machine.Deterministic) :
    StepCover (IterationBisimulation.sourceIterations machine) (configurationGSLT machine) id where
  mapStep := (iteration_step_iff machine deterministic _ _).mp
  liftStep := fun step => ⟨_, (iteration_step_iff machine deterministic _ _).mpr step, rfl⟩

theorem stepCover (machine : Machine) (deterministic : machine.Deterministic) :
    StepCover (IterationBisimulation.sourceIterations machine)
      (TuringMachine.Bridges.GSLTIL.theory machine)
      (fun state : Configuration => TuringMachine.Bridges.GSLTIL.command state.term) :=
  (tableCover machine deterministic).comp (TuringMachine.Bridges.GSLTIL.stepCover machine)

def tableTranslation (machine : Machine) (deterministic : machine.Deterministic) :
    Mettapedia.GSLT.IndexedOperational.CoveredTranslation
      (IterationBisimulation.sourceIterations machine) (configurationGSLT machine) where
  mapTerm := id
  mapEquiv := fun same => same
  cover := tableCover machine deterministic

/-- The Lisp block comparison composes in the same operational category as
the independently qualified table execution bridge. -/
def coveredTranslation (machine : Machine) (deterministic : machine.Deterministic) :
    Mettapedia.GSLT.IndexedOperational.CoveredTranslation
      (IterationBisimulation.sourceIterations machine) (TuringMachine.Bridges.GSLTIL.theory machine) :=
  (tableTranslation machine deterministic).comp (TuringMachine.Bridges.GSLTIL.coveredTranslation machine)

theorem normal_iff (machine : Machine) (deterministic : machine.Deterministic)
    (source : Configuration) :
    (IterationBisimulation.sourceIterations machine).IsNormalForm source ↔
      (TuringMachine.Bridges.GSLTIL.theory machine).IsNormalForm
        (TuringMachine.Bridges.GSLTIL.command source.term) :=
  (stepCover machine deterministic).normal_iff source

def targetObserved (machine : Machine) : ObservedGSLT (TuringMachine.Bridges.GSLTIL.theory machine) where
  Atom := Configuration
  observes := fun final state => state = TuringMachine.Bridges.GSLTIL.command final.term ∧
    (TuringMachine.Bridges.GSLTIL.theory machine).IsNormalForm state

private theorem target_observation_resp (machine : Machine) (atom : Configuration)
    {left right : Pattern}
    (same : (TuringMachine.Bridges.GSLTIL.theory machine).Equiv left right) :
    (targetObserved machine).observes atom left ↔ (targetObserved machine).observes atom right := by
  have equal := (Mettapedia.GSLT.LanguageDef.GSLTIL.FibreExecution.equiv_iff_eq
    TuringMachine.Bridges.GSLTIL.stage (TuringMachine.Bridges.GSLTIL.successors machine) left right).mp same
  cases equal
  rfl

def targetSystem (machine : Machine) : System (TuringMachine.Bridges.GSLTIL.theory machine) :=
  System.ofObserved (targetObserved machine) (target_observation_resp machine)

def observedCover (machine : Machine) (deterministic : machine.Deterministic) :
    SystemCover (IterationBisimulation.sourceSystem machine) (targetSystem machine) :=
  SystemCover.ofStepCover (stepCover machine deterministic)
    (by
      intro left right same
      cases same
      exact (Mettapedia.GSLT.LanguageDef.GSLTIL.FibreExecution.equiv_iff_eq _ _ _ _).mpr rfl)
    (IterationBisimulation.sourceObserved machine) (targetObserved machine)
    (by intro atom left right same; cases same; rfl)
    (target_observation_resp machine) id (by
      intro final source
      change (source = final ∧ _) ↔
        (TuringMachine.Bridges.GSLTIL.command source.term =
          TuringMachine.Bridges.GSLTIL.command final.term ∧ _)
      have injective : Function.Injective
          (fun state : Configuration => TuringMachine.Bridges.GSLTIL.command state.term) :=
        (Mettapedia.GSLT.LanguageDef.GSLTIL.FibreExecution.at_injective _).comp Configuration.term_injective
      exact and_congr injective.eq_iff.symm (normal_iff machine deterministic source))

theorem formula_iff (machine : Machine) (deterministic : machine.Deterministic)
    (formula : Formula Configuration Unit) (source : Configuration) :
    (IterationBisimulation.sourceSystem machine).sat formula source ↔
      (targetSystem machine).sat formula (TuringMachine.Bridges.GSLTIL.command source.term) := by
  have comparison := (observedCover machine deterministic).sat_map formula source
  have mapped : formula.map (observedCover machine deterministic).mapAtom
      (observedCover machine deterministic).mapLabel = formula := Formula.map_id formula
  rw [mapped] at comparison
  exact comparison.symm

theorem bisimilar_iff (machine : Machine) (deterministic : machine.Deterministic)
    (first second : Configuration) :
    (IterationBisimulation.sourceSystem machine).Bisimilar first second ↔
      (targetSystem machine).Bisimilar (TuringMachine.Bridges.GSLTIL.command first.term)
        (TuringMachine.Bridges.GSLTIL.command second.term) :=
  ((observedCover machine deterministic).bisimilar_map_iff
    Function.surjective_id Function.surjective_id first second).symm

theorem returns_iff (machine : Machine) (deterministic : machine.Deterministic)
    (initial final : Configuration) :
    Chaitin.GSLT.theory.MultiStep
      (Chaitin.GSLT.start (Chaitin.TuringPrograms.machineProgram machine initial))
      (Chaitin.GSLT.result (Chaitin.TuringPrograms.encodeConfiguration final)) ↔
      TuringMachine.Bridges.GSLTIL.Returns machine initial final :=
  (Chaitin.GSLT.machine_returns_iff machine initial final).trans
    (TuringMachine.Bridges.GSLTIL.returns_iff_eval machine deterministic initial final).symm

/-- The same terminal configuration is observed by all three execution views. -/
theorem petta_returns_iff (machine : Machine) (deterministic : machine.Deterministic)
    (initial final : Configuration) :
    TuringMachine.Execution.Returns machine initial final ↔
      TuringMachine.Bridges.GSLTIL.Returns machine initial final :=
  (TuringMachine.Execution.returns_iff deterministic initial final).trans
    (TuringMachine.Bridges.GSLTIL.returns_iff_eval machine deterministic initial final).symm

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.Chaitin.GSLTIL
