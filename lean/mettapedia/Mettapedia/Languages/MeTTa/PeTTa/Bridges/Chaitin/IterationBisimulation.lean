import Mettapedia.Languages.Chaitin.GSLT.TableIteration
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.TuringMachine.Tables
import Mettapedia.Languages.TuringMachine.MathlibBridge
import Mettapedia.GSLT.Logic.HennessyMilnerTransport

/-!
# Bisimulation at complete historical Lisp table iterations

Each source edge is a complete generated execution of an ordinary Lisp
program: recursive row search followed by list-based tape motion. Each
target edge is an answer of the existing PeTTa equation kernel. On
deterministic tables these edges correspond in both directions, including
every target answer leaving a translated configuration.

The resulting step cover preserves and reflects return-observing
bisimilarity and modal formulas. A returned observation includes the full
terminal configuration. Elementary evaluator steps inside a Lisp invocation
are hidden by the explicit iteration boundary; this is a block comparison,
not a weak-bisimulation theorem for arbitrary native PeTTa executions.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.Chaitin.IterationBisimulation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT
open Mettapedia.GSLT.Ultrainfinite
open Mettapedia.GSLT.HennessyMilner
open Mettapedia.Languages.TuringMachine

open Mettapedia.Languages

/-- A complete source invocation with an explicitly present successor. -/
def IterationStep (machine : Machine) (source target : Configuration) : Prop :=
  Chaitin.GSLT.theory.MultiStep (Chaitin.GSLT.start (Chaitin.GSLT.TableIteration.program machine source))
    (Chaitin.GSLT.result (Chaitin.GSLT.TableIteration.outcome (some target)))

theorem iterationStep_iff (machine : Machine) (source target : Configuration) :
    IterationStep machine source target ↔ machine.next? source = some target := by
  rw [IterationStep, Chaitin.GSLT.TableIteration.returns_iff]
  exact ⟨fun same => (Chaitin.GSLT.TableIteration.outcome_injective same).symm,
    fun same => congrArg Chaitin.GSLT.TableIteration.outcome same.symm⟩

/-- The source view hides only the finite work inside each ordinary Lisp
invocation; its rewrite relation is not defined using the target table. -/
def sourceIterations (machine : Machine) : GSLT where
  Term := Configuration
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := IterationStep machine
  rewrites_resp_left := by
    intro source other target same step
    subst other
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target other step same
    subst other
    exact step

/-- The target is the established equation judgment, with its original
pattern carrier. No target-state restriction is built into its rules. -/
def targetEquations (machine : Machine) : GSLT where
  Term := Pattern
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := TuringMachine.Tables.EquationStep machine
  rewrites_resp_left := by
    intro source other target same step
    subst other
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target other step same
    subst other
    exact step

theorem iterationStep_equationStep_iff (machine : Machine)
    (deterministic : machine.Deterministic) (source target : Configuration) :
    IterationStep machine source target ↔
      TuringMachine.Tables.EquationStep machine source.term target.term :=
  (iterationStep_iff machine source target).trans
    ((MathlibBridge.next_some_iff_step machine deterministic source target).trans
      (TuringMachine.Tables.equationStep_iff source target.term).symm)

/-- The same block comparison reaches the existing minimal `eval`
instruction, rather than an invented target reduction rule. -/
theorem iterationStep_instruction_iff (machine : Machine)
    (deterministic : machine.Deterministic) (source target : Configuration) :
    IterationStep machine source target ↔
      MeTTaStep (TuringMachine.Tables.program machine) (.apply "eval" [source.term]) target.term :=
  (iterationStep_iff machine source target).trans
    ((MathlibBridge.next_some_iff_step machine deterministic source target).trans
      (TuringMachine.Tables.instruction_iff machine source.term target.term).symm)

/-- Both directions quantify over actual equations; in particular no extra
target answer can escape the image of complete configurations. -/
theorem stepCover (machine : Machine) (deterministic : machine.Deterministic) :
    StepCover (sourceIterations machine) (targetEquations machine) Configuration.term where
  mapStep := (iterationStep_equationStep_iff machine deterministic _ _).mp
  liftStep := by
    intro source target step
    have authored := (TuringMachine.Tables.equationStep_iff source target).mp step
    obtain ⟨entry, member, applies, rfl⟩ := step_term_iff.mp authored
    refine ⟨source.after entry, ?_, rfl⟩
    exact (iterationStep_equationStep_iff machine deterministic _ _).mpr step

theorem iterationNormal_iff (machine : Machine) (source : Configuration) :
    (sourceIterations machine).IsNormalForm source ↔ machine.next? source = none := by
  change (¬ ∃ target, IterationStep machine source target) ↔ _
  simp only [iterationStep_iff]
  cases machine.next? source <;> simp

theorem normal_iff (machine : Machine) (source : Configuration) :
    (sourceIterations machine).IsNormalForm source ↔
      TuringMachine.Tables.EquationNormal machine source.term :=
  (iterationNormal_iff machine source).trans
    ((MathlibBridge.next_none_iff_halted machine source).trans
      (TuringMachine.Tables.equationNormal_iff source).symm)

abbrev IterationReaches (machine : Machine) := Relation.ReflTransGen (IterationStep machine)

theorem iterationReaches_preserved (machine : Machine) (deterministic : machine.Deterministic)
    {source target : Configuration} (path : IterationReaches machine source target) :
    TuringMachine.Tables.EquationReaches machine source.term target.term := by
  induction path with
  | refl => exact .refl
  | tail _ last ih => exact ih.tail ((stepCover machine deterministic).mapStep last)

theorem iterationReaches_reflected (machine : Machine) (deterministic : machine.Deterministic)
    (source : Configuration) {target : Pattern}
    (path : TuringMachine.Tables.EquationReaches machine source.term target) :
    ∃ final : Configuration, target = final.term ∧ IterationReaches machine source final := by
  induction path with
  | refl => exact ⟨source, rfl, .refl⟩
  | tail _ last ih =>
      obtain ⟨current, rfl, earlier⟩ := ih
      obtain ⟨next, iteration, same⟩ := (stepCover machine deterministic).liftStep last
      exact ⟨next, same.symm, earlier.tail iteration⟩

theorem iterationReaches_iff (machine : Machine) (deterministic : machine.Deterministic)
    (source target : Configuration) :
    IterationReaches machine source target ↔
      TuringMachine.Tables.EquationReaches machine source.term target.term := by
  constructor
  · exact iterationReaches_preserved machine deterministic
  · intro path
    obtain ⟨final, same, reflected⟩ := iterationReaches_reflected machine deterministic source path
    cases Configuration.term_injective same
    exact reflected

/-- The atom names the full returned configuration, and requires genuine
termination at this iteration boundary. -/
def sourceObserved (machine : Machine) : ObservedGSLT (sourceIterations machine) where
  Atom := Configuration
  observes := fun final source => source = final ∧ (sourceIterations machine).IsNormalForm source

def targetObserved (machine : Machine) : ObservedGSLT (targetEquations machine) where
  Atom := Configuration
  observes := fun final source => source = final.term ∧ TuringMachine.Tables.EquationNormal machine source

def sourceSystem (machine : Machine) : System (sourceIterations machine) :=
  System.ofObserved (sourceObserved machine) (by intro atom left right same; cases same; rfl)

def targetSystem (machine : Machine) : System (targetEquations machine) :=
  System.ofObserved (targetObserved machine) (by intro atom left right same; cases same; rfl)

/-- A behavioral cover carrying all returned-tape observations. -/
def observedCover (machine : Machine) (deterministic : machine.Deterministic) :
    SystemCover (sourceSystem machine) (targetSystem machine) :=
  SystemCover.ofStepCover (stepCover machine deterministic)
    (by intro left right same; cases same; rfl)
    (sourceObserved machine) (targetObserved machine)
    (by intro atom left right same; cases same; rfl)
    (by intro atom left right same; cases same; rfl)
    id (by
      intro final source
      change (source = final ∧ _) ↔ (source.term = final.term ∧ _)
      exact and_congr Configuration.term_injective.eq_iff.symm (normal_iff machine source))

/-- Every modal formula, including negation and exact returned tapes, has
the same truth value at corresponding iteration boundaries. -/
theorem formula_iff (machine : Machine) (deterministic : machine.Deterministic)
    (formula : Formula Configuration Unit) (source : Configuration) :
    (sourceSystem machine).sat formula source ↔
      (targetSystem machine).sat formula source.term := by
  have comparison := (observedCover machine deterministic).sat_map formula source
  have mapped : formula.map (observedCover machine deterministic).mapAtom
      (observedCover machine deterministic).mapLabel = formula := Formula.map_id formula
  rw [mapped] at comparison
  exact comparison.symm

/-- Strong bisimilarity of complete iterations is preserved and reflected.
This uses the shared GSLT comparison API rather than a new Lisp-specific
definition of bisimulation. -/
theorem bisimilar_iff (machine : Machine) (deterministic : machine.Deterministic)
    (first second : Configuration) :
    (sourceSystem machine).Bisimilar first second ↔
      (targetSystem machine).Bisimilar first.term second.term := by
  exact ((observedCover machine deterministic).bisimilar_map_iff
    Function.surjective_id Function.surjective_id first second).symm

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.Chaitin.IterationBisimulation
