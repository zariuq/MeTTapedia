import Mettapedia.GSLT.LanguageDef.GSLTILFibreExecution
import Mettapedia.Languages.TuringMachine.UniversalTable

/-!
# Turing tables in the shared GSLT-IL execution boundary

One authored table is registered as a fibre. Its successor query executes
that table's existing LanguageDef with the shared premise-aware engine; it
does not store a list of all configuration edges. The query is qualified
against the independent table-step relation, including every target answer.

The fixed universal table therefore executes on arbitrary prepared input
through the existing GSLT-IL command rules. Halting is preserved and reflected,
and its numbered input family remains undecidable. Unknown stages are inert.
This module does not claim preservation of arbitrary ambient contexts or a
particular C implementation of the relation interface.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.TuringMachine.Bridges.GSLTIL

open Mettapedia.GSLT
open Mettapedia.GSLT.Ultrainfinite
open Mettapedia.GSLT.LanguageDef.GSLTIL
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep

def stage : Pattern := .apply "TuringTable" []

/-- The guest's authored rules are the computation authority. -/
def successors (machine : Machine) (state : Pattern) : List Pattern :=
  rewriteStepWithPremisesUsing RelationEnv.empty (turingMachine machine) state

def theory (machine : Machine) : GSLT :=
  FibreExecution.theory stage (successors machine)

def command (state : Pattern) : Pattern := atPattern stage state

/-- Qualification against the independently defined table relation, on all
patterns rather than only on a supplied list of visited configurations. -/
theorem successors_iff (machine : Machine) (source target : Pattern) :
    target ∈ successors machine source ↔ Step base (turingMachine machine) source target := by
  have plain : ∀ rule, rule ∈ (turingMachine machine).rewrites →
      NoncontextualPremises rule.premises := by
    intro rule member
    rw [rewrites_premiseFree machine rule member]
    exact .nil
  rw [step_iff_rootStep_of_noncontextualRules plain]
  simp [successors, RootStep, rewriteStepWithPremisesUsing, applyRuleWithPremisesUsing]

theorem step_command_iff (machine : Machine) (source target : Pattern) :
    (theory machine).Step (command source) (command target) ↔
      Step base (turingMachine machine) source target := by
  have accepted := FibreExecution.step_at_iff stage (successors machine) source (command target)
  change (theory machine).Step (command source) (command target) ↔ _ at accepted
  rw [accepted]
  constructor
  · rintro ⟨next, member, same⟩
    have equal := FibreExecution.at_injective stage same
    subst next
    exact (successors_iff machine source target).mp member
  · intro step
    exact ⟨target, (successors_iff machine source target).mpr step, rfl⟩

/-- Every computed successor of a complete configuration is again complete. -/
theorem configuration_query_qualified (machine : Machine) (source : Configuration)
    (answer : Pattern) :
    answer ∈ successors machine source.term ↔
      ∃ next : Configuration, (configurationGSLT machine).Step source next ∧ answer = next.term := by
  rw [successors_iff]
  constructor
  · intro step
    obtain ⟨entry, member, applies, rfl⟩ := step_term_iff.mp step
    exact ⟨source.after entry, step, rfl⟩
  · rintro ⟨next, step, rfl⟩
    exact step

/-- Actual command execution covers the original configuration GSLT. -/
theorem stepCover (machine : Machine) :
    StepCover (configurationGSLT machine) (theory machine)
      (fun state : Configuration => command state.term) :=
  FibreExecution.stepCover (configurationGSLT machine) stage Configuration.term
    (successors machine) (configuration_query_qualified machine)

/-- The execution bridge is an arrow of the existing covered operational
category, so indexed diagrams and relational route equipment can reuse it. -/
def coveredTranslation (machine : Machine) :
    Mettapedia.GSLT.IndexedOperational.CoveredTranslation
      (configurationGSLT machine) (theory machine) where
  mapTerm := fun state => command state.term
  mapEquiv := by
    intro left right same
    change left = right at same
    cases same
    exact (FibreExecution.equiv_iff_eq _ _ _ _).mpr rfl
  cover := stepCover machine

theorem normal_command_iff (machine : Machine) (state : Pattern) :
    (theory machine).IsNormalForm (command state) ↔ Halted machine state := by
  constructor
  · intro normal target step
    exact normal ⟨command target, (step_command_iff machine state target).mpr step⟩
  · intro halted ⟨target, step⟩
    obtain ⟨next, member, _⟩ :=
      (FibreExecution.step_at_iff stage (successors machine) state target).mp step
    exact halted next ((successors_iff machine state next).mp member)

abbrev CommandReaches (machine : Machine) := Relation.ReflTransGen (theory machine).Step

theorem reaches_preserved (machine : Machine) {source target : Pattern}
    (path : Reaches machine source target) :
    CommandReaches machine (command source) (command target) := by
  induction path with
  | refl => exact .refl
  | tail _ last ih => exact ih.tail ((step_command_iff machine _ _).mpr last)

/-- Target endpoints are reflected without assuming they are commands. -/
theorem reaches_reflected (machine : Machine) (source : Pattern) {target : Pattern}
    (path : CommandReaches machine (command source) target) :
    ∃ final, target = command final ∧ Reaches machine source final := by
  induction path with
  | refl => exact ⟨source, rfl, .refl⟩
  | tail _ last ih =>
      obtain ⟨current, rfl, earlier⟩ := ih
      obtain ⟨next, member, same⟩ :=
        (FibreExecution.step_at_iff stage (successors machine) current _).mp last
      exact ⟨next, same, earlier.tail ((successors_iff machine current next).mp member)⟩

theorem reaches_iff (machine : Machine) (source target : Pattern) :
    CommandReaches machine (command source) (command target) ↔
      Reaches machine source target := by
  constructor
  · intro path
    obtain ⟨final, same, reflected⟩ := reaches_reflected machine source path
    have equal := FibreExecution.at_injective stage same
    subst final
    exact reflected
  · exact reaches_preserved machine

def Halts (machine : Machine) (source : Pattern) : Prop :=
  ∃ final, CommandReaches machine (command source) final ∧
    (theory machine).IsNormalForm final

theorem halts_iff (machine : Machine) (source : Pattern) :
    Halts machine source ↔ HaltsFrom machine source := by
  constructor
  · rintro ⟨target, path, normal⟩
    obtain ⟨final, rfl, reflected⟩ := reaches_reflected machine source path
    exact ⟨final, reflected, (normal_command_iff machine final).mp normal⟩
  · rintro ⟨final, path, normal⟩
    exact ⟨command final, reaches_preserved machine path,
      (normal_command_iff machine final).mpr normal⟩

/-- Returned observations retain the complete configuration, not just a
halting bit or an arbitrary normal target pattern. -/
def Returns (machine : Machine) (initial final : Configuration) : Prop :=
  CommandReaches machine (command initial.term) (command final.term) ∧
    (theory machine).IsNormalForm (command final.term)

theorem returns_iff (machine : Machine) (initial final : Configuration) :
    Returns machine initial final ↔
      Reaches machine initial.term final.term ∧ Halted machine final.term :=
  and_congr (reaches_iff machine initial.term final.term) (normal_command_iff machine final.term)

/-- The actual partial execution function and the command's terminal output
agree in both directions, without a shared fuel bound. -/
theorem returns_iff_eval (machine : Machine) (deterministic : machine.Deterministic)
    (initial final : Configuration) :
    Returns machine initial final ↔ final ∈ StateTransition.eval machine.next? initial := by
  rw [returns_iff]
  constructor
  · rintro ⟨path, halted⟩
    obtain ⟨last, same, reached⟩ := MathlibBridge.reaches_next_reflect machine deterministic path
    have equal := Configuration.term_injective same
    subst last
    exact StateTransition.mem_eval.mpr
      ⟨reached, (MathlibBridge.next_none_iff_halted machine final).mpr halted⟩
  · intro computed
    obtain ⟨reached, stopped⟩ := StateTransition.mem_eval.mp computed
    exact ⟨MathlibBridge.reaches_next_forward machine reached,
      Machine.halted_of_next?_eq_none stopped⟩

theorem universal_halts_iff (index argument : Nat) :
    Halts UniversalTable.machine (UniversalTable.inputConfiguration index argument).term ↔
      ((Denumerable.ofNat Nat.Partrec.Code index).eval argument).Dom :=
  (halts_iff _ _).trans (UniversalTable.halts_iff index argument)

/-- One fixed registered table realizes every partial-recursive function,
including its domain and complete returned-output representation. -/
theorem universal_for_partrec (function : Nat →. Nat) (effective : Nat.Partrec function) :
    ∃ index, ∀ argument,
      (Halts UniversalTable.machine (UniversalTable.inputConfiguration index argument).term ↔
        (function argument).Dom) ∧
      (∀ output, output ∈ function argument →
        ∃ final, Returns UniversalTable.machine (UniversalTable.inputConfiguration index argument) final ∧
          PartrecBridge.Represents PartrecMachine.universal (Turing.PartrecToTM2.halt [output]) final) := by
  obtain ⟨index, comparison⟩ := UniversalTable.universal_for_partrec function effective
  refine ⟨index, fun argument => ⟨(halts_iff _ _).trans (comparison argument).1, ?_⟩⟩
  intro output computed
  obtain ⟨final, returned, represented⟩ := (comparison argument).2 output computed
  exact ⟨final, (returns_iff_eval _ UniversalTable.deterministic _ _).mpr returned, represented⟩

theorem universal_output_reflected (index argument : Nat) {final : Configuration}
    (returned : Returns UniversalTable.machine (UniversalTable.inputConfiguration index argument) final) :
    ∃ output, output ∈ (Denumerable.ofNat Nat.Partrec.Code index).eval argument ∧
      PartrecBridge.Represents PartrecMachine.universal (Turing.PartrecToTM2.halt [output]) final :=
  UniversalTable.output_reflected index argument
    ((returns_iff_eval _ UniversalTable.deterministic _ _).mp returned)

theorem universal_halting_not_computable :
    ¬ ComputablePred fun index : Nat =>
      Halts UniversalTable.machine (UniversalTable.inputConfiguration index 0).term :=
  fun decided => UniversalTable.halting_family_not_computable
    (decided.of_eq fun index => halts_iff UniversalTable.machine
      (UniversalTable.inputConfiguration index 0).term)

/-- Preparation produces the actual command's structural code by a
primitive-recursive function of both the program index and its input. -/
theorem universal_commandCode_primrec :
    Primrec fun input : Nat × Nat => Mettapedia.OSLF.MeTTaIL.PatternCode.patternCode
      (command (UniversalTable.inputConfiguration input.1 input.2).term) := by
  apply ((FibreExecution.atPatternCode_primrec stage).comp
    ((InputEncoding.inputConfiguration_patternCode_primrec PartrecMachine.universal).comp
      (Primrec.list_cons.comp Primrec.fst
        (Primrec.list_cons.comp Primrec.snd (Primrec.const []))))).of_eq
  intro input
  exact FibreExecution.atPatternCode_eq stage _

/-- Halting on structurally coded commands of a fixed registered table. -/
def HaltingCode (machine : Machine) (code : Nat) : Prop :=
  ∃ state, Mettapedia.OSLF.MeTTaIL.PatternCode.patternCode (command state) = code ∧
    Halts machine state

theorem haltingCode_command (machine : Machine) (state : Pattern) :
    HaltingCode machine (Mettapedia.OSLF.MeTTaIL.PatternCode.patternCode (command state)) ↔
      Halts machine state := by
  constructor
  · rintro ⟨other, same, halted⟩
    have equal := FibreExecution.at_injective stage
      (Mettapedia.OSLF.MeTTaIL.PatternCode.patternCode_injective same)
    subst other
    exact halted
  · exact fun halted => ⟨state, rfl, halted⟩

theorem universal_haltingCode_not_computable :
    ¬ ComputablePred (HaltingCode UniversalTable.machine) := by
  intro decided
  apply universal_halting_not_computable
  obtain ⟨decidable, computable⟩ := decided
  have prepared : ComputablePred fun index : Nat =>
      HaltingCode UniversalTable.machine
        (Mettapedia.OSLF.MeTTaIL.PatternCode.patternCode
          (command (UniversalTable.inputConfiguration index 0).term)) :=
    ⟨_, computable.comp (universal_commandCode_primrec.comp
      (Primrec.pair Primrec.id (Primrec.const 0))).to_comp⟩
  exact prepared.of_eq fun index =>
    haltingCode_command UniversalTable.machine (UniversalTable.inputConfiguration index 0).term

end Mettapedia.Languages.TuringMachine.Bridges.GSLTIL
