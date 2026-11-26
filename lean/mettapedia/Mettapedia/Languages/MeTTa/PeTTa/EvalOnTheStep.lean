import Mettapedia.GSLT.Compilation.Uniform.QueryRulesOnTheStep
import Mettapedia.Languages.MeTTa.PeTTa.ConfigurationLanguageDef

/-!
# PeTTa's evaluator as an input of the uniform compiler to transform

`ConfigurationLanguageDef.language` is PeTTa's evaluator as an authored presentation.
The compiler is `GSLT.Compilation.Uniform.QueryRulesOnTheStep.compile`, the one for
every presentation. This module gives it what it reads of PeTTa and proves:

* `evalOnTheStep`: `Eval` and the transform step of the compiled program correspond, one
  transition for one firing, both ways, along runs of every length.
* `returns_on_the_step`: so what a call returns is exactly what a run of firings reads.
* `evaluator_compiles`: the authored presentation compiles, one transform rule per rule.
* `configurations_carrier`: the encoded configurations are a carrier of data closed
  under the authored steps.
* `relations_moded`, `relations_data`: the two laws the compiler asks of the relations.

The relations are the evaluator's data operations, held by the program at their graph.
They are not themselves compiled to rules here.

Control: with no output position declared, the presentation is refused
(`without_outputs_refused`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.EvalOnTheStep

open Mettapedia.GSLT.Compilation.Uniform
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextualStep (Step engineBasePremises)
open ConfigurationEncoding
open ConfigurationLanguageDef (language relationEnv)
open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.Compilation.RootRewritesOnTheStep (encode_injective sourceSystem)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open RuleSyntax
open RuleSyntax.Presentation.Schematic (SState readsAs_unique)
open RuleSyntax.Machines (ReadsBag)
open RuleSyntax.ComputedConditions (programSystem specialized rows relationGraph)

open private results encoded encodedList encodedControls from
  Mettapedia.Languages.MeTTa.PeTTa.ConfigurationLanguageDef

/-- The positions a relation of the evaluator computes. -/
def outputs : List (String × List ℕ) :=
  [("petta-list-vector", [1]), ("petta-list-append", [2]), ("petta-primitive-success", [3, 4]),
   ("petta-primitive-fault", [3]), ("petta-application", [2]), ("petta-substitute", [2]),
   ("petta-nested-lets", [2]), ("petta-read-cases", [1]), ("petta-evaluate-alternatives", [2]),
   ("petta-argument-alternatives", [6]), ("petta-binding-alternatives", [4]),
   ("petta-case-alternatives", [3]), ("petta-branch-alternatives", [4]),
   ("petta-query-alternatives", [5]), ("petta-unique-frames", [2])]

/-- Every other position is an input. -/
def inputs (relation : String) (index : ℕ) : Bool :=
  !((outputs.lookup relation).getD []).contains index

/-- **PeTTa's evaluator compiles by the uniform compiler**, rule for rule. -/
theorem evaluator_compiles :
    ∃ program, QueryRulesOnTheStep.compile inputs language = .ok program ∧ program.length = 41 := by
  have checked : (match QueryRulesOnTheStep.compile inputs language with
      | .ok program => program.length == 41
      | .error _ => false) = true := by
    decide +kernel
  split at checked
  · rename_i program compiled
    exact ⟨program, compiled, by simpa using checked⟩
  · cases checked

/-- **Negative**: read with every position an input, the presentation is refused. -/
theorem without_outputs_refused :
    (match QueryRulesOnTheStep.compile (fun _ _ => true) language with
      | .ok _ => false
      | .error _ => true) = true := by
  decide +kernel

mutual
  /-- The codec of atoms writes data. -/
  theorem encode_data : ∀ atom : Atom,
      OrderedMatching.isData (OSLFCore.Bridge.GroundData.encode atom) = true
    | .symbol _ => by rw [OSLFCore.Bridge.GroundData.encode]; rfl
    | .var _ => by rw [OSLFCore.Bridge.GroundData.encode]; rfl
    | .grounded (.int _) => by rw [OSLFCore.Bridge.GroundData.encode]; rfl
    | .grounded (.string _) => by rw [OSLFCore.Bridge.GroundData.encode]; rfl
    | .grounded (.bool false) => by rw [OSLFCore.Bridge.GroundData.encode]; rfl
    | .grounded (.bool true) => by rw [OSLFCore.Bridge.GroundData.encode]; rfl
    | .grounded (.custom _ _) => by rw [OSLFCore.Bridge.GroundData.encode]; rfl
    | .expression values => by
        simp [OSLFCore.Bridge.GroundData.encode, OrderedMatching.isData, OrderedMatching.isDataList,
          encodeList_data values]
  termination_by atom => sizeOf atom

  theorem encodeList_data : ∀ values : List Atom,
      OrderedMatching.isDataList (OSLFCore.Bridge.GroundData.encodeList values) = true
    | [] => by simp [OSLFCore.Bridge.GroundData.encodeList, OrderedMatching.isDataList]
    | value :: values => by
        simp [OSLFCore.Bridge.GroundData.encodeList, OrderedMatching.isDataList, encode_data value,
          encodeList_data values]
  termination_by values => sizeOf values
end

/-! ## The relations -/

theorem mem_of_lookup {relation : String} {positions : List ℕ} :
    ∀ {table : List (String × List ℕ)}, table.lookup relation = some positions → (relation, positions) ∈ table
  | [], found => by simp at found
  | (key, value) :: rest, found => by
      simp only [List.lookup_cons] at found
      split at found
      · rename_i same
        simp only [beq_iff_eq] at same
        simp only [Option.some.injEq] at found
        subst same found
        exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (mem_of_lookup found)

/-- A function blind to some positions agrees on lists that differ only there. -/
theorem blind_agree {α β : Type} (read : List α → β) : ∀ (positions : List ℕ),
    (∀ position ∈ positions, ∀ list value, read (list.set position value) = read list) →
    ∀ first second : List α, first.length = second.length →
      (∀ index, index ∉ positions → first[index]? = second[index]?) → read first = read second
  | [], _, first, second, _, agree => by
      rw [List.ext_getElem? fun index => agree index (by simp)]
  | position :: positions, blind, first, second, lengths, agree => by
      have later : ∀ other ∈ positions, ∀ list value, read (list.set other value) = read list :=
        fun other member => blind other (List.mem_cons_of_mem _ member)
      by_cases inside : position < second.length
      · rw [← blind position (List.mem_cons_self ..) first second[position]]
        refine blind_agree read positions later _ second (by simpa using lengths) fun index outside => ?_
        by_cases here : position = index
        · subst here
          simp [lengths, inside]
        · simp only [List.getElem?_set, if_neg here]
          exact agree index (by simp [Ne.symm here, outside])
      · refine blind_agree read positions later first second lengths fun index outside => ?_
        by_cases here : position = index
        · subst here
          rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
        · exact agree index (by simp [Ne.symm here, outside])

/-- **An output slot is never read.** -/
theorem output_unread (program : SpaceSemantics.Program) {relation : String} {positions : List ℕ}
    (declared : (relation, positions) ∈ outputs) :
    ∀ position ∈ positions, ∀ asked value,
      QueryPremises.queryRows (relationEnv program) language relation (asked.set position value) =
        QueryPremises.queryRows (relationEnv program) language relation asked := by
  simp only [outputs, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at declared
  intro position member asked value
  rcases declared with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  all_goals try rcases member with rfl | rfl
  all_goals rcases asked with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩⟩⟩⟩⟩⟩
  all_goals rfl

/-- **The evaluator's relations are moded**: their answers depend on the inputs alone. -/
theorem relations_moded (program : SpaceSemantics.Program) :
    QueryPremises.Moded (relationEnv program) language inputs := by
  intro relation asked row lengths agree
  have same : QueryPremises.queryRows (relationEnv program) language relation asked =
      QueryPremises.queryRows (relationEnv program) language relation row := by
    refine blind_agree _ ((outputs.lookup relation).getD []) ?_ asked row lengths fun index outside => ?_
    · cases found : outputs.lookup relation with
      | none => simp
      | some positions => exact output_unread program (mem_of_lookup found)
    · exact agree index (by simp [inputs, outside])
  rw [same]

/-- **The evaluator's relations answer data with data.** -/
theorem relations_data (program : SpaceSemantics.Program) :
    QueryPremises.DataRows (relationEnv program) language := by
  intro relation asked row offered data
  simp only [QueryPremises.queryRows, List.mem_append] at offered
  rcases offered with builtin | computed
  · unfold Mettapedia.OSLF.MeTTaIL.Engine.builtinRelationTuples at builtin
    split at builtin
    · simp [OrderedMatching.isDataList] at builtin data
      rcases builtin with rfl | rfl <;> simp [OrderedMatching.isDataList, data]
    · simp at builtin
  · simp only [relationEnv, ConfigurationLanguageDef.relationRows] at computed
    split at computed
    all_goals try unfold ConfigurationLanguageDef.queryRelationRows at computed
    all_goals try split at computed
    all_goals revert computed
    all_goals simp [results, Option.bind_eq_some_iff]
    all_goals repeat' first | intro _ | split
    all_goals try (rename_i found; split at found <;> simp at found)
    all_goals try obtain ⟨-, found⟩ := found
    all_goals subst_vars
    all_goals simp_all [OrderedMatching.isData, OrderedMatching.isDataList, encode_data, encodeList_data,
      encoded, encodedList, encodedControls]

/-- An encoded configuration with the store invariants that every transition keeps. -/
def Configurations (term : Pattern) : Prop :=
  ∃ (configuration : Eval.Configuration) (cells : List String),
    NamedSpaces.Store.EmptyTail configuration.state [] ∧
    (∀ name, name ∉ cells → configuration.state.cells name = none) ∧
    term = encode configuration cells

/-- **The configurations are a carrier of data closed under the authored steps.** -/
theorem configurations_carrier (program : SpaceSemantics.Program) :
    QueryRulesOnTheStep.DataCarrier (relationEnv program) language Configurations where
  data := by
    rintro _ ⟨configuration, cells, -, -, rfl⟩
    exact encode_data _
  closed := by
    rintro _ target ⟨configuration, cells, vacant, covers, rfl⟩ stepped
    have found := (Mettapedia.OSLF.Framework.TypeSynthesis.mem_rootFrontier_iff_langReducesUsing
      (relationEnv program) language ConfigurationLanguageDef.nonrecursive_rules _ target).mpr stepped
    rw [ConfigurationLanguageDef.frontier_eq_step program configuration cells vacant covers] at found
    simp only [List.mem_map, Option.mem_toList] at found
    obtain ⟨after, computed, rfl⟩ := found
    have transition := (Eval.step_iff_transition program configuration after).mp computed
    exact ⟨after, cellSupportAfter configuration cells, DeclarativeSpec.transition_empty_tail vacant transition,
      transition_support cells covers transition, rfl⟩

/-! ## The evaluator on the step -/

/-- The compiled program of the evaluator. -/
noncomputable def compiledRules :
    List (RuleSyntax.ComputedConditions.RuleWithCondition ℕ RuleSyntax.Presentation.Schematic.Tm) :=
  evaluator_compiles.choose

theorem compiledRules_compiled : QueryRulesOnTheStep.compile inputs language = .ok compiledRules :=
  evaluator_compiles.choose_spec.1

/-- The transform step of the evaluator over the relations of a PeTTa program. -/
noncomputable def stepSystem (O : Type) [DecidableEq O] (program : SpaceSemantics.Program) : GSLT :=
  programSystem O (specialized rows
    (relationGraph (QueryRulesOnTheStep.relations (relationEnv program) language)) {ρ | ρ ∈ compiledRules})

/-- A configuration is hosted by its encoding. -/
def EncodedConfiguration (configuration : Eval.Configuration) (term : Pattern) : Prop :=
  ∃ cells : List String, NamedSpaces.Store.EmptyTail configuration.state [] ∧
    (∀ name, name ∉ cells → configuration.state.cells name = none) ∧ term = encode configuration cells

/-- `Eval` and its authored presentation. -/
def presented (program : SpaceSemantics.Program) :
    OperationalCorrespondence (Eval.theory program) (sourceSystem (relationEnv program) language) where
  related := EncodedConfiguration
  readStep := by
    intro configuration term next same stepped
    obtain ⟨cells, vacant, covers, rfl⟩ := same
    have found := (Mettapedia.OSLF.Framework.TypeSynthesis.mem_rootFrontier_iff_langReducesUsing
      (relationEnv program) language ConfigurationLanguageDef.nonrecursive_rules _ next).mpr stepped
    rw [ConfigurationLanguageDef.frontier_eq_step program configuration cells vacant covers] at found
    obtain ⟨after, computed, rfl⟩ := List.mem_map.mp found
    have transition := (Eval.step_iff_transition program configuration after).mp (Option.mem_toList.mp computed)
    exact Or.inr ⟨after, transition, cellSupportAfter configuration cells,
      DeclarativeSpec.transition_empty_tail vacant transition, transition_support cells covers transition, rfl⟩
  forward := by
    intro configuration after term same transition
    obtain ⟨cells, vacant, covers, rfl⟩ := same
    refine ⟨encode after (cellSupportAfter configuration cells),
      (executionPath_nonempty_iff_multiStep _ _ _).mpr (.step ?_ (.refl _)), cellSupportAfter configuration cells,
      DeclarativeSpec.transition_empty_tail vacant transition, transition_support cells covers transition, rfl⟩
    refine (Mettapedia.OSLF.Framework.TypeSynthesis.mem_rootFrontier_iff_langReducesUsing
      (relationEnv program) language ConfigurationLanguageDef.nonrecursive_rules _ _).mp ?_
    rw [ConfigurationLanguageDef.frontier_eq_step program configuration cells vacant covers]
    exact List.mem_map.mpr
      ⟨after, Option.mem_toList.mpr ((Eval.step_iff_transition program configuration after).mpr transition), rfl⟩

/-- **PeTTa to transform**: `Eval` and the step of the compiled evaluator, one transition
for one firing, both ways. -/
noncomputable def evalOnTheStep (O : Type) [DecidableEq O] [Infinite O] (program : SpaceSemantics.Program) :
    OperationalCorrespondence (Eval.theory program) (stepSystem O program) :=
  (presented program).comp (QueryRulesOnTheStep.stepCorrespondence (relations_moded program)
    (relations_data program) (configurations_carrier program) compiledRules_compiled)

/-- A state of the step shows a configuration. -/
def Shows {O : Type} (configuration : Eval.Configuration) (state : SState O) : Prop :=
  ∃ cells : List String, NamedSpaces.Store.EmptyTail configuration.state [] ∧
    (∀ name, name ∉ cells → configuration.state.cells name = none) ∧
    ReadsBag state {Mettapedia.GSLT.Compilation.RootRewritesOnTheStep.encode (encode configuration cells)}

/-- A state shows at most one configuration. -/
theorem shows_unique {O : Type} [DecidableEq O] {state : SState O} {first second : Eval.Configuration}
    (left : Shows first state) (right : Shows second state) : first = second := by
  obtain ⟨cells, vacant, covers, reads⟩ := left
  obtain ⟨otherCells, otherVacant, otherCovers, otherReads⟩ := right
  have same := encode_injective (Multiset.singleton_inj.mp
    (readsAs_unique reads.readsAs.1 reads.readsAs.2 otherReads.readsAs.2))
  have decoded := congrArg decode same
  rw [decode_encode first cells vacant covers, decode_encode second otherCells otherVacant otherCovers] at decoded
  exact Option.some.inj decoded

/-- **What a call returns is exactly what a run of firings reads.** -/
theorem returns_on_the_step {O : Type} [DecidableEq O] [Infinite O] (program : SpaceSemantics.Program)
    (bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst) (before after : Effects.State)
    (expression : Atom) (answers : List Atom) {start : SState O}
    (shown : Shows { state := before, control := .evaluate bindings expression } start) :
    Eval.Returns program bindings before expression after answers ↔
      ∃ final, (stepSystem O program).MultiStep start final ∧ Shows (Eval.finished after answers [] []) final := by
  obtain ⟨cells, vacant, covers, reads⟩ := shown
  have related : (evalOnTheStep O program).related
      ({ state := before, control := .evaluate bindings expression } : Eval.Configuration) start :=
    ⟨_, ⟨cells, vacant, covers, rfl⟩, _, ⟨⟨_, cells, vacant, covers, rfl⟩, rfl⟩, reads⟩
  refine Iff.trans ?_ ((evalOnTheStep O program).reachable_iff
    (fun configuration => configuration = Eval.finished after answers [] [])
    (fun state => Shows (Eval.finished after answers [] []) state) (fun {origin current} hosted => ?_) related)
  · exact ⟨fun path => ⟨_, path, rfl⟩, fun ⟨_, path, same⟩ => by subst same; exact path⟩
  · obtain ⟨_, ⟨hostCells, hostVacant, hostCovers, rfl⟩, _, ⟨_, rfl⟩, hostReads⟩ := hosted
    have here : Shows origin current := ⟨hostCells, hostVacant, hostCovers, hostReads⟩
    exact ⟨fun same => same ▸ here, fun finished => shows_unique here finished⟩

#print axioms evalOnTheStep
#print axioms returns_on_the_step
#print axioms evaluator_compiles
#print axioms without_outputs_refused
#print axioms configurations_carrier
#print axioms relations_moded
#print axioms relations_data

end Mettapedia.Languages.MeTTa.PeTTa.EvalOnTheStep
