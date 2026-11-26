import Mettapedia.Languages.MeTTa.SpaceTheory.PeTTaExecution
import Mettapedia.GSLT.Compilation.Uniform.ScopedQueriesOnTheStep

/-!
# The live PeTTa theory on a single Transform program

Callability, argument demand, and application read the core atom list
of the state being rewritten. These are the only program-dependent
queries in the authored configuration rules. The query's new argument
is the already matched store, not a separately chosen registry; the
query inspects only its core. Other queries and all rule results are
unchanged. In particular, entering an already selected alternative
does not refetch a definition.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.SpaceTheory.PeTTaLiveOnTheStep

open Mettapedia.GSLT Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.Compilation
open Mettapedia.GSLT.Compilation.Uniform
open Mettapedia.GSLT.Compilation.Uniform.ScopedQueriesOnTheStep (Side expressionAt termAt)
open Mettapedia.GSLT.Compilation.RootRewritesOnTheStep (labelCode labelCode_injective encode_injective)
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.OSLFCore.Bridge
open Mettapedia.Languages.MeTTa.PeTTa
open ProgramReplay
open ConfigurationLanguageDef (language relationEnv relationRows)
open ConfigurationEncoding (stateData cellSupportAfter transition_support)
open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open NamesOnTheStep (Expr)
open RuleSyntax.Presentation.Schematic (Tm SState inst)
open RuleSyntax.Machines (row_of_singleton exists_reads)
open RuleSyntax.ComputedConditions
open PeTTaExecution (programAt)

def programQuestions : List String :=
  ["petta-application", "petta-raw-demand", "petta-evaluated-demand", "petta-callable", "petta-not-callable"]

def needsProgram (port : Nat) : Bool := (programQuestions.map labelCode).contains port

abbrev encoded (a : Atom) : Expr := RootRewritesOnTheStep.encode (GroundData.encode a)

abbrev configurationCode (configuration : Eval.Configuration) (names : List String) : Expr :=
  RootRewritesOnTheStep.encode (ConfigurationEncoding.encode configuration names)

/-- The second field of a tagged native expression. Both the store
and the configuration are such expressions. -/
def payloadPath : List Side :=
  [.right, .right, .left, .right, .right, .left, .right, .left]

def storeVariable : Nat := labelCode "state"

private theorem tagged_payload (tag field : Atom) (other : List Atom) :
    expressionAt payloadPath (encoded (.expression (tag :: field :: other))) = some (encoded field) := by
  simp [encoded, payloadPath, expressionAt, GroundData.encode, GroundData.encodeList,
    RootRewritesOnTheStep.encode, RootRewritesOnTheStep.encodeList]

theorem view_of_configuration (configuration : Eval.Configuration) (names : List String) :
    expressionAt payloadPath (configurationCode configuration names) =
      some (encoded (stateData configuration.state names)) := tagged_payload _ _ _

theorem core_of_store (state : Effects.State) (names : List String) :
    expressionAt payloadPath (encoded (stateData state names)) = some (encoded (.expression state.core)) :=
  tagged_payload _ _ _

def exposesStore (rule : RuleWithCondition Nat Tm) : Bool :=
  match rule.rule.body.take with
  | [head] =>
    match termAt payloadPath head with
    | some (.var name) => name == storeVariable
    | _ => false
  | _ => false

theorem all_compiled_rules_expose_store : EvalOnTheStep.compiledRules.all exposesStore = true := by
  have checked : (match QueryRulesOnTheStep.compile EvalOnTheStep.inputs language with
    | .ok rules => rules.all exposesStore
    | .error _ => false) = true := by decide +kernel
  rw [EvalOnTheStep.compiledRules_compiled] at checked
  exact checked

private theorem exposes_store_exact {r : RuleWithCondition Nat Tm} (listed : r ∈ EvalOnTheStep.compiledRules) :
    ∃ lhs, r.rule.body.take = [lhs] ∧ termAt payloadPath lhs = some (.var storeVariable) := by
  have checked := List.all_eq_true.mp all_compiled_rules_expose_store r listed
  unfold exposesStore at checked
  split at checked
  · rename_i head taken
    split at checked
    · rename_i name exactPath
      have same : name = storeVariable := by simpa using checked
      exact ⟨head, taken, same ▸ exactPath⟩
    · cases checked
  · cases checked

private theorem store_from_take {r : RuleWithCondition Nat Tm} (listed : r ∈ EvalOnTheStep.compiledRules)
    (configuration : Eval.Configuration) (names : List String) (assign : Nat → Expr) (rest : Multiset Expr)
    (taken : (r.rule.body.take.map (inst assign) : Multiset Expr) + rest = {configurationCode configuration names}) :
    inst assign (.var storeVariable) = encoded (stateData configuration.state names) := by
  obtain ⟨lhs, shape, found⟩ := exposes_store_exact listed
  rw [shape] at taken
  have matched : inst assign lhs = configurationCode configuration names :=
    (row_of_singleton (by simpa only [List.map_cons, List.map_nil, Multiset.coe_singleton] using taken)).1
  have projection := ScopedQueriesOnTheStep.expression_at_inst payloadPath assign lhs _ found
  rw [matched, view_of_configuration] at projection
  exact (Option.some.inj projection).symm

theorem answers_without_program (first second : SpaceSemantics.Program)
    (name : String) (arguments : List Pattern) (unused : needsProgram (labelCode name) = false) :
    relationRows first name arguments = relationRows second name arguments := by
  unfold relationRows
  split <;> try rfl
  all_goals simp [needsProgram, programQuestions] at unused

def pinned (atoms : List Atom) : Relations :=
  QueryRulesOnTheStep.relations (relationEnv (programAt atoms)) language

private theorem pinned_without_program (atoms : List Atom) (name : Nat) (arguments : List Expr) (reply : Expr)
    (unused : needsProgram name = false) : pinned [] name arguments reply ↔ pinned atoms name arguments reply := by
  change (arguments = [] ∧ ∃ q values, name = labelCode q ∧ reply = RootRewritesOnTheStep.encodeList values ∧
      values ∈ QueryPremises.queryRows (relationEnv (programAt [])) language q values) ↔ _
  constructor
  · rintro ⟨empty, query, values, rfl, rfl, known⟩
    change values ∈ Mettapedia.OSLF.MeTTaIL.Engine.builtinRelationTuples language query values ++
      relationRows (programAt []) query values at known
    rw [answers_without_program (programAt []) (programAt atoms) query values unused] at known
    exact ⟨empty, query, values, rfl, rfl, known⟩
  · rintro ⟨empty, query, values, rfl, rfl, known⟩
    change values ∈ Mettapedia.OSLF.MeTTaIL.Engine.builtinRelationTuples language query values ++
      relationRows (programAt atoms) query values at known
    rw [answers_without_program (programAt atoms) (programAt []) query values unused] at known
    exact ⟨empty, query, values, rfl, rfl, known⟩

def operations : Relations :=
  fun name arguments reply =>
    if needsProgram name then
      ∃ store tail atoms, arguments = store :: tail ∧
        expressionAt payloadPath store = some (encoded (.expression atoms)) ∧ pinned atoms name tail reply
    else pinned [] name arguments reply

theorem operations_at (state : Effects.State) (names : List String) (name : Nat) (args : List Expr) (reply : Expr) :
    operations name (if needsProgram name then encoded (stateData state names) :: args else args) reply ↔
      pinned state.core name args reply := by
  by_cases uses : needsProgram name = true
  · simp only [operations, uses, if_true]
    constructor
    · rintro ⟨store, tail, atoms, equal, captured, selected⟩
      obtain ⟨rfl, rfl⟩ := List.cons.inj equal
      rw [core_of_store] at captured
      have same := Atom.expression.inj (GroundData.encode_injective (encode_injective (Option.some.inj captured)))
      subst atoms
      exact selected
    · intro selected
      exact ⟨_, args, state.core, rfl, core_of_store state names, selected⟩
  · simp only [operations, uses]
    exact pinned_without_program state.core name args reply (Bool.eq_false_iff.mpr uses)

def scopeRule (rule : RuleWithCondition Nat Tm) : RuleWithCondition Nat Tm :=
  ScopedQueriesOnTheStep.rule needsProgram (.var storeVariable) rule

noncomputable def rules : List (RuleWithCondition Nat Tm) := EvalOnTheStep.compiledRules.map scopeRule

theorem rule_count : rules.length = 41 := by
  rw [rules, List.length_map]
  exact EvalOnTheStep.evaluator_compiles.choose_spec.2

private theorem scoped_correct (configuration : Eval.Configuration) (names : List String)
    (after : Multiset Expr) {r : RuleWithCondition Nat Tm} (listed : r ∈ EvalOnTheStep.compiledRules) :
    RelationStep operations (scopeRule r) {configurationCode configuration names} after ↔
      RelationStep (pinned configuration.state.core) r {configurationCode configuration names} after :=
  ScopedQueriesOnTheStep.exact_step needsProgram (.var storeVariable) r operations
    (pinned configuration.state.core) _ after (encoded (stateData configuration.state names))
    (store_from_take listed configuration names) (operations_at configuration.state names)

theorem relation_step_iff (configuration : Eval.Configuration) (names : List String)
    (vacant : NamedSpaces.Store.EmptyTail configuration.state [])
    (covers : ∀ name, name ∉ names → configuration.state.cells name = none) (after : Multiset Expr) :
    (∃ r ∈ rules, RelationStep operations r {configurationCode configuration names} after) ↔
      ∃ target, LiveRegistry.theory.Step configuration target ∧
        after = {configurationCode target (cellSupportAfter configuration names)} := by
  have pinnedStep := PeTTaExecution.snapshot_relation_step_iff configuration.state.core configuration names vacant covers after
  constructor
  · rintro ⟨r, member, fires⟩
    obtain ⟨original, listed, rfl⟩ := List.mem_map.mp member
    obtain ⟨target, step, produced⟩ := pinnedStep.mp ⟨original, listed, (scoped_correct configuration names after listed).mp fires⟩
    exact ⟨target, (PeTTaExecution.live_rewrite_iff _ _).mpr step, produced⟩
  · rintro ⟨target, step, produced⟩
    obtain ⟨original, listed, related⟩ := pinnedStep.mpr ⟨target, (PeTTaExecution.live_rewrite_iff _ _).mp step, produced⟩
    exact ⟨scopeRule original, List.mem_map_of_mem listed, (scoped_correct configuration names after listed).mpr related⟩

theorem rule_shape {r : RuleWithCondition Nat Tm} (member : r ∈ rules) :
    r.rule.collect = [] ∧ r.rule.body.checks.all RuleSyntax.Presentation.Schematic.isGuard = true ∧ r.RangeRestrictedWith := by
  obtain ⟨original, listed, rfl⟩ := List.mem_map.mp member
  have ok := PeTTaExecution.compiled_rule_shape listed
  exact ⟨ok.1, ok.2.1, ScopedQueriesOnTheStep.still_restricted _ _ _ ok.2.2⟩

private noncomputable abbrev program :=
  specialized rows (relationGraph operations) {r | r ∈ rules}

noncomputable def theory (O : Type) [DecidableEq O] : GSLT := programSystem O program

private theorem positive : ∀ r ∈ program, DeterminedPositive r :=
  relations_fragment (fun _ member => (rule_shape member).1) (fun _ member => (rule_shape member).2.1)
    (fun _ member => (rule_shape member).2.2)

theorem realize_step {O : Type} [DecidableEq O] [Infinite O] {before after : Eval.Configuration} {start : SState O}
    (shown : EvalOnTheStep.Shows before start) (stepped : LiveRegistry.theory.Step before after) :
    ∃ final, (theory O).Step start final ∧ EvalOnTheStep.Shows after final := by
  obtain ⟨names, vacant, covers, reads⟩ := shown
  obtain ⟨rule, listed, fires⟩ := (relation_step_iff before names vacant covers _).mpr ⟨after, stepped, rfl⟩
  obtain ⟨compiled, member, matched⟩ := (rewritesBy_relations_iff (P := {r | r ∈ rules})).mpr ⟨rule, listed, fires⟩
  obtain ⟨firing, admitted, _, result⟩ := readsBag_forward_determined member (positive compiled member) reads matched
  exact ⟨_, ⟨firing, admitted, rfl⟩, cellSupportAfter before names,
    DeclarativeSpec.transition_empty_tail vacant ((PeTTaExecution.live_rewrite_iff _ _).mp stepped),
    transition_support names covers ((PeTTaExecution.live_rewrite_iff _ _).mp stepped), result⟩

theorem reflect_step {O : Type} [DecidableEq O] {before : Eval.Configuration} {start final : SState O}
    (shown : EvalOnTheStep.Shows before start) (fired : (theory O).Step start final) :
    ∃ after, LiveRegistry.theory.Step before after ∧ EvalOnTheStep.Shows after final := by
  obtain ⟨names, vacant, covers, reads⟩ := shown
  obtain ⟨firing, admitted, rfl⟩ := fired
  obtain ⟨bag, matched, result⟩ := readsBag_backward_determined reads firing admitted
    (makesDetermined_of_writes (positive firing.rule firing.member).2.2)
  obtain ⟨after, stepped, rfl⟩ := (relation_step_iff before names vacant covers bag).mp
    (rewritesBy_relations_iff.mp ⟨firing.rule, firing.member, matched⟩)
  exact ⟨after, stepped, cellSupportAfter before names,
    DeclarativeSpec.transition_empty_tail vacant ((PeTTaExecution.live_rewrite_iff _ _).mp stepped),
    transition_support names covers ((PeTTaExecution.live_rewrite_iff _ _).mp stepped), result⟩

theorem realize_path {O : Type} [DecidableEq O] [Infinite O] {before after : Eval.Configuration} {start : SState O}
    (shown : EvalOnTheStep.Shows before start) (path : ExecutionPath LiveRegistry.theory before after) :
    ∃ final, ∃ fired : ExecutionPath (theory O) start final,
      EvalOnTheStep.Shows after final ∧ fired.length = path.length := by
  induction path generalizing start with
  | refl _ => exact ⟨start, .refl start, shown, rfl⟩
  | cons step rest ih =>
    obtain ⟨_, fired, readNext⟩ := realize_step shown step.down
    obtain ⟨final, tail, readEnd, length⟩ := ih readNext
    exact ⟨final, .cons ⟨fired⟩ tail, readEnd, congrArg (· + 1) length⟩

theorem reflect_path {O : Type} [DecidableEq O] {before : Eval.Configuration} {start final : SState O}
    (shown : EvalOnTheStep.Shows before start) (fired : ExecutionPath (theory O) start final) :
    ∃ after, ∃ path : ExecutionPath LiveRegistry.theory before after,
      EvalOnTheStep.Shows after final ∧ path.length = fired.length := by
  induction fired generalizing before with
  | refl _ => exact ⟨before, .refl before, shown, rfl⟩
  | cons first rest ih =>
    obtain ⟨_, step, readNext⟩ := reflect_step shown first.down
    obtain ⟨after, tail, readEnd, length⟩ := ih readNext
    exact ⟨after, .cons ⟨step⟩ tail, readEnd, congrArg (· + 1) length⟩

theorem shows_snapshot (initial : Snapshot) :
    ∃ state : SState Nat, EvalOnTheStep.Shows initial.decode state := by
  obtain ⟨state, shown⟩ := exists_reads {configurationCode initial.decode initial.cellNames}
  exact ⟨state, initial.cellNames, initial.decode_empty_tail, initial.decode_cell_support, shown⟩

/-- The executable source traversal derives a path with the original
step count; a budget does not charge the unused part after completion. -/
theorem snapshot_budget_path (fuel : Nat) (initial : Snapshot) :
    ∃ path : ExecutionPath LiveRegistry.theory initial.decode (LiveRegistry.nativeAdvance fuel initial).decode,
      path.length = (LiveRegistry.emitTrace fuel initial).length := by
  induction fuel generalizing initial with
  | zero => exact ⟨.refl _, rfl⟩
  | succ fuel ih =>
    cases advanced : LiveRegistry.nativeStep initial with
    | none =>
      rw [LiveRegistry.nativeAdvance, LiveRegistry.emitTrace, advanced]
      exact ⟨.refl _, rfl⟩
    | some next =>
      rw [LiveRegistry.nativeAdvance, LiveRegistry.emitTrace, advanced]
      obtain ⟨path, length⟩ := ih next
      exact ⟨.cons ⟨LiveRegistry.nativeStep_source _ _ advanced⟩ path, congrArg (· + 1) length⟩

theorem realizes_snapshot_budget {O : Type} [DecidableEq O] [Infinite O] (fuel : Nat) (initial : Snapshot)
    {start : SState O} (shown : EvalOnTheStep.Shows initial.decode start) :
    ∃ final, ∃ fired : ExecutionPath (theory O) start final,
      EvalOnTheStep.Shows (LiveRegistry.nativeAdvance fuel initial).decode final ∧
      fired.length = (LiveRegistry.emitTrace fuel initial).length := by
  obtain ⟨sourcePath, count⟩ := snapshot_budget_path fuel initial
  obtain ⟨final, fired, done, length⟩ := realize_path shown sourcePath
  exact ⟨final, fired, done, length.trans count⟩

end Mettapedia.Languages.MeTTa.SpaceTheory.PeTTaLiveOnTheStep
