import Mettapedia.Languages.MeTTa.SpaceTheory.PeTTaLiveOnTheStep
import Mettapedia.Languages.MeTTa.SpaceTheory.PeTTaEquationEntry

/-!
# An explicit equational PeTTa request

An already ready call asks for equation evidence and an ordinary captured
frontier in the same live core. Its stack and input/output are carried
structurally. The result is the ordinary configuration for the sequence
of alternatives, including an admitted empty sequence. No ordinary
call is changed by this extension.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.SpaceTheory.PeTTaEquationalOnTheStep

open Mettapedia.GSLT Mettapedia.GSLT.IndexedOperational Mettapedia.GSLT.Compilation
open Mettapedia.GSLT.Compilation.Uniform
open RootRewritesOnTheStep (appTerm symTerm labelCode encode_injective inst_appTerm inst_symTerm)
open ScopedQueriesOnTheStep (expressionAt termAt)
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis (equalityGSLT)
open Mettapedia.OSLF.MeTTaIL.PatternCode (collectionCode)
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.OSLFCore.Bridge
open Mettapedia.Languages.MeTTa.PeTTa
open ConfigurationEncoding (stateData controlData frameData configurationData cellSupportAfter transition_support)
open ProgramReplay
open PeTTaLiveOnTheStep (configurationCode encoded payloadPath core_of_store)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open NamesOnTheStep (Expr)
open RuleSyntax.Presentation.Schematic (Tm SState inst toTerm inst_toTerm isGuard)
open RuleSyntax.Machines (ReadsBag row_of_singleton)
open RuleSyntax.ComputedConditions
open StateRulesOnTheStep (packet pattern fields instantiate_fields instantiate_packet instance_var)

structure Request where
  state : Effects.State
  call : Atom
  frames : List Eval.Frame
  input : List Atom
  output : List Atom

def Request.entered (request : Request) (alternatives : List Eval.Control) : Eval.Configuration :=
  ⟨request.state, .sequence alternatives [], request.frames, request.input, request.output⟩

inductive State where
  | ready (value : Request)
  | running (configuration : Eval.Configuration)

def State.store : State → Effects.State
  | .ready pending => pending.state
  | .running configuration => configuration.state

def Request.fields (request : Request) (names : List String) : List Expr :=
  [encoded (stateData request.state names), encoded (.expression (request.frames.map frameData)),
    encoded (.expression request.input), encoded (.expression request.output), encoded request.call]

def encode (s : State) (names : List String) : Expr :=
  match s with
  | .ready request => packet 7 (request.fields names)
  | .running current => configurationCode current names

def Shows {O : Type} (s : State) (target : SState O) : Prop :=
  ∃ names, NamedSpaces.Store.EmptyTail s.store [] ∧
    (∀ name, name ∉ names → s.store.cells name = none) ∧ ReadsBag target {encode s names}

abbrev EntryView := List Atom → List Atom

/-- Only the pending request uses this choice of declarations. Later
calls and effects still read the reached store through the live theory. -/
inductive Transition (entryView : EntryView := id) : State → State → Prop where
  | enter {request alternatives} :
      (PeTTaEquationEntry.theory (entryView request.state.core)).Step (.inl request.call) (.inr alternatives) →
      Transition entryView (.ready request) (.running (request.entered alternatives))
  | ordinary {before after} : LiveRegistry.theory.Step before after →
      Transition entryView (.running before) (.running after)

def source (entryView : EntryView := id) : GSLT := equalityGSLT State (Transition entryView)

def SameCore (store : Expr) (atoms : List Atom) : Prop :=
  expressionAt payloadPath store = some (encoded (.expression atoms))

def equivalentAt (entryView : EntryView) (arguments : List Expr) (reply : Expr) : Prop :=
  ∃ store atoms call representative,
    arguments = [store, encoded call] ∧ SameCore store atoms ∧ AtomEquations.Equivalent (entryView atoms) call representative ∧
      reply = encoded representative

def captureAt (entryView : EntryView) (arguments : List Expr) (reply : Expr) : Prop :=
  ∃ store atoms representative alternatives,
    arguments = [store, encoded representative] ∧ SameCore store atoms ∧
      PeTTaEquationEntry.select (entryView atoms) representative = some alternatives ∧
      reply = encoded (controlData (.sequence alternatives []))

def operations (entryView : EntryView) : Relations := fun name args reply =>
  if name = 1 then equivalentAt entryView args reply
  else if name = 2 then captureAt entryView args reply
  else PeTTaLiveOnTheStep.operations name args reply

private def taken : Tm := pattern 7 ([0, 1, 2, 3, 4].map .var)

private def configurationFields (parts : List Expr) : Expr :=
  packet 2 [.sym (labelCode "ground-atom-expression-v1"),
    .app (.sym 6) (.app (.sym (collectionCode .vec)) (.app (fields parts) (.sym 0)))]

private def configTag : Expr := encoded (.symbol "petta-configuration-v1")

private def made : Tm :=
  let vec := appTerm (symTerm 6) (appTerm (symTerm (collectionCode .vec))
    (appTerm ([toTerm configTag, .var 0, .var 6, .var 1, .var 2, .var 3].foldr appTerm (symTerm 0)) (symTerm 0)))
  appTerm (symTerm 2) (appTerm (symTerm (labelCode "ground-atom-expression-v1")) (appTerm vec (symTerm 0)))

private def equality : Condition Nat Tm := { name := 1, arguments := [.var 0, .var 4], value := .var 5 }
private def capture : Condition Nat Tm := { name := 2, arguments := [.var 0, .var 5], value := .var 6 }

def entryRule : RuleWithCondition Nat Tm := StateRulesOnTheStep.rule taken made [equality, capture]

private theorem encode_cfg (configuration : Eval.Configuration) (names : List String) :
    configurationCode configuration names = configurationFields
      [configTag, encoded (stateData configuration.state names), encoded (controlData configuration.control),
        encoded (.expression (configuration.frames.map frameData)), encoded (.expression configuration.input),
        encoded (.expression configuration.output)] := by
  change encoded (configurationData configuration names) = _
  simp [configurationData, configurationFields, configTag, packet, fields, encoded, GroundData.encode, GroundData.encodeList,
    RootRewritesOnTheStep.encode, RootRewritesOnTheStep.encodeList, RootRewritesOnTheStep.optionRow]

theorem running_tag (configuration : Eval.Configuration) (names : List String) :
    ∃ parts, encode (.running configuration) names = packet 2 parts := by
  change ∃ parts, configurationCode configuration names = packet 2 parts
  rw [encode_cfg]
  exact ⟨_, rfl⟩

private theorem instantiate_made (assign : Nat → Expr) :
    inst assign made = configurationFields [configTag, assign 0, assign 6, assign 1, assign 2, assign 3] := by
  simp only [made, configurationFields, instantiate_fields, inst_appTerm, inst_symTerm,
    List.map_cons, List.map_nil, inst_toTerm, instance_var]
  rfl

private theorem entry_restricted : entryRule.RangeRestrictedWith := by
  apply StateRulesOnTheStep.restricted
  intro name used
  have symbols : RuleSyntax.Machines.unknowns made = [0, 6, 1, 2, 3] := by decide +kernel
  have listed : name ∈ [0, 6, 1, 2, 3] := symbols ▸ used
  by_cases answer : name = 6
  · subst name
    exact Or.inr ⟨capture, List.mem_cons_of_mem _ List.mem_cons_self, List.mem_cons_self⟩
  · apply Or.inl
    change name ∈ [0, 1, 2, 3, 4]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at listed ⊢
    tauto

private theorem core_exact (state : Effects.State) (names : List String) (atoms : List Atom)
    (read : SameCore (encoded (stateData state names)) atoms) : atoms = state.core := by
  unfold SameCore at read
  rw [core_of_store] at read
  exact (Atom.expression.inj (GroundData.encode_injective (encode_injective (Option.some.inj read)))).symm

private theorem equality_exact (entryView : EntryView) (state : Effects.State) (names : List String) (query : Atom) (value : Expr) :
    operations entryView 1 [encoded (stateData state names), encoded query] value ↔
      ∃ rep, AtomEquations.Equivalent (entryView state.core) query rep ∧ value = encoded rep := by
  change equivalentAt entryView _ _ ↔ _
  constructor
  · rintro ⟨store, atoms, call, rep, args, core, same, made⟩
    simp only [List.cons.injEq, and_true] at args
    obtain ⟨rfl, eq⟩ := args
    obtain rfl := core_exact state names atoms core
    obtain rfl := GroundData.encode_injective (encode_injective eq)
    exact ⟨rep, same, made⟩
  · rintro ⟨rep, same, made⟩
    exact ⟨_, state.core, query, rep, rfl, core_of_store state names, same, made⟩

private theorem capture_exact (entryView : EntryView) (state : Effects.State) (names : List String) (rep : Atom) (value : Expr) :
    operations entryView 2 [encoded (stateData state names), encoded rep] value ↔
      ∃ alternatives, PeTTaEquationEntry.select (entryView state.core) rep = some alternatives ∧
        value = encoded (controlData (.sequence alternatives [])) := by
  change captureAt entryView _ _ ↔ _
  constructor
  · rintro ⟨store, atoms, actual, alternatives, args, core, selected, made⟩
    simp only [List.cons.injEq, and_true] at args
    obtain ⟨rfl, eq⟩ := args
    obtain rfl := core_exact state names atoms core
    obtain rfl := GroundData.encode_injective (encode_injective eq)
    exact ⟨alternatives, selected, made⟩
  · rintro ⟨alternatives, selected, made⟩
    exact ⟨_, state.core, rep, alternatives, rfl, core_of_store state names, selected, made⟩

theorem entry_exact (entryView : EntryView) (request : Request) (names : List String) (after : Multiset Expr) :
    RelationStep (operations entryView) entryRule {encode (.ready request) names} after ↔
      ∃ alternatives, (PeTTaEquationEntry.theory (entryView request.state.core)).Step
      (.inl request.call) (.inr alternatives) ∧
        after = {configurationCode (request.entered alternatives) names} := by
  rw [entryRule, StateRulesOnTheStep.instance_iff]
  constructor
  · rintro ⟨assign, matched, checks, product⟩
    simp only [taken, encode, Request.fields, instantiate_packet, instance_var, List.map_cons, List.map_nil,
      StateRulesOnTheStep.packet_eq_iff, List.cons.injEq, and_true, true_and] at matched
    obtain ⟨s, frames, i, o, call⟩ := matched
    have eq := checks equality List.mem_cons_self
    have choose := checks capture (List.mem_cons_of_mem _ List.mem_cons_self)
    simp only [equality, List.map_cons, List.map_nil, instance_var, s, call] at eq
    obtain ⟨rep, same, witness⟩ := (equality_exact entryView request.state names request.call _).mp eq
    simp only [capture, List.map_cons, List.map_nil, instance_var, s, witness] at choose
    obtain ⟨alternatives, selected, admitted⟩ := (capture_exact entryView request.state names rep _).mp choose
    refine ⟨alternatives, (PeTTaEquationEntry.entry_exact _ _ _).mpr ⟨rep, same, selected⟩, ?_⟩
    rw [instantiate_made, s, admitted, frames, i, o] at product
    rw [encode_cfg]
    exact product
  · rintro ⟨alternatives, admitted, rfl⟩
    obtain ⟨rep, same, chosen⟩ := (PeTTaEquationEntry.entry_exact _ _ _).mp admitted
    let tape := request.fields names ++ [encoded rep, encoded (controlData (.sequence alternatives []))]
    let assign := fun n : Nat => tape[n]?.getD (.sym 0)
    refine ⟨assign, rfl, ?_, ?_⟩
    · intro condition member
      rcases List.mem_cons.mp member with rfl | later
      · exact (equality_exact entryView request.state names request.call _).mpr ⟨rep, same, rfl⟩
      · obtain rfl : condition = capture := List.mem_singleton.mp later
        exact (capture_exact entryView request.state names rep _).mpr ⟨alternatives, chosen, rfl⟩
    · rw [instantiate_made, encode_cfg]
      rfl

private def normalRoot (r : RuleWithCondition Nat Tm) : Bool :=
  match r.rule.body.take with
  | [root] =>
    match termAt [.left] root with
    | some (.const (.sym tag)) => tag == 2
    | _ => false
  | _ => false

private def separatePorts (r : RuleWithCondition Nat Tm) : Bool :=
  r.conditions.all fun c => c.name != 1 && c.name != 2

private theorem static_checks : EvalOnTheStep.compiledRules.all (fun r => normalRoot r && separatePorts r) = true := by
  have tested : (match QueryRulesOnTheStep.compile EvalOnTheStep.inputs ConfigurationLanguageDef.language with
    | .ok rules => rules.all (fun r => normalRoot r && separatePorts r)
    | .error _ => false) = true := by decide +kernel
  rw [EvalOnTheStep.compiledRules_compiled] at tested
  exact tested

private theorem original_shape {r : RuleWithCondition Nat Tm} (member : r ∈ EvalOnTheStep.compiledRules) :
    normalRoot r = true ∧ separatePorts r = true := by
  have known := List.all_eq_true.mp static_checks r member
  simpa only [Bool.and_eq_true] using known

private theorem old_tag {r : RuleWithCondition Nat Tm} (listed : r ∈ PeTTaLiveOnTheStep.rules)
    {rel : Relations} {tag : Nat} {parts : List Expr} {after : Multiset Expr}
    (fired : RelationStep rel r {packet tag parts} after) : tag = 2 := by
  obtain ⟨old, member, rfl⟩ := List.mem_map.mp listed
  have root := (original_shape member).1
  unfold normalRoot at root
  split at root
  · rename_i lhs one
    split at root
    · rename_i code expected
      have codeEq : code = 2 := by simpa using root
      rw [codeEq] at expected
      obtain ⟨assign, rest, consumed, _, _, _, _⟩ := fired
      change (old.rule.body.take.map (inst assign) : Multiset Expr) + rest = _ at consumed
      rw [one] at consumed
      have word := (row_of_singleton (by simpa only [List.map_cons, List.map_nil, Multiset.coe_singleton] using consumed)).1
      have observed := ScopedQueriesOnTheStep.expression_at_inst [.left] assign lhs _ expected
      rw [word] at observed
      exact Expr.sym.inj (Option.some.inj observed)
    · cases root
  · cases root

private theorem ordinary_operations (entryView : EntryView) {r : RuleWithCondition Nat Tm} (listed : r ∈ PeTTaLiveOnTheStep.rules)
    (before after : Multiset Expr) :
    RelationStep (operations entryView) r before after ↔ RelationStep PeTTaLiveOnTheStep.operations r before after := by
  obtain ⟨old, member, rfl⟩ := List.mem_map.mp listed
  apply StateRulesOnTheStep.operations_iff
  intro cond present args reply
  obtain ⟨previous, used, rfl⟩ := List.mem_map.mp present
  have different := List.all_eq_true.mp (original_shape member).2 previous used
  simp only [Bool.and_eq_true, bne_iff_ne] at different
  change operations entryView previous.name args reply ↔ PeTTaLiveOnTheStep.operations previous.name args reply
  unfold operations
  rw [if_neg different.1, if_neg different.2]

def nextNames (before : State) (names : List String) : List String :=
  match before with
  | .ready _ => names
  | .running current => cellSupportAfter current names

noncomputable def rules : List (RuleWithCondition Nat Tm) := entryRule :: PeTTaLiveOnTheStep.rules

private noncomputable abbrev program (entryView : EntryView) :=
  specialized rows (relationGraph (operations entryView)) {r | r ∈ rules}

noncomputable def theory (O : Type) [DecidableEq O] (entryView : EntryView := id) : GSLT :=
  programSystem O (program entryView)

theorem relation_step_iff (entryView : EntryView) (before : State) (names : List String) (vacant : NamedSpaces.Store.EmptyTail before.store [])
    (covers : ∀ name, name ∉ names → before.store.cells name = none) (after : Multiset Expr) :
    (∃ r ∈ rules, RelationStep (operations entryView) r {encode before names} after) ↔
      ∃ next, Transition entryView before next ∧ after = {encode next (nextNames before names)} := by
  cases before with
  | ready request =>
    constructor
    · rintro ⟨r, listed, fires⟩
      rcases List.mem_cons.mp listed with rfl | old
      · obtain ⟨chosen, allowed, made⟩ := (entry_exact entryView request names after).mp fires
        exact ⟨_, .enter allowed, made⟩
      · have impossible := old_tag (tag := 7) old fires
        cases impossible
    · rintro ⟨next, advances, made⟩
      cases advances with
      | enter allowed =>
        exact ⟨entryRule, List.mem_cons_self, (entry_exact entryView request names after).mpr ⟨_, allowed, made⟩⟩
  | running current =>
    constructor
    · rintro ⟨r, listed, fires⟩
      rcases List.mem_cons.mp listed with rfl | old
      · change RelationStep (operations entryView) entryRule {configurationCode current names} after at fires
        rw [encode_cfg, configurationFields, entryRule, taken] at fires
        have impossible := StateRulesOnTheStep.input_tag (writtenTag := 7) (seenTag := 2) fires
        cases impossible
      · obtain ⟨target, legal, made⟩ := (PeTTaLiveOnTheStep.relation_step_iff current names vacant covers after).mp
          ⟨r, old, (ordinary_operations entryView old _ _).mp fires⟩
        exact ⟨_, .ordinary legal, made⟩
    · rintro ⟨next, moves, made⟩
      cases moves with
      | ordinary legal =>
        obtain ⟨r, old, fired⟩ := (PeTTaLiveOnTheStep.relation_step_iff current names vacant covers after).mpr
          ⟨_, legal, made⟩
        exact ⟨r, List.mem_cons_of_mem _ old, (ordinary_operations entryView old _ _).mpr fired⟩

private theorem shape {r : RuleWithCondition Nat Tm} (member : r ∈ rules) :
    r.rule.collect = [] ∧ r.rule.body.checks.all isGuard = true ∧ r.RangeRestrictedWith := by
  rcases List.mem_cons.mp member with rfl | old
  · exact ⟨rfl, rfl, entry_restricted⟩
  · exact PeTTaLiveOnTheStep.rule_shape old

private theorem positive (entryView : EntryView) : ∀ r ∈ program entryView, DeterminedPositive r :=
  relations_fragment (fun _ member => (shape member).1) (fun _ member => (shape member).2.1)
    (fun _ member => (shape member).2.2)

private theorem carrying {entryView : EntryView} {before after : State}
    (step : Transition entryView before after) (names : List String)
    (vacant : NamedSpaces.Store.EmptyTail before.store [])
    (covers : ∀ name, name ∉ names → before.store.cells name = none) :
    NamedSpaces.Store.EmptyTail after.store [] ∧
      ∀ name, name ∉ nextNames before names → after.store.cells name = none := by
  cases step with
  | enter _ => exact ⟨vacant, covers⟩
  | ordinary moved =>
    have source := (PeTTaExecution.live_rewrite_iff _ _).mp moved
    exact ⟨DeclarativeSpec.transition_empty_tail vacant source, transition_support names covers source⟩

theorem realize_step {O : Type} [DecidableEq O] [Infinite O] {entryView : EntryView}
    {before after : State} {start : SState O}
    (shown : Shows before start) (moved : (source entryView).Step before after) :
    ∃ final, (theory O entryView).Step start final ∧ Shows after final := by
  obtain ⟨names, vacant, covers, read⟩ := shown
  obtain ⟨r, listed, fires⟩ := (relation_step_iff entryView before names vacant covers _).mpr ⟨after, moved, rfl⟩
  obtain ⟨compiled, member, matched⟩ := (rewritesBy_relations_iff (P := {r | r ∈ rules})).mpr ⟨r, listed, fires⟩
  obtain ⟨firing, admitted, _, made⟩ := readsBag_forward_determined member (positive entryView compiled member) read matched
  obtain ⟨newVacant, newCovers⟩ := carrying moved names vacant covers
  exact ⟨_, ⟨firing, admitted, rfl⟩, nextNames before names, newVacant, newCovers, made⟩

theorem reflect_step {O : Type} [DecidableEq O] {entryView : EntryView} {before : State} {start final : SState O}
    (shown : Shows before start) (fired : (theory O entryView).Step start final) :
    ∃ after, (source entryView).Step before after ∧ Shows after final := by
  obtain ⟨names, vacant, covers, read⟩ := shown
  obtain ⟨firing, admitted, rfl⟩ := fired
  obtain ⟨bag, matched, readBack⟩ := readsBag_backward_determined read firing admitted
    (makesDetermined_of_writes (positive entryView firing.rule firing.member).2.2)
  obtain ⟨after, moves, rfl⟩ := (relation_step_iff entryView before names vacant covers bag).mp
    (rewritesBy_relations_iff.mp ⟨firing.rule, firing.member, matched⟩)
  obtain ⟨newVacant, newCovers⟩ := carrying moves names vacant covers
  exact ⟨after, moves, nextNames before names, newVacant, newCovers, readBack⟩

theorem realize_path {O : Type} [DecidableEq O] [Infinite O] {entryView : EntryView}
    {before after : State} {start : SState O}
    (shown : Shows before start) (path : ExecutionPath (source entryView) before after) :
    ∃ final, ∃ fired : ExecutionPath (theory O entryView) start final, Shows after final ∧ fired.length = path.length := by
  induction path generalizing start with
  | refl _ => exact ⟨start, .refl start, shown, rfl⟩
  | cons step rest ih =>
    obtain ⟨_, fired, readNext⟩ := realize_step (entryView := entryView) shown step.down
    obtain ⟨final, tail, readEnd, length⟩ := ih readNext
    exact ⟨final, .cons ⟨fired⟩ tail, readEnd, congrArg (· + 1) length⟩

theorem reflect_path {O : Type} [DecidableEq O] {entryView : EntryView} {before : State} {start final : SState O}
    (shown : Shows before start) (fired : ExecutionPath (theory O entryView) start final) :
    ∃ after, ∃ path : ExecutionPath (source entryView) before after, Shows after final ∧ path.length = fired.length := by
  induction fired generalizing before with
  | refl _ => exact ⟨before, .refl before, shown, rfl⟩
  | cons first rest ih =>
    obtain ⟨_, step, next⟩ := reflect_step (entryView := entryView) shown first.down
    obtain ⟨after, tail, done, length⟩ := ih next
    exact ⟨after, .cons ⟨step⟩ tail, done, congrArg (· + 1) length⟩

def ordinaryPath {before after : Eval.Configuration} :
    ExecutionPath LiveRegistry.theory before after →
      ExecutionPath source (State.running before) (State.running after)
  | .refl current => .refl (State.running current)
  | .cons first rest => .cons ⟨Transition.ordinary (entryView := id) first.down⟩ (ordinaryPath rest)

theorem ordinary_path_length {before after : Eval.Configuration}
    (path : ExecutionPath LiveRegistry.theory before after) :
    (ordinaryPath path).length = path.length := by
  induction path with
  | refl _ => rfl
  | cons first rest ih => exact congrArg (· + 1) ih

end Mettapedia.Languages.MeTTa.SpaceTheory.PeTTaEquationalOnTheStep
