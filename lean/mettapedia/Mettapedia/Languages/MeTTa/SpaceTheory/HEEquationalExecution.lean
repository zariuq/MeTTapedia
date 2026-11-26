import Mettapedia.Languages.MeTTa.SpaceTheory.HEEquationEntry
import Mettapedia.GSLT.Compilation.Uniform.EquationalEntryRules
import Mettapedia.GSLT.Equations.EntryReadouts

/-!
# Explicit equational HE entry on the live Transform program

The request holds the actual ready call, not an already picked spelling.
The entry firing asks for an equation witness and a complete ordinary
frontier at that representative in the same space. It enters exactly
that frontier. Subsequent steps are the existing live HE program.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.SpaceTheory.HEEquationalExecution

open Mettapedia.GSLT Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.Compilation.Uniform
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis (equalityGSLT)
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed (Result Policy WorldEnvironment)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps (EquationWork)
open Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual (Task Continuation WorldConfiguration)
open Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual (WorldStepWith)
open Mettapedia.Languages.MeTTa.HE.ContextualData (taskData taskData_injective)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open NamesOnTheStep (Expr)
open RuleSyntax.Presentation.Schematic (Tm SState isGuard)
open RuleSyntax.Machines (ReadsBag)
open RuleSyntax.ComputedConditions
open HENativeOnTransform (Presentation atom atom_injective stackField parentsField historyField)
open HEFocused (Focus Parent)
open HEInvocationEntry (Input)

variable {Context World : Type}

def entryTask (input : Input) (expected : Atom) : Task :=
  (HEInvocationEntry.Request.invoke input (.typed expected)).task

def capturedTask (input : Input) (expected representative : Atom) (frontier : List EquationWork) : Task :=
  (HEInvocationEntry.Request.retained { input with value := Entry.Value.ofAtom representative }
    (some expected) frontier).task

structure Request (Context World : Type) where
  world : World
  scope : Context
  input : Input
  expected : Atom
  stack : List Continuation
  parents : List (Parent Context)
  emitted : List Result

def Request.captured (request : Request Context World) (representative : Atom) (frontier : List EquationWork) :
    Focus Context World :=
  ⟨request.world, request.scope, .work (capturedTask request.input request.expected representative frontier),
    request.stack, request.parents, request.emitted⟩

def Request.message (code : Presentation Context World) (request : Request Context World) : EquationalEntryRules.Pending :=
  ⟨atom (code.world request.world), atom (code.context request.scope), stackField request.stack,
    parentsField code request.parents, historyField request.emitted, atom (taskData (entryTask request.input request.expected)),
    atom request.input.value.erase⟩

inductive State (Context World : Type) where
  | pending (request : Request Context World)
  | running (configuration : WorldConfiguration Context World)

def encode (code : Presentation Context World) : State Context World → Expr
  | .pending request => EquationalEntryRules.request 11 (request.message code)
  | .running configuration => HEControlOnTransform.encodeFocus code (HEFocused.focus configuration)

def Shows {O : Type} (code : Presentation Context World) (state : State Context World) (mark : SState O) : Prop :=
  ReadsBag mark {encode code state}

def MayEnter (env : WorldEnvironment Context World) (request : Request Context World)
    (representative : Atom) (frontier : List EquationWork) : Prop :=
  (HEEquationEntry.theory (env.view request.world request.scope) env.dispatch request.expected
    request.input.live request.input.frame).Step (.inl request.input.value.erase) (.inr (representative, frontier))

theorem equivalent_queries_same_captures (env : WorldEnvironment Context World) (request : Request Context World)
    (other : Entry.Value) (representative : Atom) (frontier : List EquationWork)
    (same : AtomEquations.Equivalent (env.view request.world request.scope).atoms request.input.value.erase other.erase) :
    MayEnter env request representative frontier ↔
      MayEnter env {request with input := {request.input with value := other}} representative frontier :=
  Equations.EntryReadouts.equiv_inputs (AtomEquations.setoid (env.view request.world request.scope).atoms)
    (fun candidate (result : Atom × List EquationWork) => candidate = result.1 ∧
      HEEquationEntry.select (env.view request.world request.scope) env.dispatch request.expected
        request.input.live request.input.frame candidate result.2)
    same (representative, frontier)

inductive Transition (env : WorldEnvironment Context World) (policy : Policy) : State Context World → State Context World → Prop
  | select {request representative frontier} :
      MayEnter env request representative frontier →
      Transition env policy (.pending request) (.running (HEFocused.restore (request.captured representative frontier)))
  | ordinary {before after} :
      WorldStepWith env.arguments env.view env.services env.dispatch env.lookup policy before after →
      Transition env policy (.running before) (.running after)

def source (env : WorldEnvironment Context World) (policy : Policy) : GSLT :=
  equalityGSLT (State Context World) (Transition env policy)

abbrev ClassAuthority (Context World : Type) := World → Context → Atom → Atom → Prop

def equivalentAtFrom (code : Presentation Context World) (authority : ClassAuthority Context World)
    (args : List Expr) (reply : Expr) : Prop :=
  ∃ world scope query representative, args = [atom (code.world world), atom (code.context scope), atom query] ∧
    authority world scope query representative ∧ reply = atom representative

def equivalentAt (code : Presentation Context World) (env : WorldEnvironment Context World)
    (args : List Expr) (reply : Expr) : Prop :=
  equivalentAtFrom code (fun world scope => AtomEquations.Equivalent (env.view world scope).atoms) args reply

abbrev SelectionAuthority (Context World : Type) :=
  World → Context → Input → Atom → Atom → List EquationWork → Prop

def selectedAtFrom (code : Presentation Context World) (authority : SelectionAuthority Context World)
    (args : List Expr) (reply : Expr) : Prop :=
  ∃ world scope input expected representative frontier,
    args = [atom (code.world world), atom (code.context scope), atom (taskData (entryTask input expected)),
      atom representative] ∧
    authority world scope input expected representative frontier ∧
    reply = atom (taskData (capturedTask input expected representative frontier))

def selectedAt (code : Presentation Context World) (env : WorldEnvironment Context World)
    (args : List Expr) (reply : Expr) : Prop :=
  selectedAtFrom code (fun world scope input expected =>
    HEEquationEntry.select (env.view world scope) env.dispatch expected input.live input.frame) args reply

def operations (code : Presentation Context World) (env : WorldEnvironment Context World) (policy : Policy) : Relations :=
  fun name args reply =>
    if name < 27 then HEControlOnTransform.operations code env policy name args reply
    else match name with
      | 27 => equivalentAt code env args reply
      | 28 => selectedAt code env args reply
      | _ => False

def entryRule : RuleWithCondition Nat Tm := EquationalEntryRules.rule 11 7 27 28

def rules : List (RuleWithCondition Nat Tm) := entryRule :: HEControlOnTransform.rules

private abbrev program (code : Presentation Context World) (env : WorldEnvironment Context World) (policy : Policy) :=
  specialized rows (relationGraph (operations code env policy)) {r | r ∈ rules}

def theory (O : Type) [DecidableEq O] (code : Presentation Context World)
    (env : WorldEnvironment Context World) (policy : Policy) : GSLT := programSystem O (program code env policy)

private theorem shape {r : RuleWithCondition Nat Tm} (listed : r ∈ rules) :
    r.rule.collect = [] ∧ r.rule.body.checks.all isGuard = true ∧ r.RangeRestrictedWith := by
  rcases List.mem_cons.mp listed with rfl | ordinary
  · exact ⟨rfl, rfl, EquationalEntryRules.restricted 11 7 27 28⟩
  · exact HEControlOnTransform.ordinary_rule_shape ordinary

private theorem positive (code : Presentation Context World) (env : WorldEnvironment Context World) (policy : Policy) :
    ∀ r ∈ program code env policy, DeterminedPositive r :=
  relations_fragment (fun _ member => (shape member).1) (fun _ member => (shape member).2.1)
    (fun _ member => (shape member).2.2)

private theorem ordinary_operations (code : Presentation Context World) (env : WorldEnvironment Context World)
    (policy : Policy) {r : RuleWithCondition Nat Tm} (listed : r ∈ HEControlOnTransform.rules)
    (before after : Multiset Expr) :
    RelationStep (operations code env policy) r before after ↔
      RelationStep (HEControlOnTransform.operations code env policy) r before after := by
  apply StateRulesOnTheStep.operations_iff
  intro condition present args reply
  simp only [operations, if_pos (HEControlOnTransform.ordinary_port listed condition present)]

private theorem task_fields {a b : Input} {first second : Atom}
    (same : entryTask a first = entryTask b second) : a = b ∧ first = second := by
  have equal := HEInvocationEntry.Request.task_injective same
  simp only [HEInvocationEntry.Request.invoke.injEq, HEInvocationEntry.Mode.typed.injEq] at equal
  exact equal

private theorem eq_readback (code : Presentation Context World) (env : WorldEnvironment Context World)
    (req : Request Context World) (reply : Expr) :
    equivalentAt code env [(req.message code).world, (req.message code).scope, (req.message code).query] reply ↔
      ∃ representative, AtomEquations.Equivalent (env.view req.world req.scope).atoms req.input.value.erase representative ∧
        reply = atom representative := by
  constructor
  · rintro ⟨world, scope, query, representative, common, equivalent, made⟩
    simp only [Request.message, List.cons.injEq, and_true, atom_injective.eq_iff,
      code.world_injective.eq_iff, code.context_injective.eq_iff] at common
    obtain ⟨rfl, rfl, rfl⟩ := common
    exact ⟨representative, equivalent, made⟩
  · rintro ⟨representative, equivalent, made⟩
    exact ⟨req.world, req.scope, req.input.value.erase, representative, rfl, equivalent, made⟩

private theorem selection_readback (code : Presentation Context World) (env : WorldEnvironment Context World)
    (req : Request Context World) (representative : Atom) (reply : Expr) :
    selectedAt code env [(req.message code).world, (req.message code).scope, (req.message code).task,
      atom representative] reply ↔
      ∃ frontier, HEEquationEntry.select (env.view req.world req.scope) env.dispatch req.expected
        req.input.live req.input.frame representative frontier ∧
        reply = atom (taskData (capturedTask req.input req.expected representative frontier)) := by
  constructor
  · rintro ⟨world, scope, input, expected, rep, frontier, common, eligible, made⟩
    simp only [Request.message, List.cons.injEq, and_true, atom_injective.eq_iff,
      code.world_injective.eq_iff, code.context_injective.eq_iff, taskData_injective.eq_iff] at common
    obtain ⟨rfl, rfl, equal, rfl⟩ := common
    obtain ⟨rfl, rfl⟩ := task_fields equal
    exact ⟨frontier, eligible, made⟩
  · rintro ⟨frontier, eligible, made⟩
    exact ⟨req.world, req.scope, req.input, req.expected, representative, frontier, rfl, eligible, made⟩

private theorem encoded_captured (code : Presentation Context World) (request : Request Context World)
    (representative : Atom) (frontier : List EquationWork) :
    encode code (.running (HEFocused.restore (request.captured representative frontier))) =
      EquationalEntryRules.entered 7 (request.message code)
        (atom (taskData (capturedTask request.input request.expected representative frontier))) := by
  simp only [encode, HEFocused.focus_restore, Request.captured, capturedTask, HEControlOnTransform.encode_invocation]
  rfl

theorem entry_rule_exact (code : Presentation Context World) (env : WorldEnvironment Context World)
    (policy : Policy) (request : Request Context World) (after : Multiset Expr) :
    RelationStep (operations code env policy) entryRule {encode code (.pending request)} after ↔
      ∃ representative frontier, MayEnter env request representative frontier ∧
        after = {encode code (.running (HEFocused.restore (request.captured representative frontier)))} := by
  rw [encode, entryRule, EquationalEntryRules.exact_step]
  change (∃ rep output, equivalentAt code env [(request.message code).world, (request.message code).scope,
    (request.message code).query] rep ∧
    selectedAt code env [(request.message code).world, (request.message code).scope, (request.message code).task, rep]
      output ∧ after = {EquationalEntryRules.entered 7 (request.message code) output}) ↔ _
  constructor
  · rintro ⟨rep, output, eq, eligible, made⟩
    obtain ⟨representative, same, rfl⟩ := (eq_readback code env request rep).mp eq
    obtain ⟨frontier, selected, rfl⟩ := (selection_readback code env request representative output).mp eligible
    exact ⟨representative, frontier, (HEEquationEntry.entry_exact _ _ _ _ _ _ _ _).mpr ⟨same, selected⟩,
      made.trans (congrArg (fun e => ({e} : Multiset Expr)) (encoded_captured code request representative frontier).symm)⟩
  · rintro ⟨representative, frontier, admitted, made⟩
    obtain ⟨same, selected⟩ := (HEEquationEntry.entry_exact _ _ _ _ _ _ _ _).mp admitted
    exact ⟨atom representative, atom (taskData (capturedTask request.input request.expected representative frontier)),
      (eq_readback code env request _).mpr ⟨representative, same, rfl⟩,
      (selection_readback code env request representative _).mpr ⟨frontier, selected, rfl⟩,
      made.trans (congrArg (fun e => ({e} : Multiset Expr)) (encoded_captured code request representative frontier))⟩

theorem relation_step_iff (code : Presentation Context World) (env : WorldEnvironment Context World)
    (policy : Policy) (before : State Context World) (after : Multiset Expr) :
    (∃ r ∈ rules, RelationStep (operations code env policy) r {encode code before} after) ↔
      ∃ next, Transition env policy before next ∧ after = {encode code next} := by
  cases before with
  | pending request =>
    constructor
    · rintro ⟨r, listed, fires⟩
      rcases List.mem_cons.mp listed with rfl | ordinary
      · obtain ⟨rep, frontier, admitted, result⟩ := (entry_rule_exact code env policy request after).mp fires
        exact ⟨_, .select admitted, result⟩
      · have bad := HEControlOnTransform.ordinary_firing_tag (tag := 11) ordinary fires
        omega
    · rintro ⟨next, advance, made⟩
      cases advance with
      | select admitted =>
        exact ⟨entryRule, List.mem_cons_self, (entry_rule_exact code env policy request after).mpr
          ⟨_, _, admitted, made⟩⟩
  | running configuration =>
    constructor
    · rintro ⟨r, listed, fires⟩
      rcases List.mem_cons.mp listed with rfl | ordinary
      · obtain ⟨tag, bounded, parts, form⟩ := HEControlOnTransform.encoded_ordinary_tag code (HEFocused.focus configuration)
        simp only [encode, form] at fires
        have equal := EquationalEntryRules.input_tag (tag := 11) (enteredTag := 7) (equivalentAt := 27)
          (selectAt := 28) fires
        omega
      · have native := (ordinary_operations code env policy ordinary _ _).mp fires
        obtain ⟨next, _, step, made⟩ :=
          (HEControlOnTransform.relation_step_iff env policy code (HEFocused.focus configuration) after).mp ⟨r, ordinary, native⟩
        have live := HEFocused.restore_step step
        rw [HEFocused.restore_focus] at live
        refine ⟨.running (HEFocused.restore next), .ordinary live, ?_⟩
        simpa only [encode, HEFocused.focus_restore] using made
    · rintro ⟨next, advances, made⟩
      cases advances with
      | ordinary live =>
        obtain ⟨r, listed, native⟩ := (HEControlOnTransform.relation_step_iff env policy code _ after).mpr
          ⟨_, HEControlOnTransform.all_covered _, HEFocused.focus_step live, made⟩
        exact ⟨r, List.mem_cons_of_mem _ listed, (ordinary_operations code env policy listed _ _).mpr native⟩

theorem realize_step {O : Type} [DecidableEq O] [Infinite O] (code : Presentation Context World)
    (env : WorldEnvironment Context World) (policy : Policy) {before after : State Context World} {start : SState O}
    (shown : Shows code before start) (advance : (source env policy).Step before after) :
    ∃ final, (theory O code env policy).Step start final ∧ Shows code after final := by
  obtain ⟨r, listed, fires⟩ := (relation_step_iff code env policy before _).mpr ⟨after, advance, rfl⟩
  obtain ⟨compiled, member, matched⟩ := (rewritesBy_relations_iff (P := {r | r ∈ rules})).mpr ⟨r, listed, fires⟩
  obtain ⟨event, legal, _, made⟩ :=
    readsBag_forward_determined member (positive code env policy compiled member) shown matched
  exact ⟨_, ⟨event, legal, rfl⟩, made⟩

theorem reflect_step {O : Type} [DecidableEq O] (code : Presentation Context World)
    (env : WorldEnvironment Context World) (policy : Policy) {before : State Context World} {start final : SState O}
    (shown : Shows code before start) (firing : (theory O code env policy).Step start final) :
    ∃ next, (source env policy).Step before next ∧ Shows code next final := by
  obtain ⟨event, legal, rfl⟩ := firing
  obtain ⟨bag, matched, readBack⟩ := readsBag_backward_determined shown event legal
    (makesDetermined_of_writes (positive code env policy event.rule event.member).2.2)
  obtain ⟨next, advance, rfl⟩ := (relation_step_iff code env policy before bag).mp
    (rewritesBy_relations_iff.mp ⟨event.rule, event.member, matched⟩)
  exact ⟨next, advance, readBack⟩

theorem realize_path {O : Type} [DecidableEq O] [Infinite O] (code : Presentation Context World)
    (env : WorldEnvironment Context World) (policy : Policy) {before after : State Context World} {start : SState O}
    (shown : Shows code before start) (path : ExecutionPath (source env policy) before after) :
    ∃ final, ∃ fired : ExecutionPath (theory O code env policy) start final,
      Shows code after final ∧ fired.length = path.length := by
  induction path generalizing start with
  | refl => exact ⟨start, .refl start, shown, rfl⟩
  | cons step rest ih =>
    obtain ⟨_, fired, next⟩ := realize_step code env policy shown step.down
    obtain ⟨final, remaining, last, count⟩ := ih next
    exact ⟨final, .cons ⟨fired⟩ remaining, last, congrArg (· + 1) count⟩

theorem reflect_path {O : Type} [DecidableEq O] (code : Presentation Context World)
    (env : WorldEnvironment Context World) (policy : Policy) {before : State Context World} {start final : SState O}
    (shown : Shows code before start) (fired : ExecutionPath (theory O code env policy) start final) :
    ∃ after, ∃ path : ExecutionPath (source env policy) before after,
      Shows code after final ∧ path.length = fired.length := by
  induction fired generalizing before with
  | refl _ => exact ⟨before, .refl before, shown, rfl⟩
  | cons step rest ih =>
    obtain ⟨_, advance, next⟩ := reflect_step code env policy shown step.down
    obtain ⟨after, remaining, last, count⟩ := ih next
    exact ⟨after, .cons ⟨advance⟩ remaining, last, congrArg (· + 1) count⟩

end Mettapedia.Languages.MeTTa.SpaceTheory.HEEquationalExecution
