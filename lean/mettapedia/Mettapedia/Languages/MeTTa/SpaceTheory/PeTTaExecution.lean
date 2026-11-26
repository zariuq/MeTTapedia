import Mettapedia.Languages.MeTTa.SpaceTheory.PeTTa
import Mettapedia.Languages.MeTTa.PeTTa.ProgramReplay
import Mettapedia.Languages.MeTTa.PeTTa.EvalOnTheStep

/-!
# PeTTa execution in a space

The snapshot preparation supplies the source program to PeTTa's own
evaluation judgment. Specializing this program does not discard the
store of the running configuration. A segment at one theory can retain
space edits, and can be transported to or from live execution when the
program questions asked along that segment have the same answers.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.SpaceTheory.PeTTaExecution

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.PeTTa.ProgramReplay
open Mettapedia.Languages.MeTTa.PeTTa.Eval (Configuration ProgramAgreementAt)
open Mettapedia.GSLT

def programAt (atoms : List Atom) : SpaceSemantics.Program :=
  PeTTaPresentation.programView (PeTTaPresentation.language "MeTTaSpace" atoms) atoms

@[simp] theorem programAt_exact (atoms : List Atom) :
    programAt atoms = SpaceSemantics.index atoms :=
  PeTTaPresentation.programView_exact "MeTTaSpace" atoms

private theorem append_index {before imported : List Atom} {p q : SpaceSemantics.Program}
    (left : SpaceSemantics.Indexes before p) (right : SpaceSemantics.Indexes imported q) :
    SpaceSemantics.Indexes (before ++ imported) (p.append q) := by
  induction left with
  | nil => cases q; exact right
  | equation head arguments body tail ih => exact .equation head arguments body ih
  | declaration subject type tail ih => exact .declaration subject type ih
  | fact atom noDefinition noAssignment tail ih => exact .fact atom noDefinition noAssignment ih

/-- Composition of the declaration contribution of an imported program.
The result is about those atoms once obtained; it does not replace an
effectful initializer by a pure union or conflate repeated declarations. -/
theorem declaration_contributions_compose (before imported : List Atom) :
    programAt (before ++ imported) = (programAt before).append (programAt imported) := by
  simp only [programAt_exact]
  exact (SpaceSemantics.index_exact _).unique
    (append_index (SpaceSemantics.index_exact _) (SpaceSemantics.index_exact _))

def theoryAt (atoms : List Atom) : GSLT := Eval.theory (programAt atoms)

theorem snapshot_rewrite_iff (atoms : List Atom) (source target : Configuration) :
    (theoryAt atoms).Step source target ↔ PeTTaPresentation.step atoms source = some target := by
  change (Eval.theory (programAt atoms)).Step source target ↔ _
  rw [Eval.theory_step_iff, programAt_exact, PeTTaPresentation.step_exact]

theorem snapshot_rewrite_of_source {atoms : List Atom} {source target : Configuration}
    {program : SpaceSemantics.Program} (declared : SpaceSemantics.Indexes atoms program)
    (execution : DeclarativeSpec.Transition program source target) :
    (theoryAt atoms).Step source target := by
  change (Eval.theory (programAt atoms)).Step source target
  rw [programAt_exact]
  rw [declared.unique (SpaceSemantics.index_exact atoms)] at execution
  exact execution

theorem live_rewrite_iff (source target : Configuration) :
    LiveRegistry.theory.Step source target ↔ (theoryAt source.state.core).Step source target := by
  change LiveRegistry.Transition source target ↔ _
  rw [← LiveRegistry.step_exact, snapshot_rewrite_iff]
  rfl

/-- At a saturated ordinary invocation, the body's alternatives are
selected from the current theory. This is the entry boundary of this
source policy, not the earlier decision to evaluate the arguments. -/
theorem live_selects_current_definitions (source : Configuration)
    (bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst)
    (head : String) (values : List Atom) (position : Nat)
    (ready : source.control = .arguments bindings (.function head) [] values position)
    (ordinary : Eval.ioHead head = false) (notGrounded : StdLib.known head = false)
    (saturated : values.length ∈ Eval.arities (programAt source.state.core) head) :
    LiveRegistry.theory.Step source
      { source with control := .sequence (Eval.clauses (programAt source.state.core) head values) [] } := by
  apply (live_rewrite_iff _ _).mpr
  apply (Eval.theory_step_iff _ _ _).mpr
  simp only [Eval.step, ready, ordinary, notGrounded, Bool.false_eq_true, ↓reduceIte]
  rw [Eval.application_saturated saturated]

/-- Entering an already selected alternative does not look up the
definition again. Changes to the space can still affect future calls
made by its body. In particular this is not a frozen entire registry. -/
theorem selected_alternative_survives_registry_change
    (source : Configuration) (selected : Eval.Control) (pending : List Eval.Control)
    (previous : List Atom) (ready : source.control = .sequence (selected :: pending) previous) :
    LiveRegistry.theory.Step source
      { source with control := selected, frames := .sequence pending previous :: source.frames } := by
  apply (live_rewrite_iff _ _).mpr
  apply (Eval.theory_step_iff _ _ _).mpr
  simp [Eval.step, ready]

private theorem local_rewrite_iff (program : SpaceSemantics.Program) (source target : Configuration)
    (agreement : ProgramAgreementAt (SpaceSemantics.index source.state.core) program source) :
    LiveRegistry.theory.Step source target ↔ (Eval.theory program).Step source target := by
  change LiveRegistry.Transition source target ↔ _
  rw [← LiveRegistry.step_exact, LiveRegistry.step_eq_pinned program source agreement,
    Eval.theory_step_iff]

/-- Every reachable configuration, not just every returned value, agrees
along a segment with unchanged program observations. Effects in the actual
store are retained on both sides. The hypothesis asks about the dispatch,
argument demand, and bodies at the configurations, not about their results. -/
theorem live_segment_iff (program : SpaceSemantics.Program) {source target : Configuration}
    (agreement : ∀ current, (Eval.theory program).MultiStep source current →
      ProgramAgreementAt (SpaceSemantics.index current.state.core) program current) :
    LiveRegistry.theory.MultiStep source target ↔ (Eval.theory program).MultiStep source target := by
  exact ⟨fun path => liveToFixed program path agreement, fun path => fixedToLive program path agreement⟩
where
  liveToFixed (program : SpaceSemantics.Program) :
      {source target : Configuration} →
      LiveRegistry.theory.MultiStep source target →
      (∀ current, (Eval.theory program).MultiStep source current →
        ProgramAgreementAt (SpaceSemantics.index current.state.core) program current) →
      (Eval.theory program).MultiStep source target
    | _, _, .refl state, _ => GSLT.MultiStep.refl (S := Eval.theory program) state
    | first, _, .step one rest, agreed => by
      have fixed := (local_rewrite_iff program first _ (agreed first (.refl _))).mp one
      exact .step fixed (liveToFixed program rest fun reached path => agreed reached (.step fixed path))

  fixedToLive (program : SpaceSemantics.Program) :
      {source target : Configuration} →
      (Eval.theory program).MultiStep source target →
      (∀ current, (Eval.theory program).MultiStep source current →
        ProgramAgreementAt (SpaceSemantics.index current.state.core) program current) →
      LiveRegistry.theory.MultiStep source target
    | _, _, .refl state, _ => GSLT.MultiStep.refl (S := LiveRegistry.theory) state
    | first, _, .step one rest, agreed => by
      have live := (local_rewrite_iff program first _ (agreed first (.refl _))).mpr one
      exact .step live (fixedToLive program rest fun reached path => agreed reached (.step one path))

/-- The agreement criterion preserves the entire finite source trace.
In particular it retains the number and order of source transitions;
equality of final answers alone would not establish this. -/
theorem live_trace_iff (program : SpaceSemantics.Program) (source : Configuration)
    (agreement : ∀ current, (Eval.theory program).MultiStep source current →
      ProgramAgreementAt (SpaceSemantics.index current.state.core) program current)
    (tail : List Configuration) :
    (source :: tail).IsChain LiveRegistry.theory.Step ↔
      (source :: tail).IsChain (Eval.theory program).Step := by
  change (source :: tail).IsChain LiveRegistry.Transition ↔
    (source :: tail).IsChain (DeclarativeSpec.Transition program)
  induction tail generalizing source with
  | nil => simp
  | cons next rest ih =>
    simp only [List.isChain_cons_cons]
    have same : LiveRegistry.Transition source next ↔ DeclarativeSpec.Transition program source next :=
      local_rewrite_iff program source next (agreement source (.refl _))
    rw [same]
    apply and_congr_right
    intro first
    exact ih next (fun current path => agreement current (.step first path))

theorem live_observation_iff {Answer : Type*} (program : SpaceSemantics.Program) (source : Configuration)
    (agreement : ∀ current, (Eval.theory program).MultiStep source current →
      ProgramAgreementAt (SpaceSemantics.index current.state.core) program current)
    (observe : List Configuration → Answer) (result : Answer) :
    (∃ tail, (source :: tail).IsChain LiveRegistry.theory.Step ∧ observe (source :: tail) = result) ↔
      ∃ tail, (source :: tail).IsChain (Eval.theory program).Step ∧ observe (source :: tail) = result := by
  constructor
  · rintro ⟨tail, chain, answer⟩
    exact ⟨tail, (live_trace_iff program source agreement tail).mp chain, answer⟩
  · rintro ⟨tail, chain, answer⟩
    exact ⟨tail, (live_trace_iff program source agreement tail).mpr chain, answer⟩

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.Schematic (SState)

section Transform

open Mettapedia.GSLT.IndexedOperational Mettapedia.GSLT.Ultrainfinite
open Mettapedia.GSLT.Compilation
open Mettapedia.GSLT.Compilation.Uniform
open Mettapedia.OSLF.MeTTaIL.ContextualStep (engineBasePremises)
open Mettapedia.OSLF.Framework.TypeSynthesis (langReducesUsing mem_rootFrontier_iff_langReducesUsing)
open ConfigurationLanguageDef (language relationEnv)
open ConfigurationEncoding (cellSupportAfter transition_support)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NamesOnTheStep (Expr)
open ComputedConditions (specialized rows relationGraph DeterminedPositive relations_fragment
  rewritesBy_relations_iff readsBag_forward_determined readsBag_backward_determined makesDetermined_of_writes
  RelationStep RuleWithCondition)
open Presentation.Schematic (Tm isGuard)

private abbrev compiledProgram (program : SpaceSemantics.Program) :=
  specialized rows (relationGraph (QueryRulesOnTheStep.relations (relationEnv program) language))
    {r | r ∈ EvalOnTheStep.compiledRules}

theorem compiled_rule_shape {r : RuleWithCondition Nat Tm} (member : r ∈ EvalOnTheStep.compiledRules) :
    r.rule.collect = [] ∧ r.rule.body.checks.all isGuard = true ∧ r.RangeRestrictedWith := by
  have restricted := QueryRulesOnTheStep.compiled_restricted EvalOnTheStep.compiledRules_compiled r member
  obtain ⟨_, _, origin⟩ := (QueryRulesOnTheStep.compile_origins EvalOnTheStep.compiledRules_compiled).2 r member
  obtain ⟨_, _, _, _, _, rfl⟩ := origin.sides
  exact ⟨rfl, rfl, restricted⟩

private theorem compiled_positive (program : SpaceSemantics.Program) :
    ∀ r ∈ compiledProgram program, DeterminedPositive r :=
  relations_fragment (fun _ member => (compiled_rule_shape member).1)
    (fun _ member => (compiled_rule_shape member).2.1) (fun _ member => (compiled_rule_shape member).2.2)

private theorem authored_entry (program : SpaceSemantics.Program) (source : Configuration)
    (names : List String) (vacant : NamedSpaces.Store.EmptyTail source.state [])
    (covers : ∀ name, name ∉ names → source.state.cells name = none)
    (term : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern) :
    Mettapedia.OSLF.MeTTaIL.ContextualStep.Step (engineBasePremises (relationEnv program)) language
      (ConfigurationEncoding.encode source names) term ↔
      ∃ target, (Eval.theory program).Step source target ∧
        term = ConfigurationEncoding.encode target (cellSupportAfter source names) := by
  change langReducesUsing (relationEnv program) language (ConfigurationEncoding.encode source names) term ↔
    ∃ target, DeclarativeSpec.Transition program source target ∧
      term = ConfigurationEncoding.encode target (cellSupportAfter source names)
  rw [← mem_rootFrontier_iff_langReducesUsing
    (relationEnv program) language ConfigurationLanguageDef.nonrecursive_rules]
  rw [ConfigurationLanguageDef.frontier_eq_step program source names vacant covers]
  simp only [List.mem_map, Option.mem_toList, Eval.step_iff_transition]
  exact ⟨fun ⟨after, fires, endpoint⟩ => ⟨after, fires, endpoint.symm⟩,
    fun ⟨after, fires, endpoint⟩ => ⟨after, fires, endpoint.symm⟩⟩

/-- The conditional rewrite is the same source transition at its
actual endpoint, prior to furnishing any occurrence ticket. -/
theorem snapshot_relation_step_iff (atoms : List Atom) (source : Configuration) (names : List String)
    (vacant : NamedSpaces.Store.EmptyTail source.state [])
    (covers : ∀ name, name ∉ names → source.state.cells name = none) (after : Multiset Expr) :
    (∃ rule ∈ EvalOnTheStep.compiledRules,
      RelationStep (QueryRulesOnTheStep.relations (relationEnv (programAt atoms)) language) rule
        {RootRewritesOnTheStep.encode (ConfigurationEncoding.encode source names)} after) ↔
    ∃ target, (theoryAt atoms).Step source target ∧
      after = {RootRewritesOnTheStep.encode (ConfigurationEncoding.encode target (cellSupportAfter source names))} := by
  let program := programAt atoms
  have carried := EvalOnTheStep.configurations_carrier program
  have represented : EvalOnTheStep.Configurations (ConfigurationEncoding.encode source names) :=
    ⟨source, names, vacant, covers, rfl⟩
  have sourceData := carried.data _ represented
  constructor
  · rintro ⟨rule, member, related⟩
    obtain ⟨term, realStep, rfl⟩ := QueryRulesOnTheStep.relationStep_image
      (EvalOnTheStep.relations_moded program) (EvalOnTheStep.relations_data program)
      EvalOnTheStep.compiledRules_compiled sourceData member related
    obtain ⟨target, moved, rfl⟩ := (authored_entry program source names vacant covers term).mp realStep
    exact ⟨target, moved, rfl⟩
  · rintro ⟨target, moved, rfl⟩
    have authored := (authored_entry program source names vacant covers _).mpr ⟨target, moved, rfl⟩
    have targetData := carried.data _ (carried.closed _ _ represented authored)
    exact QueryRulesOnTheStep.relationStep_of_step (EvalOnTheStep.relations_moded program)
      (EvalOnTheStep.relations_data program) EvalOnTheStep.compiledRules_compiled sourceData targetData authored

/-- Each source transition is realized by one admitted firing, from
every state that actually shows the source configuration. -/
theorem snapshot_step_on_transform {O : Type} [DecidableEq O] [Infinite O]
    (atoms : List Atom) {source target : Configuration} {start : SState O}
    (shown : EvalOnTheStep.Shows source start) (step : (theoryAt atoms).Step source target) :
    ∃ final, (EvalOnTheStep.stepSystem O (programAt atoms)).Step start final ∧
      EvalOnTheStep.Shows target final := by
  let program := programAt atoms
  obtain ⟨names, vacant, covers, reads⟩ := shown
  have matched := (snapshot_relation_step_iff atoms source names vacant covers _).mpr ⟨target, step, rfl⟩
  obtain ⟨r, member, rewrite⟩ :=
    (rewritesBy_relations_iff (P := {r | r ∈ EvalOnTheStep.compiledRules})).mpr matched
  obtain ⟨firing, admitted, _, result⟩ :=
    readsBag_forward_determined member (compiled_positive program r member) reads rewrite
  exact ⟨_, ⟨firing, admitted, rfl⟩, cellSupportAfter source names,
    DeclarativeSpec.transition_empty_tail vacant step, transition_support names covers step, result⟩

/-- Every firing has a source transition at its actual endpoint. There
are no additional administrative firings between these configurations. -/
theorem snapshot_reflect_transform_step {O : Type} [DecidableEq O]
    (atoms : List Atom) {source : Configuration} {start final : SState O}
    (shown : EvalOnTheStep.Shows source start)
    (fired : (EvalOnTheStep.stepSystem O (programAt atoms)).Step start final) :
    ∃ target, (theoryAt atoms).Step source target ∧ EvalOnTheStep.Shows target final := by
  let program := programAt atoms
  obtain ⟨names, vacant, covers, reads⟩ := shown
  obtain ⟨firing, admitted, rfl⟩ := fired
  have makes := makesDetermined_of_writes (compiled_positive program firing.rule firing.member).2.2
  obtain ⟨bag, rewrite, reads'⟩ := readsBag_backward_determined reads firing admitted makes
  obtain ⟨target, moved, rfl⟩ := (snapshot_relation_step_iff atoms source names vacant covers bag).mp
    (rewritesBy_relations_iff.mp ⟨firing.rule, firing.member, rewrite⟩)
  exact ⟨target, moved, cellSupportAfter source names,
    DeclarativeSpec.transition_empty_tail vacant moved, transition_support names covers moved, reads'⟩

/-- The complete source path has a compiled path of exactly the same
length, counting semantic transitions, not the work inside a firing. -/
theorem snapshot_lift_transform_path {O : Type} [DecidableEq O] [Infinite O]
    (atoms : List Atom) {source target : Configuration} {start : SState O}
    (shown : EvalOnTheStep.Shows source start) (path : ExecutionPath (theoryAt atoms) source target) :
    ∃ final, ∃ fired : ExecutionPath (EvalOnTheStep.stepSystem O (programAt atoms)) start final,
      EvalOnTheStep.Shows target final ∧ fired.length = path.length := by
  induction path generalizing start with
  | refl configuration => exact ⟨start, .refl start, shown, rfl⟩
  | cons first rest ih =>
    obtain ⟨_, fired, nextShown⟩ := snapshot_step_on_transform atoms shown first.down
    obtain ⟨final, remainder, resultShown, length⟩ := ih nextShown
    exact ⟨final, .cons ⟨fired⟩ remainder, resultShown, congrArg (· + 1) length⟩

/-- Read back the given firing path, preserving both its length and
its actual endpoint. -/
theorem snapshot_read_transform_path {O : Type} [DecidableEq O]
    (atoms : List Atom) {source : Configuration} {start final : SState O}
    (shown : EvalOnTheStep.Shows source start)
    (fired : ExecutionPath (EvalOnTheStep.stepSystem O (programAt atoms)) start final) :
    ∃ target, ∃ path : ExecutionPath (theoryAt atoms) source target,
      EvalOnTheStep.Shows target final ∧ path.length = fired.length := by
  induction fired generalizing source with
  | refl present => exact ⟨source, .refl source, shown, rfl⟩
  | cons first rest ih =>
    obtain ⟨_, advanced, nextShown⟩ := snapshot_reflect_transform_step atoms shown first.down
    obtain ⟨target, remainder, resultShown, length⟩ := ih nextShown
    exact ⟨target, .cons ⟨advanced⟩ remainder, resultShown, congrArg (· + 1) length⟩

theorem snapshot_exact_length_iff {O : Type} [DecidableEq O] [Infinite O]
    (atoms : List Atom) (target : Configuration) {source : Configuration} {start : SState O}
    (shown : EvalOnTheStep.Shows source start) (steps : Nat) :
    (∃ path : ExecutionPath (theoryAt atoms) source target, path.length = steps) ↔
      ∃ final, ∃ fired : ExecutionPath (EvalOnTheStep.stepSystem O (programAt atoms)) start final,
        EvalOnTheStep.Shows target final ∧ fired.length = steps := by
  constructor
  · rintro ⟨path, count⟩
    obtain ⟨final, fired, showsTarget, sameLength⟩ := snapshot_lift_transform_path atoms shown path
    exact ⟨final, fired, showsTarget, sameLength.trans count⟩
  · rintro ⟨final, fired, showsTarget, count⟩
    obtain ⟨after, path, showsAfter, sameLength⟩ := snapshot_read_transform_path atoms shown fired
    cases EvalOnTheStep.shows_unique showsAfter showsTarget
    exact ⟨path, sameLength.trans count⟩

/-- A finished source configuration has no outgoing compiled firing,
even one that would leave the same answer visible. -/
theorem finished_has_no_firing {O : Type} [DecidableEq O]
    (atoms : List Atom) (state : Effects.State) (answers input output : List Atom) {start final : SState O}
    (shown : EvalOnTheStep.Shows (Eval.finished state answers input output) start) :
    ¬ (EvalOnTheStep.stepSystem O (programAt atoms)).Step start final := by
  intro fired
  obtain ⟨target, advanced, _⟩ := snapshot_reflect_transform_step atoms shown fired
  have impossible := (Eval.theory_step_iff (programAt atoms) _ target).mp advanced
  simp [Eval.step, Eval.finished] at impossible

/-- The compiled transform reflects arbitrary finite runs of the snapshot
theory, not just one ready-root rewrite or a completed pure value. -/
theorem snapshot_execution_on_transform {O : Type} [DecidableEq O] [Infinite O]
    (atoms : List Atom) (source target : Configuration) {start : SState O}
    (shown : EvalOnTheStep.Shows source start) :
    (theoryAt atoms).MultiStep source target ↔
      ∃ final, (EvalOnTheStep.stepSystem O (programAt atoms)).MultiStep start final ∧
        EvalOnTheStep.Shows target final := by
  constructor
  · intro path
    obtain ⟨steps⟩ := (executionPath_nonempty_iff_multiStep _ _ _).mpr path
    obtain ⟨final, fired, endpoint, _⟩ := snapshot_lift_transform_path atoms shown steps
    exact ⟨final, executionPathToMultiStep fired, endpoint⟩
  · rintro ⟨final, fired, endpoint⟩
    obtain ⟨steps⟩ := (executionPath_nonempty_iff_multiStep _ _ _).mpr fired
    obtain ⟨after, path, shownAfter, _⟩ := snapshot_read_transform_path atoms shown steps
    cases EvalOnTheStep.shows_unique shownAfter endpoint
    exact executionPathToMultiStep path

theorem live_segment_on_transform {O : Type} [DecidableEq O] [Infinite O]
    (atoms : List Atom) (source target : Configuration) {start : SState O}
    (shown : EvalOnTheStep.Shows source start)
    (agreement : ∀ current, (theoryAt atoms).MultiStep source current →
      ProgramAgreementAt (SpaceSemantics.index current.state.core) (programAt atoms) current) :
    LiveRegistry.theory.MultiStep source target ↔
      ∃ final, (EvalOnTheStep.stepSystem O (programAt atoms)).MultiStep start final ∧
        EvalOnTheStep.Shows target final :=
  (live_segment_iff (programAt atoms) agreement).trans
    (snapshot_execution_on_transform atoms source target shown)

private theorem live_path_to_snapshot (program : SpaceSemantics.Program)
    {source target : Configuration}
    (path : ExecutionPath LiveRegistry.theory source target)
    (agreement : ∀ current, (Eval.theory program).MultiStep source current →
      ProgramAgreementAt (SpaceSemantics.index current.state.core) program current) :
    ∃ pinned : ExecutionPath (Eval.theory program) source target, pinned.length = path.length := by
  induction path with
  | refl initial => exact ⟨.refl initial, rfl⟩
  | @cons before next final first rest ih =>
    have moved := (local_rewrite_iff program before next (agreement before (.refl _))).mp first.down
    obtain ⟨pinned, same⟩ := ih (fun current reached => agreement current (.step moved reached))
    exact ⟨.cons ⟨moved⟩ pinned, congrArg (· + 1) same⟩

private theorem snapshot_path_to_live (program : SpaceSemantics.Program)
    {source target : Configuration}
    (path : ExecutionPath (Eval.theory program) source target)
    (agreement : ∀ current, (Eval.theory program).MultiStep source current →
      ProgramAgreementAt (SpaceSemantics.index current.state.core) program current) :
    ∃ live : ExecutionPath LiveRegistry.theory source target, live.length = path.length := by
  induction path with
  | refl initial => exact ⟨.refl initial, rfl⟩
  | @cons before next final first rest ih =>
    have moved := (local_rewrite_iff program before next (agreement before (.refl _))).mpr first.down
    obtain ⟨live, same⟩ := ih (fun current reached => agreement current (.step first.down reached))
    exact ⟨.cons ⟨moved⟩ live, congrArg (· + 1) same⟩

/-- Exact fuel counts are interchangeable on a live segment under the
same source-observation hypothesis as untimed execution. -/
theorem live_segment_exact_length_iff {O : Type} [DecidableEq O] [Infinite O]
    (atoms : List Atom) (target : Configuration) {source : Configuration} {start : SState O}
    (shown : EvalOnTheStep.Shows source start)
    (agreement : ∀ current, (theoryAt atoms).MultiStep source current →
      ProgramAgreementAt (SpaceSemantics.index current.state.core) (programAt atoms) current)
    (steps : Nat) :
    (∃ path : ExecutionPath LiveRegistry.theory source target, path.length = steps) ↔
      ∃ final, ∃ fired : ExecutionPath (EvalOnTheStep.stepSystem O (programAt atoms)) start final,
        EvalOnTheStep.Shows target final ∧ fired.length = steps := by
  refine Iff.trans ?_ (snapshot_exact_length_iff atoms target shown steps)
  constructor
  · rintro ⟨path, length⟩
    obtain ⟨pinned, exactLength⟩ := live_path_to_snapshot (programAt atoms) path agreement
    exact ⟨pinned, exactLength.trans length⟩
  · rintro ⟨path, length⟩
    obtain ⟨live, exactLength⟩ := snapshot_path_to_live (programAt atoms) path agreement
    exact ⟨live, exactLength.trans length⟩

end Transform

section Controls

private def request : Configuration :=
  { state := Effects.empty, control := .evaluate [] (.expression [.symbol "new", .symbol "A"]) }

private def definition : Atom := .expression
  [.symbol "=", .expression [.symbol "new", .var "x"], .var "x"]

theorem a_new_definition_changes_entry :
    ¬ ProgramAgreementAt (programAt []) (programAt [definition]) request := by
  intro agreement
  have dispatch := agreement.dispatch [] "new" [.symbol "A"] rfl
  rw [programAt_exact, programAt_exact] at dispatch
  exact (show (SpaceSemantics.index []).equations.any (·.head == "new") ≠
    (SpaceSemantics.index [definition]).equations.any (·.head == "new") by decide +kernel) dispatch

theorem repeating_a_declaration_is_not_import_sharing :
    let alternatives (atoms : List Atom) := Eval.clauses (programAt atoms) "new" [.symbol "A"]
    (alternatives [definition]).length = 1 ∧
      (alternatives [definition, definition]).length = 2 := by
  simp only [programAt_exact]
  decide +kernel

/-- Plain PeTTa selection and selection modulo a written equation are
different observations. This distinguishes the existing source theory
from a dialect extension that consults the equation class at a call. -/
theorem plain_matching_does_not_consult_written_equalities :
    let pattern : Atom := .expression [.symbol "same", .var "x", .var "x"]
    let written : Atom := .expression [.symbol "=", pattern, .symbol "OK"]
    let equality : Atom := .expression [.symbol "=e", .symbol "A", .symbol "B"]
    let program := programAt [written, equality]
    (Eval.clauses program "same" [.symbol "A", .symbol "B"]).length = 0 ∧
      (Eval.clauses program "same" [.symbol "A", .symbol "A"]).length = 1 := by
  simp only [programAt_exact]
  decide +kernel

theorem a_type_assignment_can_change_argument_demand :
    let typed : Atom := .expression
      [.symbol ":", .symbol "new", .expression [.symbol "->", .symbol "Atom", .symbol "Atom"]]
    let before := programAt [definition]
    let after := programAt [definition, typed]
    before.equations = after.equations ∧
      Eval.argumentIsRaw before "new" 0 = false ∧ Eval.argumentIsRaw after "new" 0 = true := by
  simp only [programAt_exact]
  exact ⟨rfl, by decide +kernel, by decide +kernel⟩

end Controls

end Mettapedia.Languages.MeTTa.SpaceTheory.PeTTaExecution
