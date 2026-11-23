import Algorithms.MeTTa.Simple.Parser
import Mettapedia.Languages.MeTTa.MeTTaFiniteRevisionedKernel
import Mettapedia.GSLT.Core.BranchingTemporal
import Mathlib.Data.List.Chain



set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.MeTTaAuthoredProgramExecution.Search

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.OSLFCore.Bridge
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchSourceGuard)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands
open Mettapedia.Languages.MeTTa.MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional
open Mettapedia.Languages.MeTTa.MeTTaFiniteRevisionedKernel.AuthoredActivation.AtomCommands.Conditional
open Mettapedia.OSLF.MeTTaIL.GeneralPremise (signature?)
open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.GSLT.Core
open Mettapedia.GSLT.Core.BranchingTemporal

/-- A finite native table is acquired for the fixed source snapshot. Missing
registration is the ordinary finite-only relation policy; a registered but
unavailable primitive has a separate outcome. -/
def nativeRows? (environment : Environment) (relation : String) (arguments : List Atom)
    (initial : Subst) : Option (List (List Pattern)) :=
  if relation ∈ environment.registration.dynamicRelations then
    match signature? environment.registration relation arguments.length with
    | none => none
    | some signature =>
        (resolveInputs initial arguments signature.modes).bind fun resolved =>
          environment.dynamic.rows? relation resolved
  else some []

private theorem nativeRows?_source {environment : Environment} {relation : String}
    {arguments : List Atom} {initial : Subst}
    {signature : Mettapedia.OSLF.MeTTaIL.GeneralPremise.Signature}
    {resolved : List Pattern} {rows : List (List Pattern)}
    (registered : relation ∈ environment.registration.dynamicRelations)
    (declared : signature? environment.registration relation arguments.length = some signature)
    (inputs : Inputs initial arguments signature.modes resolved)
    (provided : environment.dynamic.Source relation resolved rows) :
    nativeRows? environment relation arguments initial = some rows := by
  simp only [nativeRows?, registered, ↓reduceIte, declared,
    (resolveInputs_exact _ _ _ _).mpr inputs, Option.bind_some,
    (environment.dynamic.rows_exact _ _ _).mpr provided]

structure QueryPlan where
  origins : List Origin
  unavailable : Bool
  deriving Repr, DecidableEq

def finiteOrigins (rows : List Atom) : List Origin :=
  (List.range rows.length).flatMap fun index => [.relation index, .builtin index]

/-- The plan retains physical occurrences. Individual row matching is a later
work frame; it is not an eager traversal of recursive proof search. -/
def planQuery (environment : Environment) (relation : String) (arguments : List Atom)
    (initial : Subst) : QueryPlan :=
  match nativeRows? environment relation arguments initial with
  | none => ⟨finiteOrigins environment.rows, true⟩
  | some rows =>
      ⟨finiteOrigins environment.rows ++ (List.range rows.length).map .native, false⟩

private theorem finite_origin_in_plan {environment : Environment} {relation : String}
    {arguments : List Atom} {initial : Subst} {origin : Origin}
    (member : origin ∈ finiteOrigins environment.rows) :
    origin ∈ (planQuery environment relation arguments initial).origins := by
  cases actual : nativeRows? environment relation arguments initial <;>
    simp only [planQuery, actual]
  · exact member
  · exact List.mem_append_left _ member

/-- Every independently authorized source query occurrence is scheduled. -/
theorem source_query_in_plan {environment : Environment} {relation : String}
    {arguments : List Atom} {initial final : Subst} {origin : Origin}
    (source : QueryHolds environment relation arguments initial origin final) :
    origin ∈ (planQuery environment relation arguments initial).origins := by
  cases source with
  | relation stored _ =>
      apply finite_origin_in_plan
      exact List.mem_flatMap.mpr ⟨_, List.mem_range.mpr (List.getElem?_eq_some_iff.mp stored).1,
        by simp⟩
  | builtin stored _ =>
      apply finite_origin_in_plan
      exact List.mem_flatMap.mpr ⟨_, List.mem_range.mpr (List.getElem?_eq_some_iff.mp stored).1,
        by simp⟩
  | native registered declared inputs provided selected _ =>
      rw [planQuery, nativeRows?_source registered declared inputs provided]
      exact List.mem_append_right _ (List.mem_map.mpr
        ⟨_, List.mem_range.mpr (List.getElem?_eq_some_iff.mp selected).1, rfl⟩)

/-- A finite row or a declared relation establishes a query vocabulary.
Unrecognized applications remain literal uninterpreted requests. -/
def knownQuery (environment : Environment) (relation : String) (arguments : List Atom) : Bool :=
  decide (relation ∈ environment.registration.dynamicRelations) ||
    (signature? environment.registration relation arguments.length).isSome ||
    (List.range environment.rows.length).any (fun index =>
      (tuple? environment.rows "relation!" relation index).isSome ||
        (tuple? environment.rows "builtin!" relation index).isSome)

private theorem source_query_known {environment : Environment} {relation : String}
    {arguments : List Atom} {initial final : Subst} {origin : Origin}
    (source : QueryHolds environment relation arguments initial origin final) :
    knownQuery environment relation arguments = true := by
  cases source with
  | relation stored _ =>
      have existing : (List.range environment.rows.length).any (fun index =>
          (tuple? environment.rows "relation!" relation index).isSome ||
            (tuple? environment.rows "builtin!" relation index).isSome) = true := by
        apply List.any_eq_true.mpr
        exact ⟨_, List.mem_range.mpr (List.getElem?_eq_some_iff.mp stored).1,
          by simp [(tuple?_exact _ _ _ _ _).mpr stored]⟩
      simp only [knownQuery, existing, Bool.or_true]
  | builtin stored _ =>
      have existing : (List.range environment.rows.length).any (fun index =>
          (tuple? environment.rows "relation!" relation index).isSome ||
            (tuple? environment.rows "builtin!" relation index).isSome) = true := by
        apply List.any_eq_true.mpr
        exact ⟨_, List.mem_range.mpr (List.getElem?_eq_some_iff.mp stored).1,
          by simp [(tuple?_exact _ _ _ _ _).mpr stored]⟩
      simp only [knownQuery, existing, Bool.or_true]
  | native registered _ _ _ _ _ => simp [knownQuery, registered]

inductive Frame where
  | root (declaration : Nat) (body : Atom)
  | callable (declaration : Nat) (body : Atom)
  | child (initial : Subst) (target : Atom)
  | head (remaining : List Atom)
  | tail (headProof : Evidence)
  deriving Repr, DecidableEq

inductive Value where
  | root (article : Evidence) (target : Atom)
  | callable (article : Evidence) (declaration : Nat) (bindings : Subst) (body : Atom)
  | premise (article : Evidence) (bindings : Subst)
  | premises (article : Evidence) (bindings : Subst)
  deriving Repr, DecidableEq

inductive Control where
  | root (subject : Atom)
  | callable (head : String) (values : List Atom)
  | premise (guard : Atom) (initial : Subst)
  | premises (guards : List Atom) (initial : Subst)
  | queryRow (relation : String) (arguments : List Atom) (initial : Subst) (origin : Origin)
  | value (result : Value)
  | unavailable (relation : String) (arguments : List Atom)
  | uninterpreted (guard : Atom) (initial : Subst)
  deriving Repr, DecidableEq

structure Task where
  control : Control
  frames : List Frame := []
  deriving Repr, DecidableEq

inductive Goal where
  | root (subject : Atom)
  | callable (head : String) (values : List Atom)
  | premises (guards : List Atom) (initial : Subst)
  deriving Repr, DecidableEq

def Goal.start : Goal → Task
  | .root subject => ⟨.root subject, []⟩
  | .callable head values => ⟨.callable head values, []⟩
  | .premises guards initial => ⟨.premises guards initial, []⟩

inductive Observation where
  | found (result : Value)
  | unavailable (relation : String) (arguments : List Atom)
  | uninterpreted (guard : Atom) (initial : Subst)
  deriving Repr, DecidableEq

def rootTasks (environment : Environment) (subject : Atom) (frames : List Frame) : List Task :=
  environment.rows.zipIdx.filterMap fun (atom, index) =>
    (readClause? atom).bind fun (left, right, guards) =>
      (SpaceSemantics.matchValue [] left subject).map fun initial =>
        ⟨.premises guards initial, .root index right :: frames⟩

def callTasks (environment : Environment) (head : String) (values : List Atom)
    (frames : List Frame) : List Task :=
  (prepareClauses environment.rows head values).map fun prepared =>
    ⟨.premises prepared.guards prepared.bindings,
      .callable prepared.declarationIndex prepared.equation.body :: frames⟩

/-- Every successor is a concrete retained request or continuation. The
source store/provider snapshot is a fixed parameter of this search. -/
def successors (environment : Environment) (task : Task) : List Task :=
  match task.control, task.frames with
  | .root subject, frames => rootTasks environment subject frames
  | .callable head values, frames => callTasks environment head values frames
  | .premises [] initial, frames => [⟨.value (.premises .empty initial), frames⟩]
  | .premises (guard :: guards) initial, frames =>
      [⟨.premise guard initial, .head guards :: frames⟩]
  | .premise guard initial, frames =>
      match guard with
      | .expression (.symbol relation :: arguments) =>
          if relation = "fresh" then
            match arguments with
            | [.var name, subject] =>
                if matchSourceGuard initial (.freshness name subject) then
                  [⟨.value (.premise .fresh initial), frames⟩] else []
            | _ => [⟨.uninterpreted guard initial, frames⟩]
          else if relation = "==" then
            match arguments with
            | [source, target] =>
                [⟨.root (applySubst initial source), .child initial target :: frames⟩]
            | _ => [⟨.uninterpreted guard initial, frames⟩]
          else if knownQuery environment relation arguments then
            let plan := planQuery environment relation arguments initial
            (plan.origins.map fun origin => ⟨.queryRow relation arguments initial origin, frames⟩) ++
              (if plan.unavailable then [⟨.unavailable relation arguments, frames⟩] else [])
          else [⟨.uninterpreted guard initial, frames⟩]
      | _ => [⟨.uninterpreted guard initial, frames⟩]
  | .queryRow relation arguments initial origin, frames =>
      match runQuery environment relation arguments initial origin with
      | .accepted final => [⟨.value (.premise (.query origin) final), frames⟩]
      | .refused => []
      | .unavailable missing => [⟨.unavailable missing arguments, frames⟩]
  | .value (.premises article final), .root index body :: frames =>
      [⟨.value (.root (.firing index article) (applySubst final body)), frames⟩]
  | .value (.premises article final), .callable index body :: frames =>
      [⟨.value (.callable (.firing index article) index final body), frames⟩]
  | .value (.root article target), .child initial schema :: frames =>
      (SpaceSemantics.matchValue initial schema target).toList.map fun final =>
        ⟨.value (.premise (.child article) final), frames⟩
  | .value (.premise article final), .head guards :: frames =>
      [⟨.premises guards final, .tail article :: frames⟩]
  | .value (.premises article final), .tail head :: frames =>
      [⟨.value (.premises (.cons head article) final), frames⟩]
  | _, _ => []

def judged (environment : Environment) (goal : Goal) (value : Value) : Bool :=
  match goal, value with
  | .root subject, .root article target => (kernel environment).decide (subject, target) article
  | .callable head values, .callable article index bindings body =>
      decide (runCall environment article head values = .accepted (index, .evaluate bindings body))
  | .premises guards initial, .premises article final =>
      decide (runPremises environment article guards initial = .accepted final)
  | _, _ => false

def emit (environment : Environment) (goal : Goal) (task : Task) : Option Observation :=
  match task.control, task.frames with
  | .value value, [] => if judged environment goal value then some (.found value) else none
  | .unavailable relation arguments, _ => some (.unavailable relation arguments)
  | .uninterpreted guard initial, _ => some (.uninterpreted guard initial)
  | _, _ => none

def system (environment : Environment) (goal : Goal) : BranchingSystem Task Observation where
  successors := successors environment
  emit := emit environment goal

abbrev Session := Snapshot Task Observation

def start (goal : Goal) : Session := initial [goal.start]

def run (environment : Environment) (goal : Goal) (fuel : Nat) (session : Session) : Session :=
  BranchingTemporal.run (system environment goal) Scheduler.breadthFirst fuel session

/-- Exact resumption retains the original frontier and all occurrences. -/
theorem run_add (environment : Environment) (goal : Goal) (first second : Nat) (session : Session) :
    run environment goal (first + second) session =
      run environment goal second (run environment goal first session) :=
  BranchingTemporal.run_add _ _ _ _ _

def Observation.blocked : Observation → Bool
  | .found _ => false
  | .unavailable _ _ | .uninterpreted _ _ => true

/-- A bounded silent prefix is not absence. Unavailable or uninterpreted
requests prevent completion even when the current frontier is empty. -/
def complete (session : Session) : Bool :=
  session.frontier.isEmpty && !(session.events.any fun event => event.value.blocked)


/-- The source meaning is stated with the original independent judgments,
before any search frontier or Boolean admission decision is considered. -/
def Meaning (environment : Environment) (goal : Goal) (value : Value) : Prop :=
  match goal, value with
  | .root subject, .root article target => RootFiring environment article subject target
  | .callable head values, .callable article index bindings body =>
      CallReady environment head values article index (.evaluate bindings body)
  | .premises guards initial, .premises article final =>
      PremisesHold environment article guards initial final
  | _, _ => False

@[simp] theorem judged_exact (environment : Environment) (goal : Goal) (value : Value) :
    judged environment goal value = true ↔ Meaning environment goal value := by
  cases goal <;> cases value <;>
    simp [judged, Meaning, kernel, guest, runRoot_exact, runCall_exact, runPremises_exact]

theorem emitted_found_source {environment : Environment} {goal : Goal} {task : Task} {value : Value}
    (emitted : emit environment goal task = some (.found value)) : Meaning environment goal value := by
  unfold emit at emitted
  split at emitted
  next actual =>
    split at emitted
    next checked =>
      cases Option.some.inj emitted
      exact (judged_exact _ _ _).mp checked
    next => contradiction
  next => cases emitted
  next => cases emitted
  next => contradiction

theorem emit_of_source {environment : Environment} {goal : Goal} {value : Value}
    (source : Meaning environment goal value) :
    emit environment goal ⟨.value value, []⟩ = some (.found value) := by
  simp only [emit, (judged_exact _ _ _).mpr source, ↓reduceIte]

/-- Source correctness of every bounded found observation is independent of
search completeness and independent of any completeness label. -/
theorem found_source (environment : Environment) (goal : Goal) (fuel : Nat)
    (event : Emission Task Observation) (value : Value)
    (member : event ∈ (run environment goal fuel (start goal)).events)
    (found : event.value = .found value) : Meaning environment goal value := by
  have sound := BranchingTemporal.sound_run (system environment goal) Scheduler.breadthFirst
    (BranchingTemporal.initial_sound _ [goal.start]) fuel
  have emitted := (sound.2 event member).2
  rw [found] at emitted
  exact emitted_found_source emitted

abbrev Reaches (environment : Environment) (first last : Task) :=
  Relation.ReflTransGen (fun before after => after ∈ successors environment before) first last

private theorem root_task_member {environment : Environment} {index : Nat}
    {left right subject : Atom} {guards : List Atom} {initial : Subst} (frames : List Frame)
    (stored : ClauseAt environment.rows index left right guards)
    (matched : SpaceSemantics.ValueMatch [] left subject initial) :
    (⟨.premises guards initial, .root index right :: frames⟩ : Task) ∈
      successors environment ⟨.root subject, frames⟩ := by
  obtain ⟨atom, positioned, declared⟩ := stored
  apply List.mem_filterMap.mpr
  refine ⟨(atom, index), List.mk_mem_zipIdx_iff_getElem?.mpr positioned, ?_⟩
  simp only [(readClause?_exact _ _ _ _).mpr declared, Option.bind_some,
    SpaceSemantics.matchValue_complete matched, Option.map_some]

private theorem pathRule {environment : Environment} {index : Nat} {article : Evidence}
    {left right subject target : Atom} {guards : List Atom} {initial final : Subst}
    (stored : ClauseAt environment.rows index left right guards)
    (matched : SpaceSemantics.ValueMatch [] left subject initial)
    (emitted : target = applySubst final right)
    (ih : ∀ frames, Reaches environment ⟨.premises guards initial, frames⟩
      ⟨.value (.premises article final), frames⟩) :
    ∀ frames, Reaches environment ⟨.root subject, frames⟩
      ⟨.value (.root (.firing index article) target), frames⟩ := by
  intro frames
  cases emitted
  exact (Relation.ReflTransGen.single (root_task_member frames stored matched)).trans
    ((ih (.root index right :: frames)).trans
      (Relation.ReflTransGen.single (by simp [successors])))

private theorem pathFresh {environment : Environment} {name : String} {subject : Atom}
    {initial : Subst}
    (held : Mettapedia.Languages.ProcessCalculi.MORK.SourceGuardHolds initial (.freshness name subject)) :
    ∀ frames, Reaches environment
      ⟨.premise (.expression [.symbol "fresh", .var name, subject]) initial, frames⟩
      ⟨.value (.premise .fresh initial), frames⟩ := by
  intro frames
  exact Relation.ReflTransGen.single (by
    simp [successors, (Mettapedia.Languages.ProcessCalculi.MORK.matchSourceGuard_exact _ _).mpr held])

private theorem pathChild {environment : Environment} {article : Evidence}
    {source target result : Atom} {initial final : Subst}
    (matched : SpaceSemantics.ValueMatch initial target result final)
    (ih : ∀ frames, Reaches environment ⟨.root (applySubst initial source), frames⟩
      ⟨.value (.root article result), frames⟩) :
    ∀ frames, Reaches environment
      ⟨.premise (.expression [.symbol "==", source, target]) initial, frames⟩
      ⟨.value (.premise (.child article) final), frames⟩ := by
  intro frames
  exact (Relation.ReflTransGen.single (by simp [successors])).trans
    ((ih (.child initial target :: frames)).trans
      (Relation.ReflTransGen.single (by simp [successors, SpaceSemantics.matchValue_complete matched])))

private theorem pathQuery {environment : Environment} {relation : String} {arguments : List Atom}
    {initial final : Subst} {origin : Origin}
    (ordinary : relation ≠ "fresh") (directed : relation ≠ "==")
    (queried : QueryHolds environment relation arguments initial origin final) :
    ∀ frames, Reaches environment
      ⟨.premise (.expression (.symbol relation :: arguments)) initial, frames⟩
      ⟨.value (.premise (.query origin) final), frames⟩ := by
  intro frames
  apply (Relation.ReflTransGen.single (b := ⟨.queryRow relation arguments initial origin, frames⟩) ?_).trans
  · exact Relation.ReflTransGen.single (by simp [successors, (runQuery_exact _ _ _ _ _ _).mpr queried])
  · simp only [successors, ordinary, directed, source_query_known queried, ↓reduceIte]
    exact List.mem_append_left _ (List.mem_map.mpr ⟨origin, source_query_in_plan queried, rfl⟩)

private theorem pathNil {environment : Environment} {initial : Subst} :
    ∀ frames, Reaches environment ⟨.premises [] initial, frames⟩
      ⟨.value (.premises .empty initial), frames⟩ := by
  intro frames
  exact Relation.ReflTransGen.single (by simp [successors])

private theorem pathCons {environment : Environment} {head tail : Evidence}
    {guard : Atom} {guards : List Atom} {initial middle final : Subst}
    (ihHead : ∀ frames, Reaches environment ⟨.premise guard initial, frames⟩
      ⟨.value (.premise head middle), frames⟩)
    (ihTail : ∀ frames, Reaches environment ⟨.premises guards middle, frames⟩
      ⟨.value (.premises tail final), frames⟩) :
    ∀ frames, Reaches environment ⟨.premises (guard :: guards) initial, frames⟩
      ⟨.value (.premises (.cons head tail) final), frames⟩ := by
  intro frames
  exact (Relation.ReflTransGen.single (by simp [successors])).trans
    ((ihHead (.head guards :: frames)).trans
      ((Relation.ReflTransGen.single (by simp [successors])).trans
        ((ihTail (.tail head :: frames)).trans
          (Relation.ReflTransGen.single (by simp [successors])))))

/-- Every finite source proof constructs an actual finite path through the
retained native requests and continuations. -/
theorem root_reaches {environment : Environment} {article : Evidence} {subject target : Atom}
    (source : RootFiring environment article subject target) :
    ∀ frames, Reaches environment ⟨.root subject, frames⟩
      ⟨.value (.root article target), frames⟩ :=
  RootFiring.rec
    (motive_1 := fun article subject target _ =>
      ∀ frames, Reaches environment ⟨.root subject, frames⟩ ⟨.value (.root article target), frames⟩)
    (motive_2 := fun article guard initial final _ =>
      ∀ frames, Reaches environment ⟨.premise guard initial, frames⟩
        ⟨.value (.premise article final), frames⟩)
    (motive_3 := fun article guards initial final _ =>
      ∀ frames, Reaches environment ⟨.premises guards initial, frames⟩
        ⟨.value (.premises article final), frames⟩)
    (fun stored matched _ emitted ih => pathRule stored matched emitted ih)
    pathFresh (fun _ matched ih => pathChild matched ih) pathQuery pathNil
    (fun _ _ ihHead ihTail => pathCons ihHead ihTail) source

theorem premises_reaches {environment : Environment} {article : Evidence}
    {guards : List Atom} {initial final : Subst}
    (source : PremisesHold environment article guards initial final) :
    ∀ frames, Reaches environment ⟨.premises guards initial, frames⟩
      ⟨.value (.premises article final), frames⟩ :=
  PremisesHold.rec
    (motive_1 := fun article subject target _ =>
      ∀ frames, Reaches environment ⟨.root subject, frames⟩ ⟨.value (.root article target), frames⟩)
    (motive_2 := fun article guard initial final _ =>
      ∀ frames, Reaches environment ⟨.premise guard initial, frames⟩
        ⟨.value (.premise article final), frames⟩)
    (motive_3 := fun article guards initial final _ =>
      ∀ frames, Reaches environment ⟨.premises guards initial, frames⟩
        ⟨.value (.premises article final), frames⟩)
    (fun stored matched _ emitted ih => pathRule stored matched emitted ih)
    pathFresh (fun _ matched ih => pathChild matched ih) pathQuery pathNil
    (fun _ _ ihHead ihTail => pathCons ihHead ihTail) source

theorem call_reaches {environment : Environment} {article : Evidence} {head : String}
    {values : List Atom} {index : Nat} {bindings : Subst} {body : Atom}
    (source : CallReady environment head values article index (.evaluate bindings body)) :
    ∀ frames, Reaches environment ⟨.callable head values, frames⟩
      ⟨.value (.callable article index bindings body), frames⟩ := by
  cases source with
  | guarded selected premises =>
      intro frames
      have first :
          (⟨.premises _ _, .callable _ _ :: frames⟩ : Task) ∈
            successors environment ⟨.callable head values, frames⟩ :=
        List.mem_map.mpr ⟨_, (prepareClauses_exact _ _ _ _).mpr selected, rfl⟩
      exact (Relation.ReflTransGen.single first).trans
        ((premises_reaches premises _).trans (Relation.ReflTransGen.single (by simp [successors])))

private theorem generated_of_path {environment : Environment} {goal : Goal} {first last : Task}
    (generated : Generated (system environment goal) [goal.start] first)
    (path : Reaches environment first last) : Generated (system environment goal) [goal.start] last := by
  induction path with
  | refl => exact generated
  | tail _ step ih => exact .successor ih step

/-- Fair native search discovers each finite independently judged source
article. It does not need to finish other recursive proof branches first. -/
theorem source_discovered (environment : Environment) (goal : Goal) (value : Value)
    (source : Meaning environment goal value) :
    ∃ fuel, (⟨⟨.value value, []⟩, .found value⟩ : Emission Task Observation) ∈
      (run environment goal fuel (start goal)).events := by
  have path : Reaches environment goal.start ⟨.value value, []⟩ := by
    cases goal <;> cases value <;> simp only [Meaning] at source
    · exact root_reaches source []
    · exact call_reaches source []
    · exact premises_reaches source []
  apply BranchingTemporal.fair_emits_reachable (system environment goal) Scheduler.breadthFirst
    [goal.start] (BranchingTemporal.breadthFirst_fair _ _)
  · exact generated_of_path (.root (by simp)) path
  · exact emit_of_source source


open Mettapedia.Languages.MeTTa.MeTTaFiniteRevisionedKernel.AuthoredActivation.AtomCommands (StateCode)
open Mettapedia.OSLF.MeTTaIL.GeneralPremise (ProviderSnapshot DynamicProvider)

/-- Native search captures the actual selected space, provider and command
revision. Resumption does not accept a replacement environment. -/
structure CapturedSearch where
  before : StateCode
  environment : Environment
  goal : Goal
  work : Session

/-- All source rows come from the original finite store interpretation.
Unallocated space selection refuses capture rather than fabricating an empty
space or erasing the requested source location. -/
def capture (before : StateCode) (registration : ProviderSnapshot) (dynamic : DynamicProvider)
    (goal : Goal) : Option CapturedSearch :=
  (before.decode.store.read before.decode.current).map fun rows =>
    ⟨before, ⟨rows, registration, dynamic⟩, goal, start goal⟩

def CapturedSearch.Valid (captured : CapturedSearch) : Prop :=
  captured.before.decode.store.read captured.before.decode.current =
      some captured.environment.rows ∧
    captured.work.Sound (system captured.environment captured.goal) [captured.goal.start]

theorem capture_valid {before : StateCode} {registration : ProviderSnapshot} {dynamic : DynamicProvider}
    {goal : Goal} {captured : CapturedSearch}
    (created : capture before registration dynamic goal = some captured) : captured.Valid := by
  obtain ⟨rows, allocated, same⟩ := Option.map_eq_some_iff.mp created
  cases same
  exact ⟨allocated, BranchingTemporal.initial_sound _ _⟩

def advance (fuel : Nat) (captured : CapturedSearch) : CapturedSearch :=
  {captured with work := run captured.environment captured.goal fuel captured.work}

theorem advance_valid (fuel : Nat) (captured : CapturedSearch) (valid : captured.Valid) :
    (advance fuel captured).Valid :=
  ⟨valid.1, BranchingTemporal.sound_run _ _ valid.2 fuel⟩

theorem advance_add (first second : Nat) (captured : CapturedSearch) :
    advance (first + second) captured = advance second (advance first captured) := by
  cases captured
  simp only [advance, run_add]

def CapturedSearch.current (captured : CapturedSearch) (now : StateCode) : Bool :=
  StateCode.same captured.before now

@[simp] theorem current_exact (captured : CapturedSearch) (now : StateCode) :
    captured.current now = true ↔ captured.before.decode = now.decode :=
  StateCode.same_exact _ _

/-- Currentness is executable on finite code and implies the actual selected
store read, including occurrence multiplicity, at the claimed revision. -/
theorem current_rows {captured : CapturedSearch} {now : StateCode}
    (valid : captured.Valid) (current : captured.current now = true) :
    now.decode.store.read now.decode.current = some captured.environment.rows := by
  rw [← (current_exact _ _).mp current]
  exact valid.1

inductive Resumption where
  | advanced (search : CapturedSearch)
  | stale (search : CapturedSearch) (now : StateCode)

def resume (now : StateCode) (fuel : Nat) (captured : CapturedSearch) : Resumption :=
  if captured.current now then .advanced (advance fuel captured) else .stale captured now

theorem resume_current {now : StateCode} {fuel : Nat} {captured : CapturedSearch}
    (same : captured.current now = true) : resume now fuel captured = .advanced (advance fuel captured) := by
  simp only [resume, same, ↓reduceIte]

/-- Stale work remains available for revalidation; it cannot silently acquire
a firing authority from the changed store. -/
theorem resume_stale {now : StateCode} {fuel : Nat} {captured : CapturedSearch}
    (changed : captured.current now = false) : resume now fuel captured = .stale captured now := by
  simp only [resume, changed, Bool.false_eq_true, ↓reduceIte]

theorem captured_found_source (captured : CapturedSearch) (valid : captured.Valid)
    (event : Emission Task Observation) (value : Value)
    (member : event ∈ captured.work.events) (found : event.value = .found value) :
    Meaning captured.environment captured.goal value := by
  have emitted := (valid.2.2 event member).2
  rw [found] at emitted
  exact emitted_found_source emitted

end Mettapedia.Languages.MeTTa.MeTTaAuthoredProgramExecution.Search


set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.MeTTaAuthoredProgramExecution.Search

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional
open Mettapedia.Languages.MeTTa.MeTTaFiniteRevisionedKernel.AuthoredActivation.AtomCommands (StateCode)

/-- A call receipt is permanently indexed by the actual captured source
state and by the physical search observation that produced it. The body and
its assignment remain separate original evaluator data. -/
structure CallEntry where
  before : StateCode
  environment : Environment
  head : String
  arguments : List Atom
  observation : Nat
  article : Evidence
  declaration : Nat
  bindings : Subst
  body : Atom

/-- Entry authority is the independent source call judgment at the captured
world. It makes no assertion that a subsequent mutable world is equal to it. -/
def CallEntry.Valid (entry : CallEntry) : Prop :=
  entry.before.decode.store.read entry.before.decode.current = some entry.environment.rows ∧
    CallReady entry.environment entry.head entry.arguments entry.article entry.declaration
      (.evaluate entry.bindings entry.body)

/-- The native admission replays the actual source checker once, at entry.
It does not turn later ordinary reads into implicit revalidation requests. -/
def admitCall? (captured : CapturedSearch) (observation : Nat) (value : Value) : Option CallEntry :=
  match captured.goal, value with
  | .callable head arguments, .callable article declaration bindings body =>
      if captured.before.decode.store.read captured.before.decode.current == some captured.environment.rows &&
          judged captured.environment captured.goal value then
        some ⟨captured.before, captured.environment, head, arguments, observation,
          article, declaration, bindings, body⟩
      else none
  | _, _ => none

/-- Admission retains the actual physical search occurrence. A value shared
by multiple proof branches therefore still produces distinct receipts. -/
def pinAt? (captured : CapturedSearch) (observation : Nat) : Option CallEntry :=
  captured.work.events[observation]?.bind fun event =>
    match event.value with
    | .found value => admitCall? captured observation value
    | _ => none

theorem admitCall_sound {captured : CapturedSearch} {observation : Nat} {value : Value}
    {entry : CallEntry} (accepted : admitCall? captured observation value = some entry) : entry.Valid := by
  unfold admitCall? at accepted
  split at accepted
  next _ _ head arguments article declaration bindings body goalSame =>
    split at accepted
    next checked =>
      cases Option.some.inj accepted
      have facts := (Bool.and_eq_true_iff.mp checked)
      refine ⟨beq_iff_eq.mp facts.1, ?_⟩
      have source := (judged_exact _ _ _).mp facts.2
      simpa only [goalSame, Meaning] using source
    next => contradiction
  next => contradiction

theorem pinAt_sound {captured : CapturedSearch} {observation : Nat} {entry : CallEntry}
    (accepted : pinAt? captured observation = some entry) : entry.Valid := by
  obtain ⟨event, _, selected⟩ := Option.bind_eq_some_iff.mp accepted
  cases actual : event.value with
  | found value => exact admitCall_sound (by simpa only [actual] using selected)
  | unavailable _ _ => simp only [actual] at selected; contradiction
  | uninterpreted _ _ => simp only [actual] at selected; contradiction

/-- Every source-valid captured callable value has an admitted immutable
receipt, independently of whether the rest of the search has completed. -/
theorem admitCall_complete (captured : CapturedSearch) (observation : Nat)
    (head : String) (arguments : List Atom) (article : Evidence) (declaration : Nat)
    (bindings : Subst) (body : Atom)
    (goalSame : captured.goal = .callable head arguments)
    (allocated : captured.before.decode.store.read captured.before.decode.current =
      some captured.environment.rows)
    (source : CallReady captured.environment head arguments article declaration (.evaluate bindings body)) :
    admitCall? captured observation (.callable article declaration bindings body) =
      some ⟨captured.before, captured.environment, head, arguments, observation,
        article, declaration, bindings, body⟩ := by
  have checked := (judged_exact captured.environment (.callable head arguments)
    (.callable article declaration bindings body)).mpr source
  simp only [admitCall?, goalSame, allocated, beq_self_eq_true, checked,
    Bool.true_and, ↓reduceIte]

/-- Entering a checked body updates only the control. All serial store effects,
outer continuations and external I/O already performed by other bodies remain. -/
def CallEntry.enter (entry : CallEntry) (now : Eval.Configuration) : Eval.Configuration :=
  {now with control := .evaluate entry.bindings entry.body}

@[simp] theorem enter_state (entry : CallEntry) (now : Eval.Configuration) :
    (entry.enter now).state = now.state := rfl
@[simp] theorem enter_frames (entry : CallEntry) (now : Eval.Configuration) :
    (entry.enter now).frames = now.frames := rfl
@[simp] theorem enter_input (entry : CallEntry) (now : Eval.Configuration) :
    (entry.enter now).input = now.input := rfl
@[simp] theorem enter_output (entry : CallEntry) (now : Eval.Configuration) :
    (entry.enter now).output = now.output := rfl
@[simp] theorem enter_control (entry : CallEntry) (now : Eval.Configuration) :
    (entry.enter now).control = .evaluate entry.bindings entry.body := rfl

inductive ActivationPolicy where
  | pinnedEntry
  | currentWorld
  deriving Repr, DecidableEq

/-- A source call may use entry-snapshot authority, or it may require that the
whole current command world still equals the captured one. Neither policy
commutes branch writes or silently upgrades old evidence to a new-world fact. -/
inductive Permitted (entry : CallEntry) (now : StateCode) : ActivationPolicy → Prop where
  | pinned (valid : entry.Valid) : Permitted entry now .pinnedEntry
  | current (valid : entry.Valid) (same : entry.before.decode = now.decode) :
      Permitted entry now .currentWorld

def CallEntry.current (entry : CallEntry) (now : StateCode) : Bool := StateCode.same entry.before now

@[simp] theorem entry_current_exact (entry : CallEntry) (now : StateCode) :
    entry.current now = true ↔ entry.before.decode = now.decode := StateCode.same_exact _ _

/-- A current-world commit carries the complete original receipt when stale,
so replanning cannot accidentally erase the previously found proof. -/
inductive Authorization where
  | admitted (entry : CallEntry)
  | stale (entry : CallEntry) (now : StateCode)

def authorize (policy : ActivationPolicy) (entry : CallEntry) (now : StateCode) : Authorization :=
  match policy with
  | .pinnedEntry => .admitted entry
  | .currentWorld => if entry.current now then .admitted entry else .stale entry now

theorem authorize_preserves_entry (policy : ActivationPolicy) (entry : CallEntry) (now : StateCode)
    (returned : CallEntry) (accepted : authorize policy entry now = .admitted returned) : returned = entry := by
  cases policy with
  | pinnedEntry => exact (Authorization.admitted.inj accepted).symm
  | currentWorld =>
      simp only [authorize] at accepted
      split at accepted
      · exact (Authorization.admitted.inj accepted).symm
      · contradiction

theorem authorize_exact (policy : ActivationPolicy) (entry : CallEntry) (now : StateCode)
    (valid : entry.Valid) :
    authorize policy entry now = .admitted entry ↔ Permitted entry now policy := by
  cases policy with
  | pinnedEntry => exact ⟨fun _ => .pinned valid, fun _ => rfl⟩
  | currentWorld =>
      simp only [authorize]
      constructor
      · intro admitted
        split at admitted
        next same => exact .current valid ((entry_current_exact _ _).mp same)
        next => contradiction
      · intro permitted
        cases permitted with
        | current _ same => simp only [(entry_current_exact _ _).mpr same, ↓reduceIte]

theorem changed_world_distinguishes_policies (entry : CallEntry) (now : StateCode)
    (changed : entry.current now = false) :
    authorize .pinnedEntry entry now = .admitted entry ∧
      authorize .currentWorld entry now = .stale entry now := by
  simp only [authorize, changed, Bool.false_eq_true, ↓reduceIte, and_self]

theorem current_authorization_source (entry : CallEntry) (now : StateCode)
    (valid : entry.Valid) (admitted : authorize .currentWorld entry now = .admitted entry) :
    now.decode.store.read now.decode.current = some entry.environment.rows ∧
      CallReady entry.environment entry.head entry.arguments entry.article entry.declaration
        (.evaluate entry.bindings entry.body) := by
  have permitted := (authorize_exact _ _ _ valid).mp admitted
  cases permitted with
  | current _ same => rw [← same]; exact valid

/-- Pinned evidence retains precisely its original source claim even when the
mutable world changes; this theorem does not claim current-world truth. -/
theorem pinned_source (entry : CallEntry) (valid : entry.Valid) :
    CallReady entry.environment entry.head entry.arguments entry.article entry.declaration
      (.evaluate entry.bindings entry.body) := valid.2

end Mettapedia.Languages.MeTTa.MeTTaAuthoredProgramExecution.Search


set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.MeTTaAuthoredProgramExecution.Controller

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional
open Mettapedia.Languages.MeTTa.MeTTaFiniteRevisionedKernel.AuthoredActivation.AtomCommands (StateCode)
open Mettapedia.Languages.MeTTa.MeTTaAuthoredProgramExecution.Search
open Mettapedia.OSLF.MeTTaIL.GeneralPremise (ProviderSnapshot DynamicProvider)

/-- The original pinned guest remains available unchanged. The conditional
extension is an explicit live source profile, with independently chosen
entry-snapshot or current-world guard authorization. -/
inductive Catalogue where
  | pinned (rows : List Atom)
  | live
  deriving Repr, DecidableEq

structure Settings where
  catalogue : Catalogue := .live
  activation : ActivationPolicy := .pinnedEntry
  registration : ProviderSnapshot := {signatures := [], rows := []}
  dynamic : DynamicProvider := .empty

/-- This test recognizes the actual callable guarded source declaration.
Unknown and non-callable forms are not promoted to evaluator code. -/
def guardedHead? : Atom → Option String
  | .expression (.symbol "rule!" :: .expression (.symbol head :: _) :: _ :: _) => some head
  | _ => none

def hasGuardedHead (rows : List Atom) (head : String) : Bool :=
  rows.any fun row => guardedHead? row == some head

/-- Source permission is stated by the original stored syntax, independently
of the executable membership test. -/
def GuardedHead (rows : List Atom) (head : String) : Prop :=
  ∃ arguments body guards,
    .expression (.symbol "rule!" :: .expression (.symbol head :: arguments) :: body :: guards) ∈ rows

@[simp] theorem guardedHead?_exact (atom : Atom) (head : String) :
    guardedHead? atom = some head ↔
      ∃ arguments body guards, atom = .expression
        (.symbol "rule!" :: .expression (.symbol head :: arguments) :: body :: guards) := by
  constructor
  · intro actual
    unfold guardedHead? at actual
    split at actual
    next actualHead arguments body guards =>
      cases Option.some.inj actual
      exact ⟨arguments, body, guards, rfl⟩
    next => contradiction
  · rintro ⟨arguments, body, guards, same⟩
    subst atom
    rfl

@[simp] theorem hasGuardedHead_exact (rows : List Atom) (head : String) :
    hasGuardedHead rows head = true ↔ GuardedHead rows head := by
  simp only [hasGuardedHead, List.any_eq_true, beq_iff_eq, guardedHead?_exact, GuardedHead]
  constructor
  · rintro ⟨atom, stored, arguments, body, guards, same⟩
    subst atom
    exact ⟨arguments, body, guards, stored⟩
  · rintro ⟨arguments, body, guards, stored⟩
    exact ⟨_, stored, arguments, body, guards, rfl⟩

def activeRows (settings : Settings) (world : StateCode) : Option (List Atom) :=
  match settings.catalogue with
  | .pinned rows => some rows
  | .live => world.decode.store.read world.decode.current

inductive Hook where
  | enter (bindings : Subst) (head : String) (arguments : List Atom)
  | search (head : String) (values : List Atom)
  deriving Repr, DecidableEq

/-- Native and control-form priority remains the original evaluator's.
Only explicit live guarded calls are intercepted. -/
def hook? (settings : Settings) (world : StateCode) : Option Hook :=
  match settings.catalogue with
  | .pinned _ => none
  | .live =>
      (activeRows settings world).bind fun rows =>
        match world.packet.control with
        | .evaluate bindings (.expression (.symbol head :: arguments)) =>
            if !DeclarativeSpec.controlForm (.expression (.symbol head :: arguments)) &&
                !Eval.ioHead head && !StdLib.known head && hasGuardedHead rows head then
              some (.enter bindings head arguments)
            else none
        | .arguments _ (.function head) [] values _ =>
            if !Eval.ioHead head && !StdLib.known head && hasGuardedHead rows head then
              some (.search head values)
            else none
        | _ => none

/-- The exact caller continuation and accumulated occurrences are retained
while guard search and serial body execution alternate. -/
structure CallContext where
  search : CapturedSearch
  cursor : Nat := 0
  answers : List Atom := []
  outerFrames : List Eval.Frame

inductive Phase where
  | running
  | guarding (context : CallContext)
  | blocked (context : CallContext)
  | stale (context : CallContext) (entry : CallEntry) (now : StateCode)

structure Activation where
  entry : CallEntry
  policy : ActivationPolicy
  now : StateCode

def Activation.Valid (activation : Activation) : Prop :=
  activation.entry.Valid ∧ Permitted activation.entry activation.now activation.policy

structure Session where
  world : StateCode
  phase : Phase := .running
  stack : List CallContext := []
  activations : List Activation := []

/-- Successful entry runs the original body under its original assignment.
The caller frames are held in the existing controller context; the body uses
only original evaluator frames until its result returns to that context. -/
def beginBody (settings : Settings) (session : Session) (context : CallContext)
    (entry : CallEntry) : Session :=
  match authorize settings.activation entry session.world with
  | .stale _ now => {session with phase := .stale context entry now}
  | .admitted _ =>
      { session with
        world := {session.world with packet := {session.world.packet with
          control := .evaluate entry.bindings entry.body
          frames := []}}
        phase := .running
        stack := context :: session.stack
        activations := session.activations ++ [⟨entry, settings.activation, session.world⟩] }

/-- A fresh activation log item has independent source authority and the
chosen exact snapshot policy. Later mutations do not rewrite that item. -/
theorem beginBody_source (settings : Settings) (session : Session) (context : CallContext)
    (entry : CallEntry) (valid : entry.Valid)
    (admitted : authorize settings.activation entry session.world = .admitted entry) :
    (⟨entry, settings.activation, session.world⟩ : Activation).Valid ∧
      (beginBody settings session context entry).world.packet.decode =
        {session.world.packet.decode with control := .evaluate entry.bindings entry.body, frames := []} ∧
      (beginBody settings session context entry).stack = context :: session.stack := by
  refine ⟨⟨valid, (authorize_exact _ _ _ valid).mp admitted⟩, ?_, ?_⟩
  · simp only [beginBody, admitted, ProgramReplay.Snapshot.decode]
  · simp only [beginBody, admitted]

/-- Ordinary work executes the presentation generated from the selected
space's current rows and retains the original finite store readback. -/
def ordinary (rows : List Atom) (session : Session) : Option Session :=
  (ProgramReplay.nativeStepInSpace rows session.world.packet).map fun packet =>
    {session with world := {session.world with packet}}

theorem ordinary_source (rows : List Atom) (session next : Session)
    (computed : ordinary rows session = some next) :
    DeclarativeSpec.Transition (SpaceSemantics.index rows)
      session.world.packet.decode next.world.packet.decode := by
  obtain ⟨packet, original, same⟩ := Option.map_eq_some_iff.mp computed
  subst next
  rw [ProgramReplay.nativeStepInSpace_exact] at original
  exact ProgramReplay.nativeStep_sound _ _ _ original

/-- One controller transition: one actual ordinary instruction, one retained
search task, one checked body entry or one serial return. The budget counts
these transitions and makes no physical runtime claim. -/
def step (settings : Settings) (session : Session) : Option Session :=
  match session.phase with
  | .blocked _ | .stale _ _ _ => none
  | .guarding context =>
      match context.search.work.events[context.cursor]? with
      | some event =>
          let nextContext := {context with cursor := context.cursor + 1}
          match event.value with
          | .found _ =>
              match pinAt? context.search context.cursor with
              | some entry => some (beginBody settings session nextContext entry)
              | none => some {session with phase := .blocked context}
          | .unavailable _ _ | .uninterpreted _ _ =>
              some {session with phase := .guarding nextContext}
      | none =>
          if context.search.work.frontier.isEmpty then
            if Search.complete context.search.work then
              some {session with
                world := {session.world with packet := {session.world.packet with
                  control := .returned context.answers
                  frames := context.outerFrames}}
                phase := .running}
            else some {session with phase := .blocked context}
          else some {session with
            phase := .guarding {context with search := Search.advance 1 context.search}}
  | .running =>
      match session.world.packet.control, session.world.packet.frames, session.stack with
      | .returned answers, [], context :: stack =>
          some {session with
            phase := .guarding {context with answers := context.answers ++ answers}
            stack}
      | .fault _, _, _ => none
      | _, _, _ =>
          match hook? settings session.world with
          | some (.enter bindings head arguments) =>
              some {session with world := {session.world with packet := {session.world.packet with
                control := .arguments bindings (.function head) arguments [] 0}}}
          | some (.search head values) =>
              match Search.capture session.world settings.registration settings.dynamic (.callable head values) with
              | some captured => some {session with phase := .guarding ⟨captured, 0, [], session.world.packet.frames⟩}
              | none => some {session with world := {session.world with packet := {session.world.packet with
                  control := .fault .invalidSpace}}}
          | none =>
              match activeRows settings session.world with
              | some rows => ordinary rows session
              | none => some {session with world := {session.world with packet := {session.world.packet with
                  control := .fault .invalidSpace}}}

/-- Exact budget composition keeps unfinished guards, body continuations,
observed occurrences and serial effects. -/
def advance (settings : Settings) : Nat → Session → Session
  | 0, session => session
  | fuel + 1, session =>
      match step settings session with
      | none => session
      | some next => advance settings fuel next

theorem advance_of_stuck (settings : Settings) (fuel : Nat) (session : Session)
    (stuck : step settings session = none) : advance settings fuel session = session := by
  cases fuel <;> simp only [advance, stuck]

theorem advance_add (settings : Settings) (first second : Nat) (session : Session) :
    advance settings (first + second) session = advance settings second (advance settings first session) := by
  induction first generalizing session with
  | zero => simp only [Nat.zero_add, advance]
  | succ first ih =>
      rw [Nat.succ_add]
      simp only [advance]
      cases actual : step settings session with
      | none => exact (advance_of_stuck settings second session actual).symm
      | some next => exact ih next

inductive Outcome where
  | complete (session : Session) (answers : List Atom)
  | fault (session : Session) (reason : Effects.Fault)
  | unknown (session : Session) (known : List Atom)
  | stale (session : Session) (entry : CallEntry)
  | exhausted (session : Session)

def readout (session : Session) : Outcome :=
  match session.phase with
  | .blocked context => .unknown session context.answers
  | .stale _ entry _ => .stale session entry
  | .guarding _ => .exhausted session
  | .running =>
      match session.world.packet.control, session.world.packet.frames, session.stack with
      | .returned answers, [], [] => .complete session answers
      | .fault reason, _, _ => .fault session reason
      | _, _, _ => .exhausted session

def run (settings : Settings) (fuel : Nat) (session : Session) : Outcome :=
  readout (advance settings fuel session)

@[simp] theorem pinned_hook (settings : Settings) (rows : List Atom) (world : StateCode)
    (pinned : settings.catalogue = .pinned rows) : hook? settings world = none := by
  simp only [hook?, pinned]

/-- The original pinned guest is literally delegated to the original machine;
no guarded extension is silently activated inside its stored fact rows. -/
theorem pinned_fallback (settings : Settings) (rows : List Atom) (session : Session)
    (pinned : settings.catalogue = .pinned rows)
    (running : session.phase = .running) (top : session.stack = [])
    (notFault : ∀ reason, session.world.packet.control ≠ .fault reason) :
    step settings session = ordinary rows session := by
  cases controlSame : session.world.packet.control <;>
    cases frameSame : session.world.packet.frames <;>
    simp_all [step, activeRows, hook?]

end Mettapedia.Languages.MeTTa.MeTTaAuthoredProgramExecution.Controller


set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.MeTTaAuthoredProgramExecution.Controller

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.MeTTaAuthoredProgramExecution.Search

/-- Every executed conditional body has its independent original call proof
and its explicit activation policy, retained at the state where it was used. -/
def Session.Sound (session : Session) : Prop :=
  ∀ activation ∈ session.activations, activation.Valid

theorem empty_log_sound (session : Session) (empty : session.activations = []) : session.Sound := by
  intro activation member
  simp only [empty, List.not_mem_nil] at member

theorem beginBody_sound (settings : Settings) (session : Session) (context : CallContext)
    (entry : CallEntry) (sound : session.Sound) (valid : entry.Valid) :
    (beginBody settings session context entry).Sound := by
  intro activation member
  unfold beginBody at member
  split at member
  next => exact sound activation member
  next returned accepted =>
    simp only [List.mem_append, List.mem_singleton] at member
    rcases member with old | same
    · exact sound activation old
    · subst activation
      have payload := authorize_preserves_entry settings.activation entry session.world returned accepted
      rw [payload] at accepted
      exact ⟨valid, (authorize_exact _ _ _ valid).mp accepted⟩

theorem ordinary_sound (rows : List Atom) (session next : Session)
    (sound : session.Sound) (computed : ordinary rows session = some next) : next.Sound := by
  obtain ⟨packet, _, same⟩ := Option.map_eq_some_iff.mp computed
  subst next
  exact sound

/-- One native controller step cannot invent conditional authority. The
checker is replayed at receipt admission; existing snapshots are immutable. -/
theorem step_sound (settings : Settings) (session next : Session)
    (sound : session.Sound) (computed : step settings session = some next) : next.Sound := by
  cases phase : session.phase with
  | blocked context => simp only [step, phase] at computed; contradiction
  | stale context entry now => simp only [step, phase] at computed; contradiction
  | guarding context =>
      simp only [step, phase] at computed
      cases positioned : context.search.work.events[context.cursor]? with
      | none =>
          simp only [positioned] at computed
          split at computed
          · split at computed
            · cases Option.some.inj computed; exact sound
            · cases Option.some.inj computed; exact sound
          · cases Option.some.inj computed; exact sound
      | some event =>
          simp only [positioned] at computed
          cases observed : event.value with
          | unavailable relation arguments =>
              simp only [observed] at computed
              cases Option.some.inj computed
              exact sound
          | uninterpreted guard initial =>
              simp only [observed] at computed
              cases Option.some.inj computed
              exact sound
          | found value =>
              simp only [observed] at computed
              cases admitted : pinAt? context.search context.cursor with
              | none =>
                  simp only [admitted] at computed
                  cases Option.some.inj computed
                  exact sound
              | some entry =>
                  simp only [admitted] at computed
                  cases Option.some.inj computed
                  exact beginBody_sound settings session _ entry sound (pinAt_sound admitted)
  | running =>
      simp only [step, phase] at computed
      split at computed
      · cases Option.some.inj computed; exact sound
      · contradiction
      · cases hookCase : hook? settings session.world with
        | none =>
            simp only [hookCase] at computed
            cases rowCase : activeRows settings session.world with
            | none =>
                simp only [rowCase] at computed
                cases Option.some.inj computed
                exact sound
            | some rows =>
                simp only [rowCase] at computed
                exact ordinary_sound rows session next sound computed
        | some hook =>
            simp only [hookCase] at computed
            cases hook with
            | enter bindings head arguments =>
                cases Option.some.inj computed
                exact sound
            | search head values =>
                cases captured : Search.capture session.world settings.registration settings.dynamic (.callable head values) with
                | none =>
                    simp only [captured] at computed
                    cases Option.some.inj computed
                    exact sound
                | some saved =>
                    simp only [captured] at computed
                    cases Option.some.inj computed
                    exact sound

/-- All finite executions retain independent source call authority. This is
separate from the question whether the entire answer bag is complete. -/
theorem advance_sound (settings : Settings) (fuel : Nat) (session : Session)
    (sound : session.Sound) : (advance settings fuel session).Sound := by
  induction fuel generalizing session with
  | zero => exact sound
  | succ fuel ih =>
      simp only [advance]
      cases computed : step settings session with
      | none => exact sound
      | some next => exact ih next (step_sound settings session next sound computed)

def Outcome.session : Outcome → Session
  | .complete session _ | .fault session _ | .unknown session _ |
    .stale session _ | .exhausted session => session

@[simp] theorem readout_session (session : Session) : (readout session).session = session := by
  unfold readout
  split <;> try rfl
  split <;> rfl

end Mettapedia.Languages.MeTTa.MeTTaAuthoredProgramExecution.Controller


set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.MeTTaAuthoredProgramExecution.Controller

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.MeTTaFiniteRevisionedKernel.AuthoredActivation.AtomCommands (StateCode)

theorem ordinary_fault (rows : List Atom) (session : Session) (reason : Effects.Fault)
    (fault : session.world.packet.control = .fault reason) : ordinary rows session = none := by
  have original : Eval.step (SpaceSemantics.index rows) session.world.packet.decode = none := by
    simp only [Eval.step, ProgramReplay.Snapshot.decode, fault]
  simp only [ordinary, ProgramReplay.nativeStepInSpace_exact, ProgramReplay.nativeStep, original, Option.map_none]

/-- Pinned fallback includes source faults and completed states, so the
conditional wrapper cannot change any original pinned finite execution. -/
theorem pinned_step_exact (settings : Settings) (rows : List Atom) (session : Session)
    (pinned : settings.catalogue = .pinned rows)
    (running : session.phase = .running) (top : session.stack = []) :
    step settings session = ordinary rows session := by
  by_cases fault : ∃ reason, session.world.packet.control = .fault reason
  · obtain ⟨reason, failed⟩ := fault
    simp only [step, running, failed]
    exact (ordinary_fault rows session reason failed).symm
  · exact pinned_fallback settings rows session pinned running top (by simpa using fault)

/-- The guard-free live fragment is specified by source declarations, not by
assuming that the native interception decision happens to be empty. -/
def NoGuardedDeclarations (rows : List Atom) : Prop := ∀ head, ¬GuardedHead rows head

private theorem no_guarded_head {rows : List Atom} (ordinary : NoGuardedDeclarations rows)
    (head : String) : hasGuardedHead rows head = false := by
  cases actual : hasGuardedHead rows head with
  | false => rfl
  | true => exact False.elim (ordinary head ((hasGuardedHead_exact _ _).mp actual))

theorem live_hook_guard_free (settings : Settings) (world : StateCode) (rows : List Atom)
    (live : settings.catalogue = .live) (selected : activeRows settings world = some rows)
    (plain : NoGuardedDeclarations rows) : hook? settings world = none := by
  simp only [hook?, live, selected, Option.bind_some]
  split <;> simp only [no_guarded_head plain, Bool.and_false, Bool.false_eq_true, ↓reduceIte]

/-- At every guard-free live source state, the wrapper uses exactly the old
live machine instruction, including its store effects and source refusal. -/
theorem live_step_guard_free (settings : Settings) (rows : List Atom) (session : Session)
    (live : settings.catalogue = .live)
    (selected : activeRows settings session.world = some rows)
    (plain : NoGuardedDeclarations rows)
    (running : session.phase = .running) (top : session.stack = []) :
    step settings session = ordinary rows session := by
  have unselected := live_hook_guard_free settings session.world rows live selected plain
  cases controlSame : session.world.packet.control <;>
    cases frameSame : session.world.packet.frames <;>
    simp_all [step, ordinary_fault]

/-- The original pinned evaluator is recovered over complete finite prefixes,
not only over isolated calls or a type-level compatibility observation. -/
theorem pinned_advance_original (settings : Settings) (rows : List Atom)
    (pinned : settings.catalogue = .pinned rows) (fuel : Nat) (session : Session)
    (running : session.phase = .running) (top : session.stack = []) :
    (advance settings fuel session).world.packet.decode =
      ProgramReplay.advance (SpaceSemantics.index rows) fuel session.world.packet.decode := by
  induction fuel generalizing session with
  | zero => rfl
  | succ fuel ih =>
      have delegated := pinned_step_exact settings rows session pinned running top
      simp only [advance, delegated, ordinary, ProgramReplay.nativeStepInSpace_exact]
      cases native : ProgramReplay.nativeStep (SpaceSemantics.index rows) session.world.packet with
      | none =>
          have original : Eval.step (SpaceSemantics.index rows) session.world.packet.decode = none := by
            cases actual : Eval.step (SpaceSemantics.index rows) session.world.packet.decode with
            | none => rfl
            | some next => simp [ProgramReplay.nativeStep, actual] at native
          simp only [Option.map_none, ProgramReplay.advance, original]
      | some packet =>
          have original := ProgramReplay.nativeStep_sound _ _ _ native
          have nextStep := Eval.transition_step original
          simp only [Option.map_some, ProgramReplay.advance, nextStep]
          exact ih {session with world := {session.world with packet}} running top

end Mettapedia.Languages.MeTTa.MeTTaAuthoredProgramExecution.Controller


set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.MeTTaAuthoredProgramExecution.ProgramExecution

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.OSLF.MeTTaIL.MeTTaSyntaxQuotation (Program)
open Mettapedia.Languages.MeTTa.MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands
open Mettapedia.Languages.MeTTa.MeTTaFiniteRevisionedKernel.AuthoredActivation.AtomCommands
open Mettapedia.Languages.MeTTa.MeTTaAuthoredProgramExecution
open Mettapedia.Languages.MeTTa.MeTTaFiniteRevisionedKernel.AuthoredActivation

structure Settings where
  evaluator : Controller.Settings := {}
  modules : ProvidedModules := []

/-- Caller state restored after a finite provided import. Its mutable store,
ambient bindings, revisions and I/O are deliberately not restored. -/
structure ImportFrame where
  pending : Program Atom
  offset : Nat
  origin : List Nat
  current : NamedSpaces.Handle
  deriving Repr, DecidableEq

structure Evaluation where
  machine : Controller.Session
  remaining : Nat
  command : Command
  line : Nat
  origin : List Nat

inductive Phase where
  | commands
  | evaluating (active : Evaluation)
  | exhausted (active : Evaluation)
  | blocked (active : Evaluation)
  | stale (active : Evaluation)
  | moduleHeld (command : Command) (target : NamedSpaces.Handle) (module : Atom)
  | fault (reason : Effects.Fault)

inductive Answer where
  | values (answers : List Atom)
  | retained (command : Command)
  | imported (module : Atom) (providerIndex : Nat)
  deriving Repr, DecidableEq

structure Observation where
  line : Nat
  origin : List Nat
  answer : Answer
  deriving Repr, DecidableEq

/-- Every dispatch receipt has independent original command meaning. It
retains the requested continuation rather than claiming that continuation
has already completed. -/
structure Receipt where
  command : Command
  before : StateCode
  result : Result
  line : Nat
  origin : List Nat

def Receipt.Valid (receipt : Receipt) : Prop :=
  Dispatch receipt.command receipt.before.decode receipt.result.after.decode receipt.result.action.decode

structure ImportReceipt where
  module : Atom
  index : Nat
  commands : Program Atom
  origin : List Nat

def ImportReceipt.Valid (modules : ProvidedModules) (receipt : ImportReceipt) : Prop :=
  ModuleAt modules receipt.module receipt.index receipt.commands

structure Session where
  world : StateCode
  pending : Program Atom
  offset : Nat := 0
  origin : List Nat := []
  frames : List ImportFrame := []
  phase : Phase := .commands
  observations : List Observation := []
  receipts : List Receipt := []
  imports : List ImportReceipt := []
  evaluations : List Controller.Session := []

def initial (world : StateCode) (program : Program Atom) : Session := {world, pending := program}

def note (session : Session) (line : Nat) (origin : List Nat) (answer : Answer) : Session :=
  {session with observations := session.observations ++ [⟨line, origin, answer⟩]}

/-- Complete or unresolved evaluation returns the actual retained native
machine. Partial results never stand for a completed answer bag. -/
def inspect (session : Session) (active : Evaluation) : Session :=
  match Controller.readout active.machine with
  | .complete finished answers =>
      note {session with
        world := finished.world
        phase := .commands
        evaluations := session.evaluations ++ [finished]}
        active.line active.origin (.values answers)
  | .fault failed reason =>
      {session with
        world := failed.world
        phase := .fault reason
        evaluations := session.evaluations ++ [failed]}
  | .unknown unresolved _ =>
      {session with
        world := unresolved.world
        phase := .blocked {active with machine := unresolved}}
  | .stale stale _ =>
      {session with
        world := stale.world
        phase := .stale {active with machine := stale}}
  | .exhausted _ =>
      {session with phase := if active.remaining = 0 then .exhausted active else .evaluating active}

/-- Handle one already dispatched original continuation. The command source
receipt has been earned before this function schedules evaluation or import. -/
def handleAction (settings : Settings) (next : Session) (line : Nat) (origin : List Nat)
    (command : Command) : ActionCode → Session
  | .done answers => note next line origin (.values answers)
  | .retained original => note next line origin (.retained original)
  | .fault reason => {next with phase := .fault reason}
  | .evaluate packet =>
      inspect next ⟨{world := {next.world with packet}}, next.world.fuel, command, line, origin⟩
  | .importModule target module =>
      match providedModule? settings.modules module with
      | none => {next with phase := .moduleHeld command target module}
      | some (index, commands) =>
          note {next with
            world := {next.world with current := target}
            pending := commands
            offset := 0
            origin
            frames := ⟨next.pending, next.offset, next.origin, next.world.current⟩ :: next.frames
            imports := next.imports ++ [⟨module, index, commands, origin⟩]}
            line origin (.imported module index)

/-- Run one original command dispatch, one existing conditional/evaluator
instruction, or one explicit finite-import continuation. -/
def step (settings : Settings) (session : Session) : Option Session :=
  match session.phase with
  | .fault _ | .moduleHeld _ _ _ | .blocked _ | .stale _ | .exhausted _ => none
  | .evaluating active =>
      match Controller.readout active.machine with
      | .exhausted _ =>
          match active.remaining with
          | 0 => some {session with phase := .exhausted active}
          | remaining + 1 =>
              match Controller.step settings.evaluator active.machine with
              | none => some {session with phase := .blocked active}
              | some machine => some (inspect session {active with machine, remaining})
      | _ => some (inspect session active)
  | .commands =>
      match session.pending with
      | [] =>
          match session.frames with
          | [] => none
          | frame :: rest => some {session with
              world := {session.world with current := frame.current}
              pending := frame.pending
              offset := frame.offset
              origin := frame.origin
              frames := rest}
      | (line, command) :: pending =>
          let result := AtomCommands.run command session.world
          let origin := session.origin ++ [session.offset]
          let receipt : Receipt := ⟨command, session.world, result, line, origin⟩
          let next := {session with
            world := result.after
            pending
            offset := session.offset + 1
            receipts := session.receipts ++ [receipt]}
          some (handleAction settings next line origin command result.action)

def advance (settings : Settings) : Nat → Session → Session
  | 0, session => session
  | fuel + 1, session =>
      match step settings session with
      | none => session
      | some next => advance settings fuel next

theorem advance_of_stuck (settings : Settings) (fuel : Nat) (session : Session)
    (stuck : step settings session = none) : advance settings fuel session = session := by
  cases fuel <;> simp only [advance, stuck]

theorem advance_add (settings : Settings) (first second : Nat) (session : Session) :
    advance settings (first + second) session = advance settings second (advance settings first session) := by
  induction first generalizing session with
  | zero => simp only [advance, Nat.zero_add]
  | succ first ih =>
      rw [Nat.succ_add]
      simp only [advance]
      cases computed : step settings session with
      | none => exact (advance_of_stuck settings second session computed).symm
      | some next => exact ih next

/-- Additional evaluation work is explicit. No already executed instruction,
observed result occurrence or source import is replayed by refuelling. -/
def refuel (additional : Nat) (session : Session) : Session :=
  match session.phase with
  | .exhausted active => {session with phase := .evaluating {active with remaining := active.remaining + additional}}
  | _ => session

inductive Status where
  | complete
  | exhausted
  | unknown
  | stale
  | fault (reason : Effects.Fault)
  deriving Repr, DecidableEq

def status (session : Session) : Status :=
  match session.phase with
  | .fault reason => .fault reason
  | .moduleHeld _ _ _ | .blocked _ => .unknown
  | .stale _ => .stale
  | .exhausted _ | .evaluating _ => .exhausted
  | .commands => if session.pending.isEmpty && session.frames.isEmpty then .complete else .exhausted

/-- Dispatch correctness is earned before any module or evaluator action is
performed. This covers all fourteen original source command constructors. -/
theorem dispatch_receipt_source (command : Command) (before : StateCode) (line : Nat) (origin : List Nat) :
    (⟨command, before, AtomCommands.run command before, line, origin⟩ : Receipt).Valid :=
  AtomCommands.run_source _ _

/-- A module's actual source body, physical provider coordinate and
first-match shadow policy are retained in the execution receipt. -/
theorem import_receipt_source (settings : Settings) (module : Atom) (index : Nat)
    (commands : Program Atom) (origin : List Nat)
    (selected : providedModule? settings.modules module = some (index, commands)) :
    (⟨module, index, commands, origin⟩ : ImportReceipt).Valid settings.modules :=
  (providedModule?_exact _ _ _ _).mp selected

end Mettapedia.Languages.MeTTa.MeTTaAuthoredProgramExecution.ProgramExecution


set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.MeTTaAuthoredProgramExecution.ProgramExecution

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.OSLF.MeTTaIL.MeTTaSyntaxQuotation (Program)
open Mettapedia.Languages.MeTTa.MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands
open Mettapedia.Languages.MeTTa.MeTTaFiniteRevisionedKernel.AuthoredActivation.AtomCommands
open Mettapedia.Languages.MeTTa.MeTTaFiniteRevisionedKernel.AuthoredActivation

/-- Original command and module provenance survive every bounded controller
prefix, including unresolved imports and interrupted conditional evaluation. -/
structure Session.HistorySound (settings : Settings) (session : Session) : Prop where
  dispatch : ∀ receipt ∈ session.receipts, receipt.Valid
  imports : ∀ receipt ∈ session.imports, receipt.Valid settings.modules

theorem initial_history_sound (settings : Settings) (world : StateCode) (commands : Program Atom) :
    (initial world commands).HistorySound settings := by
  constructor <;> intro receipt absent <;> cases absent

theorem note_history_sound (settings : Settings) (session : Session)
    (line : Nat) (origin : List Nat) (answer : Answer) (sound : session.HistorySound settings) :
    (note session line origin answer).HistorySound settings := ⟨sound.dispatch, sound.imports⟩

private theorem inspect_receipts (session : Session) (active : Evaluation) :
    (inspect session active).receipts = session.receipts := by
  unfold inspect
  split <;> rfl

private theorem inspect_imports (session : Session) (active : Evaluation) :
    (inspect session active).imports = session.imports := by
  unfold inspect
  split <;> rfl

theorem inspect_history_sound (settings : Settings) (session : Session) (active : Evaluation)
    (sound : session.HistorySound settings) : (inspect session active).HistorySound settings := by
  constructor
  · intro receipt member
    rw [inspect_receipts] at member
    exact sound.dispatch receipt member
  · intro receipt member
    rw [inspect_imports] at member
    exact sound.imports receipt member

theorem handleAction_history_sound (settings : Settings) (next : Session) (line : Nat)
    (origin : List Nat) (command : Command) (action : ActionCode)
    (sound : next.HistorySound settings) :
    (handleAction settings next line origin command action).HistorySound settings := by
  cases action with
  | done answers => exact note_history_sound _ _ _ _ _ sound
  | retained original => exact note_history_sound _ _ _ _ _ sound
  | fault reason => exact ⟨sound.dispatch, sound.imports⟩
  | evaluate packet => exact inspect_history_sound _ _ _ sound
  | importModule target module =>
      simp only [handleAction]
      cases selected : providedModule? settings.modules module with
      | none => exact ⟨sound.dispatch, sound.imports⟩
      | some provided =>
          obtain ⟨index, commands⟩ := provided
          apply note_history_sound
          constructor
          · exact sound.dispatch
          · intro receipt member
            rcases List.mem_append.mp member with earlier | fresh
            · exact sound.imports receipt earlier
            · have same := List.mem_singleton.mp fresh
              subst receipt
              exact import_receipt_source _ _ _ _ _ selected

/-- Every newly dispatched source command earns its original independent
judgment. Finite provided imports additionally earn their actual table index. -/
theorem step_history_sound (settings : Settings) (session next : Session)
    (sound : session.HistorySound settings) (computed : step settings session = some next) :
    next.HistorySound settings := by
  cases phase : session.phase with
  | exhausted active => simp only [step, phase] at computed; contradiction
  | blocked active => simp only [step, phase] at computed; contradiction
  | stale active => simp only [step, phase] at computed; contradiction
  | fault reason => simp only [step, phase] at computed; contradiction
  | moduleHeld command target module => simp only [step, phase] at computed; contradiction
  | evaluating active =>
      simp only [step, phase] at computed
      split at computed
      · cases budget : active.remaining with
        | zero =>
            simp only [budget] at computed
            cases Option.some.inj computed
            exact ⟨sound.dispatch, sound.imports⟩
        | succ remaining =>
            simp only [budget] at computed
            cases instruction : Controller.step settings.evaluator active.machine with
            | none =>
                simp only [instruction] at computed
                cases Option.some.inj computed
                exact ⟨sound.dispatch, sound.imports⟩
            | some machine =>
                simp only [instruction] at computed
                cases Option.some.inj computed
                exact inspect_history_sound _ _ _ sound
      · cases Option.some.inj computed
        exact inspect_history_sound _ _ _ sound
  | commands =>
      simp only [step, phase] at computed
      cases pending : session.pending with
      | nil =>
          simp only [pending] at computed
          cases frames : session.frames with
          | nil => simp only [frames] at computed; contradiction
          | cons frame rest =>
              simp only [frames] at computed
              cases Option.some.inj computed
              exact ⟨sound.dispatch, sound.imports⟩
      | cons pair pendingCommands =>
          obtain ⟨line, command⟩ := pair
          simp only [pending] at computed
          let result := AtomCommands.run command session.world
          let origin := session.origin ++ [session.offset]
          let intermediate : Session := {session with
            world := result.after
            pending := pendingCommands
            phase := .commands
            offset := session.offset + 1
            receipts := session.receipts ++ [⟨command, session.world, result, line, origin⟩]}
          have fresh : intermediate.HistorySound settings := by
            constructor
            · intro receipt member
              rcases List.mem_append.mp member with earlier | newReceipt
              · exact sound.dispatch receipt earlier
              · have same := List.mem_singleton.mp newReceipt
                subst receipt
                exact dispatch_receipt_source _ _ _ _
            · exact sound.imports
          change some (handleAction settings intermediate line origin command result.action) = some next at computed
          cases Option.some.inj computed
          exact handleAction_history_sound _ _ _ _ _ _ fresh

/-- Uniform history authority covers every finite source-command execution,
not a fixed vocabulary of successful demonstrations. -/
theorem advance_history_sound (settings : Settings) (fuel : Nat) (session : Session)
    (sound : session.HistorySound settings) : (advance settings fuel session).HistorySound settings := by
  induction fuel generalizing session with
  | zero => exact ⟨sound.dispatch, sound.imports⟩
  | succ fuel ih =>
      simp only [advance]
      cases computed : step settings session with
      | none => exact ⟨sound.dispatch, sound.imports⟩
      | some next => exact ih next (step_history_sound settings session next sound computed)

end Mettapedia.Languages.MeTTa.MeTTaAuthoredProgramExecution.ProgramExecution


set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.MeTTaAuthoredProgramExecution.Text

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.OSLF.MeTTaIL.MeTTaSyntaxQuotation (Program ProgramCommand)
open Mettapedia.Languages.MeTTa.MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands (Command)
open Mettapedia.Languages.MeTTa.MeTTaFiniteRevisionedKernel.AuthoredActivation.AtomCommands (StateCode)
open Algorithms.MeTTa.Simple.Parser (SExpr ParseError)
open MeTTailCore.MeTTaSyntax (SyntaxSpec)

/-- This target is the original Atom command AST. Both the legacy Pattern
reader and this reader use the same source command classifier. -/
def constructors : Algorithms.MeTTa.Simple.Parser.CommandConstructors Atom Command where
  symbol := .symbol
  fact := .fact
  defineEq := .defineEq
  defineRule := .defineRule
  defineType := .defineType
  relationFact := .relationFact
  builtinFact := .builtinFact
  setFuel := .setFuel
  importModule := .import
  newSpace := .newSpace
  addAtom := .addAtom
  removeAtom := .removeAtom

def readAtom (expression : SExpr) : Except ParseError Atom :=
  (SpaceSemantics.readExpression expression).mapError fun message => {message}

@[simp] theorem readAtom_exact (expression : SExpr) (atom : Atom) :
    readAtom expression = .ok atom ↔ SpaceSemantics.readExpression expression = .ok atom := by
  cases parsed : SpaceSemantics.readExpression expression <;> simp [readAtom, parsed, Except.mapError]

abbrev SourceRow := Nat × Bool × SExpr

def lowerRow (spec : SyntaxSpec) (row : SourceRow) : Except ParseError (Nat × Command) := do
  let (line, prefixed, expression) := row
  let command ← (if prefixed then (readAtom expression).map ProgramCommand.eval
    else Algorithms.MeTTa.Simple.Parser.lowerSExprWith spec readAtom constructors expression).mapError
      fun error => if error.line.isNone then {error with line := some line} else error
  return (line, command)

/-- The actual original reader is a named source boundary. Its request marker,
line and intact S-expression remain distinct from term and command lowering.
This relation does not claim grammar-as-data parse-forest adequacy. -/
inductive Lowered (spec : SyntaxSpec) : SourceRow → Nat × Command → Prop where
  | request (line : Nat) (expression : SExpr) (atom : Atom)
      (read : SpaceSemantics.readExpression expression = .ok atom) :
      Lowered spec (line, true, expression) (line, .eval atom)
  | statement (line : Nat) (expression : SExpr) (command : Command)
      (classified : Algorithms.MeTTa.Simple.Parser.lowerSExprWith spec readAtom constructors expression = .ok command) :
      Lowered spec (line, false, expression) (line, command)

@[simp] theorem lowerRow_exact (spec : SyntaxSpec) (row : SourceRow) (output : Nat × Command) :
    lowerRow spec row = .ok output ↔ Lowered spec row output := by
  constructor
  · intro actual
    obtain ⟨line, prefixed, expression⟩ := row
    cases prefixed with
    | false =>
        cases classified : Algorithms.MeTTa.Simple.Parser.lowerSExprWith spec readAtom constructors expression with
        | error reason =>
            simp only [lowerRow, classified] at actual
            cases actual
        | ok command =>
            have computed : lowerRow spec (line, false, expression) = .ok (line, command) := by
              simp only [lowerRow, classified]
              rfl
            have same := Except.ok.inj (computed.symm.trans actual)
            subst output
            exact .statement _ _ _ classified
    | true =>
        cases parsed : SpaceSemantics.readExpression expression with
        | error reason =>
            simp only [lowerRow, readAtom, parsed] at actual
            cases actual
        | ok atom =>
            have computed : lowerRow spec (line, true, expression) = .ok (line, ProgramCommand.eval atom) := by
              simp only [lowerRow, readAtom, parsed]
              rfl
            have same := Except.ok.inj (computed.symm.trans actual)
            subst output
            exact .request _ _ _ parsed
  · intro source
    cases source with
    | request line expression atom read =>
        simp only [lowerRow, readAtom, read]
        rfl
    | statement line expression command classified =>
        simp only [lowerRow, classified]
        rfl

def lowerRows (spec : SyntaxSpec) (rows : List SourceRow) : Except ParseError (Program Atom) :=
  rows.mapM (lowerRow spec)

@[simp] theorem lowerRows_exact (spec : SyntaxSpec) (rows : List SourceRow) (commands : Program Atom) :
    lowerRows spec rows = .ok commands ↔ List.Forall₂ (Lowered spec) rows commands := by
  induction rows generalizing commands with
  | nil =>
      constructor
      · intro same
        have empty : ([] : Program Atom) = commands := Except.ok.inj same
        subst commands
        exact .nil
      · intro lowered
        cases lowered
        rfl
  | cons row rows ih =>
      cases first : lowerRow spec row with
      | error reason =>
          constructor
          · intro impossible
            simp only [lowerRows, List.mapM_cons, first] at impossible
            cases impossible
          · intro lowered
            cases lowered with
            | cons head _ =>
                have admitted := (lowerRow_exact _ _ _).mpr head
                rw [first] at admitted
                cases admitted
      | ok command =>
          cases rest : lowerRows spec rows with
          | error reason =>
              constructor
              · intro impossible
                have actual : lowerRows spec (row :: rows) = .error reason := by
                  simp only [lowerRows, List.mapM_cons, first]
                  change (Except.map (List.cons command) (lowerRows spec rows)) = _
                  rw [rest]
                  rfl
                rw [actual] at impossible
                cases impossible
              · intro lowered
                cases lowered with
                | cons _ tail =>
                    have admitted := (ih _).mpr tail
                    rw [rest] at admitted
                    cases admitted
          | ok commandsTail =>
              have actual : lowerRows spec (row :: rows) = .ok (command :: commandsTail) := by
                simp only [lowerRows, List.mapM_cons, first]
                change (Except.map (List.cons command) (lowerRows spec rows)) = _
                rw [rest]
                rfl
              constructor
              · intro same
                rw [actual] at same
                cases Except.ok.inj same
                exact .cons ((lowerRow_exact _ _ _).mp first) ((ih _).mp rest)
              · intro lowered
                cases lowered with
                | cons head tail =>
                    have headSame := Except.ok.inj (first.symm.trans ((lowerRow_exact _ _ _).mpr head))
                    have tailSame := Except.ok.inj (rest.symm.trans ((ih _).mpr tail))
                    cases headSame
                    cases tailSame
                    exact actual

/-- The same original lossless scanner, request-prefix handling and Atom
reader feed the existing command AST. No Pattern-to-Atom reconstruction occurs. -/
def parseWith (spec : SyntaxSpec) (source : String) : Except ParseError (Program Atom) := do
  let rows ← Algorithms.MeTTa.Simple.Parser.parseSExprCommandsWithDetailed spec source
  lowerRows spec rows

def TextObservation (spec : SyntaxSpec) (source : String) (commands : Program Atom) : Prop :=
  ∃ rows, Algorithms.MeTTa.Simple.Parser.parseSExprCommandsWithDetailed spec source = .ok rows ∧
    List.Forall₂ (Lowered spec) rows commands

@[simp] theorem parseWith_exact (spec : SyntaxSpec) (source : String) (commands : Program Atom) :
    parseWith spec source = .ok commands ↔ TextObservation spec source commands := by
  cases scanned : Algorithms.MeTTa.Simple.Parser.parseSExprCommandsWithDetailed spec source with
  | error reason => simp [parseWith, scanned, TextObservation, bind, Except.bind]
  | ok rows =>
      simp only [parseWith, scanned, bind, Except.bind, TextObservation, Except.ok.injEq]
      constructor
      · intro converted
        exact ⟨rows, rfl, (lowerRows_exact _ _ _).mp converted⟩
      · rintro ⟨original, same, lowered⟩
        cases same
        exact (lowerRows_exact _ _ _).mpr lowered

def parse (source : String) : Except String (Program Atom) :=
  (parseWith MeTTailCore.MeTTaSyntax.petta source).mapError toString

def onText (settings : ProgramExecution.Settings) (world : StateCode)
    (source : String) (fuel : Nat) : Except String ProgramExecution.Session :=
  (parse source).map fun commands =>
    ProgramExecution.advance settings fuel (ProgramExecution.initial world commands)

theorem onText_history (settings : ProgramExecution.Settings) (world : StateCode)
    (source : String) (fuel : Nat) (session : ProgramExecution.Session)
    (executed : onText settings world source fuel = .ok session) :
    session.HistorySound settings := by
  unfold onText at executed
  cases parsed : parse source with
  | error reason => simp only [parsed, Except.map] at executed; cases executed
  | ok commands =>
      simp only [parsed, Except.map, Except.ok.injEq] at executed
      subst session
      exact ProgramExecution.advance_history_sound settings fuel _
        (ProgramExecution.initial_history_sound settings world commands)

/-- Main can observe output while a body is pending, without re-running or
clearing the retained original evaluator configuration. -/
def observedWorld (session : ProgramExecution.Session) : StateCode :=
  match session.phase with
  | .evaluating active | .exhausted active | .blocked active | .stale active => active.machine.world
  | _ => session.world

end Mettapedia.Languages.MeTTa.MeTTaAuthoredProgramExecution.Text


namespace Mettapedia.Languages.MeTTa.MeTTaAuthoredProgramExecution.Search

open Mettapedia.GSLT.Core
open Mettapedia.GSLT.Core.BranchingTemporal
open Mettapedia.Languages.MeTTa.MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional

private theorem complete_frontier {session : Session} (finished : complete session = true) :
    session.frontier = [] := by
  have empty : session.frontier.isEmpty = true := (Bool.and_eq_true_iff.mp finished).1
  exact List.isEmpty_iff.mp empty

/-- A genuinely completed retained search has already emitted every finite
independently authorized source article. Discovery and completed-state
stability supply this result; a found article alone does not. -/
theorem completed_source_coverage (environment : Environment) (goal : Goal) (fuel : Nat)
    (finished : complete (run environment goal fuel (start goal)) = true)
    (value : Value) (source : Meaning environment goal value) :
    (⟨⟨.value value, []⟩, .found value⟩ : Emission Task Observation) ∈
      (run environment goal fuel (start goal)).events := by
  obtain ⟨discovery, found⟩ := source_discovered environment goal value source
  have eventPrefix := BranchingTemporal.events_prefix_run (system environment goal)
    Scheduler.breadthFirst fuel (run environment goal discovery (start goal))
  have retained := eventPrefix.subset found
  have final : run environment goal fuel (run environment goal discovery (start goal)) =
      run environment goal fuel (start goal) := by
    rw [← run_add, Nat.add_comm discovery fuel, run_add]
    exact BranchingTemporal.run_eq_self_of_frontier_nil (system environment goal)
      Scheduler.breadthFirst _ (complete_frontier finished) discovery
  rw [show BranchingTemporal.run (system environment goal) Scheduler.breadthFirst fuel
      (run environment goal discovery (start goal)) =
        run environment goal fuel (run environment goal discovery (start goal)) from rfl,
    final] at retained
  exact retained

/-- Completion gives exact source article coverage, without identifying
articles that happen to have the same endpoint value. This theorem asserts
membership; an answer-bag multiplicity theorem requires a separate account. -/
theorem completed_source_exact (environment : Environment) (goal : Goal) (fuel : Nat)
    (finished : complete (run environment goal fuel (start goal)) = true) (value : Value) :
    Meaning environment goal value ↔
      (⟨⟨.value value, []⟩, .found value⟩ : Emission Task Observation) ∈
        (run environment goal fuel (start goal)).events := by
  constructor
  · exact completed_source_coverage environment goal fuel finished value
  · intro found
    exact found_source environment goal fuel _ value found rfl

/-- The actual work cursor is reachable from the initial source query.
Sound but fabricated empty snapshots do not obtain completion authority. -/
def CapturedSearch.Reachable (captured : CapturedSearch) : Prop :=
  ∃ fuel, captured.work = run captured.environment captured.goal fuel (start captured.goal)

theorem capture_reachable {before : MeTTaFiniteRevisionedKernel.AuthoredActivation.AtomCommands.StateCode}
    {registration : Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderSnapshot}
    {dynamic : Mettapedia.OSLF.MeTTaIL.GeneralPremise.DynamicProvider}
    {goal : Goal} {captured : CapturedSearch}
    (created : capture before registration dynamic goal = some captured) : captured.Reachable := by
  obtain ⟨rows, allocated, same⟩ := Option.map_eq_some_iff.mp created
  cases same
  exact ⟨0, rfl⟩

theorem advance_reachable (fuel : Nat) (captured : CapturedSearch)
    (reachable : captured.Reachable) : (advance fuel captured).Reachable := by
  obtain ⟨prior, computed⟩ := reachable
  refine ⟨prior + fuel, ?_⟩
  simp only [advance, run_add, computed]

/-- Coverage remains about the immutable captured source environment. It
makes no assertion that a later mutated world has the same valid articles. -/
theorem captured_completed_source_exact (captured : CapturedSearch)
    (reachable : captured.Reachable) (finished : complete captured.work = true) (value : Value) :
    Meaning captured.environment captured.goal value ↔
      (⟨⟨.value value, []⟩, .found value⟩ : Emission Task Observation) ∈ captured.work.events := by
  obtain ⟨fuel, computed⟩ := reachable
  rw [computed] at finished ⊢
  exact completed_source_exact _ _ _ finished value

end Mettapedia.Languages.MeTTa.MeTTaAuthoredProgramExecution.Search


namespace Mettapedia.Languages.MeTTa.MeTTaAuthoredProgramExecution.Controller

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MeTTaAuthoredProgramExecution.Search

private def Phase.SearchReachable : Phase → Prop
  | .running => True
  | .guarding context | .blocked context | .stale context _ _ => context.search.Reachable

/-- Every retained search was really started and advanced. Mere per-event
soundness does not authorize a fabricated empty frontier to be exhaustive. -/
def Session.SearchReachable (session : Session) : Prop :=
  session.phase.SearchReachable ∧ ∀ context ∈ session.stack, context.search.Reachable

theorem beginBody_searchReachable (settings : Settings) (session : Session) (context : CallContext)
    (entry : CallEntry) (invariant : session.SearchReachable) (reachable : context.search.Reachable) :
    (beginBody settings session context entry).SearchReachable := by
  unfold beginBody
  split
  · exact ⟨reachable, invariant.2⟩
  · refine ⟨trivial, ?_⟩
    intro retained member
    rcases List.mem_cons.mp member with same | member
    · subst retained
      exact reachable
    · exact invariant.2 _ member

theorem ordinary_searchReachable (rows : List Atom) (session next : Session)
    (invariant : session.SearchReachable) (computed : ordinary rows session = some next) :
    next.SearchReachable := by
  obtain ⟨packet, _, same⟩ := Option.map_eq_some_iff.mp computed
  subst next
  exact invariant

theorem step_searchReachable (settings : Settings) (session next : Session)
    (invariant : session.SearchReachable) (computed : step settings session = some next) :
    next.SearchReachable := by
  cases phase : session.phase with
  | blocked context => simp only [step, phase] at computed; contradiction
  | stale context entry now => simp only [step, phase] at computed; contradiction
  | guarding context =>
      have reachable : context.search.Reachable := by
        simpa only [phase, Phase.SearchReachable] using invariant.1
      simp only [step, phase] at computed
      cases positioned : context.search.work.events[context.cursor]? with
      | none =>
          simp only [positioned] at computed
          split at computed
          · split at computed
            · cases Option.some.inj computed
              exact ⟨trivial, invariant.2⟩
            · cases Option.some.inj computed
              exact ⟨reachable, invariant.2⟩
          · cases Option.some.inj computed
            exact ⟨advance_reachable 1 context.search reachable, invariant.2⟩
      | some event =>
          simp only [positioned] at computed
          cases observed : event.value with
          | unavailable relation arguments =>
              simp only [observed] at computed
              cases Option.some.inj computed
              exact ⟨reachable, invariant.2⟩
          | uninterpreted guard initial =>
              simp only [observed] at computed
              cases Option.some.inj computed
              exact ⟨reachable, invariant.2⟩
          | found value =>
              simp only [observed] at computed
              cases admitted : pinAt? context.search context.cursor with
              | none =>
                  simp only [admitted] at computed
                  cases Option.some.inj computed
                  exact ⟨reachable, invariant.2⟩
              | some entry =>
                  simp only [admitted] at computed
                  cases Option.some.inj computed
                  exact beginBody_searchReachable settings session _ entry invariant reachable
  | running =>
      simp only [step, phase] at computed
      split at computed
      · cases Option.some.inj computed
        simp_all [Session.SearchReachable, Phase.SearchReachable]
      · contradiction
      · cases hookCase : hook? settings session.world with
        | none =>
            simp only [hookCase] at computed
            cases rowCase : activeRows settings session.world with
            | none =>
                simp only [rowCase] at computed
                cases Option.some.inj computed
                exact ⟨trivial, invariant.2⟩
            | some rows =>
                simp only [rowCase] at computed
                exact ordinary_searchReachable rows session next invariant computed
        | some hook =>
            simp only [hookCase] at computed
            cases hook with
            | enter bindings head arguments =>
                cases Option.some.inj computed
                exact ⟨trivial, invariant.2⟩
            | search head values =>
                cases created : capture session.world settings.registration settings.dynamic (.callable head values) with
                | none =>
                    simp only [created] at computed
                    cases Option.some.inj computed
                    exact ⟨trivial, invariant.2⟩
                | some saved =>
                    simp only [created] at computed
                    cases Option.some.inj computed
                    exact ⟨capture_reachable created, invariant.2⟩

theorem advance_searchReachable (settings : Settings) (fuel : Nat) (session : Session)
    (invariant : session.SearchReachable) : (advance settings fuel session).SearchReachable := by
  induction fuel generalizing session with
  | zero => exact invariant
  | succ fuel ih =>
      simp only [advance]
      cases computed : step settings session with
      | none => exact invariant
      | some next => exact ih next (step_searchReachable settings session next invariant computed)

/-- The actual guarding context can use completed source coverage because
its captured queue is reachable, not merely well-formed. -/
theorem guarding_completed_source_exact (session : Session) (context : CallContext)
    (invariant : session.SearchReachable) (guarding : session.phase = .guarding context)
    (finished : Search.complete context.search.work = true) (value : Search.Value) :
    Search.Meaning context.search.environment context.search.goal value ↔
      (⟨⟨.value value, []⟩, .found value⟩ :
        Mettapedia.GSLT.Core.BranchingTemporal.Emission Search.Task Search.Observation) ∈
          context.search.work.events := by
  have reachable : context.search.Reachable := by
    simpa only [guarding, Phase.SearchReachable] using invariant.1
  exact Search.captured_completed_source_exact context.search reachable finished value

end Mettapedia.Languages.MeTTa.MeTTaAuthoredProgramExecution.Controller


namespace Mettapedia.Languages.MeTTa.MeTTaAuthoredProgramExecution.Controller.Source

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.MeTTaFiniteRevisionedKernel.AuthoredActivation.AtomCommands (StateCode)
open Mettapedia.Languages.MeTTa.MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional
open Mettapedia.Languages.MeTTa.MeTTaAuthoredProgramExecution.Search

/-- The selected source declaration store is independent of the optional
executable readout. Pinned and current-store profiles remain distinct. -/
def SelectedRows (settings : Settings) (world : StateCode) (rows : List Atom) : Prop :=
  match settings.catalogue with
  | .pinned declared => rows = declared
  | .live => world.decode.store.read world.decode.current = some rows

@[simp] theorem selectedRows_exact (settings : Settings) (world : StateCode) (rows : List Atom) :
    activeRows settings world = some rows ↔ SelectedRows settings world rows := by
  cases selected : settings.catalogue with
  | pinned declared => simp [activeRows, SelectedRows, selected, eq_comm]
  | live => simp only [activeRows, SelectedRows, selected]

/-- Conditional interception is a source permission. Original control forms,
I/O and native heads keep their original dispatch priority. -/
inductive Hooks (settings : Settings) (world : StateCode) : Hook → Prop where
  | enter {rows : List Atom} {bindings : Subst} {head : String} {arguments : List Atom}
      (live : settings.catalogue = .live)
      (allocated : world.decode.store.read world.decode.current = some rows)
      (control : world.packet.control = .evaluate bindings (.expression (.symbol head :: arguments)))
      (ordinarySyntax : DeclarativeSpec.controlForm (.expression (.symbol head :: arguments)) = false)
      (notIO : Eval.ioHead head = false) (notNative : StdLib.known head = false)
      (declared : GuardedHead rows head) :
      Hooks settings world (.enter bindings head arguments)
  | search {rows : List Atom} {bindings : Subst} {head : String} {values : List Atom} {position : Nat}
      (live : settings.catalogue = .live)
      (allocated : world.decode.store.read world.decode.current = some rows)
      (control : world.packet.control = .arguments bindings (.function head) [] values position)
      (notIO : Eval.ioHead head = false) (notNative : StdLib.known head = false)
      (declared : GuardedHead rows head) :
      Hooks settings world (.search head values)

theorem hook_complete {settings : Settings} {world : StateCode} {hook : Hook}
    (source : Hooks settings world hook) : hook? settings world = some hook := by
  cases source with
  | enter live allocated control ordinarySyntax notIO notNative declared =>
      simp only [hook?, live, activeRows, allocated, Option.bind_some, control,
        ordinarySyntax, notIO, notNative, Bool.not_false, Bool.true_and,
        (hasGuardedHead_exact _ _).mpr declared, ↓reduceIte]
  | search live allocated control notIO notNative declared =>
      simp only [hook?, live, activeRows, allocated, Option.bind_some, control,
        notIO, notNative, Bool.not_false, Bool.true_and,
        (hasGuardedHead_exact _ _).mpr declared, ↓reduceIte]

theorem hook_sound {settings : Settings} {world : StateCode} {hook : Hook}
    (actual : hook? settings world = some hook) : Hooks settings world hook := by
  cases selected : settings.catalogue with
  | pinned declared => simp only [hook?, selected] at actual; contradiction
  | live =>
      simp only [hook?, selected] at actual
      obtain ⟨rows, allocated, matched⟩ := Option.bind_eq_some_iff.mp actual
      have read : world.decode.store.read world.decode.current = some rows := by
        simpa only [activeRows, selected] using allocated
      split at matched
      next bindings head arguments control =>
        split at matched
        next permitted =>
          cases Option.some.inj matched
          simp only [Bool.and_eq_true, Bool.not_eq_true', hasGuardedHead_exact] at permitted
          obtain ⟨⟨⟨ordinarySyntax, notIO⟩, notNative⟩, declared⟩ := permitted
          exact .enter selected read control ordinarySyntax notIO notNative declared
        next => contradiction
      next bindings head values position control =>
        split at matched
        next permitted =>
          cases Option.some.inj matched
          simp only [Bool.and_eq_true, Bool.not_eq_true', hasGuardedHead_exact] at permitted
          obtain ⟨⟨notIO, notNative⟩, declared⟩ := permitted
          exact .search selected read control notIO notNative declared
        next => contradiction
      next => contradiction

@[simp] theorem hook_exact (settings : Settings) (world : StateCode) (hook : Hook) :
    hook? settings world = some hook ↔ Hooks settings world hook := ⟨hook_sound, hook_complete⟩

@[simp] theorem no_hook_exact (settings : Settings) (world : StateCode) :
    hook? settings world = none ↔ ∀ hook, ¬ Hooks settings world hook := by
  constructor
  · intro absent hook source
    have present := hook_complete source
    rw [absent] at present
    cases present
  · intro absent
    cases actual : hook? settings world with
    | none => rfl
    | some hook => exact (absent hook (hook_sound actual)).elim

end Mettapedia.Languages.MeTTa.MeTTaAuthoredProgramExecution.Controller.Source


namespace Mettapedia.Languages.MeTTa.MeTTaAuthoredProgramExecution.Controller.Source

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional
open Mettapedia.Languages.MeTTa.MeTTaAuthoredProgramExecution.Search
open Mettapedia.GSLT.Core.BranchingTemporal (Emission Scheduler)

/-- Original callable evidence, its source snapshot and its physical emission
coordinate jointly determine a receipt. This relation does not run admission. -/
inductive Admitted (captured : CapturedSearch) (observation : Nat) : Search.Value → CallEntry → Prop where
  | callable {head : String} {arguments : List Atom} {article : Evidence} {declaration : Nat}
      {bindings : Subst} {body : Atom}
      (goal : captured.goal = .callable head arguments)
      (allocated : captured.before.decode.store.read captured.before.decode.current =
        some captured.environment.rows)
      (source : CallReady captured.environment head arguments article declaration (.evaluate bindings body)) :
      Admitted captured observation (.callable article declaration bindings body)
        ⟨captured.before, captured.environment, head, arguments, observation,
          article, declaration, bindings, body⟩

theorem admitted_complete {captured : CapturedSearch} {observation : Nat}
    {value : Search.Value} {entry : CallEntry} (source : Admitted captured observation value entry) :
    admitCall? captured observation value = some entry := by
  cases source with
  | callable goal allocated source => exact admitCall_complete _ _ _ _ _ _ _ _ goal allocated source

theorem admitted_sound {captured : CapturedSearch} {observation : Nat}
    {value : Search.Value} {entry : CallEntry}
    (actual : admitCall? captured observation value = some entry) :
    Admitted captured observation value entry := by
  unfold admitCall? at actual
  split at actual
  next _ _ head arguments article declaration bindings body goal =>
    split at actual
    next checked =>
      cases Option.some.inj actual
      obtain ⟨allocated, judged⟩ := Bool.and_eq_true_iff.mp checked
      have source := (judged_exact _ _ _).mp judged
      exact .callable goal (beq_iff_eq.mp allocated) (by simpa only [goal, Meaning] using source)
    next => contradiction
  next => contradiction

@[simp] theorem admitted_exact (captured : CapturedSearch) (observation : Nat)
    (value : Search.Value) (entry : CallEntry) :
    admitCall? captured observation value = some entry ↔ Admitted captured observation value entry :=
  ⟨admitted_sound, admitted_complete⟩

def EntryAt (captured : CapturedSearch) (observation : Nat) (entry : CallEntry) : Prop :=
  ∃ event value, captured.work.events[observation]? = some event ∧
    event.value = .found value ∧ Admitted captured observation value entry

@[simp] theorem pinAt_exact (captured : CapturedSearch) (observation : Nat) (entry : CallEntry) :
    pinAt? captured observation = some entry ↔ EntryAt captured observation entry := by
  constructor
  · intro actual
    obtain ⟨event, selected, checked⟩ := Option.bind_eq_some_iff.mp actual
    cases observed : event.value with
    | found value =>
        exact ⟨event, value, selected, observed,
          admitted_sound (by simpa only [observed] using checked)⟩
    | unavailable _ _ | uninterpreted _ _ => simp only [observed] at checked; contradiction
  · rintro ⟨event, value, selected, observed, admitted⟩
    simp only [pinAt?, selected, Option.bind_some, observed, admitted_complete admitted]

theorem entryAt_valid {captured : CapturedSearch} {observation : Nat} {entry : CallEntry}
    (source : EntryAt captured observation entry) : entry.Valid :=
  pinAt_sound ((pinAt_exact _ _ _).mpr source)

@[simp] theorem no_entry_exact (captured : CapturedSearch) (observation : Nat) :
    pinAt? captured observation = none ↔ ∀ entry, ¬ EntryAt captured observation entry := by
  constructor
  · intro absent entry source
    have actual := (pinAt_exact _ _ _).mpr source
    rw [absent] at actual
    cases actual
  · intro absent
    cases actual : pinAt? captured observation with
    | none => rfl
    | some entry => exact (absent entry ((pinAt_exact _ _ _).mp actual)).elim

/-- Source emission exposes independent evidence authority for a found proof.
The two unresolved observations retain their literal pending request data. -/
inductive Emits (environment : Environment) (goal : Goal) : Task → Search.Observation → Prop where
  | found {value : Search.Value} (source : Meaning environment goal value) :
      Emits environment goal ⟨.value value, []⟩ (.found value)
  | unavailable (relation : String) (arguments : List Atom) (frames : List Search.Frame) :
      Emits environment goal ⟨.unavailable relation arguments, frames⟩ (.unavailable relation arguments)
  | uninterpreted (guard : Atom) (initial : Subst) (frames : List Search.Frame) :
      Emits environment goal ⟨.uninterpreted guard initial, frames⟩ (.uninterpreted guard initial)

theorem emit_complete {environment : Environment} {goal : Goal} {task : Task}
    {observation : Search.Observation} (source : Emits environment goal task observation) :
    Search.emit environment goal task = some observation := by
  cases source with
  | found source => exact emit_of_source source
  | unavailable => rfl
  | uninterpreted => rfl

theorem emit_sound {environment : Environment} {goal : Goal} {task : Task}
    {observation : Search.Observation}
    (actual : Search.emit environment goal task = some observation) :
    Emits environment goal task observation := by
  rcases task with ⟨control, frames⟩
  cases control with
  | value value =>
      cases frames with
      | nil =>
          simp only [Search.emit] at actual
          split at actual
          next checked =>
            cases Option.some.inj actual
            exact .found ((judged_exact _ _ _).mp checked)
          next => contradiction
      | cons first rest => simp only [Search.emit] at actual; contradiction
  | unavailable relation arguments =>
      simp only [Search.emit] at actual
      cases Option.some.inj actual
      exact .unavailable relation arguments frames
  | uninterpreted guard initial =>
      simp only [Search.emit] at actual
      cases Option.some.inj actual
      exact .uninterpreted guard initial frames
  | root _ | callable _ _ | premise _ _ | premises _ _ | queryRow _ _ _ _ =>
      simp only [Search.emit] at actual
      contradiction

@[simp] theorem emit_exact (environment : Environment) (goal : Goal) (task : Task)
    (observation : Search.Observation) :
    Search.emit environment goal task = some observation ↔ Emits environment goal task observation :=
  ⟨emit_sound, emit_complete⟩

@[simp] theorem no_emit_exact (environment : Environment) (goal : Goal) (task : Task) :
    Search.emit environment goal task = none ↔ ∀ observation, ¬ Emits environment goal task observation := by
  constructor
  · intro absent observation source
    have actual := emit_complete source
    rw [absent] at actual
    cases actual
  · intro absent
    cases actual : Search.emit environment goal task with
    | none => rfl
    | some observation => exact (absent observation (emit_sound actual)).elim

/-- One FIFO administrative action of the retained proof-search service.
This queue policy is not a result-order promise of the source language. -/
inductive Tick (environment : Environment) (goal : Goal) : Search.Session → Search.Session → Prop where
  | emitted {before : Search.Session} {task : Task} {pending : List Task} {observation : Search.Observation}
      (selected : before.frontier = task :: pending) (emitted : Emits environment goal task observation) :
      Tick environment goal before
        ⟨before.events ++ [⟨task, observation⟩], pending ++ Search.successors environment task⟩
  | silent {before : Search.Session} {task : Task} {pending : List Task}
      (selected : before.frontier = task :: pending)
      (silent : ∀ observation, ¬ Emits environment goal task observation) :
      Tick environment goal before ⟨before.events, pending ++ Search.successors environment task⟩

theorem tick_complete {environment : Environment} {goal : Goal} {before after : Search.Session}
    (source : Tick environment goal before after) :
    Search.run environment goal 1 before = after := by
  cases source with
  | emitted selected emitted =>
      simp only [Search.run, Mettapedia.GSLT.Core.BranchingTemporal.run,
        Mettapedia.GSLT.Core.BranchingTemporal.tick, Scheduler.breadthFirst, selected,
        Search.system, emit_complete emitted]
      rfl
  | silent selected silent =>
      simp only [Search.run, Mettapedia.GSLT.Core.BranchingTemporal.run,
        Mettapedia.GSLT.Core.BranchingTemporal.tick, Scheduler.breadthFirst, selected,
        Search.system, (no_emit_exact _ _ _).mpr silent]
      change ({ events := before.events ++ [], frontier := _ } : Search.Session) = _
      simp only [List.append_nil]

/-- A nonempty retained frontier takes exactly the source FIFO action. -/
theorem tick_sound (environment : Environment) (goal : Goal) (before : Search.Session)
    (nonempty : before.frontier ≠ []) : Tick environment goal before (Search.run environment goal 1 before) := by
  cases selected : before.frontier with
  | nil => exact (nonempty selected).elim
  | cons task pending =>
      cases emitted : Search.emit environment goal task with
      | none =>
          have source := Tick.silent selected ((no_emit_exact _ _ _).mp emitted)
          rw [tick_complete source]
          exact source
      | some observation =>
          have source := Tick.emitted selected (emit_sound emitted)
          rw [tick_complete source]
          exact source

def AllFound (events : List (Emission Task Search.Observation)) : Prop :=
  ∀ event ∈ events, ∃ value, event.value = .found value

private theorem observation_resolved (observation : Search.Observation) :
    observation.blocked = false ↔ ∃ value, observation = .found value := by
  cases observation <;> simp [Search.Observation.blocked]

@[simp] theorem complete_exact (session : Search.Session) :
    Search.complete session = true ↔ session.frontier = [] ∧ AllFound session.events := by
  simp only [Search.complete, Bool.and_eq_true, List.isEmpty_iff, Bool.not_eq_true',
    List.any_eq_false, Bool.not_eq_true, observation_resolved, AllFound]

/-- Authorization failure is exactly a current-world policy applied to a
source-valid snapshot whose represented command world has changed. -/
def Stale (entry : CallEntry) (now : MeTTaFiniteRevisionedKernel.AuthoredActivation.AtomCommands.StateCode)
    (policy : ActivationPolicy) : Prop :=
  policy = .currentWorld ∧ entry.before.decode ≠ now.decode

@[simp] theorem authorize_stale_exact (policy : ActivationPolicy) (entry : CallEntry)
    (now : MeTTaFiniteRevisionedKernel.AuthoredActivation.AtomCommands.StateCode) :
    authorize policy entry now = .stale entry now ↔ Stale entry now policy := by
  cases policy <;> simp [authorize, Stale, ← entry_current_exact]

end Mettapedia.Languages.MeTTa.MeTTaAuthoredProgramExecution.Controller.Source


namespace Mettapedia.Languages.MeTTa.MeTTaAuthoredProgramExecution.Controller.Source

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.MeTTaFiniteRevisionedKernel.AuthoredActivation.AtomCommands (StateCode)
open Mettapedia.Languages.MeTTa.MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional
open Mettapedia.Languages.MeTTa.MeTTaAuthoredProgramExecution.Search

/-- A completed body returns to its actual pending guarded call before any
ordinary instruction or invalid-space fallback may run. -/
def Returning (session : Controller.Session) : Prop :=
  ∃ answers context stack,
    session.world.packet.control = .returned answers ∧ session.world.packet.frames = [] ∧
      session.stack = context :: stack

def Runnable (session : Controller.Session) : Prop :=
  ¬ Returning session ∧ ∀ reason, session.world.packet.control ≠ .fault reason

/-- Source semantics for the explicit conditional extension of the original
Atom machine. The original transition judgment supplies all ordinary work;
call entry consumes independently stated source evidence. The remaining
constructors state this implementation's retained administrative policy. -/
inductive Transition (settings : Settings) : Controller.Session → Controller.Session → Prop where
  | returned {before : Controller.Session} {answers : List Atom} {context : CallContext}
      {stack : List CallContext}
      (running : before.phase = .running)
      (control : before.world.packet.control = .returned answers)
      (frames : before.world.packet.frames = []) (pending : before.stack = context :: stack) :
      Transition settings before
        {before with phase := .guarding {context with answers := context.answers ++ answers}, stack}
  | entered {before : Controller.Session} {bindings : Subst} {head : String} {arguments : List Atom}
      (running : before.phase = .running) (source : Hooks settings before.world (.enter bindings head arguments)) :
      Transition settings before {before with world := {before.world with packet :=
        {before.world.packet with control := .arguments bindings (.function head) arguments [] 0}}}
  | captured {before : Controller.Session} {head : String} {values rows : List Atom}
      (running : before.phase = .running) (source : Hooks settings before.world (.search head values))
      (allocated : before.world.decode.store.read before.world.decode.current = some rows) :
      Transition settings before {before with phase := .guarding ⟨⟨before.world, ⟨rows, settings.registration, settings.dynamic⟩, .callable head values,
          Search.start (.callable head values)⟩, 0, [], before.world.packet.frames⟩}
  | ordinary {before : Controller.Session} {rows : List Atom} {after : Eval.Configuration}
      (running : before.phase = .running)
      (selected : SelectedRows settings before.world rows)
      (ordinary : ∀ hook, ¬ Hooks settings before.world hook)
      (source : DeclarativeSpec.Transition (SpaceSemantics.index rows) before.world.packet.decode after) :
      Transition settings before {before with world := {before.world with packet := ProgramReplay.snapshot (ProgramReplay.supportAfter before.world.packet.cellNames before.world.packet.decode) after}}
  | invalidSpace {before : Controller.Session}
      (running : before.phase = .running) (runnable : Runnable before)
      (ordinary : ∀ hook, ¬ Hooks settings before.world hook)
      (unallocated : ∀ rows, ¬ SelectedRows settings before.world rows) :
      Transition settings before {before with world := {before.world with packet :=
        {before.world.packet with control := .fault .invalidSpace}}}
  | skipUnavailable {before : Controller.Session} {context : CallContext}
      {event : Mettapedia.GSLT.Core.BranchingTemporal.Emission Search.Task Search.Observation}
      {relation : String} {arguments : List Atom}
      (guarding : before.phase = .guarding context)
      (selected : context.search.work.events[context.cursor]? = some event)
      (observed : event.value = .unavailable relation arguments) :
      Transition settings before {before with phase := .guarding {context with cursor := context.cursor + 1}}
  | skipUninterpreted {before : Controller.Session} {context : CallContext}
      {event : Mettapedia.GSLT.Core.BranchingTemporal.Emission Search.Task Search.Observation}
      {guard : Atom} {initial : Subst}
      (guarding : before.phase = .guarding context)
      (selected : context.search.work.events[context.cursor]? = some event)
      (observed : event.value = .uninterpreted guard initial) :
      Transition settings before {before with phase := .guarding {context with cursor := context.cursor + 1}}
  | admitted {before : Controller.Session} {context : CallContext} {entry : CallEntry}
      (guarding : before.phase = .guarding context)
      (selected : EntryAt context.search context.cursor entry)
      (permitted : Permitted entry before.world settings.activation) :
      Transition settings before {before with
        world := {before.world with packet := {before.world.packet with
          control := .evaluate entry.bindings entry.body, frames := []}}
        phase := .running
        stack := {context with cursor := context.cursor + 1} :: before.stack
        activations := before.activations ++ [⟨entry, settings.activation, before.world⟩] }
  | stale {before : Controller.Session} {context : CallContext} {entry : CallEntry}
      (guarding : before.phase = .guarding context)
      (selected : EntryAt context.search context.cursor entry)
      (changed : Stale entry before.world settings.activation) :
      Transition settings before {before with
        phase := .stale {context with cursor := context.cursor + 1} entry before.world}
  | invalidFound {before : Controller.Session} {context : CallContext}
      {event : Mettapedia.GSLT.Core.BranchingTemporal.Emission Search.Task Search.Observation}
      {value : Search.Value}
      (guarding : before.phase = .guarding context)
      (selected : context.search.work.events[context.cursor]? = some event)
      (observed : event.value = .found value)
      (unadmittable : ∀ entry, ¬ EntryAt context.search context.cursor entry) :
      Transition settings before {before with phase := .blocked context}
  | completed {before : Controller.Session} {context : CallContext}
      (guarding : before.phase = .guarding context)
      (consumed : context.search.work.events[context.cursor]? = none)
      (exhausted : context.search.work.frontier = [])
      (resolved : AllFound context.search.work.events) :
      Transition settings before {before with
        world := {before.world with packet := {before.world.packet with
          control := .returned context.answers, frames := context.outerFrames}}
        phase := .running}
  | held {before : Controller.Session} {context : CallContext}
      (guarding : before.phase = .guarding context)
      (consumed : context.search.work.events[context.cursor]? = none)
      (exhausted : context.search.work.frontier = [])
      (unresolved : ¬ AllFound context.search.work.events) :
      Transition settings before {before with phase := .blocked context}
  | searching {before : Controller.Session} {context : CallContext} {after : Search.Session}
      (guarding : before.phase = .guarding context)
      (consumed : context.search.work.events[context.cursor]? = none)
      (pending : context.search.work.frontier ≠ [])
      (source : Tick context.search.environment context.search.goal context.search.work after) :
      Transition settings before {before with phase := .guarding {context with search := {context.search with work := after}}}

end Mettapedia.Languages.MeTTa.MeTTaAuthoredProgramExecution.Controller.Source


namespace Mettapedia.Languages.MeTTa.MeTTaAuthoredProgramExecution.Controller.Source

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.MeTTaAuthoredProgramExecution.Search

/-- Any ordinary source instruction is distinct from the administrative
return and terminal-fault cases of the conditional controller. -/
theorem ordinary_runnable {session : Controller.Session} {program : SpaceSemantics.Program}
    {after : Eval.Configuration}
    (source : DeclarativeSpec.Transition program session.world.packet.decode after) : Runnable session := by
  have actual := Eval.transition_step source
  constructor
  · rintro ⟨answers, context, stack, control, frames, pending⟩
    simp only [ProgramReplay.Snapshot.decode, control, frames, Eval.step] at actual
    contradiction
  · intro reason control
    simp only [ProgramReplay.Snapshot.decode, control, Eval.step] at actual
    contradiction

/-- Operational decomposition used only to prove refinement. The independent
source transition rules above do not mention the executable `step` equation. -/
theorem running_dispatch (settings : Settings) (session : Controller.Session)
    (running : session.phase = .running) (runnable : Runnable session) :
    Controller.step settings session =
      match hook? settings session.world with
      | some (.enter bindings head arguments) =>
          some {session with world := {session.world with packet := {session.world.packet with
            control := .arguments bindings (.function head) arguments [] 0}}}
      | some (.search head values) =>
          match Search.capture session.world settings.registration settings.dynamic (.callable head values) with
          | some captured => some {session with phase := .guarding ⟨captured, 0, [], session.world.packet.frames⟩}
          | none => some {session with world := {session.world with packet := {session.world.packet with
              control := .fault .invalidSpace}}}
      | none =>
          match activeRows settings session.world with
          | some rows => ordinary rows session
          | none => some {session with world := {session.world with packet := {session.world.packet with
              control := .fault .invalidSpace}}} := by
  cases control : session.world.packet.control with
  | fault reason => exact (runnable.2 reason control).elim
  | returned answers =>
      cases frames : session.world.packet.frames with
      | nil =>
          cases stack : session.stack with
          | nil => simp only [Controller.step, running, control, frames, stack]
          | cons context tail => exact (runnable.1 ⟨answers, context, tail, control, frames, stack⟩).elim
      | cons first rest => simp only [Controller.step, running, control, frames]
  | evaluate bindings term => simp only [Controller.step, running, control]
  | arguments bindings target remaining values position => simp only [Controller.step, running, control]
  | sequence remaining answers => simp only [Controller.step, running, control]

theorem hook_runnable {settings : Settings} {session : Controller.Session} {hook : Hook}
    (source : Hooks settings session.world hook) : Runnable session := by
  cases source with
  | enter _ _ control _ _ _ _ =>
      constructor
      · rintro ⟨answers, context, stack, other, _, _⟩
        rw [control] at other
        cases other
      · intro reason other
        rw [control] at other
        cases other
  | search _ _ control _ _ _ =>
      constructor
      · rintro ⟨answers, context, stack, other, _, _⟩
        rw [control] at other
        cases other
      · intro reason other
        rw [control] at other
        cases other

@[simp] theorem no_rows_exact (settings : Settings)
    (world : MeTTaFiniteRevisionedKernel.AuthoredActivation.AtomCommands.StateCode) :
    activeRows settings world = none ↔ ∀ rows, ¬ SelectedRows settings world rows := by
  constructor
  · intro absent rows source
    have actual := (selectedRows_exact _ _ _).mpr source
    rw [absent] at actual
    cases actual
  · intro absent
    cases actual : activeRows settings world with
    | none => rfl
    | some rows => exact (absent rows ((selectedRows_exact _ _ _).mp actual)).elim

/-- Every independently permitted source transition is executed by the
original controller without changing its serial effect/continuation policy. -/
theorem transition_complete {settings : Settings} {before after : Controller.Session}
    (source : Transition settings before after) : Controller.step settings before = some after := by
  cases source with
  | returned running control frames pending =>
      simp only [Controller.step, running, control, frames, pending]
  | entered running source =>
      rw [running_dispatch _ _ running (hook_runnable source), hook_complete source]
  | captured running source allocated =>
      rw [running_dispatch _ _ running (hook_runnable source), hook_complete source]
      simp only [Search.capture, allocated, Option.map_some]
  | ordinary running selected noHook source =>
      rw [running_dispatch _ _ running (ordinary_runnable source),
        (no_hook_exact _ _).mpr noHook, (selectedRows_exact _ _ _).mpr selected]
      simp only [Controller.ordinary, ProgramReplay.nativeStepInSpace_exact,
        (ProgramReplay.nativeStep_of_transition _ _ _ source).1,
        Option.map_some]
  | invalidSpace running runnable noHook unallocated =>
      rw [running_dispatch _ _ running runnable, (no_hook_exact _ _).mpr noHook,
        (no_rows_exact _ _).mpr unallocated]
  | skipUnavailable guarding selected observed =>
      simp only [Controller.step, guarding, selected, observed]
  | skipUninterpreted guarding selected observed =>
      simp only [Controller.step, guarding, selected, observed]
  | admitted guarding selected permitted =>
      obtain ⟨event, value, positioned, observed, admitted⟩ := selected
      have pinned := (pinAt_exact _ _ _).mpr ⟨event, value, positioned, observed, admitted⟩
      have authority := (authorize_exact _ _ _ (admitCall_sound (admitted_complete admitted))).mpr permitted
      simp only [Controller.step, guarding, positioned, observed, pinned, beginBody, authority]
  | stale guarding selected changed =>
      obtain ⟨event, value, positioned, observed, admitted⟩ := selected
      have pinned := (pinAt_exact _ _ _).mpr ⟨event, value, positioned, observed, admitted⟩
      have denied := (authorize_stale_exact _ _ _).mpr changed
      simp only [Controller.step, guarding, positioned, observed, pinned, beginBody, denied]
  | invalidFound guarding selected observed unadmittable =>
      simp only [Controller.step, guarding, selected, observed, (no_entry_exact _ _).mpr unadmittable]
  | completed guarding consumed exhausted resolved =>
      have finished := (complete_exact _).mpr ⟨exhausted, resolved⟩
      simp only [Controller.step, guarding, consumed, exhausted, List.isEmpty_nil, ↓reduceIte, finished]
  | @held context guarding consumed exhausted unresolved =>
      have unfinished : Search.complete context.search.work = false := by
        apply Bool.eq_false_iff.mpr
        intro finished
        exact unresolved ((complete_exact _).mp finished).2
      simp only [Controller.step, guarding, consumed, exhausted, List.isEmpty_nil, ↓reduceIte,
        unfinished, Bool.false_eq_true]
  | searching guarding consumed pending source =>
      have nonempty : List.isEmpty _ = false := List.isEmpty_eq_false_iff.mpr pending
      simp only [Controller.step, guarding, consumed, nonempty, Bool.false_eq_true, ↓reduceIte,
        Search.advance, tick_complete source]

end Mettapedia.Languages.MeTTa.MeTTaAuthoredProgramExecution.Controller.Source


namespace Mettapedia.Languages.MeTTa.MeTTaAuthoredProgramExecution.Controller.Source

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.MeTTaAuthoredProgramExecution.Search

private theorem actual_is_source {settings : Settings} {before expected after : Controller.Session}
    (source : Transition settings before expected)
    (actual : Controller.step settings before = some after) : Transition settings before after := by
  have same := Option.some.inj ((transition_complete source).symm.trans actual)
  exact same ▸ source

private theorem permitted_or_stale (entry : CallEntry)
    (now : MeTTaFiniteRevisionedKernel.AuthoredActivation.AtomCommands.StateCode)
    (policy : ActivationPolicy) (valid : entry.Valid) :
    Permitted entry now policy ∨ Stale entry now policy := by
  cases policy with
  | pinnedEntry => exact .inl (.pinned valid)
  | currentWorld =>
      by_cases same : entry.before.decode = now.decode
      · exact .inl (.current valid same)
      · exact .inr ⟨rfl, same⟩

/-- Every actual conditional-controller action has an independently stated
source transition, including serial returns, stale commits and unresolved
requests. The proof uses primitive source authority rather than an assumed
whole-controller correctness field. -/
theorem transition_sound {settings : Settings} {before after : Controller.Session}
    (actual : Controller.step settings before = some after) : Transition settings before after := by
  cases phase : before.phase with
  | blocked context => simp only [Controller.step, phase] at actual; contradiction
  | stale context entry now => simp only [Controller.step, phase] at actual; contradiction
  | guarding context =>
      cases positioned : context.search.work.events[context.cursor]? with
      | none =>
          by_cases exhausted : context.search.work.frontier = []
          · by_cases resolved : AllFound context.search.work.events
            · exact actual_is_source (.completed phase positioned exhausted resolved) actual
            · exact actual_is_source (.held phase positioned exhausted resolved) actual
          · exact actual_is_source (.searching phase positioned exhausted
              (tick_sound context.search.environment context.search.goal context.search.work exhausted)) actual
      | some event =>
          cases observed : event.value with
          | unavailable relation arguments =>
              exact actual_is_source (.skipUnavailable phase positioned observed) actual
          | uninterpreted guard initial =>
              exact actual_is_source (.skipUninterpreted phase positioned observed) actual
          | found value =>
              cases pinned : pinAt? context.search context.cursor with
              | none =>
                  exact actual_is_source (.invalidFound phase positioned observed
                    ((no_entry_exact _ _).mp pinned)) actual
              | some entry =>
                  have source := (pinAt_exact _ _ _).mp pinned
                  rcases permitted_or_stale entry before.world settings.activation (entryAt_valid source) with permitted | stale
                  · exact actual_is_source (.admitted phase source permitted) actual
                  · exact actual_is_source (.stale phase source stale) actual
  | running =>
      by_cases returning : Returning before
      · obtain ⟨answers, context, stack, control, frames, pending⟩ := returning
        exact actual_is_source (.returned phase control frames pending) actual
      · by_cases faulted : ∃ reason, before.world.packet.control = .fault reason
        · obtain ⟨reason, control⟩ := faulted
          simp only [Controller.step, phase, control] at actual
          contradiction
        · have runnable : Runnable before := ⟨returning, fun reason same => faulted ⟨reason, same⟩⟩
          have computed := actual
          rw [running_dispatch _ _ phase runnable] at computed
          cases hookCase : hook? settings before.world with
          | none =>
              simp only [hookCase] at computed
              have noHook := (no_hook_exact _ _).mp hookCase
              cases rowsCase : activeRows settings before.world with
              | none =>
                  exact actual_is_source (.invalidSpace phase runnable noHook
                    ((no_rows_exact _ _).mp rowsCase)) actual
              | some rows =>
                  simp only [rowsCase, Controller.ordinary, ProgramReplay.nativeStepInSpace_exact] at computed
                  obtain ⟨packet, emitted, _⟩ := Option.map_eq_some_iff.mp computed
                  exact actual_is_source (.ordinary phase ((selectedRows_exact _ _ _).mp rowsCase)
                    noHook (ProgramReplay.nativeStep_sound _ _ _ emitted)) actual
          | some hook =>
              have source := hook_sound hookCase
              cases hook with
              | enter bindings head arguments => exact actual_is_source (.entered phase source) actual
              | search head values =>
                  cases source with
                  | search live allocated control notIO notNative declared =>
                      exact actual_is_source (.captured phase
                        (.search live allocated control notIO notNative declared) allocated) actual

@[simp] theorem step_exact (settings : Settings) (before after : Controller.Session) :
    Controller.step settings before = some after ↔ Transition settings before after :=
  ⟨transition_sound, transition_complete⟩

/-- No transition is a source statement, separate from whether the current
observation is success, unknown, stale or a source fault. -/
@[simp] theorem stopped_exact (settings : Settings) (before : Controller.Session) :
    Controller.step settings before = none ↔ ∀ after, ¬ Transition settings before after := by
  constructor
  · intro absent after source
    have actual := transition_complete source
    rw [absent] at actual
    cases actual
  · intro absent
    cases actual : Controller.step settings before with
    | none => rfl
    | some after => exact (absent after (transition_sound actual)).elim

/-- A finite source execution counts actual controller actions, retaining
all intermediate source occurrences and causal serial state changes. -/
inductive Trace (settings : Settings) : Nat → Controller.Session → Controller.Session → Prop where
  | nil (session : Controller.Session) : Trace settings 0 session session
  | cons {count : Nat} {first middle last : Controller.Session}
      (step : Transition settings first middle) (rest : Trace settings count middle last) :
      Trace settings (count + 1) first last

theorem trace_realized {settings : Settings} {count : Nat} {before after : Controller.Session}
    (source : Trace settings count before after) : Controller.advance settings count before = after := by
  induction source with
  | nil => rfl
  | cons step rest ih =>
      simp only [Controller.advance, transition_complete step]
      exact ih

/-- A bounded execution has a finite source trace. If it stops early, the
trace records fewer actions rather than inventing empty execution steps. -/
theorem advance_trace (settings : Settings) (budget : Nat) (before : Controller.Session) :
    ∃ count ≤ budget, Trace settings count before (Controller.advance settings budget before) := by
  induction budget generalizing before with
  | zero => exact ⟨0, Nat.le_refl _, .nil before⟩
  | succ budget ih =>
      cases actual : Controller.step settings before with
      | none =>
          rw [Controller.advance, actual]
          exact ⟨0, Nat.zero_le _, .nil before⟩
      | some middle =>
          obtain ⟨count, bounded, source⟩ := ih middle
          rw [Controller.advance, actual]
          exact ⟨count + 1, Nat.add_le_add_right bounded 1, .cons (transition_sound actual) source⟩

end Mettapedia.Languages.MeTTa.MeTTaAuthoredProgramExecution.Controller.Source


namespace Mettapedia.Languages.MeTTa.MeTTaAuthoredProgramExecution.Controller.Source

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.MeTTaAuthoredProgramExecution.Search

/-- Independent observation of the existing retained controller state.
Success requires the original evaluator to have returned through every
pending continuation and every guarded-call context. -/
inductive View : Controller.Session → Outcome → Prop where
  | complete {session : Controller.Session} {answers : List Atom}
      (running : session.phase = .running)
      (control : session.world.packet.control = .returned answers)
      (frames : session.world.packet.frames = []) (stack : session.stack = []) :
      View session (.complete session answers)
  | fault {session : Controller.Session} {reason : Effects.Fault}
      (running : session.phase = .running) (control : session.world.packet.control = .fault reason) :
      View session (.fault session reason)
  | unknown {session : Controller.Session} {context : CallContext}
      (blocked : session.phase = .blocked context) : View session (.unknown session context.answers)
  | stale {session : Controller.Session} {context : CallContext} {entry : CallEntry}
      {now : MeTTaFiniteRevisionedKernel.AuthoredActivation.AtomCommands.StateCode}
      (stale : session.phase = .stale context entry now) : View session (.stale session entry)
  | guarding {session : Controller.Session} {context : CallContext}
      (guarding : session.phase = .guarding context) : View session (.exhausted session)
  | running {session : Controller.Session}
      (running : session.phase = .running)
      (pending : ¬ ∃ answers, session.world.packet.control = .returned answers ∧
        session.world.packet.frames = [] ∧ session.stack = [])
      (notFault : ∀ reason, session.world.packet.control ≠ .fault reason) :
      View session (.exhausted session)

theorem view_complete {session : Controller.Session} {outcome : Outcome}
    (source : View session outcome) : Controller.readout session = outcome := by
  cases source with
  | complete running control frames stack =>
      simp only [Controller.readout, running, control, frames, stack]
  | fault running control => simp only [Controller.readout, running, control]
  | unknown blocked => simp only [Controller.readout, blocked]
  | stale stale => simp only [Controller.readout, stale]
  | guarding guarding => simp only [Controller.readout, guarding]
  | running running pending notFault =>
      cases control : session.world.packet.control with
      | fault reason => exact (notFault reason control).elim
      | returned answers =>
          cases frames : session.world.packet.frames with
          | nil =>
              cases stack : session.stack with
              | nil => exact (pending ⟨answers, control, frames, stack⟩).elim
              | cons first rest => simp only [Controller.readout, running, control, frames, stack]
          | cons first rest => simp only [Controller.readout, running, control, frames]
      | evaluate _ _ | arguments _ _ _ _ _ | sequence _ _ =>
          simp only [Controller.readout, running, control]

theorem view_source (session : Controller.Session) : View session (Controller.readout session) := by
  classical
  cases phase : session.phase with
  | blocked context =>
      rw [Controller.readout, phase]
      exact .unknown phase
  | stale context entry now =>
      rw [Controller.readout, phase]
      exact .stale phase
  | guarding context =>
      rw [Controller.readout, phase]
      exact .guarding phase
  | running =>
      by_cases completed : ∃ answers, session.world.packet.control = .returned answers ∧
          session.world.packet.frames = [] ∧ session.stack = []
      · obtain ⟨answers, control, frames, stack⟩ := completed
        have source := View.complete phase control frames stack
        rw [view_complete source]
        exact source
      · by_cases faulted : ∃ reason, session.world.packet.control = .fault reason
        · obtain ⟨reason, control⟩ := faulted
          have source := View.fault phase control
          rw [view_complete source]
          exact source
        · have source := View.running phase completed (fun reason same => faulted ⟨reason, same⟩)
          rw [view_complete source]
          exact source

@[simp] theorem readout_exact (session : Controller.Session) (outcome : Outcome) :
    Controller.readout session = outcome ↔ View session outcome := by
  constructor
  · intro same
    rw [← same]
    exact view_source session
  · exact view_complete

end Mettapedia.Languages.MeTTa.MeTTaAuthoredProgramExecution.Controller.Source


namespace Mettapedia.Languages.MeTTa.MeTTaAuthoredProgramExecution.ProgramExecution.Source

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.OSLF.MeTTaIL.MeTTaSyntaxQuotation (Program)
open Mettapedia.Languages.MeTTa.MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands
open Mettapedia.Languages.MeTTa.MeTTaFiniteRevisionedKernel.AuthoredActivation
open Mettapedia.Languages.MeTTa.MeTTaFiniteRevisionedKernel.AuthoredActivation.AtomCommands

/-- Original command inference and the existing finite representation map.
No native dispatcher execution is a premise of this source relation. -/
inductive Dispatched (command : Command) (before : StateCode) : Result → Prop where
  | original {after : State} {action : Action}
      (source : Dispatch command before.decode after action) :
      Dispatched command before
        ⟨StateCode.encode before.packet.cellNames after, ActionCode.encode before.packet.cellNames action⟩

theorem dispatched_complete {command : Command} {before : StateCode} {result : Result}
    (source : Dispatched command before result) : AtomCommands.run command before = result := by
  cases source with
  | original source => simp only [AtomCommands.run, dispatch_complete source]

theorem dispatched_source (command : Command) (before : StateCode) :
    Dispatched command before (AtomCommands.run command before) := by
  unfold AtomCommands.run
  exact .original (dispatch_sound command before.decode)

@[simp] theorem dispatched_exact (command : Command) (before : StateCode) (result : Result) :
    AtomCommands.run command before = result ↔ Dispatched command before result := by
  constructor
  · intro same
    rw [← same]
    exact dispatched_source command before
  · exact dispatched_complete

/-- Source observation of a retained evaluation. A partial or unresolved
machine cannot introduce a completed command-answer bag. -/
inductive Inspect (before : ProgramExecution.Session) (active : Evaluation) : ProgramExecution.Session → Prop where
  | complete {answers : List Atom}
      (source : Controller.Source.View active.machine (.complete active.machine answers)) :
      Inspect before active {before with
        world := active.machine.world
        phase := .commands
        observations := before.observations ++ [⟨active.line, active.origin, .values answers⟩]
        evaluations := before.evaluations ++ [active.machine]}
  | fault {reason : Effects.Fault}
      (source : Controller.Source.View active.machine (.fault active.machine reason)) :
      Inspect before active {before with
        world := active.machine.world
        phase := .fault reason
        evaluations := before.evaluations ++ [active.machine]}
  | unknown {known : List Atom}
      (source : Controller.Source.View active.machine (.unknown active.machine known)) :
      Inspect before active {before with world := active.machine.world, phase := .blocked active}
  | stale {entry : Search.CallEntry}
      (source : Controller.Source.View active.machine (.stale active.machine entry)) :
      Inspect before active {before with world := active.machine.world, phase := .stale active}
  | exhausted (source : Controller.Source.View active.machine (.exhausted active.machine))
      (zero : active.remaining = 0) :
      Inspect before active {before with phase := .exhausted active}
  | evaluating (source : Controller.Source.View active.machine (.exhausted active.machine))
      (remaining : active.remaining ≠ 0) :
      Inspect before active {before with phase := .evaluating active}

theorem inspect_complete {before after : ProgramExecution.Session} {active : Evaluation}
    (source : Inspect before active after) : ProgramExecution.inspect before active = after := by
  cases source with
  | complete source => simp only [ProgramExecution.inspect, Controller.Source.view_complete source, ProgramExecution.note]
  | fault source => simp only [ProgramExecution.inspect, Controller.Source.view_complete source]
  | unknown source => simp only [ProgramExecution.inspect, Controller.Source.view_complete source]
  | stale source => simp only [ProgramExecution.inspect, Controller.Source.view_complete source]
  | exhausted source zero =>
      simp only [ProgramExecution.inspect, Controller.Source.view_complete source, zero, ↓reduceIte]
  | evaluating source remaining =>
      simp only [ProgramExecution.inspect, Controller.Source.view_complete source, if_neg remaining]

theorem inspect_source (before : ProgramExecution.Session) (active : Evaluation) :
    Inspect before active (ProgramExecution.inspect before active) := by
  generalize observed : Controller.readout active.machine = outcome
  have source := (Controller.Source.readout_exact _ _).mp observed
  cases source with
  | complete running control frames stack =>
      have source := Controller.Source.View.complete running control frames stack
      rw [inspect_complete (.complete source)]
      exact .complete source
  | fault running control =>
      have source := Controller.Source.View.fault running control
      rw [inspect_complete (.fault source)]
      exact .fault source
  | unknown blocked =>
      have source := Controller.Source.View.unknown blocked
      rw [inspect_complete (.unknown source)]
      exact .unknown source
  | stale stale =>
      have source := Controller.Source.View.stale stale
      rw [inspect_complete (.stale source)]
      exact .stale source
  | guarding guarding =>
      have source := Controller.Source.View.guarding guarding
      by_cases zero : active.remaining = 0
      · rw [inspect_complete (.exhausted source zero)]
        exact .exhausted source zero
      · rw [inspect_complete (.evaluating source zero)]
        exact .evaluating source zero
  | running running pending notFault =>
      have source := Controller.Source.View.running running pending notFault
      by_cases zero : active.remaining = 0
      · rw [inspect_complete (.exhausted source zero)]
        exact .exhausted source zero
      · rw [inspect_complete (.evaluating source zero)]
        exact .evaluating source zero

/-- Continuations of a source command retain source line/occurrence metadata,
original evaluation and finite provided-module authority. -/
inductive Handle (settings : Settings) (before : ProgramExecution.Session)
    (line : Nat) (origin : List Nat) (command : Command) : ActionCode → ProgramExecution.Session → Prop where
  | done (answers : List Atom) :
      Handle settings before line origin command (.done answers)
        {before with observations := before.observations ++ [⟨line, origin, .values answers⟩]}
  | retained (literal : Command) :
      Handle settings before line origin command (.retained literal)
        {before with observations := before.observations ++ [⟨line, origin, .retained literal⟩]}
  | fault (reason : Effects.Fault) :
      Handle settings before line origin command (.fault reason) {before with phase := .fault reason}
  | evaluate {packet : ProgramReplay.Snapshot} {after : ProgramExecution.Session}
      (source : Inspect before
        ⟨{world := {before.world with packet}}, before.world.fuel, command, line, origin⟩ after) :
      Handle settings before line origin command (.evaluate packet) after
  | imported {target : NamedSpaces.Handle} {module : Atom} {index : Nat} {commands : Program Atom}
      (source : ModuleAt settings.modules module index commands) :
      Handle settings before line origin command (.importModule target module) {before with
        world := {before.world with current := target}
        pending := commands
        offset := 0
        origin
        frames := ⟨before.pending, before.offset, before.origin, before.world.current⟩ :: before.frames
        observations := before.observations ++ [⟨line, origin, .imported module index⟩]
        imports := before.imports ++ [⟨module, index, commands, origin⟩]}
  | unprovided {target : NamedSpaces.Handle} {module : Atom}
      (source : ∀ index commands, ¬ ModuleAt settings.modules module index commands) :
      Handle settings before line origin command (.importModule target module)
        {before with phase := .moduleHeld command target module}

@[simp] theorem no_module_exact (modules : ProvidedModules) (module : Atom) :
    providedModule? modules module = none ↔ ∀ index commands, ¬ ModuleAt modules module index commands := by
  constructor
  · intro absent index commands source
    have actual := (providedModule?_exact _ _ _ _).mpr source
    rw [absent] at actual
    cases actual
  · intro absent
    cases actual : providedModule? modules module with
    | none => rfl
    | some selected =>
        rcases selected with ⟨index, commands⟩
        exact (absent index commands ((providedModule?_exact _ _ _ _).mp actual)).elim

theorem handle_complete {settings : Settings} {before after : ProgramExecution.Session}
    {line : Nat} {origin : List Nat} {command : Command} {action : ActionCode}
    (source : Handle settings before line origin command action after) :
    ProgramExecution.handleAction settings before line origin command action = after := by
  cases source with
  | done => rfl
  | retained => rfl
  | fault => rfl
  | evaluate source => exact inspect_complete source
  | imported source =>
      simp only [ProgramExecution.handleAction, (providedModule?_exact _ _ _ _).mpr source, ProgramExecution.note]
  | unprovided source =>
      simp only [ProgramExecution.handleAction, (no_module_exact _ _).mpr source]

theorem handle_source (settings : Settings) (before : ProgramExecution.Session)
    (line : Nat) (origin : List Nat) (command : Command) (action : ActionCode) :
    Handle settings before line origin command action
      (ProgramExecution.handleAction settings before line origin command action) := by
  cases action with
  | done answers => exact .done answers
  | retained literal => exact .retained literal
  | fault reason => exact .fault reason
  | evaluate packet => exact .evaluate (inspect_source _ _)
  | importModule target module =>
      cases selected : providedModule? settings.modules module with
      | none =>
          rw [handle_complete (.unprovided ((no_module_exact _ _).mp selected))]
          exact .unprovided ((no_module_exact _ _).mp selected)
      | some pair =>
          rcases pair with ⟨index, commands⟩
          rw [handle_complete (.imported ((providedModule?_exact _ _ _ _).mp selected))]
          exact .imported ((providedModule?_exact _ _ _ _).mp selected)

end Mettapedia.Languages.MeTTa.MeTTaAuthoredProgramExecution.ProgramExecution.Source


namespace Mettapedia.Languages.MeTTa.MeTTaAuthoredProgramExecution.ProgramExecution.Source

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.OSLF.MeTTaIL.MeTTaSyntaxQuotation (Program)
open Mettapedia.Languages.MeTTa.MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands
open Mettapedia.Languages.MeTTa.MeTTaFiniteRevisionedKernel.AuthoredActivation.AtomCommands

/-- Commit the independently earned command receipt at its physical source
occurrence before scheduling its evaluation or provided import continuation. -/
def recorded (before : ProgramExecution.Session) (line : Nat) (command : Command)
    (pending : Program Atom) (result : Result) : ProgramExecution.Session :=
  {before with
    world := result.after
    pending
    offset := before.offset + 1
    receipts := before.receipts ++ [⟨command, before.world, result, line,
      before.origin ++ [before.offset]⟩]}

/-- Independent source execution of all original command families. Actual
conditional-body work uses the source transition relation above. Imports
restore the caller's location while retaining the causally produced store,
bindings, revisions and I/O. -/
inductive Transition (settings : Settings) : ProgramExecution.Session → ProgramExecution.Session → Prop where
  | returnedImport {before : ProgramExecution.Session} {frame : ImportFrame} {rest : List ImportFrame}
      (commands : before.phase = .commands) (empty : before.pending = [])
      (pending : before.frames = frame :: rest) :
      Transition settings before {before with
        world := {before.world with current := frame.current}
        pending := frame.pending
        offset := frame.offset
        origin := frame.origin
        frames := rest}
  | dispatched {before after : ProgramExecution.Session} {line : Nat} {command : Command}
      {pending : Program Atom} {result : Result}
      (commands : before.phase = .commands) (pendingCommand : before.pending = (line, command) :: pending)
      (source : Dispatched command before.world result)
      (handled : Handle settings (recorded before line command pending result) line
        (before.origin ++ [before.offset]) command result.action after) :
      Transition settings before after
  | observed {before after : ProgramExecution.Session} {active : Evaluation}
      (evaluating : before.phase = .evaluating active)
      (settled : ¬ Controller.Source.View active.machine (.exhausted active.machine))
      (source : Inspect before active after) :
      Transition settings before after
  | exhausted {before : ProgramExecution.Session} {active : Evaluation}
      (evaluating : before.phase = .evaluating active)
      (unfinished : Controller.Source.View active.machine (.exhausted active.machine))
      (empty : active.remaining = 0) :
      Transition settings before {before with phase := .exhausted active}
  | unavailable {before : ProgramExecution.Session} {active : Evaluation} {remaining : Nat}
      (evaluating : before.phase = .evaluating active)
      (unfinished : Controller.Source.View active.machine (.exhausted active.machine))
      (budget : active.remaining = remaining + 1)
      (noStep : ∀ machine, ¬ Controller.Source.Transition settings.evaluator active.machine machine) :
      Transition settings before {before with phase := .blocked active}
  | evaluated {before after : ProgramExecution.Session} {active : Evaluation}
      {machine : Controller.Session} {remaining : Nat}
      (evaluating : before.phase = .evaluating active)
      (unfinished : Controller.Source.View active.machine (.exhausted active.machine))
      (budget : active.remaining = remaining + 1)
      (source : Controller.Source.Transition settings.evaluator active.machine machine)
      (observed : Inspect before {active with machine, remaining} after) :
      Transition settings before after

theorem transition_complete {settings : Settings} {before after : ProgramExecution.Session}
    (source : Transition settings before after) : ProgramExecution.step settings before = some after := by
  cases source with
  | returnedImport commands empty pending =>
      simp only [ProgramExecution.step, commands, empty, pending]
  | dispatched commands pending source handled =>
      simp only [ProgramExecution.step, commands, pending, dispatched_complete source]
      simpa only [recorded, commands] using congrArg some (handle_complete handled)
  | @observed after active evaluating settled source =>
      have original := Controller.Source.view_source active.machine
      generalize observed : Controller.readout active.machine = outcome at original
      cases original with
      | complete running control frames stack =>
          simp only [ProgramExecution.step, evaluating, observed, inspect_complete source]
      | fault running control =>
          simp only [ProgramExecution.step, evaluating, observed, inspect_complete source]
      | unknown blocked =>
          simp only [ProgramExecution.step, evaluating, observed, inspect_complete source]
      | stale stale =>
          simp only [ProgramExecution.step, evaluating, observed, inspect_complete source]
      | guarding guarding => exact (settled (.guarding guarding)).elim
      | running running pending notFault => exact (settled (.running running pending notFault)).elim
  | exhausted evaluating unfinished empty =>
      simp only [ProgramExecution.step, evaluating, Controller.Source.view_complete unfinished, empty]
  | unavailable evaluating unfinished budget noStep =>
      simp only [ProgramExecution.step, evaluating, Controller.Source.view_complete unfinished, budget,
        (Controller.Source.stopped_exact _ _).mpr noStep]
  | evaluated evaluating unfinished budget source observed =>
      simp only [ProgramExecution.step, evaluating, Controller.Source.view_complete unfinished, budget,
        Controller.Source.transition_complete source, inspect_complete observed]

end Mettapedia.Languages.MeTTa.MeTTaAuthoredProgramExecution.ProgramExecution.Source


namespace Mettapedia.Languages.MeTTa.MeTTaAuthoredProgramExecution.ProgramExecution.Source

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MeTTaFiniteRevisionedKernel.AuthoredActivation.AtomCommands

private theorem actual_is_source {settings : Settings} {before expected after : ProgramExecution.Session}
    (source : Transition settings before expected)
    (actual : ProgramExecution.step settings before = some after) : Transition settings before after := by
  have same := Option.some.inj ((transition_complete source).symm.trans actual)
  exact same ▸ source

/-- The complete command driver follows original source dispatch, original
conditional transitions and independently selected finite module bodies. -/
theorem transition_sound {settings : Settings} {before after : ProgramExecution.Session}
    (actual : ProgramExecution.step settings before = some after) : Transition settings before after := by
  cases phase : before.phase with
  | fault reason => simp only [ProgramExecution.step, phase] at actual; contradiction
  | moduleHeld command target module => simp only [ProgramExecution.step, phase] at actual; contradiction
  | blocked active => simp only [ProgramExecution.step, phase] at actual; contradiction
  | stale active => simp only [ProgramExecution.step, phase] at actual; contradiction
  | exhausted active => simp only [ProgramExecution.step, phase] at actual; contradiction
  | commands =>
      cases pending : before.pending with
      | nil =>
          cases frames : before.frames with
          | nil => simp only [ProgramExecution.step, phase, pending, frames] at actual; contradiction
          | cons frame rest => exact actual_is_source (.returnedImport phase pending frames) actual
      | cons first rest =>
          rcases first with ⟨line, command⟩
          exact actual_is_source (.dispatched phase pending (dispatched_source _ _)
            (handle_source _ _ _ _ _ _)) actual
  | evaluating active =>
      by_cases unfinished : Controller.Source.View active.machine (.exhausted active.machine)
      · cases remaining : active.remaining with
        | zero => exact actual_is_source (.exhausted phase unfinished remaining) actual
        | succ budget =>
            cases machine : Controller.step settings.evaluator active.machine with
            | none =>
                exact actual_is_source (.unavailable phase unfinished remaining
                  ((Controller.Source.stopped_exact _ _).mp machine)) actual
            | some next =>
                exact actual_is_source (.evaluated phase unfinished remaining
                  (Controller.Source.transition_sound machine) (inspect_source _ _)) actual
      · exact actual_is_source (.observed phase unfinished (inspect_source _ _)) actual

@[simp] theorem step_exact (settings : Settings) (before after : ProgramExecution.Session) :
    ProgramExecution.step settings before = some after ↔ Transition settings before after :=
  ⟨transition_sound, transition_complete⟩

@[simp] theorem stopped_exact (settings : Settings) (before : ProgramExecution.Session) :
    ProgramExecution.step settings before = none ↔ ∀ after, ¬ Transition settings before after := by
  constructor
  · intro absent after source
    have actual := transition_complete source
    rw [absent] at actual
    cases actual
  · intro absent
    cases actual : ProgramExecution.step settings before with
    | none => rfl
    | some after => exact (absent after (transition_sound actual)).elim

/-- Finite source execution is the existing relation-theoretic closure.
No alternate evaluator or private trace datatype is introduced. -/
abbrev Trace (settings : Settings) := Relation.ReflTransGen (Transition settings)

/-- Every finite source command execution has an actual native run. Each
source occurrence and causal state transition remains in the same position. -/
theorem trace_realized {settings : Settings} {before after : ProgramExecution.Session}
    (source : Trace settings before after) :
    ∃ budget, ProgramExecution.advance settings budget before = after := by
  induction source with
  | refl => exact ⟨0, rfl⟩
  | tail path transition ih =>
      obtain ⟨budget, executed⟩ := ih
      refine ⟨budget + 1, ?_⟩
      rw [ProgramExecution.advance_add, executed]
      simp only [ProgramExecution.advance, transition_complete transition]

/-- Every bounded native execution is a genuine finite source execution.
Stopping early does not invent further empty source transitions. -/
theorem advance_trace (settings : Settings) (budget : Nat) (before : ProgramExecution.Session) :
    Trace settings before (ProgramExecution.advance settings budget before) := by
  induction budget generalizing before with
  | zero => exact .refl
  | succ budget ih =>
      cases actual : ProgramExecution.step settings before with
      | none =>
          rw [ProgramExecution.advance, actual]
      | some middle =>
          rw [ProgramExecution.advance, actual]
          exact Relation.ReflTransGen.head (transition_sound actual) (ih middle)

@[simp] theorem finite_execution_exact (settings : Settings) (before after : ProgramExecution.Session) :
    (∃ budget, ProgramExecution.advance settings budget before = after) ↔ Trace settings before after := by
  constructor
  · rintro ⟨budget, executed⟩
    rw [← executed]
    exact advance_trace settings budget before
  · exact trace_realized

end Mettapedia.Languages.MeTTa.MeTTaAuthoredProgramExecution.ProgramExecution.Source


namespace Mettapedia.Languages.MeTTa.MeTTaAuthoredProgramExecution.ProgramExecution.Source

/-- A list of independently justified source states realizes exactly one
native command-machine action per link. No stopped-state padding is counted. -/
theorem path_realized {settings : Settings} {before : ProgramExecution.Session}
    {following : List ProgramExecution.Session}
    (source : List.IsChain (Transition settings) (before :: following)) :
    ProgramExecution.advance settings following.length before =
      (before :: following).getLast (by simp) := by
  induction following generalizing before with
  | nil => rfl
  | cons middle rest ih =>
      obtain ⟨first, later⟩ := List.isChain_cons_cons.mp source
      simp only [List.length_cons, ProgramExecution.advance, transition_complete first,
        List.getLast_cons_cons]
      exact ih later

/-- A bounded run records its actual source states. If fewer actions occurred
than the requested budget, its endpoint has no source successor. The list
retains every causal state and occurrence; its order is this machine's policy. -/
theorem advance_path (settings : Settings) (budget : Nat) (before : ProgramExecution.Session) :
    ∃ following : List ProgramExecution.Session,
      following.length ≤ budget ∧
      List.IsChain (Transition settings) (before :: following) ∧
      (before :: following).getLast (by simp) = ProgramExecution.advance settings budget before ∧
      (following.length < budget →
        ∀ next, ¬ Transition settings (ProgramExecution.advance settings budget before) next) := by
  induction budget generalizing before with
  | zero =>
      exact ⟨[], Nat.le_refl 0, .singleton before, rfl, by simp⟩
  | succ budget ih =>
      cases actual : ProgramExecution.step settings before with
      | none =>
          refine ⟨[], Nat.zero_le _, .singleton before, ?_, ?_⟩
          · simp only [List.getLast_singleton, ProgramExecution.advance, actual]
          · intro _
            simp only [ProgramExecution.advance, actual]
            exact (stopped_exact _ _).mp actual
      | some middle =>
          obtain ⟨following, bounded, chain, endpoint, stopped⟩ := ih middle
          refine ⟨middle :: following, Nat.succ_le_succ bounded,
            .cons_cons (transition_sound actual) chain, ?_, ?_⟩
          · simpa only [List.getLast_cons_cons, ProgramExecution.advance, actual] using endpoint
          · intro short
            have shorter : following.length < budget := by simpa only [List.length_cons,
              Nat.add_lt_add_iff_right] using short
            simpa only [ProgramExecution.advance, actual] using stopped shorter

/-- A stopped source state remains fixed under additional requested budget.
This is an execution-prefix law, not an additional source inference. -/
theorem advance_of_stopped {settings : Settings} {before : ProgramExecution.Session}
    (stopped : ∀ next, ¬ Transition settings before next) (extra : Nat) :
    ProgramExecution.advance settings extra before = before := by
  cases extra with
  | zero => rfl
  | succ extra => simp only [ProgramExecution.advance, (stopped_exact _ _).mpr stopped]

/-- Exact bounded execution: either the path uses every requested action or
its independently specified endpoint is stopped. An arbitrary short prefix
cannot certify the result of a larger execution. -/
theorem bounded_execution_path_exact (settings : Settings) (budget : Nat)
    (before after : ProgramExecution.Session) :
    ProgramExecution.advance settings budget before = after ↔
      ∃ following : List ProgramExecution.Session,
        following.length ≤ budget ∧
        List.IsChain (Transition settings) (before :: following) ∧
        (before :: following).getLast (by simp) = after ∧
        (following.length < budget → ∀ next, ¬ Transition settings after next) := by
  constructor
  · intro executed
    obtain ⟨following, bounded, source, endpoint, stopped⟩ := advance_path settings budget before
    exact ⟨following, bounded, source, endpoint.trans executed, executed ▸ stopped⟩
  · rintro ⟨following, bounded, source, endpoint, stopped⟩
    have path := (path_realized source).trans endpoint
    rcases Nat.eq_or_lt_of_le bounded with equal | short
    · simpa only [equal] using path
    · have split : budget = following.length + (budget - following.length) := by omega
      rw [split, ProgramExecution.advance_add, path]
      exact advance_of_stopped (stopped short) _

end Mettapedia.Languages.MeTTa.MeTTaAuthoredProgramExecution.ProgramExecution.Source


namespace Mettapedia.Languages.MeTTa.MeTTaAuthoredProgramExecution.Text

open Mettapedia.Languages.MeTTa.MeTTaFiniteRevisionedKernel.AuthoredActivation.AtomCommands
open Mettapedia.OSLF.MeTTaIL.MeTTaSyntaxQuotation (Program)
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

/-- The actual host reader and lossless original Atom lowering are followed
by independently justified command execution. This statement is relative to
that reader; it does not assert grammar-as-data parsing adequacy. -/
theorem onText_source (settings : ProgramExecution.Settings) (world : StateCode)
    (source : String) (budget : Nat) (session : ProgramExecution.Session)
    (executed : onText settings world source budget = .ok session) :
    ∃ commands : Program Atom, parse source = .ok commands ∧
      ProgramExecution.Source.Trace settings (ProgramExecution.initial world commands) session := by
  unfold onText at executed
  cases parsed : parse source with
  | error reason => simp only [parsed, Except.map] at executed; cases executed
  | ok commands =>
      simp only [parsed, Except.map, Except.ok.injEq] at executed
      refine ⟨commands, rfl, ?_⟩
      rw [← executed]
      exact ProgramExecution.Source.advance_trace settings budget _

/-- Every finite independently specified command execution from a program
read by the actual source reader is realizable by the retained native runner. -/
theorem finite_onText_exact (settings : ProgramExecution.Settings) (world : StateCode)
    (source : String) (session : ProgramExecution.Session) :
    (∃ budget, onText settings world source budget = .ok session) ↔
      ∃ commands : Program Atom, parse source = .ok commands ∧
        ProgramExecution.Source.Trace settings (ProgramExecution.initial world commands) session := by
  constructor
  · rintro ⟨budget, executed⟩
    exact onText_source settings world source budget session executed
  · rintro ⟨commands, parsed, path⟩
    obtain ⟨budget, executed⟩ := ProgramExecution.Source.trace_realized path
    refine ⟨budget, ?_⟩
    simp only [onText, parsed, Except.map, executed]

/-- Exact bounded textual execution retains the physical source state at
all command-machine links, including an independently stopped short prefix. -/
theorem onText_counted_exact (settings : ProgramExecution.Settings) (world : StateCode)
    (source : String) (budget : Nat) (session : ProgramExecution.Session) :
    onText settings world source budget = .ok session ↔
      ∃ (commands : Program Atom) (following : List ProgramExecution.Session),
        parse source = .ok commands ∧ following.length ≤ budget ∧
        List.IsChain (ProgramExecution.Source.Transition settings)
          (ProgramExecution.initial world commands :: following) ∧
        (ProgramExecution.initial world commands :: following).getLast (by simp) = session ∧
        (following.length < budget →
          ∀ next, ¬ ProgramExecution.Source.Transition settings session next) := by
  constructor
  · intro executed
    unfold onText at executed
    cases parsed : parse source with
    | error reason => simp only [parsed, Except.map] at executed; cases executed
    | ok commands =>
        simp only [parsed, Except.map, Except.ok.injEq] at executed
        obtain ⟨following, bounded, chain, endpoint, stopped⟩ :=
          (ProgramExecution.Source.bounded_execution_path_exact _ _ _ _).mp executed
        exact ⟨commands, following, rfl, bounded, chain, endpoint, stopped⟩
  · rintro ⟨commands, following, parsed, bounded, chain, endpoint, stopped⟩
    have executed := (ProgramExecution.Source.bounded_execution_path_exact _ _ _ _).mpr
      ⟨following, bounded, chain, endpoint, stopped⟩
    simp only [onText, parsed, Except.map, executed]

end Mettapedia.Languages.MeTTa.MeTTaAuthoredProgramExecution.Text
