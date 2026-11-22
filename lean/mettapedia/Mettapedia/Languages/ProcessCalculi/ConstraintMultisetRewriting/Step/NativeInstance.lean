import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPredicateQueryAdmission
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Interface

/-!
# Native firings are firings of the candidate step, with published results

A native state carries its private row family. A native firing's data are its rule, selection,
outputs, publication flags, predicate queries, solver budget and its **publication recipes**, fixed
before execution and absent outside the produced ports. `native` is the candidate step over these
data. It admits them exactly when a native firing with those data exists (`NativeFiring.Realized`),
and that is the interface's characterization (`native_admits_iff`): the data's shapes, the physical
enabling of the selection, semantic solvability of the actual information, and an ask of the guards
and queries at every solution.

## The result is the published state

The step's result is computed from the firing's data and the solver's return on its information
(`nativePrepare`, a residual because the information is solvable), by the formulas of the
execution's target and of its publication (`preparedTarget`, `preparedRows`, `preparedState`). No
check and no predicate query is asked for it, and nothing is chosen.

An admitted firing pins its execution in the one published-execution record,
`ContextualConditionalExecution.Published` (`NativeFiring.pinned`): the firing's own rule, selection,
outputs, publication flags and budget, its admission, and that same solver return. The record pins
the authored rule, selection, output expressions and reuse contract; it has no row decoder. The
published rows come from the structured recipes (`ContextualConditionalPublication.Recipe`): a
produced port with a recipe publishes the actual emitted output through it, and every other row is
the execution's own (`publishRows`). **The step's result is the published state** of the pinned
execution (`native_result_pinned`, `native_settle_pinned`), and of every record with the firing's
data and budget (`publishedState`, `native_published`): the solver return is computed from the data
(`firing_eq_of_data`).

* **The raw statement, under its honest name.** Without recipes the published state is the raw
  target (`publishedState_none`), so the step's result is the raw target (`native_raw_target`).
* **Publication changes rows only** (`publishedState_declarations`, `_equations`, `_present`), and
  the published state is the raw target exactly when every recipe republishes its port's raw row
  (`publishedState_eq_rawTarget_iff`).
* **They differ in general.** A conditional template keeps an unmatched dormant schema where the raw
  target holds a matchable shared row (`ContextualConditionalTemplateControls.PublicationBoundary`);
  `Step/NativePublicationControls` carries that disagreement to this step, for direct templates.
* **Open:** mixed native bodies publish through producer recipes into a packed private family
  (`NativePublication`); they are not yet a recipe instance of this step.

The native definitions are used unchanged; this module only states them as an instance.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (fire)
open ContextualPredicateQueryAdmission (WithQueries DataQuery nativeLabels)

section CandidateStep

open Interface (Frames)
open Interface.Frames (Frame)

variable (S : Signature) (O : Type) [DecidableEq O] (Γ : Ctx S) (sort : S.Srt)

/-- A native state: its private row family and the conditional-execution state over it. -/
structure NativeState : Type 1 where
  Local : Type
  localEquality : DecidableEq Local
  locals : Local → MetaArity S
  state : ContextualConditionalExecution.State locals O Γ sort

instance NativeState.decidableLocal (s : NativeState S O Γ sort) : DecidableEq s.Local :=
  s.localEquality

variable {S O Γ sort} in
/-- The frame of a firing's information at a state: the opened rule locals beside its declarations. -/
def NativeState.infoFrame (s : NativeState S O Γ sort) : Frame S :=
  ⟨_, ContextualActivatedStep.target s.locals s.state.declarations⟩

variable {S O Γ sort}

/-- Publication recipes at a state, fixed before execution: for a produced port, the private and
captured roles of its emitted output's names and its local conditions. -/
abbrev Recipes (s : NativeState S O Γ sort) :=
  O → Option (ContextualConditionalPublication.Recipe s.locals
    (ContextualActivatedStep.target s.locals s.state.declarations))

variable [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]

section Publication

variable {s : NativeState S O Γ sort}

/-- **The rows an execution publishes through its recipes**: a port with a recipe publishes the actual
emitted output through it; every other row is the execution's own. -/
def publishRows (recipes : Recipes s) (firing : ContextualConditionalExecution.Firing s.locals s.state)
    (occurrence : O) :
    ContextualConditionalRows.Row (ContextualPublication.privateFamily s.locals firing.update.declaration)
      firing.target.declarations Γ sort :=
  match recipes occurrence with
  | some recipe => ContextualConditionalPublication.extendPrivate s.locals firing.update.declaration _
      (recipe.publish (ContextualComputedFreshFrame.includeSource firing.update) (firing.outputs occurrence))
  | none => firing.target.rows occurrence

/-- **The published state** of an execution: its frame, information and occurrences, with the rows
published through the recipes. -/
def publishedState (recipes : Recipes s) (firing : ContextualConditionalExecution.Firing s.locals s.state) :
    NativeState S O Γ sort :=
  ⟨s.Local ⊕ firing.update.Variables, by letI := firing.update.equality; exact inferInstance,
    ContextualPublication.privateFamily s.locals firing.update.declaration,
    firing.target.withRows _ (publishRows recipes firing)⟩

/-- The raw target of an execution, as a native state. -/
def rawTarget (firing : ContextualConditionalExecution.Firing s.locals s.state) : NativeState S O Γ sort :=
  ⟨s.Local ⊕ firing.update.Variables, by letI := firing.update.equality; exact inferInstance,
    ContextualPublication.privateFamily s.locals firing.update.declaration, firing.target⟩

theorem publishedState_declarations (recipes : Recipes s)
    (firing : ContextualConditionalExecution.Firing s.locals s.state) :
    (publishedState recipes firing).state.declarations = firing.target.declarations := rfl

theorem publishedState_equations (recipes : Recipes s)
    (firing : ContextualConditionalExecution.Firing s.locals s.state) :
    (publishedState recipes firing).state.equations = firing.target.equations := rfl

theorem publishedState_present (recipes : Recipes s)
    (firing : ContextualConditionalExecution.Firing s.locals s.state) :
    (publishedState recipes firing).state.present = firing.target.present := rfl

/-- **Without recipes, the published state is the raw target.** -/
theorem publishedState_none (firing : ContextualConditionalExecution.Firing s.locals s.state) :
    publishedState (fun _ => none) firing = rawTarget firing :=
  rfl

/-- **The published state is the raw target exactly when every recipe republishes its port's raw
row.** -/
theorem publishedState_eq_rawTarget_iff (recipes : Recipes s)
    (firing : ContextualConditionalExecution.Firing s.locals s.state) :
    publishedState recipes firing = rawTarget firing ↔ publishRows recipes firing = firing.target.rows := by
  constructor
  · intro same
    have rowsHEq : HEq (publishedState recipes firing).state.rows (rawTarget firing).state.rows := by
      rw [same]
    exact eq_of_heq rowsHEq
  · intro same
    show (⟨_, _, _, firing.target.withRows _ (publishRows recipes firing)⟩ : NativeState S O Γ sort) =
      ⟨_, _, _, firing.target.withRows _ firing.target.rows⟩
    rw [same]

end Publication

/-- The data of a native firing, without its admission and its solver return, with its publication
recipes. -/
structure NativeFiring (s : NativeState S O Γ sort) : Type 1 where
  rule : RuleInstance (Term (signature S (ContextualActivatedStep.source s.locals s.state.declarations)) Γ sort)
  selection : Selection O
  outputs : O → Term (signature S (ContextualActivatedStep.target s.locals s.state.declarations)) Γ sort
  reusable : O → Bool
  queries : List (DataQuery (ContextualActivatedStep.target s.locals s.state.declarations)
    (O × ContextualConditionalRows.Row s.locals (ContextualActivatedStep.target s.locals s.state.declarations) Γ sort) O)
  fuel : Nat
  /-- How produced ports are published, fixed before execution. -/
  recipes : Recipes s
  /-- Recipes outside the produced ports are absent. -/
  recipes_made : ∀ occurrence, occurrence ∉ selection.made → recipes occurrence = none

namespace NativeFiring

variable {s : NativeState S O Γ sort} (f : NativeFiring s)

def information : ContextualResidual.Problem (ContextualActivatedStep.target s.locals s.state.declarations) :=
  ContextualConditionalExecution.information s.locals s.state.declarations s.state.occupied f.selection f.rule
    s.state.rows s.state.equations

/-- The rule and port views prepared at the state. -/
def prepared :=
  ContextualActivatedStep.prepared s.locals s.state.declarations s.state.occupied f.selection f.rule
    (fun occurrence => (s.state.rows occurrence).value)

/-- A native firing with these data exists. -/
def Realized : Prop :=
  ∃ native : WithQueries s.locals s.state, native.firing.rule = f.rule ∧
    native.firing.selection = f.selection ∧ native.firing.outputs = f.outputs ∧
    native.firing.reusable = f.reusable ∧ native.firing.fuel = f.fuel ∧ native.queries = f.queries

/-- The data of a native firing, with recipes. -/
def ofNative (native : WithQueries s.locals s.state) (recipes : Recipes s)
    (made : ∀ occurrence, occurrence ∉ native.firing.selection.made → recipes occurrence = none) :
    NativeFiring s :=
  ⟨native.firing.rule, native.firing.selection, native.firing.outputs, native.firing.reusable,
    native.queries, native.firing.fuel, recipes, made⟩

theorem realized_ofNative (native : WithQueries s.locals s.state) (recipes : Recipes s)
    (made : ∀ occurrence, occurrence ∉ native.firing.selection.made → recipes occurrence = none) :
    (ofNative native recipes made).Realized :=
  ⟨native, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **The admission record of a realized firing**, for its own data. -/
theorem admitted_of_realized {f : NativeFiring s} (realized : f.Realized) :
    ContextualConditionalExecution.Admitted s.locals s.state f.rule f.selection f.outputs := by
  obtain ⟨native, rule, selection, outputs, -, -, -⟩ := realized
  rw [← rule, ← selection, ← outputs]
  exact native.firing.admitted

/-- **A realized firing has solvable information.** -/
theorem solvable_of_realized {f : NativeFiring s} (realized : f.Realized) :
    (Frames.contextual S).Solvable (a := s.infoFrame) f.information :=
  (Frames.contextual_solvable_iff _).mpr (admitted_of_realized realized).solvable

end NativeFiring

/-- **A native preparation**: the solver's residual return on the firing's information, at its
budget. -/
def NativePrep {s : NativeState S O Γ sort} (f : NativeFiring s) : Type 1 :=
  { update : ContextualFrameUpdate.Update f.information //
    letI := s.state.equality
    ContextualFrameWorklist.run f.fuel (ContextualActivatedStep.target s.locals s.state.declarations)
      f.information = .residual update }

/-- **The native preparation of a firing with solvable information**: the solver does not refute
solvable information, so it returns a residual. -/
def nativePrepare {s : NativeState S O Γ sort} (f : NativeFiring s)
    (solvable : (Frames.contextual S).Solvable (a := s.infoFrame) f.information) : NativePrep f :=
  letI := s.state.equality
  match computed : ContextualFrameWorklist.run f.fuel
      (ContextualActivatedStep.target s.locals s.state.declarations) f.information with
  | .residual update => ⟨update, computed⟩
  | .refuted impossible => False.elim (by
      obtain ⟨_, future, candidate, model⟩ := (Frames.contextual_solvable_iff _).mp solvable
      exact impossible future candidate model)

/-- **The state a prepared native firing reaches**: the formula of
`ContextualConditionalExecution.Firing.target`, read from the firing's data and its preparation. -/
abbrev preparedTarget {s : NativeState S O Γ sort} (f : NativeFiring s) (p : NativePrep f) :
    ContextualConditionalExecution.State (ContextualPublication.privateFamily s.locals p.1.declaration)
      O Γ sort where
  Names := (Mettapedia.Logic.LP.ScopedVar s.Local ⊕ s.state.Names) ⊕ (p.1.Variables ⊕ Empty)
  equality := by let _ := s.state.equality; let _ := p.1.equality; infer_instance
  declarations := ContextualComputedFreshFrame.active
    (ContextualActivatedStep.target s.locals s.state.declarations) p.1.declaration
  occupied := ContextualFreshFrameScopeLedger.helperLedger
    (ContextualActivationScopes.after s.state.occupied f.selection)
  equations := ContextualResidual.mapProblem (ContextualComputedFreshFrame.includeSource p.1)
    (ContextualConditionalExecution.information s.locals s.state.declarations s.state.occupied
      f.selection f.rule s.state.rows s.state.equations)
  present := fire s.state.present (f.selection.commit (T := Unit))
  rows occurrence :=
    if occurrence ∈ f.selection.made then
      if f.reusable occurrence then
        ContextualConditionalPublication.ordinary s.locals p.1.declaration _
          (ContextualConditionalAnswers.ofUpdate p.1 (f.outputs occurrence))
      else ContextualConditionalRows.ofStored _ _ (.shared (instantiate
        (ContextualComputedFreshFrame.includeSource p.1) (f.outputs occurrence)))
    else ContextualConditionalPublication.extendPrivate s.locals p.1.declaration _
      ((s.state.rows occurrence).map s.locals s.state.declarations
        (Assignment.compose (ContextualComputedFreshFrame.includeSource p.1)
          (ContextualSelectionViews.capturedTarget s.locals s.state.declarations)))

/-- **The rows a prepared native firing publishes**: the formula of `publishRows`. -/
def preparedRows {s : NativeState S O Γ sort} (f : NativeFiring s) (p : NativePrep f) (occurrence : O) :
    ContextualConditionalRows.Row (ContextualPublication.privateFamily s.locals p.1.declaration)
      (preparedTarget f p).declarations Γ sort :=
  match f.recipes occurrence with
  | some recipe => ContextualConditionalPublication.extendPrivate s.locals p.1.declaration _
      (recipe.publish (ContextualComputedFreshFrame.includeSource p.1) (f.outputs occurrence))
  | none => (preparedTarget f p).rows occurrence

/-- **The published state of a prepared native firing**: the formula of `publishedState`. -/
def preparedState {s : NativeState S O Γ sort} (f : NativeFiring s) (p : NativePrep f) :
    NativeState S O Γ sort :=
  ⟨s.Local ⊕ p.1.Variables, by letI := p.1.equality; exact inferInstance,
    ContextualPublication.privateFamily s.locals p.1.declaration,
    (preparedTarget f p).withRows _ (preparedRows f p)⟩

namespace NativeFiring

variable {s : NativeState S O Γ sort} (f : NativeFiring s)

/-- **The pinned execution of an admitted native firing**, in the one published-execution record:
the firing's own data and admission, and the solver's return on its information. -/
def pinned (realized : f.Realized) :
    ContextualConditionalExecution.Published s.locals s.state f.rule f.selection f.outputs (.all f.reusable) :=
  ⟨⟨f.rule, f.selection, f.outputs, f.reusable, admitted_of_realized realized, f.fuel,
      (nativePrepare f (solvable_of_realized realized)).1, (nativePrepare f (solvable_of_realized realized)).2⟩,
    rfl, rfl, rfl, rfl⟩

theorem pinned_fuel (realized : f.Realized) : (f.pinned realized).firing.fuel = f.fuel :=
  rfl

end NativeFiring

/-- **Native firings with the same data are equal**: the solver return is computed from the data. -/
theorem firing_eq_of_data {s : NativeState S O Γ sort}
    (first second : ContextualConditionalExecution.Firing s.locals s.state)
    (rule : first.rule = second.rule) (selection : first.selection = second.selection)
    (outputs : first.outputs = second.outputs) (reusable : first.reusable = second.reusable)
    (fuel : first.fuel = second.fuel) : first = second := by
  obtain ⟨rule₁, selection₁, outputs₁, reusable₁, admitted₁, fuel₁, update₁, computed₁⟩ := first
  obtain ⟨rule₂, selection₂, outputs₂, reusable₂, admitted₂, fuel₂, update₂, computed₂⟩ := second
  dsimp only at rule selection outputs reusable fuel
  subst rule selection outputs reusable fuel
  have same := computed₁.symm.trans computed₂
  cases same
  rfl

/-- **The native step**: native firings as firings of the candidate step. Its result is computed from
the firing's data and the solver's return on its information, before any check or predicate query
is asked; it is the published state of the pinned execution (`native_result_pinned`). -/
def native :
    Interface.Step.Standard (Frames.contextual S) O (NativeState S O Γ sort) NativeFiring where
  frame s := ⟨s.state.Names, s.state.declarations⟩
  knowledge s := s.state.equations
  present s := s.state.present
  selection f := f.selection
  target {s} _ := s.infoFrame
  extension {s} _ := ContextualSelectionViews.capturedTarget s.locals s.state.declarations
  information f := f.information
  transported := by
    intro s f e member
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr ⟨e, member, rfl⟩))
  Shapes f := f.selection.taken.Nodup ∧ f.selection.made.Nodup ∧
    f.rule.take.length = f.selection.taken.length ∧ f.rule.read.length = f.selection.read.length ∧
    f.selection.made.map f.outputs = f.prepared.rule.produce
  Holds {s} f b σ := (∀ check ∈ f.prepared.rule.checks,
      ContextualConditionalGuards.Holds s.locals σ
        (ContextualConditionalExecution.guardRows s.locals s.state.declarations s.state.rows)
        s.state.present check) ∧
    ∀ query ∈ f.queries,
      (query.atSolution ⟨b.Names, b.arity, σ⟩).Holds (nativeLabels s.locals s.state) s.state.present
  Admits f := f.Realized
  admits_iff := by
    intro s f
    constructor
    · rintro ⟨native, rule, selection, outputs, reusable, fuel, queries⟩
      obtain ⟨rule₀, selection₀, outputs₀, reusable₀, queries₀, fuel₀, recipes₀, made₀⟩ := f
      dsimp only at rule selection outputs reusable fuel queries
      subst rule selection outputs reusable fuel queries
      have admitted := native.firing.admitted
      refine ⟨⟨admitted.take_distinct, admitted.output_distinct, admitted.take_length,
          admitted.read_length, admitted.outputs⟩,
        ⟨admitted.taken_present, admitted.read_present, admitted.apart, admitted.fresh, ?_⟩,
        (Frames.contextual_solvable_iff _).mpr admitted.solvable, ?_⟩
      · intro query member
        simp [Selection.commit] at member
      · intro b σ solved
        exact ⟨fun check member => admitted.checks check member b.Names b.arity σ solved,
          fun query member => native.observations query member b.Names b.arity σ solved⟩
    · rintro ⟨⟨takeDistinct, outputDistinct, takeLength, readLength, outputs⟩, enabled, solvable, asks⟩
      have admitted : ContextualConditionalExecution.Admitted s.locals s.state f.rule f.selection f.outputs :=
        { take_distinct := takeDistinct
          output_distinct := outputDistinct
          take_length := takeLength
          read_length := readLength
          outputs := outputs
          taken_present := enabled.taken_subset
          read_present := enabled.kept_subset
          apart := enabled.apart
          fresh := enabled.fresh
          solvable := (Frames.contextual_solvable_iff _).mp solvable
          checks := fun check member Future future candidate model =>
            (asks ⟨Future, future⟩ candidate model).1 check member }
      obtain ⟨firing, rule, selection, outputs, reusable, fuel⟩ :=
        ContextualConditionalExecution.realize_at_fuel s.locals s.state f.rule f.selection f.outputs
          f.reusable admitted f.fuel
      refine ⟨⟨firing, f.queries, ?_⟩, rule, selection, outputs, reusable, fuel, rfl⟩
      intro query member Future future candidate model
      rw [selection, rule] at model
      exact (asks ⟨Future, future⟩ candidate model).2 query member
  preparedResult f p := preparedState f (nativePrepare f p.2.2)
  present_preparedResult _ _ := rfl
  preparedSettle f p := ContextualComputedFreshFrame.includeSource (nativePrepare f p.2.2).1
  knowledge_preparedResult _ _ := rfl

/-- **The result is the published state of the pinned execution.** -/
theorem native_result_pinned {s : NativeState S O Γ sort} (f : NativeFiring s) (realized : f.Realized) :
    native.result f realized = publishedState f.recipes (f.pinned realized).firing :=
  rfl

/-- **The settlement is the inclusion of the pinned execution's information frame.** -/
theorem native_settle_pinned {s : NativeState S O Γ sort} (f : NativeFiring s) (realized : f.Realized) :
    native.settle f realized = ContextualComputedFreshFrame.includeSource (f.pinned realized).firing.update :=
  rfl

/-- **Admission of native firings is the interface's admission.** -/
theorem native_admits_iff {s : NativeState S O Γ sort} (f : NativeFiring s) :
    f.Realized ↔ (native (S := S) (O := O) (Γ := Γ) (sort := sort)).Shapes f ∧
      Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Enabled (fun _ : O => ())
        s.state.present (f.selection.commit (T := Unit)) ∧
      (Frames.contextual S).Solvable (a := s.infoFrame) f.information ∧
      (Frames.contextual S).Entails (a := s.infoFrame) f.information (native.Holds f) :=
  native.admits_iff f

/-- **The step's result is the published state** of every record that pins an execution with the
firing's data and budget. -/
theorem native_published {s : NativeState S O Γ sort} (f : NativeFiring s) (realized : f.Realized)
    (record : ContextualConditionalExecution.Published s.locals s.state f.rule f.selection f.outputs
      (.all f.reusable)) (budget : record.firing.fuel = f.fuel) :
    native.result f realized = publishedState f.recipes record.firing := by
  have reusableOne : (f.pinned realized).firing.reusable = f.reusable := (f.pinned realized).intents
  have reusableTwo : record.firing.reusable = f.reusable := record.intents
  have same : (f.pinned realized).firing = record.firing :=
    firing_eq_of_data _ _ ((f.pinned realized).authored.trans record.authored.symm)
      ((f.pinned realized).selected.trans record.selected.symm)
      ((f.pinned realized).values.trans record.values.symm)
      (reusableOne.trans reusableTwo.symm)
      ((f.pinned_fuel realized).trans budget.symm)
  change publishedState f.recipes (f.pinned realized).firing = _
  rw [same]

/-- The record of a native firing's own execution. -/
def recordOf {s : NativeState S O Γ sort} (native : WithQueries s.locals s.state) :
    ContextualConditionalExecution.Published s.locals s.state native.firing.rule native.firing.selection
      native.firing.outputs (.all native.firing.reusable) :=
  ⟨native.firing, rfl, rfl, rfl, rfl⟩

/-- **The step's result for given recipes** of a native firing's own execution. -/
theorem native_publishes {s : NativeState S O Γ sort} (firing : WithQueries s.locals s.state)
    (recipes : Recipes s)
    (made : ∀ occurrence, occurrence ∉ firing.firing.selection.made → recipes occurrence = none) :
    native.result (NativeFiring.ofNative firing recipes made) (NativeFiring.realized_ofNative firing recipes made) =
      publishedState recipes firing.firing :=
  native_published (NativeFiring.ofNative firing recipes made) (NativeFiring.realized_ofNative firing recipes made)
    (recordOf firing) rfl

/-- **The raw statement, under its honest name**: without recipes, the step's result is the native
firing's raw target. -/
theorem native_raw_target {s : NativeState S O Γ sort} (firing : WithQueries s.locals s.state) :
    native.result (NativeFiring.ofNative firing (fun _ => none) (fun _ _ => rfl))
        (NativeFiring.realized_ofNative firing (fun _ => none) (fun _ _ => rfl)) =
      rawTarget firing.firing :=
  (native_publishes firing (fun _ => none) (fun _ _ => rfl)).trans (publishedState_none firing.firing)

end CandidateStep

#print axioms NativeFiring.realized_ofNative
#print axioms NativeFiring.admitted_of_realized
#print axioms NativeFiring.solvable_of_realized
#print axioms nativePrepare
#print axioms NativeFiring.pinned_fuel
#print axioms native_result_pinned
#print axioms native_settle_pinned
#print axioms firing_eq_of_data
#print axioms native_admits_iff
#print axioms native_published
#print axioms native_publishes
#print axioms native_raw_target
#print axioms publishedState_eq_rawTarget_iff

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
