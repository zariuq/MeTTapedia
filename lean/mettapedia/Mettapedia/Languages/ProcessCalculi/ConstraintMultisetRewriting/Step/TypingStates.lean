import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentHelpers
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveSubjectReduction

/-!
# State typing at dependent frames

A **typed configuration** labels each occurrence by a term over the state's frame and gives every
present occurrence a judged entry (`Dependent.Entry`) whose term is its label (`Typed`). This is a
generative invariant of the state, not a condition on single firings.

## Helper firings preserve state typing

A helper firing extends the frame by a variable of a formed type. Labels are carried along it
(`carry`): the old ones weakened by the projection, the new occurrence labelled by the new variable.
Typed configurations stay typed (`helper_preserves`), and so along every run of the helper step
(`carryRun`, `run_preserves`).

## Computation firings carry the rule-level certificate

A **computation firing** (`computeStep`) takes one occurrence and makes another whose label is one
computation step of the taken label, under the frame's knowledge and guards. It changes neither the
frame nor the knowledge.

* `compute_preserves_of`: if computation steps preserve judgments, computation firings preserve
  state typing.
* `compute_preserves`: in particular, given the rule-level certificates of subject reduction
  (`RootPreservation` for the declared root rules, with universe regularity, the head and the Π and Σ
  conversion boundaries).
Concrete certified-program instances consume these generic contracts in their
respective language adapters.

## Controls

* `Controls.helper_typed`: the helper firing `x : g → g := λx.x` of `DependentHelpers.Consumer`,
  from the empty configuration, gives a typed configuration whose occurrence is labelled `x`.
* `Controls.universe_untyped`, `Controls.untyped_configuration`: the universe head has no type in
  that package, so a configuration labelling an occurrence by it is not typed. Typing is not a
  property of every labelling.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.TypingStates

open _root_.CategoryTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.FormationSensitive
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.FormationSensitiveContextual
open MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)
open Interface.Dependent (Entry frames State Firing helperStep)

variable {Head : Type} {rules : Rules Head} {O : Type}

/-- **A typed configuration**: every present occurrence has a judged entry at the frame whose term
is its label. -/
def Typed (Γ : Context rules) (present : Finset O) (label : O → Tm Head Γ.arity) : Prop :=
  ∀ o ∈ present, ∃ e : Entry Γ, e.term.code = label o

/-! ## Helper firings -/

variable [DecidableEq O]

/-- Labels carried along a helper firing: old labels weakened by the projection, the new
occurrence labelled by the new variable. -/
def carry {s : State rules O} (f : Firing s) (label : O → Tm Head s.frame.arity) :
    O → Tm Head (extend s.frame f.helper).arity :=
  fun o => if o = f.made then .var 0 else subst (projectionHom s.frame f.helper).substitution (label o)

/-- **Helper firings preserve state typing.** -/
theorem helper_preserves {s : State rules O} (f : Firing s)
    {label : O → Tm Head s.frame.arity} (typed : Typed s.frame s.present label) :
    Typed f.after.frame f.after.present (carry f label) := by
  intro o present
  have cases : (o ∈ s.present ∧ o ∉ (f.selection.commit (T := Unit)).taken) ∨
      o ∈ (f.selection.commit (T := Unit)).made := mem_fire.mp present
  by_cases made : o = f.made
  · exact ⟨Entry.last s.frame f.helper, by rw [carry, if_pos made]; rfl⟩
  · have old : o ∈ s.present := by
      rcases cases with ⟨old, _⟩ | new
      · exact old
      · exact absurd (by simpa [Firing.selection, Selection.commit] using new) made
    obtain ⟨e, code⟩ := typed o old
    exact ⟨e.reindex (projectionHom s.frame f.helper), by rw [carry, if_neg made, ← code]; rfl⟩

/-- Labels carried along a run of the helper step. -/
def carryRun : {s : State rules O} → (r : (helperStep (rules := rules) (O := O)).Run s) →
    (O → Tm Head s.frame.arity) → O → Tm Head r.last.frame.arity
  | _, .nil _, label => label
  | _, .cons f _ rest, label => carryRun rest (carry f label)

/-- **State typing is an invariant of the helper step.** -/
theorem run_preserves : ∀ {s : State rules O} (r : (helperStep (rules := rules) (O := O)).Run s)
    {label : O → Tm Head s.frame.arity}, Typed s.frame s.present label →
      Typed r.last.frame r.last.present (carryRun r label)
  | _, .nil _, _, typed => typed
  | _, .cons f _ rest, _, typed => run_preserves rest (helper_preserves f typed)

/-! ## Computation firings -/

variable (rules O) in
/-- A state whose occurrences carry labels over its frame. -/
structure LState where
  frame : Context rules
  knowledge : EquationStore (Entry frame)
  present : Finset O
  label : O → Tm Head frame.arity

/-- One computation step of a raw term, in a rule package. -/
abbrev Reduces (rules : Rules Head) {n : Nat} (source target : Tm Head n) : Prop :=
  Presentation.Step rules.headEq source target rules.computation

/-- **A computation firing**: it takes an occurrence and makes another, labelled by one computation
step of the taken label; its guards are equations asked at every solution. -/
structure Compute (s : LState rules O) where
  taken : O
  made : O
  target : Tm Head s.frame.arity
  reduces : Reduces rules (s.label taken) target
  guards : EquationStore (Entry s.frame)

/-- What a computation firing takes and makes. -/
def Compute.selection {s : LState rules O} (f : Compute s) : Selection O := ⟨[f.taken], [], [f.made]⟩

/-- The state after a computation firing: same frame and knowledge, the made occurrence labelled by
the target. -/
def Compute.after {s : LState rules O} (f : Compute s) : LState rules O :=
  ⟨s.frame, s.knowledge, fire s.present (f.selection.commit (T := Unit)),
    fun o => if o = f.made then f.target else s.label o⟩

/-- **The computation step at dependent frames.** -/
def computeStep : Interface.Step.Standard (frames rules) O (LState rules O) Compute where
  frame s := s.frame
  knowledge s := s.knowledge
  present s := s.present
  selection f := f.selection
  target {s} _ := s.frame
  extension {s} _ := 𝟙 s.frame
  information {s} _ := s.knowledge
  transported := by
    intro s _ e member
    show (e.1.reindex (𝟙 s.frame), e.2.reindex (𝟙 s.frame)) ∈ s.knowledge
    rw [Entry.reindex_id, Entry.reindex_id]
    exact member
  Shapes f := f.selection.made.Nodup
  Holds {s} f _ σ := (frames rules).Models (a := s.frame) σ f.guards
  Admits {s} f := f.selection.made.Nodup ∧
    Enabled (fun _ : O => ()) s.present (f.selection.commit (T := Unit)) ∧
    (frames rules).Solvable s.knowledge ∧
    (frames rules).Entails s.knowledge fun _ σ => (frames rules).Models (a := s.frame) σ f.guards
  admits_iff _ := Iff.rfl
  preparedResult f _ := f.after
  present_preparedResult _ _ := rfl
  preparedSettle {s} _ _ := 𝟙 s.frame
  knowledge_preparedResult {s} _ _ := (Interface.Frames.applyStore_id (X := frames rules) s.knowledge).symm

/-- **Computation firings preserve state typing whenever computation steps preserve judgments.** -/
theorem compute_preserves_of
    (preserve : ∀ {n : Nat} {Γ : Ctx Head n} {source target type : Tm Head n},
      Judgment rules Γ source type → Reduces rules source target → Judgment rules Γ target type)
    {s : LState rules O} (f : Compute s) (admitted : (computeStep (rules := rules) (O := O)).Admits f)
    (typed : Typed s.frame s.present s.label) :
    Typed f.after.frame f.after.present f.after.label := by
  intro o present
  have cases : (o ∈ s.present ∧ o ∉ (f.selection.commit (T := Unit)).taken) ∨
      o ∈ (f.selection.commit (T := Unit)).made := mem_fire.mp present
  by_cases made : o = f.made
  · have takenPresent : f.taken ∈ s.present :=
      admitted.2.1.taken_subset (by simp [Compute.selection, Selection.commit])
    obtain ⟨e, code⟩ := typed f.taken takenPresent
    have judged : Judgment rules s.frame.raw (s.label f.taken) e.type.code := code ▸ e.term.judgment
    have stepped := preserve judged f.reduces
    exact ⟨⟨e.type, ⟨f.target, stepped.typing⟩⟩, by simp [Compute.after, made]⟩
  · have old : o ∈ s.present := by
      rcases cases with ⟨old, _⟩ | new
      · exact old
      · exact absurd (by simpa [Compute.selection, Selection.commit] using new) made
    obtain ⟨e, code⟩ := typed o old
    exact ⟨e, by simp [Compute.after, made, code]⟩

/-- **Computation firings preserve state typing under the rule-level certificates of subject
reduction.** -/
theorem compute_preserves (universes : UniverseRegularity rules)
    (piBoundary : PiConversionBoundary rules) (sigmaBoundary : SigmaConversionBoundary rules)
    (heads : HeadPreservation rules) (roots : RootPreservation rules)
    {s : LState rules O} (f : Compute s) (admitted : (computeStep (rules := rules) (O := O)).Admits f)
    (typed : Typed s.frame s.present s.label) :
    Typed f.after.frame f.after.present f.after.label :=
  compute_preserves_of (fun judgment step =>
    judgment.step_preserves universes piBoundary sigmaBoundary heads roots step) f admitted typed

/-! ## Controls -/

namespace Controls

open Interface.Dependent.Consumer

/-- **The helper firing `x : g → g := λx.x` gives a typed configuration**, with its occurrence
labelled by `x`. -/
theorem helper_typed :
    Typed first.after.frame first.after.present (carry first (fun _ => Tm.head TinyHead.ground)) ∧
      carry first (fun _ => Tm.head TinyHead.ground) 1 = .var 0 :=
  ⟨helper_preserves first (fun o present => by cases present), by simp [carry, first]⟩

/-- The universe head has no type in the two-head package. -/
theorem universe_untyped : ∀ {n : Nat} {Γ : Ctx TinyHead n} {t A : Tm TinyHead n},
    FormationSensitive.Typing tiny Γ t A → t = .head .universe → False := by
  intro n Γ t A typed
  induction typed with
  | headType declared =>
      intro same
      cases same
      exact absurd declared.1 (by decide)
  | cumul _ _ ih => exact ih
  | conv _ _ _ _ ih _ => exact ih
  | _ => intro same; cases same

/-- **A configuration labelling an occurrence by the universe head is not typed.** -/
theorem untyped_configuration :
    ¬ Typed (empty tiny) ({0} : Finset Nat) (fun _ => Tm.head TinyHead.universe) := by
  intro typed
  obtain ⟨e, code⟩ := typed 0 (Finset.mem_singleton_self 0)
  exact universe_untyped e.term.typed code

end Controls

#print axioms helper_preserves
#print axioms run_preserves
#print axioms computeStep
#print axioms compute_preserves_of
#print axioms compute_preserves
#print axioms Controls.helper_typed
#print axioms Controls.universe_untyped
#print axioms Controls.untyped_configuration

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.TypingStates
