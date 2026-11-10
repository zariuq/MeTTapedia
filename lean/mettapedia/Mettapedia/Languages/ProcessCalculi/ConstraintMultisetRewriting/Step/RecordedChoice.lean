import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.SettlementCoverage
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.EventAccountObserver

/-!
# Recorded choice: the branch a committing firing takes, in the firing's type

A step that commits to one answer is a step like any other: it is sound
(`SettlementCoverage.Controls.committing_sound_not_covering`), and nothing requires it to declare
what it chose. When a caller wants the branch recorded, for provenance, replay or counterfactuals,
`Choices` puts the choice into the firing, so every run records it. It is an optional instrument.

## Recorded choices (`Choices`, `Choices.step`)

Choices over a step `P` give, for every firing of `P`, a type of choices; for each choice of a
prepared firing, the state it commits to and the **chosen answer**, a solution of the knowledge of
`P`'s prepared result (`chosen`, `chosen_answer`): what a firing commits is part of its effect. The
committed knowledge is the information read along `P`'s prepared settlement followed by the chosen
answer (`knowledge_result`).

* **The choice is visible in the type** (`Choices.step`): the firings of the recording step are
  pairs of a firing of `P` and a choice; admission is the firing's own (`step_admits_iff`).
* **An admitted-event observer records it** (`observer`, `record`, `record_eq_word`, `record_append`):
  the record is the word of successful firings with their choices, and records compose along runs.
* **Committed answers are answers of `P`** (`sound`).

## The recorded branches of an exhaustive step form a covering family

Choices are **exhaustive** when every answer of `P`'s result is chosen, after a faithful extension
of its frame (`Exhaustive`). The choices of a firing of an answer-covering step then form a
**covering family** of its information (`Choices.family`): each recorded choice is one branch of it.

## The control (`Controls`)

Over Boolean observations of two-bit worlds: choosing any answer of the quiet firing (`chooseAny`)
is exhaustive, so its choices cover (`chooseAny_family`). `SettlementCoverage.Controls.chooseFalse`
is its branch `allFalse`, committed without recording the choice (`chooseFalse_is_branch`): one
branch is a committing step and does not cover, while all the recorded branches together do
(`one_branch_versus_family`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RecordedChoice

open Interface (Frames)
open SettlementCoverage (Faithful CoversAnswers CoveringFamily faithful_id)
open MeTTaCalculus.OccurrenceCommits (Enabled fire)

universe uO uT uH uOcc uS uF uC

section Choices

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O] {State : Type uS} {Firing : State → Type uF}
  (P : Interface.Step X O State Firing)

/-- **Recorded choices over a step**: for every firing, a type of choices; on a prepared firing each
choice commits to a state and a chosen answer of the prepared result of `P`, so what a firing commits
is part of its effect. An optional instrument: a step that commits need not record its choice. -/
structure Choices where
  Choice : {s : State} → Firing s → Type uC
  /-- The state a choice commits to. -/
  result : {s : State} → (f : Firing s) → P.Prepares f → Choice f → State
  present_result : ∀ {s : State} (f : Firing s) (p : P.Prepares f) (c : Choice f),
    P.present (result f p c) = fire (P.present s) ((P.selection f).commit (T := Unit))
  /-- **The chosen answer** of the prepared result of `P`. -/
  chosen : {s : State} → (f : Firing s) → (p : P.Prepares f) → (c : Choice f) →
    Hom (P.frame (P.preparedResult f p)) (P.frame (result f p c))
  chosen_answer : ∀ {s : State} (f : Firing s) (p : P.Prepares f) (c : Choice f),
    X.Models (chosen f p c) (P.knowledge (P.preparedResult f p))
  /-- The committed knowledge: the information read along the settlement, then the chosen answer. -/
  knowledge_result : ∀ {s : State} (f : Firing s) (p : P.Prepares f) (c : Choice f),
    P.knowledge (result f p c) =
      X.applyStore (X.comp (chosen f p c) (P.preparedSettle f p)) (P.information f)

variable {P}

namespace Choices

variable (D : Choices.{uO, uT, uH, uOcc, uS, uF, uC} P)

/-- **The choice-indexed step**: a candidate carries an operational outcome.
This data does not assert successful admission; `record` observes admitted runs.
The choice type may be empty. -/
def step : Interface.Step X O State (fun s => Σ f : Firing s, D.Choice f) where
  frame := P.frame
  knowledge := P.knowledge
  present := P.present
  selection f := P.selection f.1
  target f := P.target f.1
  extension f := P.extension f.1
  information f := P.information f.1
  information_refines f := P.information_refines f.1
  Shapes f := P.Shapes f.1
  Admits f := P.Admits f.1
  admitted_prepares _ admitted := P.prepares admitted
  preparedResult f p := D.result f.1 p f.2
  present_preparedResult f p := D.present_result f.1 p f.2
  preparedSettle f p := X.comp (D.chosen f.1 p f.2) (P.preparedSettle f.1 p)
  result_refines f p := by
    intro b σ solved
    rw [D.knowledge_result] at solved
    exact (Frames.models_applyStore _ _ _).mp solved

instance step_guarded [P.Guarded] : D.step.Guarded where
  holds f := P.Holds f.1
  admission f := P.admits_iff_prepares f.1

instance step_literalInformation [P.LiteralInformation] : D.step.LiteralInformation :=
  ⟨fun f => P.transported f.1⟩

instance step_literalKnowledge : D.step.LiteralKnowledge :=
  ⟨fun f p => D.knowledge_result f.1 p f.2⟩

/-- **A recorded choice does not change admission.** -/
theorem step_admits_iff {s : State} (f : Firing s) (c : D.Choice f) : D.step.Admits ⟨f, c⟩ ↔ P.Admits f :=
  Iff.rfl

/-- Every later instantiation of a chosen answer still solves the prepared
result's knowledge. This uses the chosen-answer certificate, not exactness
of the base step or a second result-solvability assumption. -/
theorem sound {s : State} (f : Firing s) (admitted : P.Admits f) (c : D.Choice f) {b : Obj}
    (ρ : Hom (P.frame (D.result f (P.prepares admitted) c)) b) :
    X.Models (X.comp ρ (D.chosen f (P.prepares admitted) c)) (P.knowledge (P.result f admitted)) :=
  Frames.models_comp (D.chosen_answer f (P.prepares admitted) c) ρ

/-- Recording receives admitted events of the operational choice step. -/
def observer : Interface.EventObserver
    (Interface.EffectCore.EventObject D.step.effectCore D.step.eventAdmission) :=
  D.step.accountObserver (fun t x => FreeMonoid.of (⟨t, x⟩ : (t : State) × (Σ f : Firing t, D.Choice f)))

/-- **The record of a run** is evaluated by the admitted-event observer. -/
def record {s : State} (r : D.step.Run s) : FreeMonoid ((t : State) × (Σ f : Firing t, D.Choice f)) :=
  D.observer.evaluate (r.eventPath D.step)
    (1 : FreeMonoid ((t : State) × (Σ f : Firing t, D.Choice f)))

/-- The event-based recording agrees with the existing ordered account. -/
theorem record_eq_account {s : State} (r : D.step.Run s) :
    D.record r = r.account (fun t x => FreeMonoid.of ⟨t, x⟩) :=
  D.step.accountObserver_run_one _ r

/-- **Records compose along runs.** -/
theorem record_append {s : State} (r : D.step.Run s) (later : D.step.Run r.last) :
    D.record (r.append later) = D.record r * D.record later := by
  simp only [record_eq_account, Interface.Step.Run.account_append]

/-- **A run records its choices**: its record is its word. -/
theorem record_eq_word : ∀ {s : State} (r : D.step.Run s), D.record r = FreeMonoid.ofList r.word
  | _, r => by
      rw [record_eq_account]
      induction r with
      | nil => rfl
      | cons f admitted rest ih =>
          change FreeMonoid.of _ * rest.account _ = FreeMonoid.ofList (_ :: rest.word)
          rw [ih]
          rfl

/-- **Exhaustive choices**: every answer of `P`'s result is chosen, after a faithful extension of its
frame. -/
def Exhaustive : Prop :=
  ∀ {s : State} (f : Firing s) (admitted : P.Admits f) {b : Obj} (τ : Hom (P.frame (P.result f admitted)) b),
    X.Models τ (P.knowledge (P.result f admitted)) →
      ∃ (c : D.Choice f) (d : Obj) (j : Hom b d) (ρ : Hom (P.frame (D.result f (P.prepares admitted) c)) d),
        Faithful X j ∧ X.Models ρ (P.knowledge (D.result f (P.prepares admitted) c)) ∧
        ∀ t, X.E (X.act (X.comp j τ) t) (X.act (X.comp ρ (D.chosen f (P.prepares admitted) c)) t)

/-- **The recorded branches of an exhaustive step form a covering family**: the exhaustive choices
of a firing of an answer-covering step cover its information, each recorded choice one branch. -/
def family (covers : CoversAnswers P) (exhaustive : D.Exhaustive) {s : State} (f : Firing s)
    (admitted : P.Admits f) : CoveringFamily D.step s (P.information f) (D.Choice f) where
  firing c := ⟨f, c⟩
  admitted _ := admitted
  reads _ := X.id (P.target f)
  sound _ _ σ solved := (Frames.models_congr (fun t => Frames.act_comp_id σ t) _).mp solved
  covers σ solved := by
    obtain ⟨_, j₁, τ₁, faithful₁, solved₁, agree₁⟩ := covers f admitted σ solved
    obtain ⟨c, d, j₂, ρ, faithful₂, solved₂, agree₂⟩ := exhaustive f admitted τ₁ solved₁
    refine ⟨c, d, X.comp j₂ j₁, ρ, faithful₁.comp faithful₂, solved₂, fun t => ?_⟩
    have first := agree₁ t
    simp only [X.act_comp] at first
    have second := (congrArg₂ (fun u v => X.E u v) (X.act_comp j₂ τ₁ (X.act (P.settle f admitted) t))
      (X.act_comp ρ (D.chosen f (P.prepares admitted) c) (X.act (P.settle f admitted) t))).mp
      (agree₂ (X.act (P.settle f admitted) t))
    show X.E (X.act (X.comp (X.comp j₂ j₁) σ) t)
      (X.act (X.comp ρ (X.comp (X.comp (D.chosen f (P.prepares admitted) c) (P.preparedSettle f (P.prepares admitted)))
        (X.id (P.target f)))) t)
    simp only [X.act_comp, X.act_id]
    exact (X.equivalence d).trans (X.preserves j₂ first) second

end Choices

end Choices

/-! ## The control -/

namespace Controls

open AdmissionObservationCover.Controls (World frame)
open SettlementCoverage.Controls (quiet keepOpen chooseFalse allFalse quiet_admitted keepOpen_coversAnswers
  chooseFalse_not_coversAnswers)

/-- An operational choice family may be empty even for an admitted base firing. -/
def noChoices : Choices.{0, 0, 0, 0, 0, 0, 0} keepOpen.step.toStep where
  Choice _ := Empty
  result _ _ choice := nomatch choice
  present_result _ _ choice := nomatch choice
  chosen _ _ choice := nomatch choice
  chosen_answer _ _ choice := nomatch choice
  knowledge_result _ _ choice := nomatch choice

theorem empty_choices_do_not_force_an_outcome :
    keepOpen.step.Admits (s := ()) () ∧
      ¬∃ firing : Σ f : Unit, noChoices.Choice (s := ()) f,
        noChoices.step.Admits (s := ()) firing :=
  ⟨quiet_admitted _, fun ⟨⟨_, choice⟩, _⟩ => nomatch choice⟩

/-- **Choose any answer** of the quiet firing: a recorded choice of a world map. -/
def chooseAny : Choices.{0, 0, 0, 0, 0, 0, 0} keepOpen.step.toStep where
  Choice _ := World → World
  result _ _ _ := ()
  present_result f p _ := keepOpen.step.present_preparedResult f p
  chosen _ _ c := c
  chosen_answer _ _ _ := Frames.models_nil _
  knowledge_result _ _ _ := rfl

/-- **Choosing any answer is exhaustive.** -/
theorem chooseAny_exhaustive : chooseAny.Exhaustive := by
  intro _ _ _ b τ _
  exact ⟨τ, b, frame.id b, frame.id b, faithful_id b, Frames.models_nil _, fun _ => rfl⟩

/-- **Its choices cover the quiet firing's information.** -/
def chooseAny_family :
    CoveringFamily chooseAny.step () (a := ()) (keepOpen.step.information (s := ()) ()) (World → World) :=
  chooseAny.family keepOpen_coversAnswers chooseAny_exhaustive () (quiet_admitted id)

/-- **`chooseFalse` is the branch `allFalse` of `chooseAny`, committed without recording the
choice**: the same settlement and the same result. -/
theorem chooseFalse_is_branch :
    chooseAny.step.settle (s := ()) ⟨(), fun _ => allFalse⟩ (quiet_admitted id) =
        chooseFalse.step.settle (s := ()) () (quiet_admitted _) ∧
      chooseAny.step.result (s := ()) ⟨(), fun _ => allFalse⟩ (quiet_admitted id) =
        chooseFalse.step.result (s := ()) () (quiet_admitted _) :=
  ⟨rfl, rfl⟩

/-- **One branch versus all branches**: the committing step `chooseFalse`, one branch, does not
cover its answers; the recorded choices of `chooseAny`, all the branches, form a covering family. -/
theorem one_branch_versus_family :
    ¬ CoversAnswers chooseFalse.step.toStep ∧
      Nonempty (CoveringFamily chooseAny.step () (a := ()) (keepOpen.step.information (s := ()) ())
        (World → World)) :=
  ⟨chooseFalse_not_coversAnswers, ⟨chooseAny_family⟩⟩

end Controls

#print axioms Choices.step_admits_iff
#print axioms Choices.sound
#print axioms Choices.record_append
#print axioms Choices.record_eq_word
#print axioms Choices.family
#print axioms Controls.chooseAny_exhaustive
#print axioms Controls.chooseAny_family
#print axioms Controls.chooseFalse_is_branch
#print axioms Controls.one_branch_versus_family

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RecordedChoice
