import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.EvidenceInterface
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Spaces
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AdmissionObservationCoverControls

/-!
# Answer-covering settlement: the property of exhaustive steps

`Interface.Step` lets an admitted firing settle along any morphism out of its target frame; the
result's knowledge refines the information read along the settlement. The step's one law is soundness
(`Interface.Step.models_along`, stated as `Sound`, which every step has: `sound`): a firing only
refines knowledge, so every solution after it pulls back to a solution before it. A step may keep
every answer of its information, an **exhaustive**
step, or commit to some of them, a **committing** step; both are steps. `EvidenceInterface` asks that
settlement keep solvable information solvable (`SettlesConservatively`); with exact result knowledge
this keeps result consistency, but does not keep every answer. A step with no tells may settle every
open name to one value, stay consistent and stay sound
(`Controls.chooseFalse`).

## Answer coverage (`CoversAnswers`)

Answer coverage is the property that exhaustive steps have, and the hypothesis an enumeration
completeness theorem needs. Every solution `σ : target ⟶ b` of an admitted firing's information is
recovered, after a **faithful** extension `j : b ⟶ c` of its frame (one that identifies no two terms
that were apart, `Faithful`), by a solution `τ` of the result's knowledge read through the
settlement: `j ∘ σ ≈ τ ∘ settle` on every term. The extension makes room for helpers a firing mints
in its result frame; faithfulness forbids a quotient that would erase the distinctions an answer
makes.

* **Settled answers are answers**: result refinement always gives this direction.
  Under optional exactness, `models_result_iff` also gives the reverse for the same morphism.
* **For exact steps, coverage is a factorization property** (`coversAnswers_iff_extends`): the
  result-solution part follows from exactness, and coverage asks for factoring morphisms.
* **The strong same-target form** (`CoversSettlement`, `j` the identity) is a special case
  (`CoversSettlement.coversAnswers`). With exactness, a retracting settlement satisfies both (`covers_of_retracts`,
  `coversAnswers_of_retracts`); more generally, so does every settlement along which every morphism
  extends (`Extends`, `extends_of_retraction`, `coversAnswers_of_extends`).
* **Coverage implies consistency** (`CoversAnswers.conservative`); the converse fails
  (`Controls.consistency_does_not_imply_coverage`).
* **Restrictions keep both forms** (`coversAnswers_restrict`, `covers_restrict`).

## Branching (`CoveringFamily`)

A step that branches covers a problem by a family of admitted firings, each reading the problem at
its target: every solution of a branch's information solves the problem, and every solution of the
problem is recovered by some branch's result. A covering firing is the one-branch family of its
information (`CoversAnswers.singleton`).

## The controls (`Controls`)

Over the frame of Boolean observations of two-bit worlds, `quiet` is the firing that takes, reads,
makes and tells nothing:
* settled to the all-false world (`chooseFalse`), it is a **committing step**: admitted, conservative
  and sound (`chooseFalse_sound`), and it covers neither in the strong form nor after any faithful
  extension (`chooseFalse_not_covers`, `chooseFalse_not_coversAnswers`); the generic answer is
  committed away (`committing_sound_not_covering`);
* settled by the identity (`keepOpen`), it is exhaustive: it covers (`keepOpen_covers`,
  `keepOpen_coversAnswers`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SettlementCoverage

open Interface (Frames)
open EvidenceInterface (RetractsSettlement SettlesConservatively)
open MeTTaCalculus.OccurrenceCommits (Enabled fire)

universe uO uT uH uOcc uS uF uB

/-! ## Faithful morphisms and extension along a morphism -/

section Faithful

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}

variable (X : Frames Tm Hom) in
/-- A morphism **reflects the equivalence**: it identifies no two terms that were apart. -/
def Faithful {a b : Obj} (j : Hom a b) : Prop :=
  ∀ {u v : Tm a}, X.E (X.act j u) (X.act j v) → X.E u v

variable {X : Frames Tm Hom}

theorem faithful_id (a : Obj) : Faithful X (X.id a) := by
  intro _ _ same
  rwa [X.act_id, X.act_id] at same

theorem Faithful.comp {a b c : Obj} {j : Hom a b} {k : Hom b c} (first : Faithful X j)
    (second : Faithful X k) : Faithful X (X.comp k j) := by
  intro _ _ same
  rw [X.act_comp, X.act_comp] at same
  exact first (second same)

/-- Models depend on a morphism only up to the equivalence of its action. -/
theorem models_of_equivalent {a b : Obj} {f g : Hom a b} (same : ∀ t, X.E (X.act f t) (X.act g t))
    {store : EquationStore (Tm a)} (solved : X.Models f store) : X.Models g store := by
  intro e member
  exact (X.equivalence b).trans ((X.equivalence b).symm (same e.1))
    ((X.equivalence b).trans (solved e member) (same e.2))

variable (X) in
/-- **Every morphism extends along `e`**: for each `σ` out of the source of `e` there are a faithful
extension `j` of the frame `σ` lands in and a morphism `τ` out of the target of `e` with
`j ∘ σ ≈ τ ∘ e`. -/
def Extends {a a' : Obj} (e : Hom a a') : Prop :=
  ∀ {b : Obj} (σ : Hom a b), ∃ (c : Obj) (j : Hom b c) (τ : Hom a' c),
    Faithful X j ∧ ∀ t, X.E (X.act (X.comp j σ) t) (X.act (X.comp τ e) t)

/-- **A morphism with a retraction extends**, by the identity extension. -/
theorem extends_of_retraction {a a' : Obj} {e : Hom a a'} (back : Hom a' a)
    (retracts : ∀ t, X.E (X.act (X.comp back e) t) t) : Extends X e := by
  intro b σ
  refine ⟨b, X.id b, X.comp σ back, faithful_id b, fun t => ?_⟩
  have left : X.act (X.comp (X.id b) σ) t = X.act σ t := by simp only [X.act_comp, X.act_id]
  have right : X.act (X.comp (X.comp σ back) e) t = X.act σ (X.act (X.comp back e) t) := by
    simp only [X.act_comp]
  rw [left, right]
  exact (X.equivalence b).symm (X.preserves σ (retracts t))

end Faithful

/-! ## Answer coverage -/

section Coverage

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O] {State : Type uS} {Firing : State → Type uF}
  (P : Interface.Step X O State Firing)

/-- **Same-target coverage**, the strong form: every solution of an admitted firing's information
is, up to the equivalence, a solution of the result's knowledge into the same frame, read through
the settlement. -/
def CoversSettlement : Prop :=
  ∀ {s : State} (f : Firing s) (admitted : P.Admits f) {b : Obj} (σ : Hom (P.target f) b),
    X.Models σ (P.information f) →
      ∃ τ : Hom (P.frame (P.result f admitted)) b,
        X.Models τ (P.knowledge (P.result f admitted)) ∧
        ∀ t, X.E (X.act σ t) (X.act (X.comp τ (P.settle f admitted)) t)

/-- **Answer-covering settlement**, the property of exhaustive steps: every solution `σ` of an
admitted firing's information is recovered, after a faithful extension `j` of its frame, by a
solution `τ` of the result's knowledge read through the settlement. -/
def CoversAnswers : Prop :=
  ∀ {s : State} (f : Firing s) (admitted : P.Admits f) {b : Obj} (σ : Hom (P.target f) b),
    X.Models σ (P.information f) →
      ∃ (c : Obj) (j : Hom b c) (τ : Hom (P.frame (P.result f admitted)) c),
        Faithful X j ∧ X.Models τ (P.knowledge (P.result f admitted)) ∧
        ∀ t, X.E (X.act (X.comp j σ) t) (X.act (X.comp τ (P.settle f admitted)) t)

/-- **Soundness**, the step's one law: a firing only refines knowledge, so every solution after an
admitted firing pulls back along it to a solution of the knowledge it fired from. Every step is
sound (`sound`), exhaustive and committing alike. -/
def Sound : Prop :=
  ∀ {s : State} {f : Firing s} (admitted : P.Admits f) {b : Obj}
    (σ : Hom (P.frame (P.result f admitted)) b),
    X.Models σ (P.knowledge (P.result f admitted)) →
      X.Models (X.comp σ (P.along f admitted)) (P.knowledge s)

/-- **Every step is sound** (`Interface.Step.models_along`). -/
theorem sound : Sound P := by
  intro _ _ admitted _ σ solved
  exact P.models_along admitted σ solved

/-- **A covering family of branches** for the problem `K` at `a`, from the state `s`, indexed by
`Branch`: admitted firings at `s`, each reading the problem at its target along `reads`; every
solution of a branch's information solves the problem read back (`sound`); and every solution of
the problem is recovered by some branch's result, after a faithful extension of its frame
(`covers`). -/
structure CoveringFamily (s : State) {a : Obj} (K : EquationStore (Tm a)) (Branch : Type uB) where
  firing : Branch → Firing s
  admitted : ∀ i, P.Admits (firing i)
  reads : ∀ i, Hom a (P.target (firing i))
  sound : ∀ i {b : Obj} (σ : Hom (P.target (firing i)) b), X.Models σ (P.information (firing i)) →
    X.Models (X.comp σ (reads i)) K
  covers : ∀ {b : Obj} (σ : Hom a b), X.Models σ K →
    ∃ (i : Branch) (c : Obj) (j : Hom b c) (τ : Hom (P.frame (P.result (firing i) (admitted i))) c),
      Faithful X j ∧ X.Models τ (P.knowledge (P.result (firing i) (admitted i))) ∧
      ∀ t, X.E (X.act (X.comp j σ) t)
        (X.act (X.comp τ (X.comp (P.settle (firing i) (admitted i)) (reads i))) t)

variable {P}

/-- **Settled answers are answers**: a solution of the result's knowledge is exactly a morphism
whose reading through the settlement solves the information. -/
theorem models_result_iff [P.Exact] {s : State} (f : Firing s) (admitted : P.Admits f) {b : Obj}
    (τ : Hom (P.frame (P.result f admitted)) b) :
    X.Models τ (P.knowledge (P.result f admitted)) ↔
      X.Models (X.comp τ (P.settle f admitted)) (P.information f) :=
  P.effectCore.models_result_iff P.effectCore_exact f (P.prepares admitted) τ

/-- **Coverage is a factorization property**: the solution part of `CoversAnswers` is automatic. -/
theorem coversAnswers_iff_extends [P.Exact] : CoversAnswers P ↔
    ∀ {s : State} (f : Firing s) (admitted : P.Admits f) {b : Obj} (σ : Hom (P.target f) b),
      X.Models σ (P.information f) →
        ∃ (c : Obj) (j : Hom b c) (τ : Hom (P.frame (P.result f admitted)) c),
          Faithful X j ∧ ∀ t, X.E (X.act (X.comp j σ) t) (X.act (X.comp τ (P.settle f admitted)) t) := by
  constructor
  · intro covers s f admitted b σ solved
    obtain ⟨c, j, τ, faithful, -, agree⟩ := covers f admitted σ solved
    exact ⟨c, j, τ, faithful, agree⟩
  · intro factors s f admitted b σ solved
    obtain ⟨c, j, τ, faithful, agree⟩ := factors f admitted σ solved
    exact ⟨c, j, τ, faithful, (models_result_iff f admitted τ).mpr
      (models_of_equivalent agree (Frames.models_comp solved j)), agree⟩

/-- **A step whose settlements all extend covers its answers.** -/
theorem coversAnswers_of_extends [P.Exact]
    (extend : ∀ {s : State} (f : Firing s) (admitted : P.Admits f), Extends X (P.settle f admitted)) :
    CoversAnswers P :=
  coversAnswers_iff_extends.mpr fun f admitted _ σ _ => extend f admitted σ

/-- **A retracting settlement covers answers.** -/
theorem coversAnswers_of_retracts [P.Exact] (retracts : RetractsSettlement P) : CoversAnswers P :=
  coversAnswers_of_extends fun f admitted => by
    obtain ⟨back, retraction⟩ := retracts f admitted
    exact extends_of_retraction back retraction

/-- **A retracting settlement covers in the strong same-target form.** -/
theorem covers_of_retracts [P.Exact] (retracts : RetractsSettlement P) : CoversSettlement P := by
  intro s f admitted b σ solved
  obtain ⟨back, retraction⟩ := retracts f admitted
  have agree (t : Tm (P.target f)) :
      X.E (X.act σ t) (X.act (X.comp (X.comp σ back) (P.settle f admitted)) t) := by
    have right : X.act (X.comp (X.comp σ back) (P.settle f admitted)) t =
        X.act σ (X.act (X.comp back (P.settle f admitted)) t) := by
      simp only [X.act_comp]
    rw [right]
    exact (X.equivalence b).symm (X.preserves σ (retraction t))
  exact ⟨X.comp σ back, (models_result_iff f admitted _).mpr (models_of_equivalent agree solved), agree⟩

/-- **The strong form is a special case of answer coverage**, with the identity extension. -/
theorem CoversSettlement.coversAnswers (covers : CoversSettlement P) : CoversAnswers P := by
  intro s f admitted b σ solved
  obtain ⟨τ, solvedResult, agree⟩ := covers f admitted σ solved
  refine ⟨b, X.id b, τ, faithful_id b, solvedResult, fun t => ?_⟩
  have left : X.act (X.comp (X.id b) σ) t = X.act σ t := by simp only [X.act_comp, X.act_id]
  rw [left]
  exact agree t

/-- **Coverage implies consistency**: a covering step settles conservatively. -/
theorem CoversAnswers.conservative (covers : CoversAnswers P) : SettlesConservatively P := by
  intro s f admitted solvable
  obtain ⟨b, σ, solved⟩ := solvable
  obtain ⟨c, _, τ, _, solvedResult, _⟩ := covers f admitted σ solved
  refine ⟨c, τ, ?_⟩
  exact (Frames.models_applyStore _ _ _).mpr
    (P.result_refines f (P.prepares admitted) τ solvedResult)

/-- Coverage directly supplies a result solution; exactness is unnecessary. -/
theorem CoversAnswers.result_solvable (covers : CoversAnswers P) {s : State}
    (f : Firing s) (admitted : P.Admits f) : X.Solvable (P.knowledge (P.result f admitted)) := by
  obtain ⟨b, σ, solved⟩ := P.solvable_information admitted
  obtain ⟨c, _, τ, _, result, _⟩ := covers f admitted σ solved
  exact ⟨c, τ, result⟩

/-- **A covering firing is the one-branch covering family of its information.** -/
def CoversAnswers.singleton (covers : CoversAnswers P) {s : State} (f : Firing s)
    (admitted : P.Admits f) : CoveringFamily P s (P.information f) Unit where
  firing _ := f
  admitted _ := admitted
  reads _ := X.id (P.target f)
  sound _ _ σ solved := (Frames.models_congr (fun t => Frames.act_comp_id σ t) _).mp solved
  covers σ solved := by
    obtain ⟨c, j, τ, faithful, solvedResult, agree⟩ := covers f admitted σ solved
    refine ⟨(), c, j, τ, faithful, solvedResult, fun t => ?_⟩
    have right : X.act (X.comp τ (X.comp (P.settle f admitted) (X.id (P.target f)))) t =
        X.act (X.comp τ (P.settle f admitted)) t := by
      simp only [X.act_comp, X.act_id]
    rw [right]
    exact agree t

/-- **Restrictions keep answer coverage.** -/
theorem coversAnswers_restrict (covers : CoversAnswers P) (allowed : ∀ {s : State}, Firing s → Prop) :
    CoversAnswers (Spaces.restrict P allowed) :=
  fun f admitted _ σ solved => covers f admitted.1 σ solved

/-- **Restrictions keep the strong form.** -/
theorem covers_restrict (covers : CoversSettlement P) (allowed : ∀ {s : State}, Firing s → Prop) :
    CoversSettlement (Spaces.restrict P allowed) :=
  fun f admitted _ σ solved => covers f admitted.1 σ solved

end Coverage

/-! ## The controls: a committing settlement and an exhaustive one -/

namespace Controls

open AdmissionObservationCover.Controls (World frame)
open DisequalityFrames (Prestep)

/-- The world whose two bits are `false`. -/
def allFalse : World := fun _ => false

/-- **The quiet firing**: one state, one firing that takes, reads, makes and tells nothing, with
empty information, settled along `toWorld`. -/
def quiet (toWorld : World → World) : Prestep frame Nat Unit (fun _ => Unit) where
  frame _ := ()
  knowledge _ := []
  present _ := ∅
  selection _ := ⟨[], [], []⟩
  target _ := ()
  extension _ := id
  information _ := []
  transported _ _ member := False.elim (List.not_mem_nil member)
  Shapes _ := ([] : List Nat).Nodup
  Holds _ b σ := frame.Models (a := ()) (b := b) σ []
  result _ _ := ()
  present_result _ _ := by ext o; simp [fire, Selection.commit]
  settle _ _ := toWorld
  knowledge_result _ _ := rfl

/-- **Settling every open bit to `false`**: a committing step. It is sound and conservative, and it
does not cover its answers. -/
abbrev chooseFalse := quiet fun _ => allFalse

/-- The same firing settled by the identity. -/
abbrev keepOpen := quiet id

theorem quiet_admitted (toWorld : World → World) : (quiet toWorld).step.toStep.Admits (s := ()) () := by
  refine ⟨List.nodup_nil, EvidenceInterface.Controls.enabled_nothing ∅,
    ⟨(), id, Frames.models_nil _⟩, ?_⟩
  intro b σ _
  exact Frames.models_nil (X := frame) (a := ()) (b := b) σ

/-- **Every quiet settlement is conservative.** -/
theorem quiet_conservative (toWorld : World → World) : SettlesConservatively (quiet toWorld).step.toStep := by
  intro _ _ _ _
  exact ⟨(), id, Frames.models_nil _⟩

/-- **Settling to `false` loses the generic answer**, after every faithful extension. -/
theorem chooseFalse_not_coversAnswers : ¬ CoversAnswers chooseFalse.step.toStep := by
  intro covers
  obtain ⟨c, j, _, faithful, _, agree⟩ :=
    covers (s := ()) () (quiet_admitted _) (b := ()) (frame.id ()) (Frames.models_nil _)
  have pulled : frame.E (a := c) (frame.act (a := ()) (b := c) j (fun w => w 0))
      (frame.act (a := ()) (b := c) j (fun _ => false)) :=
    agree (fun w => w 0)
  have same := faithful pulled
  have point := congrFun same (fun _ => true)
  change true = false at point
  cases point

theorem chooseFalse_not_covers : ¬ CoversSettlement chooseFalse.step.toStep := fun covers =>
  chooseFalse_not_coversAnswers covers.coversAnswers

/-- **Consistency does not imply coverage**: `chooseFalse` settles conservatively and commits an
answer away. -/
theorem consistency_does_not_imply_coverage :
    SettlesConservatively chooseFalse.step.toStep ∧ ¬ CoversAnswers chooseFalse.step.toStep :=
  ⟨quiet_conservative _, chooseFalse_not_coversAnswers⟩

/-- **The committing step is sound**: `chooseFalse` satisfies the step's one law. -/
theorem chooseFalse_sound : Sound chooseFalse.step.toStep :=
  sound chooseFalse.step.toStep

/-- **Committing is sound and not answer-covering**: `chooseFalse` is a step of a different kind
than an exhaustive one, not a defect. -/
theorem committing_sound_not_covering : Sound chooseFalse.step.toStep ∧ ¬ CoversAnswers chooseFalse.step.toStep :=
  ⟨chooseFalse_sound, chooseFalse_not_coversAnswers⟩

/-- **The identity settlement covers**, in the strong form. -/
theorem keepOpen_covers : CoversSettlement keepOpen.step.toStep := by
  apply covers_of_retracts
  intro _ _ _
  exact ⟨id, fun _ => rfl⟩

theorem keepOpen_coversAnswers : CoversAnswers keepOpen.step.toStep :=
  keepOpen_covers.coversAnswers

end Controls

#print axioms faithful_id
#print axioms Faithful.comp
#print axioms extends_of_retraction
#print axioms sound
#print axioms models_result_iff
#print axioms coversAnswers_iff_extends
#print axioms coversAnswers_of_extends
#print axioms coversAnswers_of_retracts
#print axioms covers_of_retracts
#print axioms CoversSettlement.coversAnswers
#print axioms CoversAnswers.conservative
#print axioms CoversAnswers.singleton
#print axioms coversAnswers_restrict
#print axioms covers_restrict
#print axioms Controls.quiet_admitted
#print axioms Controls.chooseFalse_not_coversAnswers
#print axioms Controls.chooseFalse_not_covers
#print axioms Controls.consistency_does_not_imply_coverage
#print axioms Controls.chooseFalse_sound
#print axioms Controls.committing_sound_not_covering
#print axioms Controls.keepOpen_covers

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SettlementCoverage
