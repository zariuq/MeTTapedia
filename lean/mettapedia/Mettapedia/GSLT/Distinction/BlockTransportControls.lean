import Mettapedia.GSLT.Distinction.BlockTransport
import Mettapedia.GSLT.Distinction.IsometryControls

/-!
# Instances and controls for block transport

The source is one exchange, `ready → done`, read by its own step, with one
observation: whether the exchange has finished.

* **A four-step lowering** (`fourBlocks`): three administrative steps and a
  completing one, with every field of `CompiledBlocks` proved, including the
  reflection of every block and of every primitive protocol prefix.  A
  one-step lowering (`oneBlocks`) also compiles the exchange.
* **Equal block observations, different accounts** (`accounts_control`): every
  source formula has the same value at both compiled states, while the
  existing realization accounts count `4` and `1` communications.
* **Primitive discounting separates the lowerings** (`primitive_control`): in
  one target holding both, the block reading puts the two compiled starts at
  distance `0` and the primitive reading at distance at least the discount.
* **An extra target interaction** (`interaction_control`): an extra step from an
  administrative state is a block when it is read as completing an action;
  then a formula changes value, so no compilation of the exchange onto that
  reading preserves formula values, and the extra state violates prefix
  reflection.  Read as external to the protocol, the same target compiles the
  exchange (`boundedBlocks`).
* **Divergence, deadlock and return** (`ending_control`): blocks put a stuck
  state and a silently divergent one at distance `0`, while the primitive
  reading separates them by the discount; a returned state is separated from a
  stuck one only through the observation that reads return.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Distinction.BlockTransportControls

open Mettapedia.GSLT
open Mettapedia.GSLT.HennessyMilner
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.Distinction
open Mettapedia.GSLT.Distinction.IsometryControls

/-- One reading, `1` where a flag holds. -/
noncomputable abbrev flagReading (Term : Type) (step : Term → Term → Prop) (flag : Term → Bool) :
    GradedObservations.{0, 0} (plainGSLT Term step) where
  Atom := Unit
  value _ term := if flag term then 1 else 0
  value_nonneg _ term := by split_ifs <;> norm_num
  value_le_one _ term := by split_ifs <;> norm_num
  value_resp _ _ _ equal := by rw [show _ = _ from equal]

/-! ## The source exchange -/

/-- The phases of one exchange. -/
inductive Phase where
  | ready
  | done
  deriving DecidableEq

/-- The exchange. -/
def exchangeStep (source target : Phase) : Prop := source = .ready ∧ target = .done

abbrev exchange : GSLT.{0} := plainGSLT Phase exchangeStep

def Phase.finished : Phase → Bool
  | .ready => false
  | .done => true

/-- The source, read by its own step, with the finished observation. -/
noncomputable abbrev exchangeGraded : GradedSystem.{0, 0, 0, 0} exchange :=
  GradedSystem.stepping exchange (flagReading Phase exchangeStep Phase.finished) 1 zero_le_one le_rfl

theorem exchange_imageFinite : exchangeGraded.dynamics.ImageFiniteModulo := by
  intro _ _
  refine ⟨{Phase.done}, Set.finite_singleton _, ?_⟩
  intro target step
  change exchangeStep _ target at step
  obtain ⟨-, rfl⟩ := step
  exact ⟨Phase.done, rfl, rfl⟩

/-! ## The four-step lowering -/

/-- The states of the four-step protocol. -/
inductive Lowered where
  | ready
  | first
  | second
  | third
  | done
  deriving DecidableEq

/-- Its primitive steps. -/
inductive LoweredStep : Lowered → Lowered → Prop where
  | opening : LoweredStep .ready .first
  | sending : LoweredStep .first .second
  | receiving : LoweredStep .second .third
  | closing : LoweredStep .third .done

abbrev fourStep : GSLT.{0} := plainGSLT Lowered LoweredStep

def Lowered.finished : Lowered → Bool
  | .done => true
  | _ => false

/-- The block reading: the first three steps are administrative and the last
completes the exchange. -/
def fourReading : BlockReading fourStep Unit where
  silent source target := LoweredStep source target ∧ target ≠ .done
  complete _ source target := source = .third ∧ target = .done
  external _ _ := False
  silent_step := fun silences => silences.1
  complete_step := by
    rintro _ _ _ ⟨rfl, rfl⟩
    exact LoweredStep.closing
  external_step := fun never => never.elim
  classify := by
    intro source target step
    cases step with
    | opening => exact Or.inl ⟨LoweredStep.opening, by decide⟩
    | sending => exact Or.inl ⟨LoweredStep.sending, by decide⟩
    | receiving => exact Or.inl ⟨LoweredStep.receiving, by decide⟩
    | closing => exact Or.inr (Or.inl ⟨(), rfl, rfl⟩)
  silent_resp_left := by
    intro _ _ target equal silences
    exact ⟨target, equal ▸ silences, rfl⟩
  complete_resp_left := by
    intro _ _ _ target equal completes
    exact ⟨target, equal ▸ completes, rfl⟩
  complete_resp_right := by
    intro _ _ _ _ completes equal
    exact equal ▸ completes

/-- Compile the phases. -/
def lowerFour : Phase → Lowered
  | .ready => .ready
  | .done => .done

/-- The four-step block of the exchange. -/
def fourPath : {source target : Phase} → exchange.Step source target →
    ExecutionPath fourStep (lowerFour source) (lowerFour target)
  | .ready, .done, _ =>
      .cons ⟨LoweredStep.opening⟩ (.cons ⟨LoweredStep.sending⟩ (.cons ⟨LoweredStep.receiving⟩
        (.cons ⟨LoweredStep.closing⟩ (.refl _))))
  | .ready, .ready, step => absurd step.2 (by decide)
  | .done, _, step => absurd step.1 (by decide)

/-- The four-step realization: a path-valued compiler realization. -/
def fourRealization : OperationalRealization exchange fourStep where
  mapTerm := lowerFour
  mapEquiv := fun equal => congrArg lowerFour equal
  mapStep := fun step => fourPath step

theorem silentStar_done {middle : Lowered}
    (administrative : Relation.ReflTransGen fourReading.silent .done middle) : middle = .done := by
  induction administrative with
  | refl => rfl
  | tail _ last inductionHypothesis =>
      subst inductionHypothesis
      obtain ⟨step, -⟩ := last
      cases step

theorem protocolStar_done {target : Lowered}
    (protocol : Relation.ReflTransGen fourReading.ProtocolStep .done target) : target = .done := by
  induction protocol with
  | refl => rfl
  | tail _ last inductionHypothesis =>
      subst inductionHypothesis
      rcases last with ⟨step, -⟩ | ⟨_, absurdity, -⟩
      · cases step
      · cases absurdity

/-- Every state before completion is administratively reachable from `ready`. -/
theorem silentStar_ready (target : Lowered) (notDone : target ≠ .done) :
    Relation.ReflTransGen fourReading.silent .ready target := by
  have open' : fourReading.silent .ready .first := ⟨LoweredStep.opening, by decide⟩
  have send : fourReading.silent .first .second := ⟨LoweredStep.sending, by decide⟩
  have receive : fourReading.silent .second .third := ⟨LoweredStep.receiving, by decide⟩
  cases target with
  | ready => exact .refl
  | first => exact .single open'
  | second => exact (Relation.ReflTransGen.single open').tail send
  | third => exact ((Relation.ReflTransGen.single open').tail send).tail receive
  | done => exact absurd rfl notDone

/-- **The four-step lowering compiles the exchange in blocks.** -/
def fourBlocks : CompiledBlocks exchange fourStep fourReading where
  realization := fourRealization
  realizedBlocks := by
    intro source target step
    match source, target, step with
    | .ready, .done, _ =>
        exact BlockReading.IsBlock.silent (B := fourReading) LoweredStep.opening
          ⟨LoweredStep.opening, by decide⟩
          (BlockReading.IsBlock.silent (B := fourReading) LoweredStep.sending
            ⟨LoweredStep.sending, by decide⟩
            (BlockReading.IsBlock.silent (B := fourReading) LoweredStep.receiving
              ⟨LoweredStep.receiving, by decide⟩
              (BlockReading.IsBlock.complete (B := fourReading) LoweredStep.closing ⟨rfl, rfl⟩)))
    | .ready, .ready, step => exact absurd step.2 (by decide)
    | .done, _, step => exact absurd step.1 (by decide)
  reflectBlock := by
    intro source target' block
    obtain ⟨middle, administrative, rfl, rfl⟩ := block
    cases source with
    | ready => exact ⟨Phase.done, ⟨rfl, rfl⟩, rfl⟩
    | done =>
        have := silentStar_done administrative
        cases this
  prefixReflection := by
    intro source target' protocol
    cases source with
    | ready =>
        by_cases finished : target' = .done
        · subst finished
          exact ⟨Phase.done, .single ⟨rfl, rfl⟩, Lowered.done, rfl, .refl⟩
        · exact ⟨Phase.ready, .refl, Lowered.ready, rfl, silentStar_ready target' finished⟩
    | done =>
        have := protocolStar_done protocol
        subst this
        exact ⟨Phase.done, .refl, Lowered.done, rfl, .refl⟩

/-! ## The one-step lowering -/

/-- The block reading of the exchange itself: its step completes. -/
def oneReading : BlockReading exchange Unit where
  silent _ _ := False
  complete _ source target := exchangeStep source target
  external _ _ := False
  silent_step := fun never => never.elim
  complete_step := fun completes => completes
  external_step := fun never => never.elim
  classify := fun step => Or.inr (Or.inl ⟨(), step⟩)
  silent_resp_left := fun _ never => never.elim
  complete_resp_left := by
    intro _ _ _ target equal completes
    exact ⟨target, equal ▸ completes, rfl⟩
  complete_resp_right := by
    intro _ _ _ _ completes equal
    exact equal ▸ completes

/-- **The one-step lowering compiles the exchange in blocks.** -/
def oneBlocks : CompiledBlocks exchange exchange oneReading where
  realization := OperationalRealization.id exchange
  realizedBlocks := fun step => .complete step step
  reflectBlock := by
    rintro source target' ⟨middle, administrative, completes⟩
    cases administrative with
    | refl => exact ⟨target', completes, rfl⟩
    | tail _ never => exact never.elim
  prefixReflection := by
    intro source target' protocol
    refine ⟨target', ?_, target', rfl, .refl⟩
    induction protocol with
    | refl => exact .refl
    | tail _ last inductionHypothesis =>
        rcases last with never | ⟨_, completes⟩
        · exact never.elim
        · exact inductionHypothesis.tail completes

/-! ## Equal block observations, different accounts -/

/-- The four-step block system. -/
noncomputable abbrev fourGraded : GradedSystem.{0, 0, 0, 0} fourStep :=
  fourReading.graded (flagReading Lowered LoweredStep Lowered.finished) 1 zero_le_one le_rfl

/-- The one-step block system. -/
noncomputable abbrev oneGraded : GradedSystem.{0, 0, 0, 0} exchange :=
  oneReading.graded (flagReading Phase exchangeStep Phase.finished) 1 zero_le_one le_rfl

/-- The four-step transport. -/
noncomputable def fourTransport : ObservationBisimulation exchangeGraded fourGraded :=
  fourBlocks.transport _ _ zero_le_one le_rfl id fun _ phase => by
    cases phase <;> rfl

/-- The one-step transport. -/
noncomputable def oneTransport : ObservationBisimulation exchangeGraded oneGraded :=
  oneBlocks.transport _ _ zero_le_one le_rfl id fun _ phase => by
    cases phase <;> rfl

/-- The one source run. -/
def exchangeRun : ExecutionPath exchange Phase.ready Phase.done :=
  .cons ⟨(⟨rfl, rfl⟩ : exchangeStep .ready .done)⟩ (.refl _)

/-- **Equal block observations with different communication accounts.** Every
source formula takes the same value at the two compiled states of each
phase; the existing realization accounts count four communications and one. -/
theorem accounts_control :
    (∀ (formula : exchangeGraded.Formula) (phase : Phase),
      fourGraded.eval (fourTransport.translate formula) (lowerFour phase) =
        oneGraded.eval (oneTransport.translate formula) phase) ∧
      fourRealization.blockAccount.of exchangeRun = Multiplicative.ofAdd 4 ∧
      (OperationalRealization.id exchange).blockAccount.of exchangeRun = Multiplicative.ofAdd 1 := by
  exact ⟨fun formula phase => (fourTransport.eval_translate formula phase).trans
    (oneTransport.eval_translate formula phase).symm, rfl, rfl⟩

/-- **Block distances transport** onto both lowerings. -/
theorem blocks_transport (left right : Phase) :
    fourGraded.behaviouralDistance (lowerFour left) (lowerFour right) =
        exchangeGraded.behaviouralDistance left right ∧
      oneGraded.behaviouralDistance left right = exchangeGraded.behaviouralDistance left right :=
  ⟨fourBlocks.behaviouralDistance_eq _ _ zero_le_one le_rfl id (fun _ phase => by cases phase <;> rfl)
      (fun observation => ⟨observation, rfl⟩) exchange_imageFinite left right,
    oneBlocks.behaviouralDistance_eq _ _ zero_le_one le_rfl id (fun _ phase => by cases phase <;> rfl)
      (fun observation => ⟨observation, rfl⟩) exchange_imageFinite left right⟩

/-! ## Primitive discounting separates the lowerings -/

/-- One target holding both lowerings. -/
inductive BothStep : Phase ⊕ Lowered → Phase ⊕ Lowered → Prop where
  | short {source target : Phase} : exchangeStep source target → BothStep (.inl source) (.inl target)
  | long {source target : Lowered} : LoweredStep source target → BothStep (.inr source) (.inr target)

abbrev both : GSLT.{0} := plainGSLT (Phase ⊕ Lowered) BothStep

def bothFinished : Phase ⊕ Lowered → Bool
  | .inl phase => phase.finished
  | .inr state => state.finished

/-- The block reading of both lowerings. -/
def bothReading : BlockReading both Unit where
  silent source target := ∃ left right, source = .inr left ∧ target = .inr right ∧
    fourReading.silent left right
  complete _ source target := (source = .inl .ready ∧ target = .inl .done) ∨
    (source = .inr .third ∧ target = .inr .done)
  external _ _ := False
  silent_step := by
    rintro _ _ ⟨left, right, rfl, rfl, step, -⟩
    exact BothStep.long step
  complete_step := by
    rintro _ _ _ (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact BothStep.short ⟨rfl, rfl⟩
    · exact BothStep.long LoweredStep.closing
  external_step := fun never => never.elim
  classify := by
    intro source target step
    cases step with
    | short completes =>
        obtain ⟨rfl, rfl⟩ := completes
        exact Or.inr (Or.inl ⟨(), Or.inl ⟨rfl, rfl⟩⟩)
    | long step =>
        cases step with
        | opening => exact Or.inl ⟨_, _, rfl, rfl, LoweredStep.opening, by decide⟩
        | sending => exact Or.inl ⟨_, _, rfl, rfl, LoweredStep.sending, by decide⟩
        | receiving => exact Or.inl ⟨_, _, rfl, rfl, LoweredStep.receiving, by decide⟩
        | closing => exact Or.inr (Or.inl ⟨(), Or.inr ⟨rfl, rfl⟩⟩)
  silent_resp_left := by
    intro _ _ target equal silences
    exact ⟨target, equal ▸ silences, rfl⟩
  complete_resp_left := by
    intro _ _ _ target equal completes
    exact ⟨target, equal ▸ completes, rfl⟩
  complete_resp_right := by
    intro _ _ _ _ completes equal
    exact equal ▸ completes

/-- The block system of both lowerings. -/
noncomputable abbrev bothBlocks (discount : ℝ) (nonneg : 0 ≤ discount) (le_one : discount ≤ 1) :
    GradedSystem.{0, 0, 0, 0} both :=
  bothReading.graded (flagReading (Phase ⊕ Lowered) BothStep bothFinished) discount nonneg le_one

/-- The primitive reading of both lowerings: every target step is a step. -/
noncomputable abbrev bothPrimitive (discount : ℝ) (nonneg : 0 ≤ discount) (le_one : discount ≤ 1) :
    GradedSystem.{0, 0, 0, 0} both :=
  GradedSystem.stepping both (flagReading (Phase ⊕ Lowered) BothStep bothFinished) discount
    nonneg le_one

theorem both_unfinished_block (state : Phase ⊕ Lowered) (unfinished : bothFinished state = false) :
    ∃ target, bothReading.Block () state target ∧ bothFinished target = true := by
  have silentAt : ∀ left right : Lowered, LoweredStep left right → right ≠ .done →
      bothReading.silent (.inr left) (.inr right) :=
    fun left right step notDone => ⟨left, right, rfl, rfl, step, notDone⟩
  rcases state with phase | lowered
  · cases phase with
    | ready => exact ⟨.inl .done, ⟨_, .refl, Or.inl ⟨rfl, rfl⟩⟩, rfl⟩
    | done => exact absurd unfinished (by decide)
  · have closing : bothReading.complete () (.inr .third) (.inr .done) := Or.inr ⟨rfl, rfl⟩
    refine ⟨.inr .done, ?_, rfl⟩
    have s1 := silentAt _ _ LoweredStep.opening (by decide)
    have s2 := silentAt _ _ LoweredStep.sending (by decide)
    have s3 := silentAt _ _ LoweredStep.receiving (by decide)
    cases lowered with
    | ready => exact ⟨.inr .third, ((Relation.ReflTransGen.single s1).tail s2).tail s3, closing⟩
    | first => exact ⟨.inr .third, (Relation.ReflTransGen.single s2).tail s3, closing⟩
    | second => exact ⟨.inr .third, Relation.ReflTransGen.single s3, closing⟩
    | third => exact ⟨.inr .third, .refl, closing⟩
    | done => exact absurd unfinished (by decide)

theorem both_finished_no_block {state target : Phase ⊕ Lowered}
    (finished : bothFinished state = true) : ¬ bothReading.Block () state target := by
  rintro ⟨middle, administrative, completes⟩
  have stays : middle = state := by
    clear completes
    induction administrative with
    | refl => rfl
    | tail _ last inductionHypothesis =>
        subst inductionHypothesis
        obtain ⟨left, right, rfl, rfl, step, notDone⟩ := last
        cases step
        all_goals simp_all [bothFinished, Lowered.finished]
  subst stays
  rcases completes with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp_all [bothFinished, Phase.finished,
    Lowered.finished]

/-- **The block reading identifies the lowerings**: the compiled starts are at
block distance `0`, at every discount. -/
theorem both_block_zero (discount : ℝ) (nonneg : 0 ≤ discount) (le_one : discount ≤ 1) :
    (bothBlocks discount nonneg le_one).logicalDistance (.inl .ready) (.inr .ready) = 0 := by
  refine (bothBlocks discount nonneg le_one).logicalDistance_eq_zero_of_gradedBisimilar
    ⟨fun first second => bothFinished first = bothFinished second, ⟨?_, ?_, ?_⟩, rfl⟩
  · intro first second related _ first' block
    have unfinished : bothFinished first = false := by
      by_contra finished
      exact both_finished_no_block (Bool.eq_true_of_not_eq_false finished) block
    obtain ⟨second', secondBlock, secondFinished⟩ :=
      both_unfinished_block second (related ▸ unfinished)
    refine ⟨second', secondBlock, ?_⟩
    have firstFinished : bothFinished first' = true := by
      obtain ⟨middle, administrative, completes⟩ := block
      rcases completes with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> rfl
    change bothFinished first' = bothFinished second'
    rw [firstFinished, secondFinished]
  · intro first second related _ second' block
    have unfinished : bothFinished second = false := by
      by_contra finished
      exact both_finished_no_block (Bool.eq_true_of_not_eq_false finished) block
    obtain ⟨first', firstBlock, firstFinished⟩ :=
      both_unfinished_block first (related.symm ▸ unfinished)
    refine ⟨first', firstBlock, ?_⟩
    have secondFinished : bothFinished second' = true := by
      obtain ⟨middle, administrative, completes⟩ := block
      rcases completes with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> rfl
    change bothFinished first' = bothFinished second'
    rw [firstFinished, secondFinished]
  · intro first second related _
    change (if bothFinished first then (1 : ℝ) else 0) = if bothFinished second then 1 else 0
    rw [show bothFinished first = bothFinished second from related]

/-- **The primitive reading separates the lowerings** by at least the
discount: after one primitive step the one-step lowering has finished and the
four-step lowering has not. -/
theorem both_primitive_separates (discount : ℝ) (nonneg : 0 ≤ discount) (le_one : discount ≤ 1) :
    discount ≤ (bothPrimitive discount nonneg le_one).logicalDistance (.inl .ready) (.inr .ready) := by
  have probe := (bothPrimitive discount nonneg le_one).abs_eval_sub_le_logicalDistance
    (.dia () (.atom ())) (.inl .ready) (.inr .ready)
  have shortSuccessors : (bothPrimitive discount nonneg le_one).successors () (.inl .ready) =
      {.inl .done} := by
    ext target
    constructor
    · intro step
      change BothStep (.inl .ready) target at step
      cases step with
      | short completes => obtain ⟨-, rfl⟩ := completes; rfl
    · rintro rfl
      exact BothStep.short ⟨rfl, rfl⟩
  have longSuccessors : (bothPrimitive discount nonneg le_one).successors () (.inr .ready) =
      {.inr .first} := by
    ext target
    constructor
    · intro step
      change BothStep (.inr .ready) target at step
      cases step with
      | long step => cases step; rfl
    · rintro rfl
      exact BothStep.long LoweredStep.opening
  rw [GradedSystem.eval_dia, GradedSystem.eval_dia, shortSuccessors, longSuccessors,
    Set.image_singleton, Set.image_singleton, csSup_singleton, csSup_singleton,
    GradedSystem.eval_atom, GradedSystem.eval_atom] at probe
  change |discount * (if bothFinished (.inl .done) then (1 : ℝ) else 0) -
    discount * (if bothFinished (.inr .first) then (1 : ℝ) else 0)| ≤ _ at probe
  simp only [bothFinished, Phase.finished, Lowered.finished, if_true, Bool.false_eq_true,
    if_false, mul_one, mul_zero, sub_zero, abs_of_nonneg nonneg] at probe
  exact probe

/-- **Primitive discounting separates a one-step from a four-step lowering**,
while their blocks agree. -/
theorem primitive_control (discount : ℝ) (positive : 0 < discount) (le_one : discount ≤ 1) :
    (bothBlocks discount positive.le le_one).logicalDistance (.inl .ready) (.inr .ready) = 0 ∧
      0 < (bothPrimitive discount positive.le le_one).logicalDistance (.inl .ready) (.inr .ready) :=
  ⟨both_block_zero discount positive.le le_one,
    lt_of_lt_of_le positive (both_primitive_separates discount positive.le le_one)⟩

/-! ## An extra target interaction -/

/-- The four-step protocol with an extra interaction from its first
administrative state. -/
inductive LeakyStep : Option Lowered → Option Lowered → Prop where
  | protocol {source target : Lowered} : LoweredStep source target →
      LeakyStep (some source) (some target)
  | leak : LeakyStep (some .first) none

abbrev leaky : GSLT.{0} := plainGSLT (Option Lowered) LeakyStep

def leakyFinished : Option Lowered → Bool
  | some state => state.finished
  | none => false

/-- Administrative steps of the leaky protocol. -/
def leakySilent (source target : Option Lowered) : Prop :=
  ∃ left right, source = some left ∧ target = some right ∧ fourReading.silent left right

/-- The completing step of the protocol. -/
def leakyComplete (source target : Option Lowered) : Prop :=
  source = some .third ∧ target = some .done

/-- **Read as completing an action**, the extra interaction is a block. -/
def visibleReading : BlockReading leaky Unit where
  silent := leakySilent
  complete _ source target := leakyComplete source target ∨ (source = some .first ∧ target = none)
  external _ _ := False
  silent_step := by
    rintro _ _ ⟨left, right, rfl, rfl, step, -⟩
    exact LeakyStep.protocol step
  complete_step := by
    rintro _ _ _ (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact LeakyStep.protocol LoweredStep.closing
    · exact LeakyStep.leak
  external_step := fun never => never.elim
  classify := by
    intro source target step
    cases step with
    | protocol step =>
        cases step with
        | opening => exact Or.inl ⟨_, _, rfl, rfl, LoweredStep.opening, by decide⟩
        | sending => exact Or.inl ⟨_, _, rfl, rfl, LoweredStep.sending, by decide⟩
        | receiving => exact Or.inl ⟨_, _, rfl, rfl, LoweredStep.receiving, by decide⟩
        | closing => exact Or.inr (Or.inl ⟨(), Or.inl ⟨rfl, rfl⟩⟩)
    | leak => exact Or.inr (Or.inl ⟨(), Or.inr ⟨rfl, rfl⟩⟩)
  silent_resp_left := by
    intro _ _ target equal silences
    exact ⟨target, equal ▸ silences, rfl⟩
  complete_resp_left := by
    intro _ _ _ target equal completes
    exact ⟨target, equal ▸ completes, rfl⟩
  complete_resp_right := by
    intro _ _ _ _ completes equal
    exact equal ▸ completes

/-- **Read as external**, the extra interaction lies outside the observed
protocol. -/
def boundedReading : BlockReading leaky Unit where
  silent := leakySilent
  complete _ := leakyComplete
  external source target := source = some .first ∧ target = none
  silent_step := by
    rintro _ _ ⟨left, right, rfl, rfl, step, -⟩
    exact LeakyStep.protocol step
  complete_step := by
    rintro _ _ _ ⟨rfl, rfl⟩
    exact LeakyStep.protocol LoweredStep.closing
  external_step := by
    rintro _ _ ⟨rfl, rfl⟩
    exact LeakyStep.leak
  classify := by
    intro source target step
    cases step with
    | protocol step =>
        cases step with
        | opening => exact Or.inl ⟨_, _, rfl, rfl, LoweredStep.opening, by decide⟩
        | sending => exact Or.inl ⟨_, _, rfl, rfl, LoweredStep.sending, by decide⟩
        | receiving => exact Or.inl ⟨_, _, rfl, rfl, LoweredStep.receiving, by decide⟩
        | closing => exact Or.inr (Or.inl ⟨(), rfl, rfl⟩)
    | leak => exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  silent_resp_left := by
    intro _ _ target equal silences
    exact ⟨target, equal ▸ silences, rfl⟩
  complete_resp_left := by
    intro _ _ _ target equal completes
    exact ⟨target, equal ▸ completes, rfl⟩
  complete_resp_right := by
    intro _ _ _ _ completes equal
    exact equal ▸ completes

/-- Compile the phases into the leaky protocol. -/
def lowerLeaky : Phase → Option Lowered
  | .ready => some .ready
  | .done => some .done

/-- The four-step block of the exchange in the leaky protocol. -/
def leakyPath : {source target : Phase} → exchange.Step source target →
    ExecutionPath leaky (lowerLeaky source) (lowerLeaky target)
  | .ready, .done, _ =>
      .cons ⟨LeakyStep.protocol LoweredStep.opening⟩
        (.cons ⟨LeakyStep.protocol LoweredStep.sending⟩
          (.cons ⟨LeakyStep.protocol LoweredStep.receiving⟩
            (.cons ⟨LeakyStep.protocol LoweredStep.closing⟩ (.refl _))))
  | .ready, .ready, step => absurd step.2 (by decide)
  | .done, _, step => absurd step.1 (by decide)

theorem leakySilentStar {source middle : Option Lowered}
    (administrative : Relation.ReflTransGen leakySilent source middle) :
    (∃ start, source = some start) → ∃ finish, middle = some finish := by
  intro sourceSome
  induction administrative with
  | refl => exact sourceSome
  | tail _ last _ =>
      obtain ⟨_, right, -, rfl, -⟩ := last
      exact ⟨right, rfl⟩

theorem leakySilentStar_done {middle : Option Lowered}
    (administrative : Relation.ReflTransGen leakySilent (some .done) middle) :
    middle = some .done := by
  induction administrative with
  | refl => rfl
  | tail _ last inductionHypothesis =>
      subst inductionHypothesis
      obtain ⟨left, right, sourceEq, rfl, step, -⟩ := last
      cases sourceEq
      cases step

/-- **With the interaction outside the observer boundary**, the leaky target
compiles the exchange in blocks. -/
def boundedBlocks : CompiledBlocks exchange leaky boundedReading where
  realization :=
    { mapTerm := lowerLeaky
      mapEquiv := fun equal => congrArg lowerLeaky equal
      mapStep := fun step => leakyPath step }
  realizedBlocks := by
    intro source target step
    match source, target, step with
    | .ready, .done, _ =>
        exact BlockReading.IsBlock.silent (B := boundedReading) (LeakyStep.protocol LoweredStep.opening)
          ⟨_, _, rfl, rfl, LoweredStep.opening, by decide⟩
          (BlockReading.IsBlock.silent (B := boundedReading) (LeakyStep.protocol LoweredStep.sending)
            ⟨_, _, rfl, rfl, LoweredStep.sending, by decide⟩
            (BlockReading.IsBlock.silent (B := boundedReading)
              (LeakyStep.protocol LoweredStep.receiving)
              ⟨_, _, rfl, rfl, LoweredStep.receiving, by decide⟩
              (BlockReading.IsBlock.complete (B := boundedReading)
                (LeakyStep.protocol LoweredStep.closing) ⟨rfl, rfl⟩)))
    | .ready, .ready, step => exact absurd step.2 (by decide)
    | .done, _, step => exact absurd step.1 (by decide)
  reflectBlock := by
    intro source target' block
    obtain ⟨middle, administrative, rfl, rfl⟩ := block
    cases source with
    | ready => exact ⟨Phase.done, ⟨rfl, rfl⟩, rfl⟩
    | done =>
        have := leakySilentStar_done administrative
        cases this
  prefixReflection := by
    intro source target' protocol
    have leakySilentAt : ∀ left right : Lowered, LoweredStep left right → right ≠ .done →
        leakySilent (some left) (some right) :=
      fun left right step notDone => ⟨left, right, rfl, rfl, step, notDone⟩
    cases source with
    | ready =>
        have reach : ∀ state : Lowered, state ≠ .done →
            Relation.ReflTransGen leakySilent (some .ready) (some state) := by
          intro state notDone
          have s1 := leakySilentAt _ _ LoweredStep.opening (by decide)
          have s2 := leakySilentAt _ _ LoweredStep.sending (by decide)
          have s3 := leakySilentAt _ _ LoweredStep.receiving (by decide)
          cases state with
          | ready => exact .refl
          | first => exact .single s1
          | second => exact (Relation.ReflTransGen.single s1).tail s2
          | third => exact ((Relation.ReflTransGen.single s1).tail s2).tail s3
          | done => exact absurd rfl notDone
        have someTarget : ∃ state, target' = some state := by
          induction protocol with
          | refl => exact ⟨.ready, rfl⟩
          | tail _ last _ =>
              rcases last with ⟨_, right, -, rfl, -⟩ | ⟨_, -, rfl⟩
              · exact ⟨right, rfl⟩
              · exact ⟨.done, rfl⟩
        obtain ⟨state, rfl⟩ := someTarget
        by_cases finished : state = .done
        · subst finished
          exact ⟨Phase.done, .single ⟨rfl, rfl⟩, some Lowered.done, rfl, .refl⟩
        · exact ⟨Phase.ready, .refl, some Lowered.ready, rfl, reach state finished⟩
    | done =>
        have stays : target' = some .done := by
          induction protocol with
          | refl => rfl
          | tail _ last inductionHypothesis =>
              subst inductionHypothesis
              rcases last with ⟨left, right, sourceEq, rfl, step, -⟩ | ⟨_, sourceEq, -⟩
              · cases sourceEq
                cases step
              · cases sourceEq
        subst stays
        exact ⟨Phase.done, .refl, some Lowered.done, rfl, .refl⟩

/-- The block system of the visible reading. -/
noncomputable abbrev visibleGraded : GradedSystem.{0, 0, 0, 0} leaky :=
  visibleReading.graded (flagReading (Option Lowered) LeakyStep leakyFinished) 1 zero_le_one le_rfl

/-- The probe: some block reaches an unfinished state. -/
def unfinishedProbe : exchangeGraded.Formula := .dia () (.neg (.atom ()))

theorem exchange_probe : exchangeGraded.eval unfinishedProbe Phase.ready = 0 := by
  have successors : exchangeGraded.successors () Phase.ready = {Phase.done} := by
    ext target
    constructor
    · intro step
      change exchangeStep _ target at step
      exact step.2
    · rintro rfl
      exact ⟨rfl, rfl⟩
  rw [unfinishedProbe, GradedSystem.eval_dia, successors, Set.image_singleton, csSup_singleton,
    GradedSystem.eval_neg, GradedSystem.eval_atom]
  change (1 : ℝ) * (1 - (if Phase.finished .done then 1 else 0)) = 0
  norm_num [Phase.finished]

theorem visible_probe :
    visibleGraded.eval (.dia () (.neg (.atom ()))) (some .ready) = 1 := by
  have reachesLeak : none ∈ visibleGraded.successors () (some .ready) :=
    ⟨some .first, .single ⟨_, _, rfl, rfl, LoweredStep.opening, by decide⟩, Or.inr ⟨rfl, rfl⟩⟩
  rw [GradedSystem.eval_dia]
  have upper := visibleGraded.sSup_image_le_one (.neg (.atom ())) (visibleGraded.successors () (some .ready))
  have lower : visibleGraded.eval (.neg (.atom ())) none ≤
      sSup (visibleGraded.eval (.neg (.atom ())) '' visibleGraded.successors () (some .ready)) :=
    le_csSup (visibleGraded.bddAbove_image _ _) ⟨none, reachesLeak, rfl⟩
  have leakValue : visibleGraded.eval (.neg (.atom ())) none = 1 := by
    rw [GradedSystem.eval_neg, GradedSystem.eval_atom]
    change 1 - (if leakyFinished none then (1 : ℝ) else 0) = 1
    norm_num [leakyFinished]
  change (1 : ℝ) * _ = 1
  rw [one_mul]
  linarith

/-- **An extra target interaction breaks preservation unless the observer
boundary excludes it.** Read as completing an action, the interaction makes a
block that changes the value of a source formula, so no observation-preserving
functional bisimulation compiles `ready` to the leaky `ready`; and the leak
state is reached by protocol steps without being an administrative descendant
of any compiled state.  Read as external, the same target compiles the
exchange (`boundedBlocks`). -/
theorem interaction_control :
    (∀ map : ObservationBisimulation exchangeGraded visibleGraded,
        map.mapTerm Phase.ready = some .ready → False) ∧
      Relation.ReflTransGen visibleReading.ProtocolStep (some .ready) none ∧
      (∀ phase settled, lowerLeaky phase = settled →
        ¬ Relation.ReflTransGen visibleReading.silent settled none) ∧
      Nonempty (CompiledBlocks exchange leaky boundedReading) := by
  refine ⟨fun map ready => ?_, ?_, ?_, ⟨boundedBlocks⟩⟩
  · have preserved := map.eval_translate unfinishedProbe Phase.ready
    rw [exchange_probe, ready] at preserved
    have translated : map.translate unfinishedProbe = .dia () (.neg (.atom ())) := rfl
    rw [translated, visible_probe] at preserved
    norm_num at preserved
  · have opening : visibleReading.ProtocolStep (some .ready) (some .first) :=
      Or.inl ⟨_, _, rfl, rfl, LoweredStep.opening, by decide⟩
    have leaking : visibleReading.ProtocolStep (some .first) none :=
      Or.inr ⟨(), Or.inr ⟨rfl, rfl⟩⟩
    exact (Relation.ReflTransGen.single opening).tail leaking
  · intro phase settled compiled administrative
    obtain ⟨right, isSome⟩ := leakySilentStar administrative
      (by cases phase <;> exact ⟨_, compiled.symm⟩)
    cases isSome

/-! ## Divergence, deadlock and return -/

/-- A returned state, a stuck administrative state and a silently divergent
one. -/
inductive Ending where
  | returned
  | stuck
  | spinning
  deriving DecidableEq

def endingStep (source target : Ending) : Prop := source = .spinning ∧ target = .spinning

abbrev ending : GSLT.{0} := plainGSLT Ending endingStep

def Ending.finished : Ending → Bool
  | .returned => true
  | _ => false

/-- The block reading: the divergent loop is administrative. -/
def endingReading : BlockReading ending Unit where
  silent := endingStep
  complete _ _ _ := False
  external _ _ := False
  silent_step := fun step => step
  complete_step := fun never => never.elim
  external_step := fun never => never.elim
  classify := fun step => Or.inl step
  silent_resp_left := by
    intro _ _ target equal silences
    exact ⟨target, equal ▸ silences, rfl⟩
  complete_resp_left := fun _ never => never.elim
  complete_resp_right := fun never _ => never.elim

theorem ending_no_block (state target : Ending) : ¬ endingReading.Block () state target := by
  rintro ⟨_, _, never⟩
  exact never

/-- **Blocks see neither divergence nor deadlock**, and they see return only
through an observation that reads it; the primitive reading separates a stuck
state from a divergent one by the discount. -/
theorem ending_control (discount : ℝ) (positive : 0 < discount) (le_one : discount ≤ 1) :
    (endingReading.graded (flagReading Ending endingStep Ending.finished) discount positive.le
        le_one).logicalDistance .stuck .spinning = 0 ∧
      (endingReading.graded (noReadings ending) discount positive.le le_one).logicalDistance
        .returned .stuck = 0 ∧
      (endingReading.graded (flagReading Ending endingStep Ending.finished) discount positive.le
        le_one).logicalDistance .returned .stuck = 1 ∧
      discount ≤ (GradedSystem.stepping ending (noReadings ending) discount positive.le
        le_one).logicalDistance .stuck .spinning := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine GradedSystem.logicalDistance_eq_zero_of_gradedBisimilar _
      ⟨fun first second => Ending.finished first = Ending.finished second,
        ⟨fun _ _ _ _ _ block => (ending_no_block _ _ block).elim,
          fun _ _ _ _ _ block => (ending_no_block _ _ block).elim, ?_⟩, rfl⟩
    intro first second related _
    change (if Ending.finished first then (1 : ℝ) else 0) = if Ending.finished second then 1 else 0
    rw [show Ending.finished first = Ending.finished second from related]
  · exact GradedSystem.logicalDistance_eq_zero_of_gradedBisimilar _
      ⟨fun _ _ => True, ⟨fun _ _ _ _ _ block => (ending_no_block _ _ block).elim,
        fun _ _ _ _ _ block => (ending_no_block _ _ block).elim, fun _ _ _ atom => atom.elim⟩,
        trivial⟩
  · refine le_antisymm (GradedSystem.logicalDistance_le_one _ _ _) ?_
    have probe := (endingReading.graded (flagReading Ending endingStep Ending.finished) discount
      positive.le le_one).abs_eval_sub_le_logicalDistance (.atom ()) .returned .stuck
    change |(if Ending.finished .returned then (1 : ℝ) else 0) -
      (if Ending.finished .stuck then 1 else 0)| ≤ _ at probe
    norm_num [Ending.finished] at probe
    exact probe
  · have probe := (GradedSystem.stepping ending (noReadings ending) discount positive.le
      le_one).abs_eval_sub_le_logicalDistance (.dia () .top) .stuck .spinning
    have stuckSuccessors : (GradedSystem.stepping ending (noReadings ending) discount positive.le
        le_one).successors () .stuck = ∅ := by
      ext target
      simp only [Set.mem_empty_iff_false, iff_false]
      intro step
      change endingStep .stuck target at step
      exact absurd step.1 (by decide)
    have spinningSuccessors : (GradedSystem.stepping ending (noReadings ending) discount
        positive.le le_one).successors () .spinning = {.spinning} := by
      ext target
      constructor
      · intro step
        change endingStep .spinning target at step
        exact step.2
      · rintro rfl
        exact ⟨rfl, rfl⟩
    rw [GradedSystem.eval_dia, GradedSystem.eval_dia, stuckSuccessors, spinningSuccessors,
      Set.image_empty, Set.image_singleton, Real.sSup_empty, csSup_singleton,
      GradedSystem.eval_top] at probe
    norm_num [abs_of_nonneg positive.le] at probe
    exact probe

end Mettapedia.GSLT.Distinction.BlockTransportControls
