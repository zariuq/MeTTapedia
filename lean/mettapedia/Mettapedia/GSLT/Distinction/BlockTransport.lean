import Mettapedia.GSLT.Distinction.Isometry
import Mettapedia.GSLT.Core.OperationalRealizationAccounts

/-!
# Metric transport at compilation blocks

A compiler may lower one source event to several target steps: a binary
communication becomes four unary ones.  A metric that discounts every
primitive target step sees that delay, so a compiler preserves behavioural
distance only for a declared reading of target execution in blocks.

* **A block reading** (`BlockReading`) classifies each primitive step of the
  target, a GSLT with its own independently defined steps, as administrative
  (silent), as completing a labelled action, or as an external interaction
  outside the observed protocol.  It is a reading of the target's steps; it is
  not defined from source transitions.
* **Blocks** (`BlockReading.Block`): finitely many administrative steps, then
  one completing step.  The endpoint is the actual target state after
  completion.  Blocks are the labelled steps of a system over the target
  (`BlockReading.blockSystem`), which carries the target's own graded
  observations (`BlockReading.graded`).  A reflexive–transitive closure of the
  primitive steps is not a block: it has no completing step and no label.
* **What blocks observe.**  Completed actions with their endpoints, and what
  the declared observations read there.  They do not observe administrative
  divergence or administrative deadlock: a block that never completes is no
  block at all.  Successful return is observed only through an observation
  that reads it.  The controls in `BlockTransportControls` prove each of these.
* **The compiler interface** (`CompiledBlocks`).  A path-valued
  `OperationalRealization` whose realized source steps are blocks
  (`IsBlock`), the reflection of every target block leaving a compiled state,
  and the reflection of every primitive protocol prefix to a source run plus
  administrative steps.  The realization's existing `blockAccount` counts the
  primitive communications; the metric does not.
* **Transport** (`CompiledBlocks.transport`): such a compilation, with the
  graded readings preserved, is an observation-preserving functional
  bisimulation from the source's stepping system to the target's block system,
  so logical and behavioural distances transport
  (`CompiledBlocks.logicalDistance_eq`, `CompiledBlocks.behaviouralDistance_eq`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Distinction

open Mettapedia.GSLT
open Mettapedia.GSLT.HennessyMilner
open Mettapedia.GSLT.IndexedOperational

universe uS uT uL uO uO'

/-- A **block reading** of a target GSLT: each primitive step is administrative,
completes a labelled action, or is an external interaction outside the
observed protocol. -/
structure BlockReading (T : GSLT.{uT}) (Label : Type uL) where
  /-- Administrative steps, silent to the observer. -/
  silent : T.Term → T.Term → Prop
  /-- Steps that complete a labelled action. -/
  complete : Label → T.Term → T.Term → Prop
  /-- Interactions outside the observed protocol. -/
  external : T.Term → T.Term → Prop
  silent_step : ∀ {term term'}, silent term term' → T.Step term term'
  complete_step : ∀ {label term term'}, complete label term term' → T.Step term term'
  external_step : ∀ {term term'}, external term term' → T.Step term term'
  /-- Every primitive step is read. -/
  classify : ∀ {term term'}, T.Step term term' →
    silent term term' ∨ (∃ label, complete label term term') ∨ external term term'
  silent_resp_left : ∀ {term other term'}, T.Equiv term other → silent term term' →
    ∃ other', silent other other' ∧ T.Equiv term' other'
  complete_resp_left : ∀ {label term other term'}, T.Equiv term other →
    complete label term term' → ∃ other', complete label other other' ∧ T.Equiv term' other'
  complete_resp_right : ∀ {label term term' other'}, complete label term term' →
    T.Equiv term' other' → complete label term other'

namespace BlockReading

variable {T : GSLT.{uT}} {Label : Type uL} (B : BlockReading T Label)

/-- A step of the observed protocol: administrative or completing. -/
def ProtocolStep (term term' : T.Term) : Prop :=
  B.silent term term' ∨ ∃ label, B.complete label term term'

/-- **A block**: finitely many administrative steps, then one completing step. -/
def Block (label : Label) (term term' : T.Term) : Prop :=
  ∃ middle, Relation.ReflTransGen B.silent term middle ∧ B.complete label middle term'

theorem administrative_resp_left {term other middle : T.Term} (equivalent : T.Equiv term other)
    (administrative : Relation.ReflTransGen B.silent term middle) :
    ∃ middle', Relation.ReflTransGen B.silent other middle' ∧ T.Equiv middle middle' := by
  induction administrative with
  | refl => exact ⟨other, .refl, equivalent⟩
  | tail _ last inductionHypothesis =>
      obtain ⟨middle', administrative', close⟩ := inductionHypothesis
      obtain ⟨next, silentNext, closeNext⟩ := B.silent_resp_left close last
      exact ⟨next, administrative'.tail silentNext, closeNext⟩

/-- **The block system** of a reading: its labelled steps are blocks. -/
abbrev blockSystem : System.{0, uL} T where
  Atom := Empty
  observes atom _ := atom.elim
  observes_resp atom := atom.elim
  Label := Label
  act := B.Block
  act_resp_left := by
    rintro label term other target equivalent ⟨middle, administrative, completing⟩
    obtain ⟨middle', administrative', close⟩ := B.administrative_resp_left equivalent administrative
    obtain ⟨target', completing', closeTarget⟩ := B.complete_resp_left close completing
    exact ⟨target', ⟨middle', administrative', completing'⟩, closeTarget⟩
  act_resp_right := by
    rintro label term target target' ⟨middle, administrative, completing⟩ equivalent
    exact ⟨middle, administrative, B.complete_resp_right completing equivalent⟩

/-- The block system with the target's own graded observations. -/
noncomputable abbrev graded (observations : GradedObservations.{uT, uO} T) (discount : ℝ)
    (discount_nonneg : 0 ≤ discount) (discount_le_one : discount ≤ 1) :
    GradedSystem.{uT, 0, uL, uO} T where
  dynamics := B.blockSystem
  observations := observations
  discount := discount
  discount_nonneg := discount_nonneg
  discount_le_one := discount_le_one

/-- A primitive execution path is **one block** for a label: administrative
steps, then one completing step, with nothing after it. -/
inductive IsBlock (label : Label) : {term term' : T.Term} → ExecutionPath T term term' → Prop where
  | complete {term term' : T.Term} (step : T.Step term term') (completes : B.complete label term term') :
      IsBlock label (.cons ⟨step⟩ (.refl term'))
  | silent {term middle term' : T.Term} (step : T.Step term middle) (silences : B.silent term middle)
      {rest : ExecutionPath T middle term'} :
      IsBlock label rest → IsBlock label (.cons ⟨step⟩ rest)

/-- A primitive path that is one block is a block transition. -/
theorem IsBlock.block {label : Label} {term term' : T.Term} {path : ExecutionPath T term term'}
    (isBlock : B.IsBlock label path) : B.Block label term term' := by
  induction isBlock with
  | complete step completes => exact ⟨_, .refl, completes⟩
  | silent step silences rest inductionHypothesis =>
      obtain ⟨middle, administrative, completing⟩ := inductionHypothesis
      exact ⟨middle, Relation.ReflTransGen.head silences administrative, completing⟩

end BlockReading

/-! ## The compiler interface -/

/-- **What a compiler supplies for block transport**, from a source GSLT read by
its own steps to a target with a block reading:

* a path-valued realization whose realized source steps are single blocks;
* the reflection of every target block leaving a compiled state to a source
  step whose compiled endpoint is equated with the block's endpoint;
* the reflection of every primitive protocol prefix leaving a compiled state to
  a source run followed by administrative steps from its compiled endpoint.

The realization is the compiler's existing execution object; its
`blockAccount` counts the primitive communications. -/
structure CompiledBlocks (S : GSLT.{uS}) (T : GSLT.{uT}) (B : BlockReading T Unit) where
  realization : OperationalRealization S T
  realizedBlocks : ∀ {term term' : S.Term} (step : S.Step term term'),
    B.IsBlock () (realization.mapStep step)
  reflectBlock : ∀ {term : S.Term} {target' : T.Term},
    B.Block () (realization.mapTerm term) target' →
      ∃ target, S.Step term target ∧ T.Equiv (realization.mapTerm target) target'
  prefixReflection : ∀ {term : S.Term} {target' : T.Term},
    Relation.ReflTransGen B.ProtocolStep (realization.mapTerm term) target' →
      ∃ target, Relation.ReflTransGen S.Step term target ∧
        ∃ settled, T.Equiv (realization.mapTerm target) settled ∧
          Relation.ReflTransGen B.silent settled target'

namespace CompiledBlocks

variable {S : GSLT.{uS}} {T : GSLT.{uT}} {B : BlockReading T Unit}
  (compiled : CompiledBlocks S T B) (observations : GradedObservations.{uS, uO} S)
  (observations' : GradedObservations.{uT, uO'} T) {discount : ℝ}
  (discount_nonneg : 0 ≤ discount) (discount_le_one : discount ≤ 1)

/-- **Block transport**: with the graded readings preserved, a compilation is
an observation-preserving functional bisimulation from the source's stepping
system to the target's block system. -/
def transport (atom : observations.Atom → observations'.Atom)
    (value_map : ∀ observation term,
      observations'.value (atom observation) (compiled.realization.mapTerm term) =
        observations.value observation term) :
    ObservationBisimulation (GradedSystem.stepping S observations discount discount_nonneg
        discount_le_one)
      (B.graded observations' discount discount_nonneg discount_le_one) where
  mapTerm := compiled.realization.mapTerm
  mapEquiv := compiled.realization.mapEquiv
  atom := atom
  label := id
  discount_eq := rfl
  value_map := value_map
  mapAct _ _ _ step := (compiled.realizedBlocks step).block
  liftAct _ _ _ block := compiled.reflectBlock block

/-- **Logical distances transport through the blocks.** -/
theorem logicalDistance_eq (atom : observations.Atom → observations'.Atom)
    (value_map : ∀ observation term,
      observations'.value (atom observation) (compiled.realization.mapTerm term) =
        observations.value observation term)
    (atomSurjective : Function.Surjective atom) (left right : S.Term) :
    (B.graded observations' discount discount_nonneg discount_le_one).logicalDistance
        (compiled.realization.mapTerm left) (compiled.realization.mapTerm right) =
      (GradedSystem.stepping S observations discount discount_nonneg
        discount_le_one).logicalDistance left right :=
  (compiled.transport observations observations' discount_nonneg discount_le_one atom
    value_map).logicalDistance_map atomSurjective (fun label => ⟨label, rfl⟩) left right

/-- **Behavioural distances transport through the blocks**, under finite
branching of the source. -/
theorem behaviouralDistance_eq (atom : observations.Atom → observations'.Atom)
    (value_map : ∀ observation term,
      observations'.value (atom observation) (compiled.realization.mapTerm term) =
        observations.value observation term)
    (atomSurjective : Function.Surjective atom)
    (finite : (GradedSystem.stepping S observations discount discount_nonneg
      discount_le_one).dynamics.ImageFiniteModulo)
    (left right : S.Term) :
    (B.graded observations' discount discount_nonneg discount_le_one).behaviouralDistance
        (compiled.realization.mapTerm left) (compiled.realization.mapTerm right) =
      (GradedSystem.stepping S observations discount discount_nonneg
        discount_le_one).behaviouralDistance left right :=
  (compiled.transport observations observations' discount_nonneg discount_le_one atom
    value_map).behaviouralDistance_map atomSurjective (fun label => ⟨label, rfl⟩) finite left right

/-- The communication count of a source run is the length of its realized
target run, in the realization's existing account. -/
theorem blockAccount_eq {term term' : S.Term} (path : ExecutionPath S term term') :
    compiled.realization.blockAccount.of path =
      Multiplicative.ofAdd (compiled.realization.mapRoute path).length :=
  rfl

end CompiledBlocks

end Mettapedia.GSLT.Distinction
