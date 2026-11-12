import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.NarrowingToRho

/-!
# Two redexes, one result: reflection makes rho's lifts ambiguous on firings

A forwarder `for(y <- x) x!(*y)` receives a name and sends its drop back on `x`. When the message
it receives is itself a drop of a name, `x!(*n)`, the result is that same message: the continuation
instantiated at `@*n` is `x!(*@*n)`, and the name equation `@*n = n` (`quote_drop`) makes it
`x!(*n)` (`forward_target`).

So the process `x!(*@V) | x!(*@0) | for(y <- x) x!(*y)`, with `V` the visible output and `x = @0`,
has two different communication redexes with the same result `x!(*@V) | x!(*@0)`. On the store
holding its three components (`ambiguous_store`), the channel fragment fires both
(`rho_lifts_not_unique_on_firings`): the two firings consume different bags (`messages_differ`) and
reach stores with the same bag. The narrowing to rho's reduction therefore has lifts unique only up
to heating of their ends, already on rho's own communication. In this example the two results
coincide through reflection: the name equation makes the forwarded message the received one.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.RhoRedexAmbiguity

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open RhoSchema RhoQuotationClassFibres RhoEquationConstructorControls RhoIntrinsicReadback
open RhoScopedParallelInventory RhoScopedConstructorInventory
open ContextualCommunicationProfiles ContextualCommunicationAdequacy ContextualCommunicationPlugging
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (labels)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical
open HeatingBisimulation RhoChannelFragment

local instance : DecidableEq (Process []) := Classical.decEq _

/-- The channel `@0`, in every context. -/
abbrev channel {Γ : Ctx sig} : Term sig Γ Srt.nm := quoteRaw null

/-- The forwarder's continuation `x!(*y)`. -/
abbrev forward : Term sig [Srt.nm] Srt.pr := outputRaw channel (dropRaw (.var .zero))

/-- The payload `*@V`, the drop of the visible output's name. -/
abbrev dropVisible : Term sig [] Srt.pr := dropRaw (quoteRaw RhoSourceOutputPredicate.output)

/-- The payload `*@0`. -/
abbrev dropNull : Term sig [] Srt.pr := dropRaw (quoteRaw null)

/-- **Forwarding a dropped name sends the same message back**: `(x!(*y)){@*n/y} = x!(*n)`. -/
theorem forward_target (name : Term sig [] Srt.nm) :
    (communicationRoot channel (dropRaw name) forward).target =
      outputClass (project channel) (project (dropRaw name)) := by
  rw [communication_target_is_capture_avoiding]
  change project (outputRaw channel (dropRaw (quoteRaw (dropRaw name)))) = _
  rw [← outputClass_project, ← drop_project (quoteRaw (dropRaw name)), ← quote_project (dropRaw name),
    ← drop_project name, quote_drop]

/-- The two messages and the forwarder. -/
abbrev messageVisible : Process [] := outputClass (project channel) (project dropVisible)
abbrev messageNull : Process [] := outputClass (project channel) (project dropNull)
abbrev forwarder : Process [] := inputClass (project channel) (project forward)

abbrev viaVisible := communicationRoot channel dropVisible forward
abbrev viaNull := communicationRoot channel dropNull forward

theorem source_visible : normalized viaVisible.source = {messageVisible} + {forwarder} := by
  rw [communication_source, normalized_join, normalized_output, normalized_input]

theorem source_null : normalized viaNull.source = {messageNull} + {forwarder} := by
  rw [communication_source, normalized_join, normalized_output, normalized_input]

theorem target_visible : normalized viaVisible.target = {messageVisible} := by
  rw [forward_target, normalized_output]

theorem target_null : normalized viaNull.target = {messageNull} := by
  rw [forward_target, normalized_output]

/-- **The two messages differ**: their canonical encodings differ. -/
theorem messages_differ : messageVisible ≠ messageNull := by
  intro equal
  rw [messageVisible, messageNull, outputClass_project, outputClass_project] at equal
  have encoded := congrArg RhoSchema.IntrinsicEncoding.encodeEquationClass equal
  change canonicalize (RhoSchema.IntrinsicEncoding.encodeTerm (outputRaw channel dropVisible)) =
    canonicalize (RhoSchema.IntrinsicEncoding.encodeTerm (outputRaw channel dropNull)) at encoded
  have different : canonicalize (RhoSchema.IntrinsicEncoding.encodeTerm (outputRaw channel dropVisible)) ≠
      canonicalize (RhoSchema.IntrinsicEncoding.encodeTerm (outputRaw channel dropNull)) := by
    decide +kernel
  exact different encoded

theorem sources_differ : normalized viaVisible.source ≠ normalized viaNull.source := by
  rw [source_visible, source_null]
  intro same
  exact messages_differ (Multiset.singleton_inj.mp (add_right_cancel same))

/-- A firing of a given redex from a store whose labels are its source's components beside a frame. -/
theorem fires_redex (root : ContextualCommunicationProfiles.Root RhoScopedParallelEvents.core [])
    (C : Configuration (Process []) (Occurrence [])) (empty : C.equations = [])
    (frame : Multiset (Process []))
    (holds : labels label C.present = frame + normalized root.source) :
    ∃ selection : Selection (Occurrence []),
      selection.Valid (action []) label (instanceRule root) C ∧
      ChannelStep C (selection.result label (instanceRule root) C) ∧
      labels label (selection.result label (instanceRule root) C).present = frame + normalized root.target := by
  have source : labels (PositiveResourceProjection.realized (action []) (action []).identity label) C.present =
      frame + ((instanceRule root).take.map ((action []).apply (action []).identity) : Multiset (Process [])) := by
    rw [realized_identity, map_identity, instance_take, holds]
  have background : (action []).Models (action []).identity C.equations := by
    rw [empty]
    exact (action []).models_nil _
  obtain ⟨selection, valid, solved, target⟩ :=
    PositiveResourceProjection.lift_no_read_frame (action []) (action []).identity label rfl
      IndexedOccurrences.supply (instanceRule root) rfl rfl C background ((action []).models_nil _) frame source
  rw [realized_identity, map_identity, instance_produce] at target
  exact ⟨selection, valid, ⟨instanceRule root, compiled_in_fragment ⟨root, rfl⟩, ⟨selection, valid, rfl⟩, solved⟩,
    target⟩

/-- **The store of the ambiguous process**: both messages and the forwarder. -/
theorem ambiguous_store : ∃ C : Configuration (Process []) (Occurrence []), C.equations = [] ∧
    labels label C.present = {messageVisible} + ({messageNull} + {forwarder}) := by
  obtain ⟨world, realized⟩ := IndexedOccurrences.realize ({messageVisible} + ({messageNull} + {forwarder}))
  exact ⟨⟨[], world⟩, rfl, realized⟩

/-- **Lifts are not unique on firings, on rho's own communication.** From the store of
`x!(*@V) | x!(*@0) | for(y <- x) x!(*y)`, the channel fragment fires the redex of each message; the
two firings consume different bags and reach stores with the same bag. -/
theorem rho_lifts_not_unique_on_firings :
    ∃ C C₁ C₂ : Configuration (Process []) (Occurrence []),
      Represents C (join messageVisible (join messageNull forwarder)) ∧
      ChannelStep C C₁ ∧ ChannelStep C C₂ ∧
      labels label C₁.present = labels label C₂.present ∧
      (∃ s₁ : Selection (Occurrence []), s₁.Valid (action []) label (instanceRule viaVisible) C ∧
        C₁ = s₁.result label (instanceRule viaVisible) C ∧
        labels label s₁.taken.toFinset = normalized viaVisible.source) ∧
      (∃ s₂ : Selection (Occurrence []), s₂.Valid (action []) label (instanceRule viaNull) C ∧
        C₂ = s₂.result label (instanceRule viaNull) C ∧
        labels label s₂.taken.toFinset = normalized viaNull.source) ∧
      normalized viaVisible.source ≠ normalized viaNull.source := by
  obtain ⟨C, empty, holds⟩ := ambiguous_store
  have visibleFrame : labels label C.present = {messageNull} + normalized viaVisible.source := by
    rw [holds, source_visible, add_left_comm]
  have nullFrame : labels label C.present = {messageVisible} + normalized viaNull.source := by
    rw [holds, source_null]
  obtain ⟨s₁, valid₁, step₁, after₁⟩ := fires_redex viaVisible C empty _ visibleFrame
  obtain ⟨s₂, valid₂, step₂, after₂⟩ := fires_redex viaNull C empty _ nullFrame
  have represented : Represents C (join messageVisible (join messageNull forwarder)) := by
    refine ⟨by rw [empty]; exact (action []).models_nil _, ?_⟩
    rw [holds, normalized_join, normalized_join, normalized_output, normalized_output, normalized_input]
  have solved₁ : (action []).Models (action []).identity (s₁.result label (instanceRule viaVisible) C).equations := by
    obtain ⟨_, _, _, models⟩ := step₁
    exact models
  have solved₂ : (action []).Models (action []).identity (s₂.result label (instanceRule viaNull) C).equations := by
    obtain ⟨_, _, _, models⟩ := step₂
    exact models
  refine ⟨C, _, _, represented, step₁, step₂, ?_, ⟨s₁, valid₁, rfl, (NarrowingToRho.lift_footprint valid₁ solved₁).1⟩,
    ⟨s₂, valid₂, rfl, (NarrowingToRho.lift_footprint valid₂ solved₂).1⟩, sources_differ⟩
  rw [after₁, after₂, target_visible, target_null, add_comm]

#print axioms forward_target
#print axioms messages_differ
#print axioms rho_lifts_not_unique_on_firings

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.RhoRedexAmbiguity
