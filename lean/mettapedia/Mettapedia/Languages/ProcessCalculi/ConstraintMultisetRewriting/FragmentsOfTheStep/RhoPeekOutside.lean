import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.RhoChannelFragment
import Mettapedia.OSLF.Syntax.RhoScopedChannelSeparation

/-!
# A receive that keeps its message is not rho

A **peek** receives a message without consuming it (a read in the step's vocabulary; Linda's `rd`).
On the step it is a rule that takes the receiver and reads the message, so it lies just outside the
channel-communication fragment (`peek_outside`). It is not rho: from the store of
`x!(0) | for(y <- x) 0`, the peek leaves the message in place, while the only rho step from that
process consumes the message and the receiver together and leaves nothing (`peek_not_rho`).
Representation is therefore not a bisimulation for the peek rule set, and the restriction under which
the step is rho excludes reads, as it excludes absence.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.RhoPeekOutside

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open RhoSchema RhoQuotationClassFibres RhoEquationConstructorControls RhoIntrinsicReadback
open RhoScopedParallelInventory RhoScopedConstructorInventory RhoIntrinsicCanonicalBag
open RhoScopedInstanceReadout (receive receive_project)
open ContextualCommunicationProfiles ContextualCommunicationAdequacy
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (labels Enabled fire labels_fire)
open HeatingBisimulation TransitionMaps RhoChannelFragment

local instance : DecidableEq (Process []) := Classical.decEq _

/-- The channel `@0`. -/
abbrev channelName : Name [] := project (quoteRaw null)
/-- The message `x!(0)`. -/
abbrev message : Process [] := outputClass channelName (zero [])
/-- The discarding continuation `0`, under the received name. -/
abbrev discard : Process [Srt.nm] := project null
/-- The receiver `for(y <- x) 0`. -/
abbrev receiver : Process [] := inputClass channelName discard

/-- **The peek**: take the receiver, read the message, make the continuation's components (none). -/
def peek : RuleInstance (Process []) := ⟨[receiver], [message], [], [], []⟩

def peekRules : RuleSet (Process []) := (· = peek)

/-- The peek reads, so it is just outside the channel-communication fragment. -/
theorem peek_outside : ¬ ChannelCommunication peek := by
  rintro ⟨noReads, _⟩
  simp [peek] at noReads

/-- The step of the peek rule set at the identity. -/
abbrev PeekStep := RuleStep (action []) label (action []).identity peekRules

def world : Finset (Occurrence []) := {((0 : ℕ), message), ((1 : ℕ), receiver)}

def start : Configuration (Process []) (Occurrence []) := ⟨[], world⟩

theorem start_labels : labels label start.present = {message} + {receiver} := by
  have notIn : ((0 : ℕ), message) ∉ ({((1 : ℕ), receiver)} : Finset (Occurrence [])) := by simp
  change (insert ((0 : ℕ), message) {((1 : ℕ), receiver)} : Finset (Occurrence [])).val.map label = _
  rw [Finset.insert_val_of_notMem notIn]
  simp [label, IndexedOccurrences.label]

theorem start_represents : Represents start (join message receiver) := by
  refine ⟨(action []).models_nil _, ?_⟩
  rw [start_labels, normalized_join, normalized_output, normalized_input]

def peekAt : Selection (Occurrence []) := ⟨[((1 : ℕ), receiver)], [((0 : ℕ), message)], []⟩

theorem peek_solved : (action []).Models (action []).identity (peekAt.problem label peek start) := by
  intro e member
  simp [Selection.problem, Selection.equations, peekAt, peek, start, label, IndexedOccurrences.label]
    at member
  rcases member with rfl | rfl <;> exact rfl

theorem peek_valid : peekAt.Valid (action []) label peek start := by
  refine ⟨by simp [peekAt], by simp [peekAt], rfl, rfl, rfl, ⟨?_, ?_, ?_, ?_, ?_⟩,
    ⟨(action []).identity, peek_solved⟩, ?_⟩
  · intro o member
    simp [peekAt, Selection.commit] at member
    subst member
    simp [start, world]
  · intro o member
    simp [peekAt, Selection.commit] at member
    subst member
    simp [start, world]
  · simp [peekAt, Selection.commit]
  · simp [peekAt, Selection.commit]
  · intro query member
    simp [Selection.commit] at member
  · intro c member
    simp [peek] at member

theorem peek_step : PeekStep start (peekAt.result label peek start) :=
  ⟨peek, rfl, ⟨peekAt, peek_valid, rfl⟩, peek_solved⟩

/-- **The peek keeps the message.** -/
theorem after_labels : labels label (peekAt.result label peek start).present = {message} := by
  change labels label (fire start.present (peekAt.commit (T := Process []))) = _
  rw [labels_fire peek_valid.occurrences, start_labels]
  have taken : labels label (peekAt.commit (T := Process [])).taken = {receiver} := by
    simp [peekAt, Selection.commit, labels, label, IndexedOccurrences.label]
  have made : labels label (peekAt.commit (T := Process [])).made = 0 := by
    simp [peekAt, Selection.commit, labels]
  rw [taken, made, add_zero, add_tsub_cancel_right]

theorem output_ne_input {name name' : Name []} {payload : Process []} {body : Process [Srt.nm]} :
    outputClass name payload ≠ inputClass name' body := by
  intro same
  have read := congrArg components same
  rw [output_components, input_components] at read
  exact RhoScopedChannelSeparation.output_not_input _ _ (Multiset.singleton_inj.mp read)

theorem normalized_zero : normalized (zero []) = (0 : Multiset (Process [])) := by
  simp [normalized, read_zero]

/-- **The peek is not rho**: representation is not a bisimulation for the peek rule set. -/
theorem peek_not_rho : ¬ IsBisimulation PeekStep RhoStep Represents := by
  rintro ⟨forward, _⟩
  obtain ⟨after, event, represented⟩ := forward start_represents peek_step
  have afterBag : normalized after = {message} := represented.2.symm.trans after_labels
  obtain ⟨root, surrounding, sourceShape, targetShape⟩ :=
    (RhoScopedParallelEvents.step_iff_root_surrounding _ _).mp event
  obtain ⟨name, payload, body, source, target⟩ := core_root_shape root
  have bags : ({message} + {receiver} : Multiset (Process [])) =
      ({outputClass name payload} + {inputClass name body}) + normalized surrounding := by
    have read := congrArg normalized sourceShape
    rw [normalized_join, normalized_output, normalized_input, normalized_join, source, normalized_join,
      normalized_output, normalized_input] at read
    exact read
  have emptySurrounding : normalized surrounding = 0 := by
    have counted := congrArg Multiset.card bags
    simp only [Multiset.card_add, Multiset.card_singleton] at counted
    exact Multiset.card_eq_zero.mp (by omega)
  rw [emptySurrounding, add_zero] at bags
  have outputMember : outputClass name payload ∈ ({message} + {receiver} : Multiset (Process [])) := by
    rw [bags]
    simp
  have inputMember : inputClass name body ∈ ({message} + {receiver} : Multiset (Process [])) := by
    rw [bags]
    simp
  have outputIs : outputClass name payload = message := by
    rcases Multiset.mem_add.mp outputMember with here | there
    · exact Multiset.mem_singleton.mp here
    · exact absurd (Multiset.mem_singleton.mp there) output_ne_input
  have inputIs : inputClass name body = receiver := by
    rcases Multiset.mem_add.mp inputMember with here | there
    · exact absurd (Multiset.mem_singleton.mp here).symm output_ne_input
    · exact Multiset.mem_singleton.mp there
  have payloadIs : payload = zero [] := by
    have read := congrArg components outputIs
    rw [output_components, output_components] at read
    exact congrArg Prod.snd (outputPattern_injective [] (Multiset.singleton_inj.mp read))
  have bodyIs : body = discard := by
    have read := congrArg components inputIs
    rw [input_components, input_components] at read
    exact congrArg Prod.snd (inputPattern_injective [] (Multiset.singleton_inj.mp read))
  have targetZero : root.target = zero [] := by
    rw [target, payloadIs, bodyIs]
    change receive (quote (project null)) (project null) = project null
    rw [quote_project, receive_project]
    rfl
  have targetBag := congrArg normalized targetShape
  rw [normalized_join, targetZero, normalized_zero, emptySurrounding, add_zero, afterBag] at targetBag
  exact Multiset.singleton_ne_zero _ targetBag

#print axioms peek_outside
#print axioms after_labels
#print axioms peek_not_rho

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.RhoPeekOutside
