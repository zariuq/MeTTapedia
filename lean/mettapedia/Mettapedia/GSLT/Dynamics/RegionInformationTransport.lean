import Mettapedia.GSLT.Dynamics.RegionInformationCoding

/-!
# Composing observer-sufficient information interfaces

An admitted operation translates each output question into an input question
and a checked answer readout. It therefore descends to semantic classes and
can run between their finite interface codes. Decoding failure remains
failure; composition does not invent an arbitrary state for an unused code.

The carrier is the existing future-observation quotient. This module adds
its operation transport, not another semantics or interpreter. Actual input
arrival, revision changes and resource publication require their own source
operations and stability evidence.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.RegionInformationTransport

open RegionObservations
open Mettapedia.InformationTheory.FiniteInterfaceCoding

universe u v w

structure Transport {Source Target : Type u}
    (input : Family.{u, v, w} Source) (output : Family.{u, v, w} Target) where
  run : Source → Target
  pullback : output.Question → input.Question
  readout : (question : output.Question) → input.Answer (pullback question) → output.Answer question
  exact : ∀ question state, readout question (input.read (pullback question) state) = output.read question (run state)

namespace Transport

variable {Source Target Next : Type u}
variable {input : Family.{u, v, w} Source} {output : Family.{u, v, w} Target}
variable {final : Family.{u, v, w} Next}

theorem equivalent (transport : Transport input output) {left right : Source}
    (same : input.Equivalent left right) : output.Equivalent (transport.run left) (transport.run right) := by
  intro question
  rw [← transport.exact question left, ← transport.exact question right, same (transport.pullback question)]

def classes (transport : Transport input output) : input.Classes → output.Classes :=
  Quotient.lift (fun state => output.classOf (transport.run state))
    (fun _ _ same => (output.classOf_eq_iff _ _).mpr (transport.equivalent same))

theorem classes_exact (transport : Transport input output) (state : Source) :
    transport.classes (input.classOf state) = output.classOf (transport.run state) := rfl

def comp (first : Transport input output) (later : Transport output final) : Transport input final where
  run state := later.run (first.run state)
  pullback question := first.pullback (later.pullback question)
  readout question value := later.readout question (first.readout (later.pullback question) value)
  exact question state := by rw [first.exact, later.exact]

theorem classes_comp (first : Transport input output) (later : Transport output final)
    (value : input.Classes) : (first.comp later).classes value = later.classes (first.classes value) := by
  induction value using Quotient.inductionOn with
  | h state => rfl

/-- The intermediate information is decoded as a semantic class, not an
invented concrete state or a replay of the original source computation. -/
noncomputable def throughCodes (transport : Transport input output) {inputBits outputBits : Nat}
    (sourceCode : Code input.Classes inputBits) (targetCode : Code output.Classes outputBits) :
    Word inputBits → Option (Word outputBits) :=
  fun word => (sourceCode.decode word).map (fun cls => targetCode.encode (transport.classes cls))

theorem throughCodes_exact (transport : Transport input output) {inputBits outputBits : Nat}
    (sourceCode : Code input.Classes inputBits) (targetCode : Code output.Classes outputBits)
    (state : Source) :
    transport.throughCodes sourceCode targetCode (sourceCode.encode (input.classOf state)) =
      some (targetCode.encode (output.classOf (transport.run state))) := by
  simp only [throughCodes, sourceCode.roundtrip, Option.map_some, classes_exact]

theorem unused_input_stays_refused (transport : Transport input output) {inputBits outputBits : Nat}
    (sourceCode : Code input.Classes inputBits) (targetCode : Code output.Classes outputBits)
    (word : Word inputBits) (missing : sourceCode.decode word = none) :
    transport.throughCodes sourceCode targetCode word = none := by
  simp [throughCodes, missing]

theorem throughCodes_comp (first : Transport input output) (later : Transport output final)
    {inputBits middleBits finalBits : Nat} (sourceCode : Code input.Classes inputBits)
    (middleCode : Code output.Classes middleBits) (finalCode : Code final.Classes finalBits)
    (word : Word inputBits) :
    (first.throughCodes sourceCode middleCode word).bind (later.throughCodes middleCode finalCode) =
      (first.comp later).throughCodes sourceCode finalCode word := by
  cases found : sourceCode.decode word with
  | none => simp [throughCodes, found]
  | some value => simp [throughCodes, found, middleCode.roundtrip, classes_comp]

/-- The reachable output class space cannot exceed the input class space.
An operation may have a larger globally possible target type, so its whole
target space is not substituted for this reachable image. -/
theorem reachable_card_bound (transport : Transport input output) [Finite input.Classes] :
    Nat.card (Set.range transport.classes) ≤ Nat.card input.Classes :=
  Nat.card_le_card_of_surjective _ (Set.rangeFactorization_surjective)

theorem all_target_classes_reached (transport : Transport input output)
    (onto : Function.Surjective transport.run) : Function.Surjective transport.classes := by
  intro target
  induction target using Quotient.inductionOn with
  | h state =>
      obtain ⟨source, rfl⟩ := onto state
      exact ⟨input.classOf source, rfl⟩

theorem onto_budget_bound (transport : Transport input output) [Finite input.Classes]
    (onto : Function.Surjective transport.run) :
    RegionInformationCoding.requiredBits output ≤ RegionInformationCoding.requiredBits input := by
  apply Nat.clog_mono_right 2
  exact Nat.card_le_card_of_surjective _ (transport.all_target_classes_reached onto)

end Transport

namespace Controls

open RegionObservations.Controls

def complementVisible : Transport stateAndHidden stateAndHidden where
  run state := (!state.1, state.2)
  pullback question := question
  readout _ answer := !answer
  exact _ _ := rfl

theorem complement_composes_without_hidden_data (state : Bool × Bool) :
    (complementVisible.comp complementVisible).classes (stateAndHidden.classOf state) =
      stateAndHidden.classOf state := by
  simp [Transport.classes_exact, Transport.comp, complementVisible]

/-- A future operation that exposes the discarded field cannot be admitted
under the smaller observation interface. -/
theorem swapping_hidden_into_visible_is_not_admitted :
    ¬∃ transport : Transport stateAndHidden stateAndHidden, transport.run = Prod.swap := by
  rintro ⟨transport, swapped⟩
  have same : stateAndHidden.Equivalent (false, false) (false, true) := fun _ => rfl
  have result := transport.equivalent same ()
  rw [swapped] at result
  exact Bool.false_ne_true result

end Controls

end Mettapedia.GSLT.Dynamics.RegionInformationTransport
