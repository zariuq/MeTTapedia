import Mettapedia.Languages.MeTTa.SpaceTheory.ModuleTheories

/-!
# A native first-order forwarding rule

One authored definition matches a send and a receiver at the same
literal channel. Its only body is the captured datum. The two channel
positions contain the same metavariable; they are not two independent
matches, or an invocation of a channel-name interpreter.

The ambient operation consumes the two matched occurrences and puts
back the datum, leaving the rest of the multiset alone.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.SpaceTheory.FirstOrderForwarding

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.OSLFCore.Bridge
open Mettapedia.OSLF.MeTTaIL.Match (Bindings matchPattern matchArgs mergeBindings applyBindings)

def send (channel datum : Atom) : Atom := .expression [.symbol "send", channel, datum]
def wait (channel : Atom) : Atom := .expression [.symbol "forward", channel]
def request (offered waiting : Atom) : Atom := .expression [.symbol "communicate", offered, waiting]

def lhs : Atom := request (send (.var "c") (.var "payload")) (wait (.var "c"))
def declaration : Atom := .expression [.symbol "=", lhs, .var "payload"]

private def captured (channel datum : Atom) : Bindings :=
  [("payload", GroundData.encode datum), ("c", GroundData.encode channel)]

private theorem fields (pattern values : List Atom) :
    matchPattern (GroundData.schema (.expression pattern)) (GroundData.encode (.expression values)) =
      matchArgs (GroundData.schemaList pattern) (GroundData.encodeList values) := by
  simp [GroundData.schema, GroundData.encode, matchPattern, matchArgs, mergeBindings]

private theorem matchVariable (name : String) (value : Atom) :
    matchPattern (GroundData.schema (.var name)) (GroundData.encode value) =
      [[(name, GroundData.encode value)]] := by simp [GroundData.schema, matchPattern]

private theorem tagCommunicate :
    matchPattern (GroundData.schema (.symbol "communicate")) (GroundData.encode (.symbol "communicate")) = [[]] := by
  decide +kernel

private theorem tagSend :
    matchPattern (GroundData.schema (.symbol "send")) (GroundData.encode (.symbol "send")) = [[]] := by
  decide +kernel

private theorem tagForward :
    matchPattern (GroundData.schema (.symbol "forward")) (GroundData.encode (.symbol "forward")) = [[]] := by
  decide +kernel

private theorem matches_pair (offered waiting datum : Atom) :
    matchPattern (GroundData.schema lhs) (GroundData.encode (request (send offered datum) (wait waiting))) =
      if offered = waiting then [captured offered datum] else [] := by
  by_cases same : offered = waiting
  · subst waiting
    simp [lhs, request, send, wait, fields, matchVariable, GroundData.schemaList, GroundData.encodeList,
      matchArgs, mergeBindings, tagCommunicate, tagSend, tagForward, captured]
  · have unequal : GroundData.encode offered ≠ GroundData.encode waiting :=
      fun eq => same (GroundData.encode_injective eq)
    simp [lhs, request, send, wait, fields, matchVariable, GroundData.schemaList, GroundData.encodeList,
      matchArgs, mergeBindings, tagCommunicate, tagSend, tagForward, same, unequal]

private theorem instantiated_payload (channel datum : Atom) :
    GroundData.decode (applyBindings (captured channel datum) (GroundData.schema (.var "payload"))) =
      some datum := by
  change GroundData.decode (applyBindings (captured channel datum) (.fvar "payload")) = some datum
  simpa only [captured, applyBindings, List.find?_cons, beq_self_eq_true] using GroundData.decode_encode datum

theorem one_definition_matches_iff (offered waiting datum returned : Atom) :
    ModuleTheories.InstanceOf declaration (request (send offered datum) (wait waiting)) returned ↔
      offered = waiting ∧ returned = datum := by
  unfold ModuleTheories.InstanceOf
  change (∃ first second, Atoms.Content.definition lhs (.var "payload") = .definition first second ∧
    ∃ binding ∈ matchPattern (GroundData.schema first)
        (GroundData.encode (request (send offered datum) (wait waiting))),
      GroundData.decode (applyBindings binding (GroundData.schema second)) = some returned) ↔ _
  constructor
  · rintro ⟨first, second, written, match_, listed, output⟩
    obtain ⟨rfl, rfl⟩ := Atoms.Content.definition.inj written
    rw [matches_pair] at listed
    split at listed
    · rename_i same
      obtain rfl := List.mem_singleton.mp listed
      rw [instantiated_payload] at output
      exact ⟨same, (Option.some.inj output).symm⟩
    · cases listed
  · rintro ⟨same, result⟩
    subst waiting
    subst returned
    refine ⟨lhs, .var "payload", rfl, captured offered datum, ?_, instantiated_payload _ _⟩
    simp [matches_pair]

def Step (before after : Multiset Atom) : Prop :=
  ∃ offered waiting datum returned : Atom, ∃ frame : Multiset Atom,
    before = {send offered datum} + {wait waiting} + frame ∧
    ModuleTheories.InstanceOf declaration (request (send offered datum) (wait waiting)) returned ∧
    after = {returned} + frame

theorem step_exact (before after : Multiset Atom) :
    Step before after ↔
      ∃ channel datum : Atom, ∃ frame : Multiset Atom,
        before = {send channel datum} + {wait channel} + frame ∧ after = {datum} + frame := by
  constructor
  · rintro ⟨offered, waiting, datum, returned, frame, source, matched, target⟩
    obtain ⟨rightChannel, rightPayload⟩ := (one_definition_matches_iff _ _ _ _).mp matched
    subst waiting
    subst returned
    exact ⟨offered, datum, frame, source, target⟩
  · rintro ⟨channel, datum, frame, source, target⟩
    exact ⟨channel, channel, datum, datum, frame, source, (one_definition_matches_iff _ _ _ _).mpr ⟨rfl, rfl⟩, target⟩

theorem duplicated_send_consumes_only_one (channel datum : Atom) :
    Step ({send channel datum} + {wait channel} + {send channel datum}) ({datum} + {send channel datum}) := by
  exact (step_exact _ _).mpr ⟨channel, datum, {send channel datum}, rfl, rfl⟩

theorem different_channel_fails {offered waiting datum returned : Atom} (different : offered ≠ waiting) :
    ¬ModuleTheories.InstanceOf declaration (request (send offered datum) (wait waiting)) returned :=
  fun derives => different ((one_definition_matches_iff _ _ _ _).mp derives).1

end Mettapedia.Languages.MeTTa.SpaceTheory.FirstOrderForwarding
