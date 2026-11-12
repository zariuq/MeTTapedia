import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaOccurrenceOverlay
import Mettapedia.Languages.MeTTa.PeTTa.DestinationRefinement

/-!
# Typed phases transport positional obligations on the existing host

The semantic return obligation is a parameter. Its local protection,
frame-update and inner-return laws suffice for the actual argument and body
guard continuations below. Variable and compound return instances discharge
these laws separately; no source or native execution equality is assumed.

Row capture is separate: compound data requires a real callable-head test.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSelectedFrameTransport

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open EagerDFS.Destination
open PettaOccurrenceOverlay

structure Laws {User : Type} (Held : Nat → Work User → Prop) : Prop where
  extendOrigins : ∀ {index : Nat} {control : DControl} {context : Context User} {origins : List Nat},
    Held index (control, context, origins) → ∀ suffix,
      Held index (control, context, origins ++ suffix)
  protect : ∀ {index : Nat} {item : Work User}, Held index item →
    ∀ (operations : Services User) (source : State User),
      Held index (PettaOccurrenceOverlay.protect operations source item.1 item.2.1, item.2)
  update : ∀ {index : Nat} (control : DControl) (context : Context User) (origins : List Nat)
      (frame : CallFrame) (rest : List CallFrame),
    Held (index + 1) (control, context, origins) → context.calls = frame :: rest →
    ∀ (after : DControl) (updated : CallFrame),
      RefinementTransport.Extends control.bindings after.bindings →
      updated.callerGoals = frame.callerGoals → updated.callerDestination = frame.callerDestination →
      Held (index + 1) (after, {context with calls := updated :: rest}, origins)
  pop : ∀ {index : Nat} (control : DControl) (context : Context User) (origins : List Nat)
      (frame : CallFrame) (rest : List CallFrame),
    Held (index + 1) (control, context, origins) → context.calls = frame :: rest →
      Held index (resumeCaller control frame, {context with calls := rest}, origins)

def Replaces {User : Type} (Held : Nat → Work User → Prop) (index : Nat)
    (source : State User) (current : Scope User) (parents : List (Scope User))
    (pending : List (Work User)) (reply : Step User) : Prop :=
  (∃ request, reply = .call request source) ∨
    ∃ generated, reply = .silent (install source current parents generated pending) ∧
      ∀ item ∈ generated, Held index item

theorem next_argument {User : Type} {Held : Nat → Work User → Prop} (laws : Laws Held) {index : Nat}
    (operations : Services User) (source : State User) (current : Scope User) (parents : List (Scope User))
    (control : DControl) (context : Context User) (origins : List Nat) (pending : List (Work User))
    (frame : CallFrame) (rest : List CallFrame)
    (held : Held (index + 1) (control, context, origins)) (calls : context.calls = frame :: rest) :
    Replaces Held (index + 1) source current parents pending
      (nextArgument operations source current parents control context origins pending frame rest) := by
  cases remaining : frame.remaining with
  | nil =>
    simp only [nextArgument, remaining]
    refine .inr ⟨_, rfl, ?_⟩
    intro item member
    cases List.mem_singleton.mp member
    exact laws.protect (laws.update control context origins frame rest held calls
      {control with goals := [.invoke frame.head frame.ready frame.callDestination], destination := frame.callDestination}
      {frame with remaining := [], phase := .body} (.refl _) rfl rfl) operations source
  | cons parameter unprocessed =>
    rcases parameter with ⟨formal, value⟩
    by_cases raw : demand formal = .raw
    · simp only [nextArgument, remaining, if_pos raw]
      refine .inr ⟨_, rfl, ?_⟩
      intro item member
      cases List.mem_singleton.mp member
      exact laws.protect (laws.update control context origins frame rest held calls control
        {frame with remaining := unprocessed, ready := frame.ready ++ [value], index := frame.index + 1}
        (.refl _) rfl rfl) operations source
    · simp only [nextArgument, remaining, if_neg raw]
      refine .inr ⟨_, rfl, ?_⟩
      intro item member
      cases List.mem_singleton.mp member
      let prepared := PettaOccurrenceOverlay.protect operations source control context
      let slot := Atom.var (freshName prepared 0)
      exact laws.protect (laws.update control context origins frame rest held calls
        {prepared with goals := [.evaluate value slot], destination := slot}
        {frame with remaining := unprocessed, phase := .argument formal slot} (.refl _) rfl rfl) operations source

theorem argument_continuations {User : Type} {Held : Nat → Work User → Prop} (laws : Laws Held) {index : Nat}
    (operations : Services User) (source : State User) (control : DControl) (context : Context User)
    (origins : List Nat) (frame : CallFrame) (rest : List CallFrame) (slot : Atom) (stores : List Store)
    (held : Held (index + 1) (control, context, origins)) (calls : context.calls = frame :: rest) :
    ∀ item ∈ argumentContinuations operations source control context origins frame rest slot stores,
      Held (index + 1) item := by
  intro item member
  obtain ⟨⟨store, occurrence⟩, _present, rfl⟩ := List.mem_map.mp member
  exact laws.protect
    (laws.update control context (origins ++ [occurrence]) frame rest (laws.extendOrigins held [occurrence]) calls control
      {frame with ready := frame.ready ++ [slot], store := store, index := frame.index + 1, phase := .nextArgument}
      (.refl _) rfl rfl) operations source

theorem argument_guard {User : Type} {Held : Nat → Work User → Prop} (laws : Laws Held) {index : Nat}
    (operations : Services User) (source : State User) (current : Scope User) (parents : List (Scope User))
    (control : DControl) (context : Context User) (origins : List Nat) (pending : List (Work User))
    (frame : CallFrame) (rest : List CallFrame) (formal : Ty String) (slot value : Atom)
    (held : Held (index + 1) (control, context, origins)) (calls : context.calls = frame :: rest) :
    Replaces Held (index + 1) source current parents pending
      (consumeArgument operations source current parents control context origins pending frame rest formal slot value) := by
  unfold consumeArgument
  split
  · exact .inl ⟨_, rfl⟩
  · exact .inr ⟨_, rfl, argument_continuations laws operations source control context origins frame rest slot _ held calls⟩

theorem body_guard {User : Type} {Held : Nat → Work User → Prop} (laws : Laws Held) {index : Nat}
    (operations : Services User) (source : State User) (current : Scope User) (parents : List (Scope User))
    (control : DControl) (context : Context User) (origins : List Nat) (pending : List (Work User))
    (frame : CallFrame) (rest : List CallFrame) (value : Atom)
    (held : Held (index + 1) (control, context, origins)) (calls : context.calls = frame :: rest) :
    Replaces Held index source current parents pending
      (consumeBody operations source current parents control context origins pending frame rest value) := by
  unfold consumeBody
  split
  · exact .inl ⟨_, rfl⟩
  · refine .inr ⟨_, rfl, ?_⟩
    intro item member
    obtain ⟨⟨_store, occurrence⟩, _present, rfl⟩ := List.mem_map.mp member
    exact laws.protect (laws.pop control context (origins ++ [occurrence]) frame rest
      (laws.extendOrigins held [occurrence]) calls) operations source

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSelectedFrameTransport
