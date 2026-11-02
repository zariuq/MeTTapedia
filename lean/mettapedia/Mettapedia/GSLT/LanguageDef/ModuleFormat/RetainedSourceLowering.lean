import Mettapedia.GSLT.LanguageDef.ModuleFormat.SourcePacketCertificate

/-! Compose a checked retained syntax core with an existing language's
source elaboration. Printing consumes syntax data, and execution consumes the
lowered value. This adapter proves neither the source elaboration's semantics
nor complete native parser/selection coverage. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.RetainedSourceLowering

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.Parsing.LanguageDefScalarPrinter (stringScalars)
open ScalarSyntaxCore

structure Retained (α : Type) where
  sourceCore : Pattern
  lowered : α

/-- Advance the interpretation while retaining the original source syntax.
The continuation sees the previous IR, not a reparsed packet. -/
def continueWith {α β : Type} (next : α → Except String β)
    (input : Except String (Retained α)) : Except String (Retained β) :=
  match input with
  | .error reason => .error reason
  | .ok retained => match next retained.lowered with
    | .error reason => .error reason
    | .ok value => .ok ⟨retained.sourceCore, value⟩

theorem continueWith_ok_iff {α β : Type} (next : α → Except String β)
    (input : Except String (Retained α)) (output : Retained β) :
    continueWith next input = .ok output ↔
      ∃ retained, input = .ok retained ∧ next retained.lowered = .ok output.lowered ∧
        retained.sourceCore = output.sourceCore := by
  cases input with
  | error reason => simp [continueWith]
  | ok retained =>
      cases h : next retained.lowered <;> cases output <;> simp [continueWith, h, Retained.mk.injEq, and_comm]

theorem continueWith_comp {α β γ : Type} (first : α → Except String β)
    (second : β → Except String γ) (input : Except String (Retained α)) :
    continueWith second (continueWith first input) =
      continueWith (fun value => (first value).bind second) input := by
  cases input with
  | error reason => rfl
  | ok retained => cases h : first retained.lowered <;> simp [continueWith, h, Except.bind]

def lower {α : Type} (description : Description) (parser : Parser description) (shape : Shape description)
    (elaborate : String → SourcePacket.Packet → Except String α)
    (input : String) (packet : SourcePacket.Packet) : Except String (Retained α) :=
  match SourcePacketCertificate.core? description parser shape (stringScalars input) description.profile.startSort packet with
  | none => .error "selected source packet failed independent certificate replay"
  | some core =>
    match elaborate input packet with
    | .error reason => .error reason
    | .ok value => .ok ⟨core, value⟩

/-- Staged IR lowering and fused lowering agree, including the first error.
Independent source replay is performed only at entry. -/
theorem lower_then {α β : Type} (description : Description) (parser : Parser description)
    (shape : Shape description) (elaborate : String → SourcePacket.Packet → Except String α)
    (next : α → Except String β) (input : String) (packet : SourcePacket.Packet) :
    continueWith next (lower description parser shape elaborate input packet) =
      lower description parser shape (fun text tree => (elaborate text tree).bind next) input packet := by
  unfold lower
  dsimp only
  cases SourcePacketCertificate.core? description parser shape (stringScalars input)
    description.profile.startSort packet with
  | none => rfl
  | some core =>
    cases h : elaborate input packet with
    | error reason => rfl
    | ok value => simp only [Except.bind, continueWith]

theorem lower_readback {α : Type} {description : Description} {parser : Parser description} {shape : Shape description}
    {elaborate : String → SourcePacket.Packet → Except String α} {input : String} {packet : SourcePacket.Packet}
    {retained : Retained α} (accepted : lower description parser shape elaborate input packet = .ok retained) :
    SourcePacketCertificate.core? description parser shape (stringScalars input) description.profile.startSort packet =
        some retained.sourceCore ∧ elaborate input packet = .ok retained.lowered := by
  unfold lower at accepted
  cases parsed : SourcePacketCertificate.core? description parser shape (stringScalars input) description.profile.startSort packet with
  | none => simp [parsed] at accepted
  | some core =>
    cases compiled : elaborate input packet with
    | error reason => simp [parsed, compiled] at accepted
    | ok value =>
      simp only [parsed, compiled, Except.ok.injEq] at accepted
      cases accepted
      exact ⟨rfl, rfl⟩

theorem lower_prints {α : Type} {description : Description} {parser : Parser description} {shape : Shape description}
    {elaborate : String → SourcePacket.Packet → Except String α} {input : String} {packet : SourcePacket.Packet}
    {retained : Retained α} (accepted : lower description parser shape elaborate input packet = .ok retained) :
    printText? description description.profile.startSort retained.sourceCore = some input := by
  have scalars := SourcePacketCertificate.core?_prints (lower_readback accepted).1
  unfold printText?
  rw [scalars]
  simp [stringScalars, List.map_map, Function.comp_def]

#print axioms lower_readback
#print axioms lower_prints

end Mettapedia.GSLT.LanguageDef.ModuleFormat.RetainedSourceLowering
