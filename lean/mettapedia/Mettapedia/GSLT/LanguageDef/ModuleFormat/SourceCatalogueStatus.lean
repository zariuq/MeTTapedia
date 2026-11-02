import Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceCatalogue

/-! Malformed native data, unfinished catalogue construction, differing
results and completed agreement are separate public outcomes. Preparation
performs identity/forest validation once before catalogue construction. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceCatalogue

open Mettapedia.GSLT.Parsing
open ClassAwareParserPackCorrespondence ClassAwareParserPackCertificate
open ClassAwareNativeForestFamilyCompleteness ClassAwareNativeForestParserCompleteness ClassAwarePackedForest

structure Request where
  forest : Forest
  input : List Nat
  root : NodeKey
  native : List Certificate

def prepare? (spec : Portable.SyntaxDescription) (input : String)
    (forestBytes identityBytes : List UInt8) (packets : List SourcePacket.Packet) : Option Request := do
  let plan ← SourceSyntaxExport.plan? spec
  let snapshot ← ClassAwareNativeForestWire.decodeSnapshot? forestBytes
  let identity ← ClassAwareNativeForestIdentityWire.decodeSnapshot? identityBytes
  let view ← snapshot.completedView?
  if view.codepoints != input.toList.map Char.toNat then none else do
    let inventory ← identity.resolveInventory? plan
    if !validateExactFamilyRepresentation view inventory spec.profile plan then none else do
      let native ← certificates? plan view.codepoints packets
      some ⟨decodedForestData view inventory spec.profile, view.codepoints,
        ⟨plan.lexical.startSort, 0, view.codepoints.length⟩, native⟩

def Request.run? (request : Request) (filters : List SourceSyntax.FamilyFilter) (rounds : Nat) : Option Bool :=
  ClassAwareCatalogueValidation.validate? request.forest (SourcePacketSelection.allows filters request.input)
    request.root rounds request.native

theorem prepared_agrees {spec : Portable.SyntaxDescription} {input : String}
    {forestBytes identityBytes : List UInt8} {packets : List SourcePacket.Packet} {request : Request}
    (prepared : prepare? spec input forestBytes identityBytes packets = some request)
    (filters : List SourceSyntax.FamilyFilter) (rounds : Nat) :
    validate? spec filters input forestBytes identityBytes packets rounds = request.run? filters rounds := by
  unfold prepare? at prepared
  obtain ⟨plan, compiled, rest⟩ := Option.bind_eq_some_iff.mp prepared
  obtain ⟨snapshot, forestRead, rest⟩ := Option.bind_eq_some_iff.mp rest
  obtain ⟨identity, identityRead, rest⟩ := Option.bind_eq_some_iff.mp rest
  obtain ⟨view, viewed, rest⟩ := Option.bind_eq_some_iff.mp rest
  split at rest
  · cases rest
  · rename_i scalarValid
    obtain ⟨inventory, resolved, rest⟩ := Option.bind_eq_some_iff.mp rest
    split at rest
    · cases rest
    · rename_i forestValid
      obtain ⟨native, decoded, same⟩ := Option.bind_eq_some_iff.mp rest
      cases Option.some.inj same
      simp only [validate?, compiled, forestRead, identityRead, viewed, Bind.bind, Option.bind,
        scalarValid, resolved, forestValid, decoded, Request.run?]
      rfl

inductive Status where
  | invalid
  | pending
  | different
  | complete
  deriving DecidableEq, Repr

def check (spec : Portable.SyntaxDescription) (filters : List SourceSyntax.FamilyFilter) (input : String)
    (forestBytes identityBytes : List UInt8) (packets : List SourcePacket.Packet) (rounds : Nat) : Status :=
  match prepare? spec input forestBytes identityBytes packets with
  | none => .invalid
  | some request => match request.run? filters rounds with
      | none => .pending
      | some false => .different
      | some true => .complete

theorem complete_sound {spec : Portable.SyntaxDescription} {filters : List SourceSyntax.FamilyFilter} {input : String}
    {forestBytes identityBytes : List UInt8} {packets : List SourcePacket.Packet} {rounds : Nat}
    (accepted : check spec filters input forestBytes identityBytes packets rounds = .complete) :
    validate? spec filters input forestBytes identityBytes packets rounds = some true := by
  unfold check at accepted
  cases prepared : prepare? spec input forestBytes identityBytes packets with
  | none => simp [prepared] at accepted
  | some request =>
    rw [prepared_agrees prepared]
    cases result : request.run? filters rounds with
    | none => simp [prepared, result] at accepted
    | some value => cases value <;> simp_all

theorem pending_has_valid_inputs {spec : Portable.SyntaxDescription} {filters : List SourceSyntax.FamilyFilter}
    {input : String} {forestBytes identityBytes : List UInt8} {packets : List SourcePacket.Packet} {rounds : Nat}
    (pending : check spec filters input forestBytes identityBytes packets rounds = .pending) :
    ∃ request, prepare? spec input forestBytes identityBytes packets = some request ∧ request.run? filters rounds = none := by
  unfold check at pending
  cases prepared : prepare? spec input forestBytes identityBytes packets with
  | none => simp [prepared] at pending
  | some request =>
    cases result : request.run? filters rounds with
    | none => exact ⟨request, rfl, result⟩
    | some value => cases value <;> simp [prepared, result] at pending

theorem complete_iff {spec : Portable.SyntaxDescription} {filters : List SourceSyntax.FamilyFilter} {input : String}
    {forestBytes identityBytes : List UInt8} {packets : List SourcePacket.Packet} {rounds : Nat} :
    check spec filters input forestBytes identityBytes packets rounds = .complete ↔
      validate? spec filters input forestBytes identityBytes packets rounds = some true := by
  constructor
  · exact complete_sound
  · intro accepted
    unfold validate? at accepted
    obtain ⟨plan, compiled, rest⟩ := Option.bind_eq_some_iff.mp accepted
    obtain ⟨snapshot, forestRead, rest⟩ := Option.bind_eq_some_iff.mp rest
    obtain ⟨identity, identityRead, rest⟩ := Option.bind_eq_some_iff.mp rest
    obtain ⟨view, viewed, rest⟩ := Option.bind_eq_some_iff.mp rest
    split at rest
    · cases rest
    · rename_i scalarValid
      obtain ⟨inventory, resolved, rest⟩ := Option.bind_eq_some_iff.mp rest
      split at rest
      · cases rest
      · rename_i forestValid
        obtain ⟨native, decoded, finished⟩ := Option.bind_eq_some_iff.mp rest
        simp only [check, prepare?, compiled, forestRead, identityRead, viewed, Bind.bind, Option.bind,
          scalarValid, resolved, forestValid, decoded]
        change (match Request.run? _ filters rounds with
          | none => Status.pending | some false => Status.different | some true => Status.complete) = .complete
        dsimp only [Request.run?]
        rw [finished]

#print axioms complete_iff
#print axioms pending_has_valid_inputs
#print axioms prepared_agrees
#print axioms complete_sound

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceCatalogue
