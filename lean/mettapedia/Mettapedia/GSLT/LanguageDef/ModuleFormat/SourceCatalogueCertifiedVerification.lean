import Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceCatalogueVerification
import Mettapedia.GSLT.Parsing.ClassAwareChartCertificate
import Mettapedia.GSLT.Parsing.ClassAwareForestCatalogueIndexed

/-! Execution admission with warm-started whole-input coverage. The checks and
their order are those of `SourceCatalogueVerification.verify?`; only the
coverage reference chart starts from the forest under test instead of the
empty state. The allowance bounds the worklist and the chart rounds;
exhausting either is unfinished. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceCatalogueCertifiedVerification

open Mettapedia.GSLT.Parsing
open ClassAwareNativeForestContract ClassAwareNativeForestIdentityInventory
open ClassAwareNativeForestFamilyWitness ClassAwareNativeForestQualification
open ClassAwareNativeForestFamilyCompleteness ClassAwareNativeForestReachabilityFrontier
open ClassAwareNativeForestParserCompleteness

/-- Worklist steps and chart rounds granted for an allowance. A chart stops at
its first fixed point, so a generous round bound costs nothing when the
warm-started chart converges early. -/
def fuel (rounds : Nat) : Nat := 65536 * (rounds + 1)
def chartRounds (rounds : Nat) : Nat := 1024 * (rounds + 1)

def complete? (spec : Portable.SyntaxDescription) (input : String)
    (forestBytes identityBytes : List UInt8) (rounds : Nat) : Option Bool :=
  match SourceSyntaxExport.plan? spec,
      ClassAwareNativeForestWire.decodeSnapshot? forestBytes,
      ClassAwareNativeForestIdentityWire.decodeSnapshot? identityBytes with
  | some plan, some snapshot, some identity =>
    match snapshot.completedView? with
    | some view =>
      if view.codepoints == input.toList.map Char.toNat then
        ClassAwareChartCertificate.validate? identity view spec.profile plan (fuel rounds) (chartRounds rounds)
      else some false
    | none => some false
  | _, _, _ => some false

theorem complete?_sound {spec : Portable.SyntaxDescription} {input : String}
    {forestBytes identityBytes : List UInt8} {rounds : Nat}
    (accepted : complete? spec input forestBytes identityBytes rounds = some true) :
    ∃ plan snapshot identity view, ∃ inventory : Inventory,
      SourceSyntaxExport.plan? spec = some plan ∧
      ClassAwareNativeForestWire.decodeSnapshot? forestBytes = some snapshot ∧
      ClassAwareNativeForestIdentityWire.decodeSnapshot? identityBytes = some identity ∧
      snapshot.completedView? = some view ∧
      view.codepoints = input.toList.map Char.toNat ∧
      identity.resolveInventory? plan = some inventory ∧
      ∃ inputs : RootedFamilyDecodingInputs view inventory spec.profile plan,
        ParserCompleteRepresentation view inventory spec.profile plan
          (decodedForest inputs.families (enumerateFamilyWitnesses view)) := by
  unfold complete? at accepted
  cases hp : SourceSyntaxExport.plan? spec with
  | none => simp [hp] at accepted
  | some plan =>
    cases hf : ClassAwareNativeForestWire.decodeSnapshot? forestBytes with
    | none => simp [hp, hf] at accepted
    | some snapshot =>
      cases hi : ClassAwareNativeForestIdentityWire.decodeSnapshot? identityBytes with
      | none => simp [hp, hf, hi] at accepted
      | some identity =>
        cases hv : snapshot.completedView? with
        | none => simp [hp, hf, hi, hv] at accepted
        | some view =>
          simp only [hp, hf, hi, hv] at accepted
          split at accepted
          · rename_i same
            obtain ⟨inventory, resolves, inputs, complete⟩ := ClassAwareChartCertificate.validate?_sound accepted
            exact ⟨plan, snapshot, identity, view, inventory, rfl, rfl, rfl, hv,
              by simpa only [beq_iff_eq] using same, resolves, inputs, complete⟩
          · cases accepted

/-- `SourceSyntaxForest.check` with the representation check over frontier rounds. -/
def check (spec : Portable.SyntaxDescription) (input : String)
    (forestBytes identityBytes : List UInt8) : Bool :=
  match SourceSyntaxExport.plan? spec,
      ClassAwareNativeForestWire.decodeSnapshot? forestBytes,
      ClassAwareNativeForestIdentityWire.decodeSnapshot? identityBytes with
  | some plan, some snapshot, some identity =>
      match snapshot.completedView? with
      | some view => view.codepoints == input.toList.map Char.toNat &&
          match identity.resolveInventory? plan with
          | none => false
          | some inventory => validateExactFamilyRepresentationFrontier view inventory spec.profile plan
      | none => false
  | _, _, _ => false

theorem check_eq (spec : Portable.SyntaxDescription) (input : String)
    (forestBytes identityBytes : List UInt8) :
    check spec input forestBytes identityBytes = SourceSyntaxForest.check spec input forestBytes identityBytes := by
  unfold check SourceSyntaxForest.check validateResolvedExactFamilyRepresentation
  simp only [validateExactFamilyRepresentationFrontier_eq]
  rfl

/-- `SourceCatalogue.validate?` with the representation check over frontier rounds. -/
def catalogue? (spec : Portable.SyntaxDescription) (filters : List SourceSyntax.FamilyFilter) (input : String)
    (forestBytes identityBytes : List UInt8) (packets : List SourcePacket.Packet) (rounds : Nat) : Option Bool := do
  let plan ← SourceSyntaxExport.plan? spec
  let snapshot ← ClassAwareNativeForestWire.decodeSnapshot? forestBytes
  let identity ← ClassAwareNativeForestIdentityWire.decodeSnapshot? identityBytes
  let view ← snapshot.completedView?
  if view.codepoints != input.toList.map Char.toNat then some false else do
    let inventory ← identity.resolveInventory? plan
    if !validateExactFamilyRepresentationFrontier view inventory spec.profile plan then some false else do
      let native ← SourceCatalogue.certificates? plan view.codepoints packets
      let forest := decodedForestData view inventory spec.profile
      ClassAwareForestCatalogueIndexed.validateIndexed? forest (SourcePacketSelection.allows filters view.codepoints)
        ⟨plan.lexical.startSort, 0, view.codepoints.length⟩ rounds native

theorem catalogue?_eq (spec : Portable.SyntaxDescription) (filters : List SourceSyntax.FamilyFilter)
    (input : String) (forestBytes identityBytes : List UInt8) (packets : List SourcePacket.Packet)
    (rounds : Nat) :
    catalogue? spec filters input forestBytes identityBytes packets rounds =
      SourceCatalogue.validate? spec filters input forestBytes identityBytes packets rounds := by
  unfold catalogue? SourceCatalogue.validate?
  simp only [validateExactFamilyRepresentationFrontier_eq, ClassAwareForestCatalogueIndexed.validateIndexed?_eq]

def verify? (spec : Portable.SyntaxDescription) (filters : List SourceSyntax.FamilyFilter)
    (input : String) (forest identity : List UInt8) (packets : List SourcePacket.Packet)
    (rounds : Nat) : Option Bool :=
  if !check spec input forest identity then some false else
    match SourceSyntaxExport.plan? spec with
    | none => some false
    | some plan =>
      if (SourceCatalogue.certificates? plan (input.toList.map Char.toNat) packets).isNone then some false else
        match complete? spec input forest identity rounds with
        | none => none
        | some false => some false
        | some true => catalogue? spec filters input forest identity packets (chartRounds rounds)

theorem verify?_sound (spec : Portable.SyntaxDescription) (filters : List SourceSyntax.FamilyFilter)
    (input : String) (forest identity : List UInt8) (packets : List SourcePacket.Packet) (rounds : Nat)
    (verified : verify? spec filters input forest identity packets rounds = some true) :
    complete? spec input forest identity rounds = some true ∧
      SourceCatalogue.validate? spec filters input forest identity packets (chartRounds rounds) = some true := by
  unfold verify? at verified
  split at verified
  · cases verified
  · cases plan : SourceSyntaxExport.plan? spec with
    | none => simp [plan] at verified
    | some plan =>
      simp only [plan] at verified
      split at verified
      · cases verified
      · cases complete : complete? spec input forest identity rounds with
        | none => simp [complete] at verified
        | some result =>
          cases result with
          | false => simp [complete] at verified
          | true => exact ⟨rfl, by simpa only [complete, catalogue?_eq] using verified⟩

#print axioms complete?_sound
#print axioms verify?_sound
#print axioms check_eq
#print axioms catalogue?_eq

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceCatalogueCertifiedVerification
