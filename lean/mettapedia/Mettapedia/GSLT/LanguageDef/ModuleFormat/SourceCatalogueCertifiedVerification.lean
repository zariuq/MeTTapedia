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

/-- Worklist events and chart rounds granted for an allowance. The closure
stops when its worklist empties and the chart at its first fixed point, so a
generous bound costs nothing on inputs that finish early. -/
def fuel (rounds : Nat) : Nat := 4194304 * (rounds + 1)
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

/-! ### Admission stages

Each stage either refuses, stays pending, or hands its result to the rest of
admission. Later stages run only when the earlier ones pass. -/

def afterInventory (resolved : Option Inventory) (rest : Inventory → Option Bool) : Option Bool :=
  match resolved with
  | none => some false
  | some inventory => rest inventory

def afterRepresentation (represented : Bool) (rest : Unit → Option Bool) : Option Bool :=
  if represented then rest () else some false

def afterCertificates (certified : Option (List ClassAwareParserPackCertificate.Certificate))
    (rest : List ClassAwareParserPackCertificate.Certificate → Option Bool) :
    Option Bool :=
  match certified with
  | none => some false
  | some native => rest native

def afterCoverage (covered : Option Bool) (rest : Unit → Option Bool) : Option Bool :=
  match covered with
  | none => none
  | some false => some false
  | some true => rest ()

theorem afterInventory_true {resolved : Option Inventory} {rest : Inventory → Option Bool}
    (accepted : afterInventory resolved rest = some true) :
    ∃ inventory, resolved = some inventory ∧ rest inventory = some true := by
  cases resolved with
  | none => simp [afterInventory] at accepted
  | some inventory => exact ⟨inventory, rfl, accepted⟩

theorem afterRepresentation_true {represented : Bool} {rest : Unit → Option Bool}
    (accepted : afterRepresentation represented rest = some true) :
    represented = true ∧ rest () = some true := by
  cases represented with
  | false => simp [afterRepresentation] at accepted
  | true => exact ⟨rfl, accepted⟩

theorem afterCertificates_true {certified : Option (List ClassAwareParserPackCertificate.Certificate)}
    {rest : List ClassAwareParserPackCertificate.Certificate → Option Bool}
    (accepted : afterCertificates certified rest = some true) :
    ∃ native, certified = some native ∧ rest native = some true := by
  cases certified with
  | none => simp [afterCertificates] at accepted
  | some native => exact ⟨native, rfl, accepted⟩

theorem afterCoverage_true {covered : Option Bool} {rest : Unit → Option Bool}
    (accepted : afterCoverage covered rest = some true) :
    covered = some true ∧ rest () = some true := by
  cases covered with
  | none => simp [afterCoverage] at accepted
  | some value =>
    cases value with
    | false => simp [afterCoverage] at accepted
    | true => exact ⟨rfl, accepted⟩

/-- The shared stages of admission once the forest view is decoded: the
representation check, packet certificates and decoded families are computed
once and serve both the coverage and the catalogue checks. -/
def admitView? (spec : Portable.SyntaxDescription) (filters : List SourceSyntax.FamilyFilter)
    (plan : ClassAwareParserPackCorrespondence.CompiledParserPackPlan)
    (table : ClassAwareNativeForestIdentityWire.Snapshot)
    (view : ClassAwareNativeForestWire.NativeForestView) (packets : List SourcePacket.Packet)
    (rounds : Nat) : Option Bool :=
  afterInventory (table.resolveInventory? plan) fun inventory =>
  afterRepresentation (validateExactFamilyRepresentationFrontier view inventory spec.profile plan) fun _ =>
  afterCertificates (SourceCatalogue.certificates? plan view.codepoints packets) fun native =>
  let decoded := decodedForestData view inventory spec.profile
  afterCoverage (ClassAwareChartCertificate.coverageAt? spec.profile plan view.codepoints decoded
      (fuel rounds) (chartRounds rounds)) fun _ =>
  ClassAwareForestCatalogueIndexed.validateIndexed? decoded
    (SourcePacketSelection.allows filters view.codepoints)
    ⟨plan.lexical.startSort, 0, view.codepoints.length⟩ (chartRounds rounds) native

theorem admitView?_true {spec : Portable.SyntaxDescription} {filters : List SourceSyntax.FamilyFilter}
    {plan : ClassAwareParserPackCorrespondence.CompiledParserPackPlan}
    {table : ClassAwareNativeForestIdentityWire.Snapshot}
    {view : ClassAwareNativeForestWire.NativeForestView} {packets : List SourcePacket.Packet}
    {rounds : Nat} (accepted : admitView? spec filters plan table view packets rounds = some true) :
    ∃ inventory, table.resolveInventory? plan = some inventory ∧
      validateExactFamilyRepresentationFrontier view inventory spec.profile plan = true ∧
      ∃ native, SourceCatalogue.certificates? plan view.codepoints packets = some native ∧
        ClassAwareChartCertificate.coverageAt? spec.profile plan view.codepoints
          (decodedForestData view inventory spec.profile) (fuel rounds) (chartRounds rounds) = some true ∧
        ClassAwareForestCatalogueIndexed.validateIndexed? (decodedForestData view inventory spec.profile)
          (SourcePacketSelection.allows filters view.codepoints)
          ⟨plan.lexical.startSort, 0, view.codepoints.length⟩ (chartRounds rounds) native = some true := by
  obtain ⟨inventory, resolved, accepted⟩ := afterInventory_true accepted
  obtain ⟨represented, accepted⟩ := afterRepresentation_true accepted
  obtain ⟨native, certified, accepted⟩ := afterCertificates_true accepted
  obtain ⟨covered, accepted⟩ := afterCoverage_true accepted
  exact ⟨inventory, resolved, represented, native, certified, covered, accepted⟩

/-- Admission in one pass, with the checks and their order of `check`,
`complete?` and `catalogue?`. -/
def verify? (spec : Portable.SyntaxDescription) (filters : List SourceSyntax.FamilyFilter)
    (input : String) (forest identity : List UInt8) (packets : List SourcePacket.Packet)
    (rounds : Nat) : Option Bool :=
  match SourceSyntaxExport.plan? spec, ClassAwareNativeForestWire.decodeSnapshot? forest,
      ClassAwareNativeForestIdentityWire.decodeSnapshot? identity with
  | some plan, some snapshot, some table =>
    match snapshot.completedView? with
    | none => some false
    | some view =>
      if view.codepoints != input.toList.map Char.toNat then some false
      else admitView? spec filters plan table view packets rounds
  | _, _, _ => some false

theorem verify?_sound (spec : Portable.SyntaxDescription) (filters : List SourceSyntax.FamilyFilter)
    (input : String) (forest identity : List UInt8) (packets : List SourcePacket.Packet) (rounds : Nat)
    (verified : verify? spec filters input forest identity packets rounds = some true) :
    complete? spec input forest identity rounds = some true ∧
      SourceCatalogue.validate? spec filters input forest identity packets (chartRounds rounds) = some true := by
  unfold verify? at verified
  split at verified
  · rename_i plan snapshot table hp hf hi
    split at verified
    · exact absurd verified (by simp)
    · rename_i view hv
      split at verified
      · exact absurd verified (by simp)
      · rename_i matched
        have same : view.codepoints = input.toList.map Char.toNat := by
          simpa [bne_iff_ne] using matched
        obtain ⟨inventory, resolved, represented, native, certified, covered, catalogued⟩ :=
          admitView?_true verified
        constructor
        · unfold complete?
          rw [hp, hf, hi]
          dsimp only
          rw [hv]
          dsimp only
          rw [if_pos (by simp [same])]
          unfold ClassAwareChartCertificate.validate?
          rw [resolved]
          dsimp only
          rw [if_pos represented]
          exact covered
        · rw [← catalogue?_eq]
          unfold catalogue?
          rw [hp, hf, hi]
          simp only [Option.bind_eq_bind, Option.bind_some]
          rw [hv]
          simp only [Option.bind_some]
          rw [if_neg (by simp [same]), resolved]
          simp only [Option.bind_some]
          rw [if_neg (by simp [represented]), certified]
          simp only [Option.bind_some]
          exact catalogued
  · exact absurd verified (by simp)

#print axioms complete?_sound
#print axioms verify?_sound
#print axioms check_eq
#print axioms catalogue?_eq

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceCatalogueCertifiedVerification
