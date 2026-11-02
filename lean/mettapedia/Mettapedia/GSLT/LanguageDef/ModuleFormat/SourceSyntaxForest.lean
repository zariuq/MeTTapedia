import Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceSyntaxExport
import Mettapedia.GSLT.Parsing.ClassAwareNativeForestQualification
import Mettapedia.GSLT.Parsing.ClassAwareNativeForestWire
import Mettapedia.GSLT.Parsing.ClassAwareChartCoverage

/-! Resolve a live native forest against the authored source grammar. Exact
representation and independent whole-input completeness are separate checks;
the latter can remain pending while its reference chart is constructed. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceSyntaxForest

open Mettapedia.GSLT.Parsing
open ClassAwareNativeForestContract ClassAwareNativeForestIdentityInventory
open ClassAwareNativeForestFamilyWitness ClassAwareNativeForestQualification

def check (spec : Portable.SyntaxDescription) (input : String)
    (forestBytes identityBytes : List UInt8) : Bool :=
  match SourceSyntaxExport.plan? spec,
      ClassAwareNativeForestWire.decodeSnapshot? forestBytes,
      ClassAwareNativeForestIdentityWire.decodeSnapshot? identityBytes with
  | some plan, some snapshot, some identity =>
      match snapshot.completedView? with
      | some view => view.codepoints == input.toList.map Char.toNat &&
          validateResolvedExactFamilyRepresentation identity view spec.profile plan
      | none => false
  | _, _, _ => false

theorem check_sound {spec : Portable.SyntaxDescription} {input : String}
    {forestBytes identityBytes : List UInt8}
    (accepted : check spec input forestBytes identityBytes = true) :
    ∃ plan snapshot identity view, ∃ inventory : Inventory,
      SourceSyntaxExport.plan? spec = some plan ∧
      ClassAwareNativeForestWire.decodeSnapshot? forestBytes = some snapshot ∧
      ClassAwareNativeForestIdentityWire.decodeSnapshot? identityBytes = some identity ∧
      snapshot.completedView? = some view ∧
      view.codepoints = input.toList.map Char.toNat ∧
      identity.resolveInventory? plan = some inventory ∧
      ∃ inputs : RootedFamilyDecodingInputs view inventory spec.profile plan,
        Represents view inventory.toTable spec.profile view.codepoints
          (decodedForest inputs.families (enumerateFamilyWitnesses view)) := by
  unfold check at accepted
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
          simp only [hp, hf, hi, hv, Bool.and_eq_true, beq_iff_eq] at accepted
          rcases validateResolvedExactFamilyRepresentation_sound accepted.2 with
            ⟨inventory, resolves, inputs, represents⟩
          exact ⟨plan, snapshot, identity, view, inventory, rfl, rfl, rfl, hv,
            accepted.1, resolves, inputs, represents⟩

def complete? (spec : Portable.SyntaxDescription) (input : String)
    (forestBytes identityBytes : List UInt8) (rounds : Nat) : Option Bool :=
  match SourceSyntaxExport.plan? spec,
      ClassAwareNativeForestWire.decodeSnapshot? forestBytes,
      ClassAwareNativeForestIdentityWire.decodeSnapshot? identityBytes with
  | some plan, some snapshot, some identity =>
    match snapshot.completedView? with
    | some view =>
      if view.codepoints == input.toList.map Char.toNat then
        ClassAwareChartCoverage.validate? identity view spec.profile plan rounds
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
            obtain ⟨inventory, resolves, inputs, complete⟩ := ClassAwareChartCoverage.validate?_sound accepted
            exact ⟨plan, snapshot, identity, view, inventory, rfl, rfl, rfl, hv,
              by simpa only [beq_iff_eq] using same, resolves, inputs, complete⟩
          · cases accepted

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceSyntaxForest
