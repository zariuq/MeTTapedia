import Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceCatalogue

/-! Execution admission checks whole-input forest coverage before the
selected catalogue. Unfinished independent construction remains pending;
only two successful checks admit execution. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceCatalogueVerification

def verify? (spec : Portable.SyntaxDescription) (filters : List SourceSyntax.FamilyFilter)
    (input : String) (forest identity : List UInt8) (packets : List SourcePacket.Packet)
    (rounds : Nat) : Option Bool :=
  if !SourceSyntaxForest.check spec input forest identity then some false else
    match SourceSyntaxExport.plan? spec with
    | none => some false
    | some plan =>
      if (SourceCatalogue.certificates? plan (input.toList.map Char.toNat) packets).isNone then some false else
        match SourceSyntaxForest.complete? spec input forest identity rounds with
        | none => none
        | some false => some false
        | some true => SourceCatalogue.validate? spec filters input forest identity packets rounds

theorem verify?_sound (spec : Portable.SyntaxDescription) (filters : List SourceSyntax.FamilyFilter)
    (input : String) (forest identity : List UInt8) (packets : List SourcePacket.Packet) (rounds : Nat)
    (verified : verify? spec filters input forest identity packets rounds = some true) :
    SourceSyntaxForest.complete? spec input forest identity rounds = some true ∧
      SourceCatalogue.validate? spec filters input forest identity packets rounds = some true := by
  unfold verify? at verified
  split at verified
  · cases verified
  · rename_i represented
    cases plan : SourceSyntaxExport.plan? spec with
    | none => simp [plan] at verified
    | some plan =>
      simp only [plan] at verified
      split at verified
      · cases verified
      · rename_i certificates
        cases complete : SourceSyntaxForest.complete? spec input forest identity rounds with
        | none => simp [complete] at verified
        | some result =>
          cases result with
          | false => simp [complete] at verified
          | true => exact ⟨rfl, by simpa only [complete] using verified⟩

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceCatalogueVerification
