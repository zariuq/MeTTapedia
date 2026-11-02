import Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceSyntaxForest
import Mettapedia.GSLT.Parsing.LanguageDefScalarSyntax

/-! Native whole-input completeness reaches the original authored grammar,
not just the compiled parser plan. Each source derivation retains its CST
and its physical occurrence certificate in the checked native forest. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceSyntaxCoverage

open Mettapedia.GSLT.Parsing
open ClassAwareParserPackCorrespondence ClassAwareParserPackCertificate
open ClassAwareNativeForestContract ClassAwareNativeForestIdentityInventory
open ClassAwareNativeForestFamilyWitness ClassAwareNativeForestQualification
open ClassAwarePackedForest PresentationExprSemantics

theorem authored_covered {spec : Portable.SyntaxDescription} {input : String}
    {forestBytes identityBytes : List UInt8} {rounds : Nat}
    (accepted : SourceSyntaxForest.complete? spec input forestBytes identityBytes rounds = some true) :
    ∃ plan snapshot identity view, ∃ inventory : Inventory,
      SourceSyntaxExport.plan? spec = some plan ∧
      ClassAwareNativeForestWire.decodeSnapshot? forestBytes = some snapshot ∧
      ClassAwareNativeForestIdentityWire.decodeSnapshot? identityBytes = some identity ∧
      snapshot.completedView? = some view ∧
      view.codepoints = input.toList.map Char.toNat ∧
      identity.resolveInventory? plan = some inventory ∧
      ∀ tree, Nonempty (LanguageDefScalarSyntax.DerivesAt SourceSyntaxExport.literalScalars?
        spec.profile spec.grammar view.codepoints spec.profile.startSort 0 view.codepoints.length tree) →
        Nonempty (NativePackedFibre view inventory.toTable spec.profile plan view.codepoints
          spec.profile.startSort 0 view.codepoints.length tree) := by
  obtain ⟨plan, snapshot, identity, view, inventory, compiled, forestRead, identityRead,
    viewed, scalars, resolved, inputs, qualified⟩ := SourceSyntaxForest.complete?_sound accepted
  refine ⟨plan, snapshot, identity, view, inventory, compiled, forestRead, identityRead,
    viewed, scalars, resolved, ?_⟩
  obtain ⟨rules, rulesCompiled, planCompiled⟩ := Option.bind_eq_some_iff.mp compiled
  have agreement := ParserPackPlanAgreement.of_compilation planCompiled
  intro tree source
  obtain ⟨source⟩ := source
  obtain ⟨sourcePlan⟩ := LanguageDefScalarSyntax.preserve rulesCompiled source
  have target := preserveSourcePlanDerivation agreement sourcePlan
  have rootTarget : ParserPackRootDerives spec.profile plan view.codepoints tree := by
    simpa only [ParserPackRootDerives, agreement.startSort_eq] using target
  have packed := (qualified.rootDerivationEquiv tree) rootTarget
  exact ⟨by simpa only [agreement.startSort_eq] using packed⟩

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceSyntaxCoverage
