import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogParserHeight

/-! An independent complete reference forest for the authored Datalog
grammar. Native packed forests can be compared with its complete catalogue;
their result count alone supplies no completeness evidence. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.SourceReader

open Mettapedia.GSLT.Parsing
open ClassAwarePackedForest ClassAwareParserPackCertificate
open ClassAwareParserPackCorrespondence ClassAwareNativeForestQualification
open PresentationExprSemantics

def referenceForest (input : List Nat) : Forest :=
  pack ((completeCatalogue input).entries.map fun entry => (plan.lexical.startSort,entry.1))

theorem referenceForest_complete (input : List Nat) :
    RootParserComplete (referenceForest input) SourceViews.profile plan input := by
  intro tree derivation
  apply member_pack_rootUnfolds
  exact List.mem_map.mpr ⟨(Certificate.ofDerivation derivation,tree),
    (completeCatalogue input).complete tree derivation,rfl⟩

noncomputable def referenceForest_derivationEquiv (input : List Nat) (tree : CST) :
    ParserPackRootDerives SourceViews.profile plan input tree ≃
      PackedFibre (referenceForest input) SourceViews.profile plan input plan.lexical.startSort 0 input.length tree :=
  completeDerivationEquiv (referenceForest_complete input tree)

def validateNativeCoverage (input : List Nat) (forest : Forest) : Bool :=
  validateCatalogueCoverage forest (completeCatalogue input)

theorem validateNativeCoverage_sound (input : List Nat) (forest : Forest)
    (accepted : validateNativeCoverage input forest = true) :
    RootParserComplete forest SourceViews.profile plan input :=
  validateCatalogueCoverage_sound (completeCatalogue input) accepted

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.SourceReader
