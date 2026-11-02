import Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRTermReading
import Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRValueInjectivity

/-! A retained compiled head match identifies the independent source head
instance, provided the source environment has been read into that assignment.
The request-prefix law supplies the literal pools. Extracting the complete
source environment from every native publication remains a separate contract.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRCompilation.HeadCorrespondence

open Mettapedia.Languages.CHR
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding GeneralScopedMatch Match
open GeneralFirstOrderProjection

theorem matched_head_instance (vocabulary : Vocabulary) (environment : Environment)
    (source : Head) (schema target : Pattern) (sourceValue actualValue : Constraint)
    {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat} {site : RulePatternSite} {path : List Nat}
    {initial captured chosen : ScopedRuleMatching.Assignment}
    (pools : RequestPools.Read vocabulary (ordinary chosen))
    (variableRead : TermReading.VariablesRead vocabulary environment (ordinary chosen))
    (compiled : head? vocabulary source = some schema)
    (instantiated : source.instantiate environment = some sourceValue)
    (encoded : constraint? vocabulary actualValue = some target)
    (matched : Matches rule spec ambient site path 0 initial schema target captured)
    (later : Extends captured chosen) (roots : GeneralPremise.RootValues ambient chosen) :
    sourceValue = actualValue := by
  have reconstructed := vector_matching_readout (HeadShape.head_shape vocabulary source schema compiled)
    matched later roots
  have sourceRead := TermReading.head_instantiation vocabulary environment (ordinary chosen)
    pools variableRead source schema sourceValue compiled instantiated
  rw [reconstructed] at sourceRead
  exact ValueInjectivity.constraint_injective vocabulary sourceValue actualValue target sourceRead encoded

#print axioms matched_head_instance

end Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRCompilation.HeadCorrespondence
