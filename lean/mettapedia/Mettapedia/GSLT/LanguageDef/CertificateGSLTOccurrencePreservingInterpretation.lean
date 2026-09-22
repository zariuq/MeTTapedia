import Mettapedia.GSLT.LanguageDef.CertificateGSLTInterpretation
import Mettapedia.GSLT.LanguageDef.CertificateGSLTOpenSearchMachine

/-!
# Ordered premise use under CertificateGSLT interpretation

An interpretation can preserve an open proof while copying or dropping its
premises. The exact resource condition is local: each translated primitive
rule template must use every ordered premise position once, in order. Under
that condition, translation preserves the occurrence ledger of every open
derivation. Without it, proof preservation alone carries no such guarantee.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CertificateGSLT

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.Ultrainfinite
open OpenSearchMachine

namespace Interpretation

/-- A rule template is ordered-linear when it uses each source premise
position once, in order. The condition is imposed on actual admitted rule
applications, not on arbitrary uninhabited schemas. -/
def PreservesOrderedPremises {source target : Object}
    (interpretation : Interpretation source target) : Prop :=
  ∀ (ruleInstance : RuleInstance) {premises : List Pattern}
    {conclusion : Pattern}
    (application : RuleApplication source.definition ruleInstance premises conclusion),
    holeOccurrences (interpretation.onRule ruleInstance application) =
      List.finRange premises.length

mutual

/-- A locally ordered-linear interpretation preserves every occurrence of
an open proof, including distinct occurrences with equal judgment labels. -/
theorem holeOccurrences_mapOpen
    {source target : Object}
    (interpretation : Interpretation source target)
    (linear : interpretation.PreservesOrderedPremises)
    {context : List Pattern} {goal : Pattern}
    (derivation : OpenDerivation source.definition context goal) :
    holeOccurrences (interpretation.mapOpen derivation) =
      holeOccurrences derivation := by
  cases derivation with
  | assumption index => rfl
  | byRule ruleInstance application children =>
      simp only [mapOpen, holeOccurrences_bind]
      rw [linear ruleInstance application]
      rw [← holeOccurrencesList_eq_finRange_flatMap
        (interpretation.mapOpenList children)]
      exact holeOccurrencesList_mapOpen interpretation linear children

/-- The ordered resource law holds pointwise for vectors of proofs. -/
theorem holeOccurrencesList_mapOpen
    {source target : Object}
    (interpretation : Interpretation source target)
    (linear : interpretation.PreservesOrderedPremises)
    {context goals : List Pattern}
    (derivations : OpenDerivationList source.definition context goals) :
    holeOccurrencesList (interpretation.mapOpenList derivations) =
      holeOccurrencesList derivations := by
  cases derivations with
  | nil => rfl
  | cons head tail =>
      simp only [mapOpenList, holeOccurrencesList]
      rw [holeOccurrences_mapOpen interpretation linear head,
        holeOccurrencesList_mapOpen interpretation linear tail]

end

/-- The identity environment discharges each ordered premise position once. -/
theorem holeOccurrencesList_assumptionEnvironment
    {definition : ValidatedCalculusLanguageDef}
    (context : List Pattern) :
    holeOccurrencesList (assumptionEnvironment definition context) =
      List.finRange context.length := by
  rw [holeOccurrencesList_eq_finRange_flatMap]
  simp [assumptionEnvironment, OpenDerivationList.get_ofFn,
    holeOccurrences]

/-- Local ordered linearity is not merely sufficient: it is exactly the
condition for an interpretation to preserve every open proof's ledger.
The converse tests a primitive rule against the identity premise environment. -/
theorem preservesOrderedPremises_iff_all
    {source target : Object}
    (interpretation : Interpretation source target) :
    interpretation.PreservesOrderedPremises ↔
      ∀ (context : List Pattern) (goal : Pattern)
        (derivation : OpenDerivation source.definition context goal),
        holeOccurrences (interpretation.mapOpen derivation) =
          holeOccurrences derivation := by
  constructor
  · intro linear context goal derivation
    exact holeOccurrences_mapOpen interpretation linear derivation
  · intro all ruleInstance premises conclusion application
    have tested := all premises conclusion
      (OpenDerivation.byRule ruleInstance application
        (assumptionEnvironment source.definition premises))
    simp only [mapOpen, mapOpenList_assumptionEnvironment,
      OpenDerivation.bind_assumptionEnvironment, holeOccurrences] at tested
    rw [holeOccurrencesList_assumptionEnvironment] at tested
    exact tested

/-- Identity theory translation is ordered-linear. -/
theorem id_preservesOrderedPremises (object : Object) :
    (id object).PreservesOrderedPremises := by
  apply (preservesOrderedPremises_iff_all (id object)).2
  intro context goal derivation
  rw [id_mapOpen]

/-- Ordered-linear interpretations are closed under theory translation
composition, so resource correctness survives multi-stage compilation. -/
theorem comp_preservesOrderedPremises
    {first middle last : Object}
    (earlier : Interpretation first middle)
    (later : Interpretation middle last)
    (earlierLinear : earlier.PreservesOrderedPremises)
    (laterLinear : later.PreservesOrderedPremises) :
    (comp earlier later).PreservesOrderedPremises := by
  apply (preservesOrderedPremises_iff_all (comp earlier later)).2
  intro context goal derivation
  rw [comp_mapOpen,
    holeOccurrences_mapOpen later laterLinear,
    holeOccurrences_mapOpen earlier earlierLinear]

/-- A certified source proof compiles constructively to a target execution
route with the exact same final ordered discharge ledger. This does not map
uncertified source steps or identify individual source and target routes. -/
def runTranslated
    {source target : Object}
    (interpretation : Interpretation source target)
    (linear : interpretation.PreservesOrderedPremises)
    {context : List Pattern} {goal : Pattern}
    (derivation : OpenDerivation source.definition context goal) :
    Route (OpenSearchMachine.Step target.definition context)
      ⟨[goal], []⟩ ⟨[], holeOccurrences derivation⟩ := by
  simpa [holeOccurrences_mapOpen interpretation linear derivation] using
    OpenSearchMachine.runToCompletion (interpretation.mapOpen derivation)

end Interpretation
end Mettapedia.GSLT.LanguageDef.CertificateGSLT

#print axioms Mettapedia.GSLT.LanguageDef.CertificateGSLT.Interpretation.holeOccurrences_mapOpen
#print axioms Mettapedia.GSLT.LanguageDef.CertificateGSLT.Interpretation.holeOccurrencesList_mapOpen
#print axioms Mettapedia.GSLT.LanguageDef.CertificateGSLT.Interpretation.preservesOrderedPremises_iff_all
#print axioms Mettapedia.GSLT.LanguageDef.CertificateGSLT.Interpretation.comp_preservesOrderedPremises
#print axioms Mettapedia.GSLT.LanguageDef.CertificateGSLT.Interpretation.runTranslated
