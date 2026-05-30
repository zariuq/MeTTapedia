import Mettapedia.Languages.GF.USConstitution.GeneratedConformance
import Mettapedia.Languages.GF.USConstitution.MainText
import Mettapedia.Languages.GF.USConstitution.Pretty

/-!
# US Constitution GF-to-Lean Diagnostics

Small executable checks for the Constitution experiment:

* generated witness counts match the current ParseEng export;
* newly added presentment/signature/law and presidential-age fragments are grounded;
* known ungrounded fragments stay visible as parse failures;
* the shallow semantic record is satisfiable by a tiny nonempty model.
-/

namespace Mettapedia.Languages.GF.USConstitution.Diagnostics

open Mettapedia.Languages.GF.USConstitution.Generated.Witnesses
open Mettapedia.Languages.GF.USConstitution.GeneratedConformance
open Mettapedia.Languages.GF.USConstitution.MainText
open Mettapedia.Languages.GF.USConstitution.Pretty

example : sourceHash.length = 64 := by native_decide
example : allClauseIds.length = 21 := by native_decide
example : acceptedClauseIds.length = 18 := by native_decide
example : failedClauseIds.length = 3 := by native_decide
example : contextCorrectionIds.length = 4 := by native_decide
example : contextCorrectedFailedClauseIds.length = 3 := by native_decide
example : contextUncorrectedFailedClauseIds.length = 0 := by native_decide
example : parseRoundTrips .articleVIIRatification = true := by native_decide

example : acceptedParseCount .articleISection7EveryBillPresented = 1 := by native_decide
example : acceptedParseCount .articleISection7PresidentSigns = 1 := by native_decide
example : acceptedParseCount .articleISection7BecomesLaw = 1 := by native_decide
example : acceptedParseCount .articleIISection1PresidentAge = 1 := by native_decide
example : acceptedParseCount .articleIVSection1FullFaithCredit = 1 := by native_decide

example : acceptedParseCount .articleISection3SenateImpeachments = 0 := by native_decide
example : acceptedParseCount .articleISection8DeclareWar = 0 := by native_decide
example : acceptedParseCount .articleVProposeAmendments = 0 := by native_decide

example :
    parseError .articleISection3SenateImpeachments =
      some "no accepted parse without PGF meta holes" := by
  native_decide

example : treeChecks articleISection7EveryBillPresentedParse1 = true := by native_decide
example : treeChecks articleISection7PresidentSignsParse1 = true := by native_decide
example : treeChecks articleISection7BecomesLawParse1 = true := by native_decide
example : treeChecks articleIISection1PresidentAgeParse1 = true := by native_decide
example : treeChecks articleIVSection1FullFaithCreditParse1 = true := by native_decide

abbrev CompletionId :=
  Mettapedia.Languages.GF.USConstitution.Generated.ContextCompletions.CorrectionId

def senatePowerSubfragment : CompletionId :=
  .articleISection3SenateImpeachmentsExactSubfragment1

def senateTryCompletion : CompletionId :=
  .articleISection3SenateImpeachmentsContextCompletion1

def declareWarCompletion : CompletionId :=
  .articleISection8DeclareWarContextCompletion1

def proposeAmendmentsCompletion : CompletionId :=
  .articleVProposeAmendmentsContextCompletion1

example :
    Mettapedia.Languages.GF.USConstitution.Generated.ContextCompletions.confidencePermille
      senatePowerSubfragment = 990 := by
  native_decide

example :
    Mettapedia.Languages.GF.USConstitution.Generated.ContextCompletions.confidencePermille
      declareWarCompletion = 760 := by
  native_decide

example :
    Mettapedia.Languages.GF.USConstitution.Generated.ContextCompletions.sourceClause
      proposeAmendmentsCompletion = .articleVProposeAmendments := by
  native_decide

example :
    treeChecks
      (Mettapedia.Languages.GF.USConstitution.Generated.ContextCompletions.correctionParses
        senateTryCompletion).head! = true := by
  native_decide

def unitDomain : ConstitutionDomain where
  Person := Unit
  State := Unit
  Bill := Unit
  Office := Unit

def sampleMain : ConstitutionMain unitDomain where
  age := fun _ => 35
  yearsUSCitizen := fun _ => 7
  yearsUSResident := fun _ => 14
  inhabitantOf := fun _ _ => True
  naturalBornCitizen := fun _ => True
  citizenAtAdoption := fun _ => False
  eligibleRepresentative := fun _ _ => True
  eligiblePresident := fun _ => True
  passedHouse := fun _ => True
  passedSenate := fun _ => True
  presidentSigns := fun _ => True
  twoThirdsHouseOverride := fun _ => True
  twoThirdsSenateOverride := fun _ => True
  becomesLaw := fun _ => True
  religiousTestRequired := fun _ => False
  publicTrustUnderUS := fun _ => True
  legislativePowerVestedInCongress := True
  executivePowerVestedInPresident := True
  commanderInChiefClause := True
  supremacyClause := True
  ratificationByNineStatesSufficient := True
  representativeEligibilityRule := by
    intro _ _ _
    exact ⟨by decide, by decide, trivial⟩
  presidentEligibilityRule := by
    intro _ _
    exact ⟨Or.inl trivial, by decide, by decide⟩
  signedBillBecomesLawRule := by
    intro _ _ _ _
    trivial
  vetoOverrideBecomesLawRule := by
    intro _ _ _ _ _
    trivial
  noReligiousTestRule := by
    intro _ _ h
    exact h
  legislativePowerVestedInCongress_grounded := rfl
  representativeEligibilityRule_grounded := rfl
  presentmentFragment_grounded := rfl
  presidentSignsFragment_grounded := rfl
  billBecomesLawFragment_grounded := rfl
  presidentAgeFragment_grounded := rfl
  executivePowerVestedInPresident_grounded := rfl
  commanderInChiefClause_grounded := rfl
  supremacyClause_grounded := rfl
  noReligiousTestRule_grounded := rfl
  ratificationByNineStatesSufficient_grounded := rfl

example : 25 ≤ sampleMain.age () :=
  ConstitutionMain.representative_min_age sampleMain (s := ()) trivial

example : 35 ≤ sampleMain.age () :=
  ConstitutionMain.president_min_age sampleMain trivial

example : sampleMain.becomesLaw () :=
  ConstitutionMain.signed_bill_becomes_law sampleMain trivial trivial trivial

example : ¬ sampleMain.religiousTestRequired () :=
  ConstitutionMain.no_religious_test_for_public_trust sampleMain trivial

end Mettapedia.Languages.GF.USConstitution.Diagnostics
