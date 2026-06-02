import Mettapedia.Languages.GF.USConstitution.MainText
import Mettapedia.Languages.GF.USConstitution.Pretty
import Mettapedia.Logic.DDLPlus.Core

set_option autoImplicit false

/-!
# US Constitution Canaries

These checks are meant to fail if the formalization starts over-claiming:

* context-completed GF witnesses must remain visibly different from literal
  source text;
* Article I "may/power" readings must not collapse into obligation;
* positive semantic rules stay one-way unless the text and model justify
  the converse.
-/

namespace Mettapedia.Languages.GF.USConstitution.Canaries

open Mettapedia.Languages.GF.USConstitution.Generated.Witnesses
open Mettapedia.Languages.GF.USConstitution.MainText
open Mettapedia.Logic.DDLPlus.Core

/-! ## Source-faithfulness canaries -/

example : acceptedParseCount .articleISection8DeclareWar = 0 := by decide

example :
    Mettapedia.Languages.GF.USConstitution.Generated.ContextCompletions.correctionKind
        .articleISection8DeclareWarContextCompletion1 =
      Mettapedia.Languages.GF.USConstitution.Generated.ContextCompletions.CorrectionKind.contextCompletion := rfl

example :
    Mettapedia.Languages.GF.USConstitution.Generated.ContextCompletions.correctionParserInput
        .articleISection8DeclareWarContextCompletion1 ≠
      clauseText .articleISection8DeclareWar := by
  decide

example :
    Mettapedia.Languages.GF.USConstitution.Generated.ContextCompletions.correctionParserInput
        .articleISection3SenateImpeachmentsExactSubfragment1 ≠
      clauseText .articleISection3SenateImpeachments := by
  decide

example : (clauseGFLinearizations .articleISection1Vesting).length = 1 := by decide

example : (clauseGFBracketedLinearizations .articleISection1Vesting).length = 1 := by decide

/-! ## Legal-theory canary: may/permission/possibility is not obligation -/

def noObligationFrame : DDLPlusFrame Unit where
  av := fun _ _ => True
  pv := fun _ _ => True
  ob := fun _ _ => False
  sem_3a := by
    intro _
    exact ⟨(), trivial⟩
  sem_4a := by
    intro _ _ _
    trivial
  sem_4b := by
    intro _
    trivial
  sem_5a := by
    intro _ h
    exact h
  sem_5b := by
    intro _ _ _ _
    constructor <;> intro h <;> exact h
  sem_5c := by
    intro _ _ _ _ h _ 
    exact h
  sem_5d := by
    intro _ _ _ _ h _
    exact h
  sem_5e := by
    intro _ _ _ _ h _
    exact h

def declareWarMeaning : Meaning Unit Unit :=
  fun _ _ => True

/-- Permission as non-obligation of the negation, the familiar deontic reading. -/
def legalPermission {c w : Type} (F : DDLPlusFrame w) (φ : Meaning c w) : Meaning c w :=
  pnot (ideal_obl F (pnot φ))

theorem possible_does_not_imply_ideal_obligation :
    dia_p noObligationFrame declareWarMeaning () () ∧
      ¬ ideal_obl noObligationFrame declareWarMeaning () () := by
  constructor
  · simp [dia_p, declareWarMeaning, noObligationFrame]
  · simp [ideal_obl, noObligationFrame]

theorem permission_does_not_imply_ideal_obligation :
    legalPermission noObligationFrame declareWarMeaning () () ∧
      ¬ ideal_obl noObligationFrame declareWarMeaning () () := by
  constructor <;> simp [legalPermission, pnot, ideal_obl, declareWarMeaning, noObligationFrame]

/-! ## Constitutional semantic non-overclaiming canary -/

def unitDomain : ConstitutionDomain where
  Person := Unit
  State := Unit
  Bill := Unit
  Office := Unit

def ageOnlyPresidentModel : ConstitutionMain unitDomain where
  age := fun _ => 35
  yearsUSCitizen := fun _ => 0
  yearsUSResident := fun _ => 0
  inhabitantOf := fun _ _ => False
  naturalBornCitizen := fun _ => False
  citizenAtAdoption := fun _ => False
  eligibleRepresentative := fun _ _ => False
  eligiblePresident := fun _ => False
  passedHouse := fun _ => False
  passedSenate := fun _ => False
  presidentSigns := fun _ => False
  twoThirdsHouseOverride := fun _ => False
  twoThirdsSenateOverride := fun _ => False
  becomesLaw := fun _ => False
  religiousTestRequired := fun _ => False
  publicTrustUnderUS := fun _ => False
  legislativePowerVestedInCongress := True
  executivePowerVestedInPresident := True
  commanderInChiefClause := True
  supremacyClause := True
  ratificationByNineStatesSufficient := True
  representativeEligibilityRule := by
    intro _ _ h
    cases h
  presidentEligibilityRule := by
    intro _ h
    cases h
  signedBillBecomesLawRule := by
    intro _ h
    cases h
  vetoOverrideBecomesLawRule := by
    intro _ h
    cases h
  noReligiousTestRule := by
    intro _ h
    cases h
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

theorem age_thirty_five_does_not_force_presidential_eligibility :
    ageOnlyPresidentModel.age () = 35 ∧ ¬ ageOnlyPresidentModel.eligiblePresident () := by
  simp [ageOnlyPresidentModel]

end Mettapedia.Languages.GF.USConstitution.Canaries
