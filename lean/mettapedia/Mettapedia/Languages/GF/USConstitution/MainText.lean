import Mettapedia.Languages.GF.USConstitution.Generated.Witnesses

/-!
# Original US Constitution Main Text — Shallow GF-Traceable Semantics

This file is the legal-interpretation layer above the GF witness lane.
The GF side certifies that selected official English fragments have
well-typed ParseEng trees. The record below says what semantic clauses a
downstream constitutional model assumes from those fragments.

Scope: original Preamble and Articles I--VII fragments only; no amendments
or current-law supersession are incorporated here.
-/

namespace Mettapedia.Languages.GF.USConstitution.MainText

open Mettapedia.Languages.GF.USConstitution.Generated.Witnesses

universe u

/-- Domain sorts for the shallow constitutional model. -/
structure ConstitutionDomain where
  Person : Type u
  State : Type u
  Bill : Type u
  Office : Type u

/-- A clause whose surface fragment has at least one accepted GF parse witness. -/
structure GroundedClause where
  id : ClauseId
  accepted : 0 < acceptedParseCount id

def groundedArticleISection1Vesting : GroundedClause :=
  ⟨.articleISection1Vesting, by decide⟩

def groundedArticleISection2RepresentativeAge : GroundedClause :=
  ⟨.articleISection2RepresentativeAge, by decide⟩

def groundedArticleISection2HouseComposition : GroundedClause :=
  ⟨.articleISection2HouseComposition, by decide⟩

def groundedArticleISection5Rules : GroundedClause :=
  ⟨.articleISection5Rules, by decide⟩

def groundedArticleISection7EveryBillPresented : GroundedClause :=
  ⟨.articleISection7EveryBillPresented, by decide⟩

def groundedArticleISection7PresidentSigns : GroundedClause :=
  ⟨.articleISection7PresidentSigns, by decide⟩

def groundedArticleISection7BecomesLaw : GroundedClause :=
  ⟨.articleISection7BecomesLaw, by decide⟩

def groundedArticleISection9Habeas : GroundedClause :=
  ⟨.articleISection9Habeas, by decide⟩

def groundedArticleISection9NoTitleOfNobility : GroundedClause :=
  ⟨.articleISection9NoTitleOfNobility, by decide⟩

def groundedArticleIISection1ExecutiveVesting : GroundedClause :=
  ⟨.articleIISection1ExecutiveVesting, by decide⟩

def groundedArticleIISection1PresidentAge : GroundedClause :=
  ⟨.articleIISection1PresidentAge, by decide⟩

def groundedArticleIISection2CommanderInChief : GroundedClause :=
  ⟨.articleIISection2CommanderInChief, by decide⟩

def groundedArticleIIISection3Treason : GroundedClause :=
  ⟨.articleIIISection3Treason, by decide⟩

def groundedArticleIVSection1FullFaithCredit : GroundedClause :=
  ⟨.articleIVSection1FullFaithCredit, by decide⟩

def groundedArticleVISupremacy : GroundedClause :=
  ⟨.articleVISupremacy, by decide⟩

def groundedArticleVINoReligiousTest : GroundedClause :=
  ⟨.articleVINoReligiousTest, by decide⟩

def groundedArticleVIIRatification : GroundedClause :=
  ⟨.articleVIIRatification, by decide⟩

/--
Shallow legal semantics for the GF-grounded main-text fragments.

The `*_grounded` fields make the source boundary explicit: these clauses
are not bare invented assumptions; they are tied to accepted GF parse
witnesses. The legal predicates themselves remain abstract so deeper legal
semantics can refine them later.
-/
structure ConstitutionMain (D : ConstitutionDomain) where
  age : D.Person → Nat
  yearsUSCitizen : D.Person → Nat
  yearsUSResident : D.Person → Nat
  inhabitantOf : D.Person → D.State → Prop
  naturalBornCitizen : D.Person → Prop
  citizenAtAdoption : D.Person → Prop
  eligibleRepresentative : D.Person → D.State → Prop
  eligiblePresident : D.Person → Prop
  passedHouse : D.Bill → Prop
  passedSenate : D.Bill → Prop
  presidentSigns : D.Bill → Prop
  twoThirdsHouseOverride : D.Bill → Prop
  twoThirdsSenateOverride : D.Bill → Prop
  becomesLaw : D.Bill → Prop
  religiousTestRequired : D.Office → Prop
  publicTrustUnderUS : D.Office → Prop
  legislativePowerVestedInCongress : Prop
  executivePowerVestedInPresident : Prop
  commanderInChiefClause : Prop
  supremacyClause : Prop
  ratificationByNineStatesSufficient : Prop
  representativeEligibilityRule :
    ∀ p s, eligibleRepresentative p s →
      25 ≤ age p ∧ 7 ≤ yearsUSCitizen p ∧ inhabitantOf p s
  presidentEligibilityRule :
    ∀ p, eligiblePresident p →
      (naturalBornCitizen p ∨ citizenAtAdoption p) ∧ 35 ≤ age p ∧ 14 ≤ yearsUSResident p
  signedBillBecomesLawRule :
    ∀ b, passedHouse b → passedSenate b → presidentSigns b → becomesLaw b
  vetoOverrideBecomesLawRule :
    ∀ b, passedHouse b → passedSenate b → twoThirdsHouseOverride b →
      twoThirdsSenateOverride b → becomesLaw b
  noReligiousTestRule :
    ∀ o, publicTrustUnderUS o → ¬ religiousTestRequired o
  legislativePowerVestedInCongress_grounded :
    groundedArticleISection1Vesting.id = .articleISection1Vesting
  representativeEligibilityRule_grounded :
    groundedArticleISection2RepresentativeAge.id = .articleISection2RepresentativeAge
  presentmentFragment_grounded :
    groundedArticleISection7EveryBillPresented.id = .articleISection7EveryBillPresented
  presidentSignsFragment_grounded :
    groundedArticleISection7PresidentSigns.id = .articleISection7PresidentSigns
  billBecomesLawFragment_grounded :
    groundedArticleISection7BecomesLaw.id = .articleISection7BecomesLaw
  presidentAgeFragment_grounded :
    groundedArticleIISection1PresidentAge.id = .articleIISection1PresidentAge
  executivePowerVestedInPresident_grounded :
    groundedArticleIISection1ExecutiveVesting.id = .articleIISection1ExecutiveVesting
  commanderInChiefClause_grounded :
    groundedArticleIISection2CommanderInChief.id = .articleIISection2CommanderInChief
  supremacyClause_grounded :
    groundedArticleVISupremacy.id = .articleVISupremacy
  noReligiousTestRule_grounded :
    groundedArticleVINoReligiousTest.id = .articleVINoReligiousTest
  ratificationByNineStatesSufficient_grounded :
    groundedArticleVIIRatification.id = .articleVIIRatification

namespace ConstitutionMain

variable {D : ConstitutionDomain} (C : ConstitutionMain D)

theorem representative_min_age {p : D.Person} {s : D.State}
    (h : C.eligibleRepresentative p s) : 25 ≤ C.age p :=
  (C.representativeEligibilityRule p s h).1

theorem representative_min_citizenship {p : D.Person} {s : D.State}
    (h : C.eligibleRepresentative p s) : 7 ≤ C.yearsUSCitizen p :=
  (C.representativeEligibilityRule p s h).2.1

theorem representative_must_inhabit_state {p : D.Person} {s : D.State}
    (h : C.eligibleRepresentative p s) : C.inhabitantOf p s :=
  (C.representativeEligibilityRule p s h).2.2

theorem president_natural_born_or_citizen_at_adoption {p : D.Person}
    (h : C.eligiblePresident p) : C.naturalBornCitizen p ∨ C.citizenAtAdoption p :=
  (C.presidentEligibilityRule p h).1

theorem president_min_age {p : D.Person}
    (h : C.eligiblePresident p) : 35 ≤ C.age p :=
  (C.presidentEligibilityRule p h).2.1

theorem president_min_residence {p : D.Person}
    (h : C.eligiblePresident p) : 14 ≤ C.yearsUSResident p :=
  (C.presidentEligibilityRule p h).2.2

theorem signed_bill_becomes_law {b : D.Bill}
    (hh : C.passedHouse b) (hs : C.passedSenate b) (hp : C.presidentSigns b) :
    C.becomesLaw b :=
  C.signedBillBecomesLawRule b hh hs hp

theorem veto_override_bill_becomes_law {b : D.Bill}
    (hh : C.passedHouse b) (hs : C.passedSenate b)
    (hoh : C.twoThirdsHouseOverride b) (hos : C.twoThirdsSenateOverride b) :
    C.becomesLaw b :=
  C.vetoOverrideBecomesLawRule b hh hs hoh hos

theorem no_religious_test_for_public_trust {o : D.Office}
    (h : C.publicTrustUnderUS o) : ¬ C.religiousTestRequired o :=
  C.noReligiousTestRule o h

theorem source_hash_nonempty : 0 < sourceHash.length := by decide

end ConstitutionMain

end Mettapedia.Languages.GF.USConstitution.MainText
