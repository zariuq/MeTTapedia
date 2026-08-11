import Mettapedia.GSLT.LanguageDef.CompletenessSpectrumSAT
import Mettapedia.GSLT.LanguageDef.NIKDefaultProfile

/-!
# Positive and refutation authorities in NIK

Checker rejection says only that one submitted certificate did not replay.
It is not evidence that the claim is false.  Refutation therefore occupies a
separate authority fibre with its own certificate type, exact certified scope,
and projection into its intended negative meaning.

The two meanings are not assumed to be Boolean complements.  Classical SAT
and UNSAT do satisfy that stronger law; paraconsistent and evidential systems
may instead support both lanes or neither.  Complementarity is consequently
an explicit property, not a hidden law of the dispatcher.
-/

namespace Mettapedia.GSLT.LanguageDef.NIKPolarizedAuthority

open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.GSLT.LanguageDef.CheckerAuthorityFamily
open Mettapedia.GSLT.LanguageDef.NIKDefaultProfile

universe uClaim uCertificate

/-- The two independently certified evidence directions. -/
inductive Polarity where
  | support
  | refutation
deriving DecidableEq, Repr

/-- Two independently admitted authorities over one claim language.  The
negative lane may denote countermodels, exhaustive failed search, explicit
strong-negation proofs, or another declared refutation semantics. -/
structure PolarizedAuthority (Claim : Type uClaim) where
  SupportCertificate : Type uCertificate
  RefutationCertificate : Type uCertificate
  supportChecker : Checker Claim SupportCertificate
  refutationChecker : Checker Claim RefutationCertificate
  SupportCertified : Claim → Prop
  RefutationCertified : Claim → Prop
  SupportMeaning : Claim → Prop
  RefutationMeaning : Claim → Prop
  supportProjection : supportChecker.AuthorityProjection
    SupportCertified SupportMeaning
  refutationProjection : refutationChecker.AuthorityProjection
    RefutationCertified RefutationMeaning

namespace PolarizedAuthority

variable {Claim : Type uClaim} (authority : PolarizedAuthority Claim)

/-- The two evidence directions become ordinary fibres of the one open NIK
authority family. -/
def toFamily : AuthorityFamily Polarity where
  Claim := fun _ => Claim
  Certificate
    | .support => authority.SupportCertificate
    | .refutation => authority.RefutationCertificate
  checker
    | .support => authority.supportChecker
    | .refutation => authority.refutationChecker
  Certified
    | .support => authority.SupportCertified
    | .refutation => authority.RefutationCertified
  Meaning
    | .support => authority.SupportMeaning
    | .refutation => authority.RefutationMeaning
  projection
    | .support => authority.supportProjection
    | .refutation => authority.refutationProjection

/-- Classical complementarity is an additional semantic law.  It is not
required merely to host checked evidence in both directions. -/
def Complementary : Prop :=
  ∀ claim, authority.RefutationMeaning claim ↔ ¬ authority.SupportMeaning claim

@[simp] theorem toFamily_support_checker :
    (authority.toFamily.checker .support) = authority.supportChecker :=
  rfl

@[simp] theorem toFamily_refutation_checker :
    (authority.toFamily.checker .refutation) = authority.refutationChecker :=
  rfl

/-- Accepted support evidence has the independently declared positive
meaning. -/
theorem accepted_support_meaning {claim : Claim}
    {certificate : authority.SupportCertificate}
    (accepted : authority.supportChecker.check claim certificate = true) :
    authority.SupportMeaning claim :=
  authority.supportProjection.sound claim certificate accepted

/-- Accepted refutation evidence has the independently declared negative
meaning. -/
theorem accepted_refutation_meaning {claim : Claim}
    {certificate : authority.RefutationCertificate}
    (accepted : authority.refutationChecker.check claim certificate = true) :
    authority.RefutationMeaning claim :=
  authority.refutationProjection.sound claim certificate accepted

end PolarizedAuthority

/-! ## SAT/UNSAT: a non-vacuous exact instance -/

namespace SAT

open Mettapedia.GSLT.LanguageDef.CompletenessSpectrum.SAT

variable {Var : Type uClaim} [Fintype Var] [DecidableEq Var]

/-- SAT assignments and complete UNSAT truth tables form an exact polarized
authority.  Efficient LRAT or resolution refutations may later refine the
negative certificate carrier without changing this semantic interface. -/
def authority : PolarizedAuthority (CNF Var) where
  SupportCertificate := Assignment Var
  RefutationCertificate := TruthTableCertificate Var
  supportChecker := assignmentChecker
  refutationChecker := truthTableChecker
  SupportCertified := Satisfiable
  RefutationCertified := Unsatisfiable
  SupportMeaning := Satisfiable
  RefutationMeaning := Unsatisfiable
  supportProjection := assignmentChecker_authority.toProjection
  refutationProjection := truthTableChecker_authority.toProjection

/-- In the classical finite SAT instance, the two independently checked
meanings happen to be exact complements. -/
theorem complementary : (authority (Var := Var)).Complementary := by
  intro formula
  exact unsatisfiable_iff_not_satisfiable formula

end SAT

/-! ## Separating witnesses -/

namespace Canary

open Mettapedia.GSLT.LanguageDef.CompletenessSpectrum.SAT
open Mettapedia.GSLT.LanguageDef.CompletenessSpectrum.SAT.Canary

def satFamily : AuthorityFamily Polarity :=
  (SAT.authority (Var := OneVar)).toFamily

def satFrontend : Frontend satFamily (TypedSubmission satFamily) :=
  Frontend.typed satFamily

def rejectedAssignmentSubmission : TypedSubmission satFamily :=
  ⟨.support, positiveFormula, falseAssignment⟩

def supportedClaim : satFamily.PackedClaim :=
  ⟨.support, positiveFormula⟩

/-- A bad positive certificate is rejected. -/
theorem bad_assignment_rejected :
    satFrontend.run rejectedAssignmentSubmission =
      .rejected supportedClaim :=
  rfl

theorem positive_formula_satisfiable : Satisfiable positiveFormula :=
  ⟨trueAssignment, positive_assignment_accepted⟩

theorem positive_formula_not_unsatisfiable :
    ¬ Unsatisfiable positiveFormula := by
  intro unsatisfiable
  exact ((unsatisfiable_iff_not_satisfiable positiveFormula).mp unsatisfiable)
    positive_formula_satisfiable

/-- The load-bearing negative canary: checker rejection is compatible with a
true claim and therefore cannot be interpreted as refutation. -/
theorem rejection_is_not_refutation :
    satFrontend.run rejectedAssignmentSubmission =
        .rejected supportedClaim ∧
      Satisfiable positiveFormula ∧
      ¬ Unsatisfiable positiveFormula :=
  ⟨bad_assignment_rejected, positive_formula_satisfiable,
    positive_formula_not_unsatisfiable⟩

noncomputable def acceptedRefutationSubmission : TypedSubmission satFamily :=
  ⟨.refutation, contradictionFormula, fullTruthTable⟩

def refutedClaim : satFamily.PackedClaim :=
  ⟨.refutation, contradictionFormula⟩

/-- A complete negative certificate is accepted in the distinct refutation
fibre and establishes UNSAT. -/
theorem complete_refutation_accepted :
    satFrontend.run acceptedRefutationSubmission =
      .accepted refutedClaim := by
  apply satFrontend.run_of_check_true
      (parsed := acceptedRefutationSubmission)
      (submission := acceptedRefutationSubmission)
  · rfl
  · rfl
  · exact complete_truth_table_accepted

theorem accepted_refutation_has_negative_meaning :
    satFamily.packedMeaning refutedClaim :=
  satFrontend.accepted_implies_meaning complete_refutation_accepted

end Canary

end Mettapedia.GSLT.LanguageDef.NIKPolarizedAuthority
