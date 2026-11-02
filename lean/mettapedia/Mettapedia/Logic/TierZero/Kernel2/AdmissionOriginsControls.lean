import Mettapedia.Logic.TierZero.Kernel2.AdmissionOrigins

/-!
# Admission-origin controls on the executable kernel

A valid admitted rule supports two successive promotions. A mismatched claim,
an undetermined admission and a name collision contribute no root. A proposed
self-supporting claim remains unaccepted. Unprocessed mailbox entries are not
counted as admissions.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Kernel2.AdmissionOrigins.Controls

def seed : Rule := ⟨0, [], pjd "proves" [psym "a"]⟩

def undetermined : Rule := ⟨1, [], pjd "proves" [pv 0]⟩

def closedClaim (name source : String) (conclusion : Pat) : Claim String :=
  ⟨name, [], [], [], [], [], conclusion, [], [⟨0, source, []⟩], .node 0⟩

def chain : List (ClientAct String) :=
  [ .sendAdmission (.judgment "proves" 1),
    .sendAdmission (.rule "seed" seed),
    .sendAdmission (.rule "undetermined" undetermined),
    .sendClaim (closedClaim "derived" "seed" (pjd "proves" [psym "a"])),
    .sendClaim (closedClaim "use" "derived" (pjd "proves" [psym "a"])),
    .sendClaim (closedClaim "wrong" "derived" (pjd "proves" [psym "b"])),
    .sendAdmission (.rule "use" seed) ]

theorem two_promotions_are_accepted :
    (observeProgram 8 chain).2.T = ["derived", "use"] := by decide +kernel

theorem promoted_and_refused_rules_are_not_roots :
    (observeProgram 8 chain).1.map Prod.fst = ["seed"] := by decide +kernel

theorem promotions_remain_available_on_the_rule_board :
    (observeProgram 8 chain).2.L.rules.map Prod.fst = ["seed", "derived", "use"] := by decide +kernel

theorem unprocessed_admissions_are_not_roots :
    (observeProgram 0 chain).1.map Prod.fst = [] := by decide +kernel

def selfSupport : List (ClientAct String) :=
  [ .sendAdmission (.judgment "proves" 1),
    .sendClaim (closedClaim "self" "self" (pjd "proves" [psym "a"])) ]

theorem a_proposed_claim_cannot_admit_itself :
    (observeProgram 8 selfSupport).2.T = [] ∧
      (observeProgram 8 selfSupport).1.map Prod.fst = [] := by decide +kernel

theorem no_roots_and_no_hypotheses_prove_nothing (goal : Tm) :
    ¬Derivable (basisPres ([] : List (String × Rule)) ⟨0, []⟩) [] goal := by
  rw [empty_basis_iff]
  simp

theorem logical_hypotheses_are_retained (hypothesis : Tm) :
    Derivable (basisPres ([] : List (String × Rule)) ⟨0, []⟩) [hypothesis] hypothesis := by
  apply empty_basis_iff.mpr
  simp

end Mettapedia.Logic.TierZero.Kernel2.AdmissionOrigins.Controls
