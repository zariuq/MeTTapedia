import Mettapedia.GSLT.LanguageDef.DerivationCheckMachine
import Mettapedia.GSLT.LanguageDef.TptpGroundResolutionEvidenceSynthesis
import Mettapedia.Languages.TPTP.StatusSemantics

/-!
# Ground-resolution semantic service for derivation checking

This module is the single semantic implementation of the small ground-CNF
resolution calculus used by the official-TSTP canaries.  It knows nothing
about TSTP syntax, names, source ordering, root selection, or proof search.
Those concerns belong to the official derivation projection and the generic
`DerivationCheckMachine` respectively.

The service checks one claimed resolvent when its `infer` transition runs.
Its soundness theorem is the calculus boundary consumed by every list, word,
and future generated StructuredC realization.  No compiler is defined here.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpGroundResolutionCheckService

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.DerivationCheckMachine
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.TptpGroundResolutionProblemAuthority
open Mettapedia.GSLT.LanguageDef.TptpGroundResolutionEvidenceSynthesis
open Mettapedia.Languages.TPTP
open Mettapedia.Languages.TPTP.StatusSemantics
open Mettapedia.Languages.TPTP.NIKAuthority
open Mettapedia.Languages.TPTP.GroundCNFAuthority

abbrev Formula := SemanticFormula
abbrev Rule := RuleKey
abbrev Provenance := ParsedClause Pattern
abbrev Obligation := SemanticFormula
abbrev Evidence := Unit
abbrev Program := List
  (Instruction Formula Rule Evidence Provenance Obligation)

/-- Check whether a claimed inference is an exact ground resolvent of its two
parents.  Evidence synthesis occurs only at this semantic service boundary. -/
def inferAccepted (rule : Rule) (parents : List Formula)
    (conclusion : Formula) : Bool :=
  decide (rule = TptpGroundResolutionProblemAuthority.resolutionKey) &&
    match parents, conclusion with
    | [.clause left, .clause right], .clause result =>
        (synthesizeEvidence? left right result).isSome
    | _, _ => false

theorem inferAccepted_sound (rule : Rule) (parents : List Formula)
    (conclusion : Formula) (accepted : inferAccepted rule parents conclusion = true) :
    (Formula.semantics (Atom := Pattern)).TheoremRelation
      { parents := parents, inferred := conclusion } := by
  simp only [inferAccepted, Bool.and_eq_true] at accepted
  have ruleShape :
      rule = TptpGroundResolutionProblemAuthority.resolutionKey :=
    of_decide_eq_true accepted.1
  subst rule
  cases parents with
  | nil => simp at accepted
  | cons first rest =>
      cases rest with
      | nil => simp at accepted
      | cons second tail =>
          cases tail with
          | cons third tail => simp at accepted
          | nil =>
              cases first with
              | negation formula => simp at accepted
              | clause left =>
                  cases second with
                  | negation formula => simp at accepted
                  | clause right =>
                      cases conclusion with
                      | negation formula => simp at accepted
                      | clause result =>
                          cases synthesized :
                              synthesizeEvidence? left right result with
                          | none => simp [synthesized] at accepted
                          | some certificate =>
                              have localMeaning := evidenceCheck_sound
                                TptpGroundResolutionProblemAuthority.resolutionKey
                                ({ parents := [.clause left, .clause right],
                                   inferred := .clause result } :
                                  RelationClaim Formula)
                                certificate.1 certificate.2
                              simpa [TptpGroundResolutionProblemAuthority.resolutionKey,
                                ClassicalModelSemantics.commonStatusMeaning]
                                using localMeaning

def services (problem : ParsedProblem) :
    Services Formula Rule Evidence Provenance Obligation Unit where
  initial := ()
  input := fun state provenance formula =>
    if decide (provenance ∈ problem.clauses &&
        formula = .clause provenance.literals) then some state else none
  infer := fun state rule parents _ conclusion =>
    if inferAccepted rule parents conclusion then some state else none
  root := fun _ formula obligation => decide (formula = obligation)

def RelativeTheorem (problem : ParsedProblem) (formula : Formula) : Prop :=
  ∀ valuation,
    (Formula.semantics (Atom := Pattern)).SatisfiesAll valuation
      problem.formulas →
    (Formula.semantics (Atom := Pattern)).satisfies valuation formula

def services_sound (problem : ParsedProblem) :
    SoundServices (services problem) where
  Valid := RelativeTheorem problem
  Objective := RelativeTheorem problem
  StateValid := fun _ => True
  initial_sound := trivial
  input_sound := by
    intro state provenance formula nextState accepted _stateValid
    simp [services] at accepted
    constructor
    · intro valuation problemSatisfied
      rw [accepted.2]
      apply problemSatisfied
      exact List.mem_map.mpr ⟨provenance, accepted.1, rfl⟩
    · trivial
  infer_sound := by
    intro state rule parents evidence conclusion nextState accepted
      _stateValid parentsValid
    simp [services] at accepted
    constructor
    · have localTheorem := inferAccepted_sound rule parents conclusion accepted
      intro valuation problemSatisfied
      apply localTheorem valuation
      intro parent membership
      exact parentsValid parent membership valuation problemSatisfied
    · trivial
  root_sound := by
    intro state formula obligation accepted _stateValid valid
    have equal : formula = obligation := of_decide_eq_true accepted
    simpa [equal] using valid

def ProblemUnsatisfiable (problem : ParsedProblem) : Prop :=
  ∀ valuation,
    ¬ (∀ formula, formula ∈ problem.formulas →
      Formula.Satisfies valuation formula)

#print axioms inferAccepted_sound
#print axioms services_sound

end Mettapedia.GSLT.LanguageDef.TptpGroundResolutionCheckService
