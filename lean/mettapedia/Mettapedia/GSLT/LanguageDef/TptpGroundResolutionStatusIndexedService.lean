import Mettapedia.GSLT.LanguageDef.TptpGroundResolutionCheckService
import Mettapedia.GSLT.LanguageDef.TptpOfficialStatusIndexedService

/-!
# Ground resolution as a status-indexed TSTP calculus service

This adapter connects the existing authored ground-resolution authority to
the general status-indexed edge interface.  It admits only `status(thm)` and
delegates the actual resolvent decision to the single shared ground-resolution
service.  It does not inspect TSTP syntax or implement a second resolution
rule.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpGroundResolutionStatusIndexedService

open Mettapedia.GSLT.LanguageDef.TptpGroundResolutionCheckService
open Mettapedia.GSLT.LanguageDef.TptpGroundResolutionProblemAuthority
open Mettapedia.GSLT.LanguageDef.TptpOfficialStatusIndexedService
open Mettapedia.GSLT.LanguageDef.TptpOfficialPrincipalSymbols
open Mettapedia.Languages.TPTP.StatusSemantics

def literalPrincipalSymbols? :
    Mettapedia.Languages.TPTP.GroundCNFAuthority.Literal
      Mettapedia.OSLF.MeTTaIL.Syntax.Pattern ->
      Option (Finset PrincipalSymbolId)
  | .positive atom | .negative atom => principalSymbolSet? atom

def clausePrincipalSymbols? :
    Mettapedia.Languages.TPTP.GroundCNFAuthority.Clause
      Mettapedia.OSLF.MeTTaIL.Syntax.Pattern ->
      Option (Finset PrincipalSymbolId)
  | [] => some ∅
  | literal :: literals => do
      let first <- literalPrincipalSymbols? literal
      let rest <- clausePrincipalSymbols? literals
      some (first ∪ rest)

def formulaPrincipalSymbols? : Formula -> Option (Finset PrincipalSymbolId)
  | .clause literals => clausePrincipalSymbols? literals
  | .negation formula => formulaPrincipalSymbols? formula

/-- Ground resolution consumes only problem inputs and conclusions of earlier
theorem-preserving inferences.  Counter-theorems and equisatisfiable
replacements are not ordinary positive clauses. -/
def theoremPremiseOriginB : NodeOrigin -> Bool
  | .input => true
  | .inferred .thm => true
  | _ => false

/-- Status-indexed projection of the shared authored ground-resolution
checker.  Non-theorem statuses fail before the resolvent checker runs. -/
def calculus : Calculus Formula Rule Unit where
  meaning :=
    (Mettapedia.Languages.TPTP.GroundCNFAuthority.Formula.semantics
      (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)).commonStatusMeaning
  parentOriginsAccepted := fun _ _ origins =>
    origins.all theoremPremiseOriginB
  ruleMetadataAccepted := fun _ _ _ => true
  check := fun rule status parents _ conclusion =>
    decide (status = .thm) && inferAccepted rule parents conclusion
  check_sound := by
    intro rule status parents evidence conclusion accepted
    simp only [Bool.and_eq_true] at accepted
    have statusEq : status = .thm := of_decide_eq_true accepted.1
    subst status
    simpa [ClassicalModelSemantics.commonStatusMeaning] using
      inferAccepted_sound rule parents conclusion accepted.2

/-- Ground resolution supplies only the calculus component.  TSTP metadata,
problem provenance, and the root condition remain owned by the generic
status-indexed host and its problem boundary. -/
def service : Service Formula Rule Unit where
  formulaSignature := { principalSymbols? := formulaPrincipalSymbols? }
  calculus := calculus

namespace Canary

open TptpGroundResolutionProblemAuthority.Canary
open Mettapedia.GSLT.LanguageDef.TptpGroundResolutionEvidenceSynthesis.Canary

def pSymbol : PrincipalSymbolId := { kind := .functor, name := "p" }
def qSymbol : PrincipalSymbolId := { kind := .functor, name := "q" }

def officialAtom (name : String) : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern :=
  .apply "tptp92-ast:fof-atomic-formula:alt-1" [
    .apply "tptp92-ast:fof-plain-atomic-formula:alt-1" [
      .apply "tptp92-ast:fof-plain-term:alt-1" [
        .apply "tptp92-ast:constant:alt-1" [
          .apply "tptp92-ast:functor:alt-1" [
            .apply "tptp92-ast:atomic-word:alt-1" [
              .apply "tptp92-ast:token:lower-word" [.apply name []]]]]]]]

theorem semantic_formula_signature_is_recovered_from_its_official_atoms :
    formulaPrincipalSymbols? (.clause [
      .positive (officialAtom "p"),
      .negative (officialAtom "q")]) =
        some ([pSymbol, qSymbol].toFinset) := by
  rfl

theorem non_official_semantic_atom_has_no_tptp_signature :
    formulaPrincipalSymbols? (.clause [
      .positive (.fvar "not-official-tptp")]) = none := by
  rfl

def claim : RelationClaim Formula := {
  parents := [.clause disjunction, .clause negativeP]
  inferred := .clause positiveQ
}

theorem theorem_status_edge_is_accepted :
    calculus.check resolutionKey .thm claim.parents () claim.inferred = true := by
  simp [calculus, inferAccepted, claim, first_resolution_synthesized]

theorem countertheorem_status_is_not_reinterpreted_as_theorem :
    calculus.check resolutionKey .cth claim.parents () claim.inferred = false := by
  rfl

theorem accepted_edge_has_theorem_meaning :
    calculus.meaning.Meaning .thm claim := by
  exact calculus.check_sound resolutionKey .thm claim.parents () claim.inferred
    theorem_status_edge_is_accepted

end Canary

#print axioms calculus
#print axioms Canary.semantic_formula_signature_is_recovered_from_its_official_atoms
#print axioms Canary.non_official_semantic_atom_has_no_tptp_signature
#print axioms Canary.theorem_status_edge_is_accepted
#print axioms Canary.countertheorem_status_is_not_reinterpreted_as_theorem
#print axioms Canary.accepted_edge_has_theorem_meaning

end Mettapedia.GSLT.LanguageDef.TptpGroundResolutionStatusIndexedService
