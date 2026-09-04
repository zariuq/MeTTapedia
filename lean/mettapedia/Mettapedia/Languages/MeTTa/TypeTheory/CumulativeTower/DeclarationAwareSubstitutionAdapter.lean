import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.DeclarationAwareSubstitutionBoundary

/-!
# Exact declaration-aware substitution adapter

The canonical Prime wire stores intrinsically scoped variables as tagged data,
not as generic `Pattern` binders.  This module supplies the smallest correct
computational adapter for that representation: decode the two intrinsic terms,
perform the already verified intrinsic substitution, and re-encode the result.

The adapter constructs no trace or proof object at runtime.  Its static
theorems prove exact behavior on canonical inputs, reflection of every returned
result to intrinsic substitution, typed beta preservation, and rejection of a
malformed body.  It is not yet an authored GSLT inference presentation; a
generated presentation must independently implement this relation and prove a
commuting theorem against this boundary.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.DeclarationAwareSubstitutionAdapter

open Mettapedia.GSLT.LanguageDef.KernelAuthority.Checker
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.DeclarationAwarePatternCodec
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.DeclarationAwareSubstitutionBoundary
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution

variable {Head : Type} {n : Nat}

/-- Decode two canonical terms, instantiate the newest variable, and return
the canonical encoding of the intrinsic result. -/
def instantiateEncodedTm? (headCodec : PartialCodec Head Pattern) (n : Nat)
    (replacement body : Pattern) : Option Pattern := do
  let replacementTerm ← decodeTm? headCodec n replacement
  let bodyTerm ← decodeTm? headCodec (n + 1) body
  pure (encodeTm headCodec (inst0 replacementTerm bodyTerm))

/-- Canonical inputs compute to exactly the canonical intrinsic substitution. -/
@[simp] theorem instantiateEncodedTm?_encode
    (headCodec : PartialCodec Head Pattern)
    (replacement : Tm Head n) (body : Tm Head (n + 1)) :
    instantiateEncodedTm? headCodec n
        (encodeTm headCodec replacement) (encodeTm headCodec body) =
      some (encodeTm headCodec (inst0 replacement body)) := by
  simp [instantiateEncodedTm?, decodeTm?_encodeTm]

/-- Every successful adapter result reflects to two decoded intrinsic inputs
and their exact intrinsic substitution. -/
theorem instantiateEncodedTm?_reflects
    (headCodec : PartialCodec Head Pattern) (n : Nat)
    {replacement body result : Pattern}
    (accepted : instantiateEncodedTm? headCodec n replacement body =
      some result) :
    ∃ replacementTerm : Tm Head n, ∃ bodyTerm : Tm Head (n + 1),
      decodeTm? headCodec n replacement = some replacementTerm ∧
      decodeTm? headCodec (n + 1) body = some bodyTerm ∧
      result = encodeTm headCodec (inst0 replacementTerm bodyTerm) := by
  cases replacementDecoded : decodeTm? headCodec n replacement with
  | none =>
      simp [instantiateEncodedTm?, replacementDecoded] at accepted
  | some replacementTerm =>
      cases bodyDecoded : decodeTm? headCodec (n + 1) body with
      | none =>
          simp [instantiateEncodedTm?, replacementDecoded, bodyDecoded] at accepted
      | some bodyTerm =>
          simp [instantiateEncodedTm?, replacementDecoded, bodyDecoded] at accepted
          exact
            ⟨replacementTerm, bodyTerm, rfl, rfl,
              accepted.symm⟩

/-- Every successful output decodes back to the intrinsic substitution it
claims to represent. -/
theorem instantiateEncodedTm?_output_decodes
    (headCodec : PartialCodec Head Pattern) (n : Nat)
    {replacement body result : Pattern}
    (accepted : instantiateEncodedTm? headCodec n replacement body =
      some result) :
    ∃ replacementTerm : Tm Head n, ∃ bodyTerm : Tm Head (n + 1),
      decodeTm? headCodec n replacement = some replacementTerm ∧
      decodeTm? headCodec (n + 1) body = some bodyTerm ∧
      decodeTm? headCodec n result =
        some (inst0 replacementTerm bodyTerm) := by
  obtain ⟨replacementTerm, bodyTerm, replacementDecoded, bodyDecoded,
      resultEncoded⟩ := instantiateEncodedTm?_reflects headCodec n accepted
  subst result
  exact
    ⟨replacementTerm, bodyTerm, replacementDecoded, bodyDecoded,
      decodeTm?_encodeTm headCodec _⟩

/-- Typed intrinsic substitution supplies the subject-reduction boundary for
the exact same encoded result returned by the adapter. -/
theorem instantiateEncodedTm?_typed
    (headCodec : PartialCodec Head Pattern)
    {R : Rules Head} {Gamma : Ctx Head n}
    {domain : Tm Head n} {body bodyType : Tm Head (n + 1)}
    {argument : Tm Head n}
    (bodyTyping : HasType R (.snoc Gamma domain) body bodyType)
    (argumentTyping : HasType R Gamma argument domain) :
    instantiateEncodedTm? headCodec n
        (encodeTm headCodec argument) (encodeTm headCodec body) =
        some (encodeTm headCodec (inst0 argument body)) ∧
      HasType R Gamma (inst0 argument body) (inst0 argument bodyType) := by
  exact
    ⟨instantiateEncodedTm?_encode headCodec argument body,
      bodyTyping.betaTarget argumentTyping⟩

/-! ## Positive and negative controls -/

/-- The exact adapter computes the canonical-variable example on which direct
generic binder instantiation fails. -/
theorem adapter_repairsCanonicalVariableBoundary :
    instantiateEncodedTm? towerHeadCodec 0
        (encodeTm towerHeadCodec closedArgument)
        (encodeTm towerHeadCodec openVariable) =
          some (encodeTm towerHeadCodec
            (inst0 closedArgument openVariable)) ∧
      instantiateBVar (encodeTm towerHeadCodec closedArgument)
          (encodeTm towerHeadCodec openVariable) ≠
        encodeTm towerHeadCodec (inst0 closedArgument openVariable) := by
  exact
    ⟨instantiateEncodedTm?_encode towerHeadCodec closedArgument openVariable,
      canonicalData_genericBinder_doesNotCommute⟩

/-- Malformed noncanonical bodies are rejected rather than assigned an
invented substitution meaning. -/
theorem malformedBody_rejected (n : Nat) (replacement : Pattern) :
    instantiateEncodedTm? towerHeadCodec n replacement
      (.fvar "not-canonical-prime-data") = none := by
  cases decoded : decodeTm? towerHeadCodec n replacement <;>
    simp [instantiateEncodedTm?, decoded, decodeTm?]

/-! ## Axiom audit -/

#print axioms instantiateEncodedTm?_encode
#print axioms instantiateEncodedTm?_reflects
#print axioms instantiateEncodedTm?_output_decodes
#print axioms instantiateEncodedTm?_typed
#print axioms adapter_repairsCanonicalVariableBoundary
#print axioms malformedBody_rejected

end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.DeclarationAwareSubstitutionAdapter
