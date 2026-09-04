import Mettapedia.GSLT.LanguageDef.NIKMetalogic
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.DeclarationAwareFormedTyping

/-!
# NIK authority for the declaration-aware formed Prime fragment

This module packages the existing exact intrinsic/checker boundary as a NIK
theory and authority contract.  Its scope is the currently supported formed
structural fragment: context formation, type formation, and structural typing.
It is not a claim that the full cumulative Prime DTT is already covered.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.DeclarationAwareNIKAuthority

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.GSLT.LanguageDef.NIKMetalogic
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.DeclarationAwareFormedTyping

/-- The validated authored calculus is the signature selected by this one
fragment profile. -/
def theory : TheoryFamily Unit where
  Signature := ValidatedCalculusLanguageDef
  signatureOf := fun _ => formedTypingExtension.target
  Claim := fun _ => FormedTypingQuery
  Scope := fun _ query => Nonempty (IntrinsicFormedTyping query)
  Meaning := fun _ query => Nonempty (IntrinsicFormedTyping query)
  scope_sound := by
    intro kind query evidence
    exact evidence

/-- Native replay uses the already-qualified nodewise-canonical checker. -/
def checker : Checker FormedTypingQuery RawFormedProof where
  check := checkCanonicalRaw

/-- Exactness is inherited from the proved forward compiler and arbitrary
accepted-proof reflection boundary, not from defining scope by replay. -/
theorem checker_authority :
    checker.Authority (fun query => Nonempty (IntrinsicFormedTyping query)) where
  sound := by
    intro query proof accepted
    exact ⟨reflectCanonicalAcceptedRaw proof accepted⟩
  complete := by
    intro query evidence
    obtain ⟨intrinsic⟩ := evidence
    exact ⟨intrinsic.raw, intrinsic.canonicalRaw_accepted⟩

/-- The proof-carrying NIK contract for the currently supported formed DTT
fragment. -/
def contract : AuthorityContract theory where
  Certificate := fun _ => RawFormedProof
  checker := fun _ => checker
  scopeAuthority := fun _ => checker_authority

/-- The ordinary packed NIK authority family. -/
def family := contract.toAuthorityFamily

/-! ## Positive and negative controls -/

open DeclarationAwareFormedTyping.Examples

/-- Positive control: the existing nontrivial dependent function example is
accepted through the NIK-packaged checker without changing its proof. -/
theorem simplePi_replays :
    (contract.checker ()).check simplePiQuery simplePiIntrinsic.raw = true :=
  simplePi_canonical_raw_accepted

/-- Negative control: the nodewise canonical boundary rejects the existing
wrong-universe proof package. -/
theorem wrongLevel_rejected :
    (contract.checker ()).check wrongLevelQuery simplePiIntrinsic.raw = false := by
  apply Bool.eq_false_of_not_eq_true
  intro accepted
  exact wrongLevel_has_no_canonical_accepted_bundle
    ⟨simplePiIntrinsic.raw, accepted⟩

/-- Exact authority turns every accepted native certificate back into the
intrinsic formed judgment. -/
theorem accepted_reflects_intrinsic
    (query : FormedTypingQuery) (proof : RawFormedProof)
    (accepted : (contract.checker ()).check query proof = true) :
    Nonempty (IntrinsicFormedTyping query) :=
  (contract.scopeAuthority ()).sound query proof accepted

#print axioms checker_authority
#print axioms simplePi_replays
#print axioms wrongLevel_rejected
#print axioms accepted_reflects_intrinsic

end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.DeclarationAwareNIKAuthority
