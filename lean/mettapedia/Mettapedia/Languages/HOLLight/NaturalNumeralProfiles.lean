import Mettapedia.Languages.HOLLight.NaturalPrimitiveProfiles
import Mettapedia.Logic.HOL.NaturalNumeralProofs

/-!
# Finite constructor-tag proofs from the native natural profiles

The two premises are the existing native separation and injectivity formulas.
The general numeral proof builder retains them as explicit assumptions until
their actual checked cache roots are supplied by hypothesis discharge.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.HOLLight.NaturalNumeralProfiles

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open HOL

abbrev Signature := NaturalModelCategoricity.Signature

def assumptions (signature : Signature) : List (ClosedFormula Symbol) :=
  [NaturalPrimitiveProfiles.separationNative signature, NaturalPrimitiveProfiles.injectivityNative signature]

def numeral (signature : Signature) (n : Nat) : ClosedTerm Symbol signature.number :=
  NaturalNumeralProofs.numeral signature.zero signature.successor n

def statement (signature : Signature) (first second : Nat) : ClosedFormula Symbol :=
  .not (.eq (numeral signature first) (numeral signature second))

theorem separation_native (signature : Signature) :
    NaturalNumeralProofs.separation signature.zero signature.successor =
      NaturalPrimitiveProfiles.separationNative signature := rfl

theorem injectivity_native (signature : Signature) :
    NaturalNumeralProofs.injectivity signature.successor =
      NaturalPrimitiveProfiles.injectivityNative signature := rfl

def separationPremise (signature : Signature) :
    ProofSyntax Symbol (assumptions signature)
      (NaturalNumeralProofs.separation signature.zero signature.successor) :=
  ProofSyntax.castIndices rfl (separation_native signature).symm (.hyp ⟨0, by simp [assumptions]⟩)

def injectivityPremise (signature : Signature) :
    ProofSyntax Symbol (assumptions signature) (NaturalNumeralProofs.injectivity signature.successor) :=
  ProofSyntax.castIndices rfl (injectivity_native signature).symm (.hyp ⟨1, by simp [assumptions]⟩)

def proof (signature : Signature) (first second : Nat) (different : first ≠ second) :
    ProofSyntax Symbol (assumptions signature) (statement signature first second) :=
  NaturalNumeralProofs.unequal signature.zero signature.successor
    (separationPremise signature) (injectivityPremise signature) first second different

def proof? (signature : Signature) (first second : Nat) :
    Option (ProofSyntax Symbol (assumptions signature) (statement signature first second)) :=
  if different : first ≠ second then some (proof signature first second different) else none

theorem equal_refused (signature : Signature) (n : Nat) : (proof? signature n n).isNone = true := by
  simp [proof?]

theorem proof_free (signature : Signature) (first second : Nat) (different : first ≠ second) :
    (proof signature first second different).FunctionExtensionalityFree := by
  apply NaturalNumeralProofs.unequal_free
  · unfold separationPremise
    apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    trivial
  · unfold injectivityPremise
    apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    trivial

local instance : DecidablePred emptyAxiomPolicy := fun _ => isFalse id

def compile (signature : Signature) (first second : Nat) (different : first ≠ second)
    (origin : ProofExecution.Origin) :=
  RetainedCompilation.compileWithoutFunctionExtensionality emptyAxiomPolicy
    (proof signature first second different) (proof_free signature first second different)
    ReverseTranslation.Naming.empty origin

theorem compile_conclusion (signature : Signature) (first second : Nat) (different : first ≠ second)
    (origin : ProofExecution.Origin) :
    (compile signature first second different origin).proof.result.sequent.concl =
      CachedSourceExpansion.encode (statement signature first second) :=
  (compile signature first second different origin).conclusion_exact

#print axioms proof_free
#print axioms compile_conclusion

end Mettapedia.Languages.HOLLight.NaturalNumeralProfiles
