import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.TypedBetaSubjectReduction
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.DeclarationAwarePatternCodec
import Mettapedia.GSLT.LanguageDef.LF.RootedBetaEtaCorrespondence
import Mettapedia.Cybernetics.DistinctionConservation

/-!
# Declaration-aware substitution boundary

Two lossless encodings expose binders differently.

The rooted LF encoding maps runtime variables to `Pattern.bvar`, so generic
binder instantiation commutes exactly with LF substitution.  The canonical
Prime data encoding instead records an intrinsically scoped variable as an
ordinary tagged data constructor.  This is correct for decoding and structural
checking, but generic `Pattern` binder instantiation intentionally leaves that
constructor untouched.

The negative theorem below rules out a tempting but invalid implementation of
typed Prime beta: applying the generic binder operation directly to canonical
data is not the encoding of intrinsic substitution.  A future authored beta
adapter must therefore decode and re-encode, use a binder-exposing view, or
prove another independently defined operation commutes with intrinsic
substitution.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.DeclarationAwareSubstitutionBoundary

open Mettapedia.Cybernetics
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.LF
open Mettapedia.GSLT.LanguageDef.LFTyping
open Mettapedia.GSLT.LanguageDef.LFRootedBetaEtaCorrespondence
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.DeclarationAwarePatternCodec
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution

/-! ## Positive binder-exposing face -/

/-- The LF carrier exposes object variables as generic bound variables, so
generic binder instantiation is exactly runtime LF beta substitution. -/
theorem lfBinderEncoding_commutes
    (replacement body : LF.Term) :
    instantiateBVar (encodeTerm replacement) (encodeTerm body) =
      encodeTerm (LFTyping.subst0 replacement body) :=
  (encodeTerm_subst0 replacement body).symm

/-! ## Negative canonical-data boundary -/

/-- One open intrinsic variable, represented as canonical Prime data. -/
def openVariable : Tower.Tm 1 :=
  .var 0

/-- One closed intrinsic argument whose outer constructor differs from a
variable encoding. -/
def closedArgument : Tower.Tm 0 :=
  .head (.sort Tower.zero)

/-- Generic binder instantiation cannot see the intrinsically scoped variable
inside its canonical data tag. -/
theorem genericBinder_leavesCanonicalVariable :
    instantiateBVar (encodeTm towerHeadCodec closedArgument)
        (encodeTm towerHeadCodec openVariable) =
      encodeTm towerHeadCodec openVariable := by
  simp [instantiateBVar, instantiateBVarAt, openVariable, closedArgument,
    encodeTm, encodeNat]

/-- Intrinsic substitution does see the newest variable and replaces it. -/
theorem intrinsicOpening_replacesCanonicalVariable :
    encodeTm towerHeadCodec (inst0 closedArgument openVariable) =
      encodeTm towerHeadCodec closedArgument := by
  rfl

/-- The naïve direct use of generic binder instantiation on canonical Prime
data does not commute with intrinsic substitution. -/
theorem canonicalData_genericBinder_doesNotCommute :
    instantiateBVar (encodeTm towerHeadCodec closedArgument)
        (encodeTm towerHeadCodec openVariable) ≠
      encodeTm towerHeadCodec (inst0 closedArgument openVariable) := by
  rw [genericBinder_leavesCanonicalVariable,
    intrinsicOpening_replacesCanonicalVariable]
  simp [openVariable, closedArgument, encodeTm]

/-! ## Exact distinction conservation -/

/-- The rooted LF encoding preserves every exact syntactic distinction. -/
theorem lfEncoding_conservesExactDistinctions :
    Distinction.Conserves
      (Distinction.inequality LF.Term)
      (Distinction.inequality Pattern)
      encodeTerm :=
  (Distinction.conserves_inequality_iff_injective encodeTerm).2
    encodeTerm_injective

/-- The canonical Prime encoding also preserves every exact intrinsic
distinction.  The failed commutation theorem is therefore about operational
binder structure, not an encoding collision. -/
theorem canonicalEncoding_conservesExactDistinctions (n : Nat) :
    Distinction.Conserves
      (Distinction.inequality (Tower.Tm n))
      (Distinction.inequality Pattern)
      (encodeTm towerHeadCodec) :=
  (Distinction.conserves_inequality_iff_injective
      (encodeTm towerHeadCodec : Tower.Tm n → Pattern)).2
    (tmCodec towerHeadCodec n).encode_injective

/-! ## Axiom audit -/

#print axioms lfBinderEncoding_commutes
#print axioms canonicalData_genericBinder_doesNotCommute
#print axioms lfEncoding_conservesExactDistinctions
#print axioms canonicalEncoding_conservesExactDistinctions

end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.DeclarationAwareSubstitutionBoundary
