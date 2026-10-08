import Mettapedia.GSLT.LanguageDef.BootstrapCell.Replay
import Mathlib.Logic.Equiv.Basic

/-!
# Accepted raw certificates are in bijection with derivations

`Replay` proves the two halves: a raw certificate is accepted for a goal
exactly when it is the erasure of a derivation of that goal
(`G2_checkRaw_iff_exists_derivation_erases_to`), and a derivation is
determined by its erasure (`ReplaySignature.Deriv.eq_of_erase_eq`).  This
module states them together, for the checker of a validated calculus: erasure
is a bijection from the derivations of a goal onto its accepted raw
certificates (`checkedEquiv`).

So acceptance by replay is proof-relevant.  An accepted certificate is not
only evidence that some derivation exists; it is one derivation, and two
certificates are two derivations.

The inverse is given here by unique existence.  A computed inverse, by
recursion over the certificate, is `reconstruct` in
`Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.MILNativeMaterialization`.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.BootstrapCell

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker

variable {definition : ValidatedCalculusLanguageDef} {goal : Pattern}

/-- **A derivation is determined by its raw certificate.** -/
theorem erase_injective :
    Function.Injective (Derivation.erase : Derivation definition goal → RawProof) := by
  intro first second same
  have replayed : (toDeriv first).erase = (toDeriv second).erase := by
    rw [toDeriv_erase, toDeriv_erase, same]
  exact (derivationEquiv definition goal).injective
    (ReplaySignature.Deriv.eq_of_erase_eq _ _ replayed)

/-- The accepted raw certificate of a derivation. -/
def toChecked (derivation : Derivation definition goal) : CheckedProof definition goal :=
  ⟨derivation.erase, checkRaw_erase derivation⟩

theorem toChecked_bijective :
    Function.Bijective (toChecked : Derivation definition goal → CheckedProof definition goal) := by
  constructor
  · intro first second same
    exact erase_injective (congrArg Subtype.val same)
  · rintro ⟨raw, accepted⟩
    obtain ⟨derivation, erased⟩ := G2_checkRaw_iff_exists_derivation_erases_to.mp accepted
    exact ⟨derivation, Subtype.ext erased⟩

/-- **The derivations of a goal are its accepted raw certificates.** -/
noncomputable def checkedEquiv (definition : ValidatedCalculusLanguageDef) (goal : Pattern) :
    Derivation definition goal ≃ CheckedProof definition goal :=
  Equiv.ofBijective toChecked toChecked_bijective

@[simp] theorem checkedEquiv_apply (derivation : Derivation definition goal) :
    (checkedEquiv definition goal derivation).1 = derivation.erase := rfl

/-- The derivation that an accepted raw certificate is. -/
noncomputable def derivationOf (raw : RawProof) (accepted : checkRaw definition goal raw = true) :
    Derivation definition goal :=
  (checkedEquiv definition goal).symm ⟨raw, accepted⟩

@[simp] theorem derivationOf_erase (raw : RawProof)
    (accepted : checkRaw definition goal raw = true) :
    (derivationOf raw accepted).erase = raw :=
  congrArg Subtype.val ((checkedEquiv definition goal).apply_symm_apply ⟨raw, accepted⟩)

@[simp] theorem derivationOf_of_erase (derivation : Derivation definition goal) :
    derivationOf derivation.erase (checkRaw_erase derivation) = derivation :=
  (checkedEquiv definition goal).symm_apply_apply derivation

#print axioms erase_injective
#print axioms checkedEquiv
#print axioms derivationOf_erase

end Mettapedia.GSLT.LanguageDef.BootstrapCell
