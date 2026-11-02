import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.TierZeroKernel
import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.Calculus

/-!
# The core tier-zero theorem on the shared term store

The co-de-Bruijn execution is first refined to the guarded rewriting calculus on unfolded
binding trees. The core tier-zero theorem then preserves derivability at the
theorem space. Store growth, canonicality and reference validity are retained
at the same boundary.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.TierZeroKernel

open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
open Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting
open Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings

universe uN

variable {Head V : Type} {N : Type uN} [DecidableEq V] [DecidableEq Head] [DecidableEq N]
  {space : Mettapedia.GSLT.LanguageDef.SignatureIndexedABT.Term Head → N}

/-- **Shared-store tier zero.** A shared process step grows the canonical
store, preserves valid references, and preserves derivability of every value
at the theorem space under the installed guarded rewriting rule instances. -/
theorem sharedProcessStep_allDerivable
    {process : (treeCalculus (V := V) space).Process}
    {store store' : Store Head} {bag bag' : Multiset Ref}
    (canonical : Canonical store) (validBag : ∀ reference ∈ bag, CanonRef store reference)
    (step : SharedProcessStep process store bag store' bag')
    {theorems : N}
    {initial : Mettapedia.GSLT.LanguageDef.SignatureIndexedABT.Term Head → Prop}
    (validBefore :
      Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.TierZeroKernel.AllDerivable
        (treeCalculus (V := V) space) theorems
        (Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.TierZeroKernel.Derivable
          initial
          (Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.TierZeroKernel.InstalledInfers
            (treeCalculus (V := V) space) theorems process.rules))
        (trees store bag)) :
    store <+: store' ∧ Canonical store' ∧
      (∀ reference ∈ bag', CanonRef store' reference) ∧
      Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.TierZeroKernel.AllDerivable
        (treeCalculus (V := V) space) theorems
        (Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.TierZeroKernel.Derivable
          initial
          (Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.TierZeroKernel.InstalledInfers
            (treeCalculus (V := V) space) theorems process.rules))
        (trees store' bag') := by
  obtain ⟨growth, canonical', validBag', treeStep⟩ :=
    sharedProcessStep_sound canonical validBag step
  exact ⟨growth, canonical', validBag',
    Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.TierZeroKernel.Calculus.Process.Step.allDerivable
      treeStep validBefore⟩

end Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.TierZeroKernel
