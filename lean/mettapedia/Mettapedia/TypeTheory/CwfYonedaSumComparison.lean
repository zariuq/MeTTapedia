import Mettapedia.TypeTheory.ContextualSumComprehension
import Mettapedia.TypeTheory.DisplayedPresheafSigma

/-!
# Source dependent sums and complete native pair families

The source sum's local beta, eta and substitution laws give its actual
comprehension isomorphism. Representing that isomorphism identifies the
source sum family with the native dependent sum, retaining both original
display-map witnesses in every contextual fibre.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.CwfYoneda

open CategoryTheory Opposite
open Mettapedia.GSLT.Core.ContextualLadder
open DisplayedPresheafTransport DisplayedPresheafComprehension
open DisplayedPresheafSigma ContextualSumComprehension
open DisplayedPresheafIndexedCwfBridge CategoryIndexedFamilyTypeFormers

universe u w w'
variable (C : Cwf.{u, u, w, w'})

/-- The original dependent codomain lives over the complete represented
first-variable context, rather than only over its current evidence. -/
def dependentBodyFamily {Γ : C.Ctx} (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) :
    DisplayedFamily (totalSpace (family C A)) :=
  reindexDisplayed (comprehensionIso C A).hom (family C B)

def representedSumFamily {Γ : C.Ctx} (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) :
    DisplayedFamily (contextFace C Γ) :=
  sigmaDisplayed (family C A) (dependentBodyFamily C A B)

theorem representedSum_second_restriction {Γ : C.Ctx}
    (A : C.Ty Γ) (B : C.Ty (C.ext Γ A))
    {first second : (contextFace C Γ).Elements} (before : first ⟶ second)
    (receipt : (representedSumFamily C A B).obj first) :
    ((representedSumFamily C A B).map before receipt).2.val =
      C.compS receipt.2.val before.val.unop := by
  change C.compS receipt.2.val
    (((displayedToTotalElements (family C A)).map
      (elementLift (context := Cat.of (contextFace C Γ).Elements)
        (family C A) before receipt.1)).val.unop) = _
  rw [displayedToTotalElements_underlying]
  rfl

/-- Unpack the source sum display witness into its two original display
witnesses. The second witness remains indexed by the first. -/
def sumFamilyForward (sums : StableSums C) {Γ : C.Ctx}
    (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) :
    family C (sums.operations.sigma A B) ⟶ representedSumFamily C A B where
  app point := TypeCat.ofHom fun receipt =>
    let tuple := unpackArrow sums A B receipt.val
    ⟨⟨C.compS (C.wk B) tuple,
        (unpackArrow_base sums A B receipt.val).trans receipt.property⟩,
      ⟨tuple, rfl⟩⟩
  naturality first second before := by
    ext receipt
    let paired : (representedSumFamily C A B).obj first :=
      ⟨⟨C.compS (C.wk B) (unpackArrow sums A B receipt.val),
        (unpackArrow_base sums A B receipt.val).trans receipt.property⟩,
        ⟨unpackArrow sums A B receipt.val, rfl⟩⟩
    apply Sigma.ext
    · apply Subtype.ext
      change C.compS (C.wk B) (unpackArrow sums A B (C.compS receipt.val before.val.unop)) =
        C.compS (C.compS (C.wk B) (unpackArrow sums A B receipt.val)) before.val.unop
      rw [unpackArrow_comp, C.comp_assoc]
    · apply (Subtype.heq_iff_coe_eq ?_).mpr
      · change unpackArrow sums A B (C.compS receipt.val before.val.unop) =
          ((representedSumFamily C A B).map before paired).2.val
        rw [representedSum_second_restriction]
        exact unpackArrow_comp sums A B receipt.val before.val.unop
      · intro candidate
        change (C.compS (C.wk B) candidate =
          C.compS (C.wk B) (unpackArrow sums A B (C.compS receipt.val before.val.unop))) ↔
          C.compS (C.wk B) candidate =
            C.compS (C.compS (C.wk B) (unpackArrow sums A B receipt.val)) before.val.unop
        rw [unpackArrow_comp, C.comp_assoc]

/-- Pair the supplied two complete witnesses using the original source
sum operations. No witness is selected or forgotten. -/
def sumFamilyBackward (sums : StableSums C) {Γ : C.Ctx}
    (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) :
    representedSumFamily C A B ⟶ family C (sums.operations.sigma A B) where
  app point := TypeCat.ofHom fun receipt =>
    ⟨packArrow sums A B receipt.2.val, by
      have over := packArrow_base sums A B receipt.2.val
      have second := receipt.2.property
      change C.compS (C.wk B) receipt.2.val = receipt.1.val at second
      rw [second] at over
      exact over.trans receipt.1.property⟩
  naturality first second before := by
    ext receipt
    apply Subtype.ext
    change packArrow sums A B ((representedSumFamily C A B).map before receipt).2.val =
        C.compS (packArrow sums A B receipt.2.val) before.val.unop
    rw [representedSum_second_restriction]
    exact packArrow_comp sums A B receipt.2.val before.val.unop

/-- The entire source sum family is the actual native dependent pair
family, naturally over all original substitutions. -/
def sumFamilyIso (sums : StableSums C) {Γ : C.Ctx}
    (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) :
    family C (sums.operations.sigma A B) ≅ representedSumFamily C A B where
  hom := sumFamilyForward C sums A B
  inv := sumFamilyBackward C sums A B
  hom_inv_id := by
    ext point receipt
    apply Subtype.ext
    exact pack_unpackArrow sums A B receipt.val
  inv_hom_id := by
    ext point receipt
    apply Sigma.ext
    · apply Subtype.ext
      change C.compS (C.wk B) (unpackArrow sums A B (packArrow sums A B receipt.2.val)) =
        receipt.1.val
      rw [unpack_packArrow]
      exact receipt.2.property
    · apply (Subtype.heq_iff_coe_eq ?_).mpr
      · exact unpack_packArrow sums A B receipt.2.val
      · intro candidate
        have second := receipt.2.property
        change C.compS (C.wk B) receipt.2.val = receipt.1.val at second
        change (C.compS (C.wk B) candidate =
          C.compS (C.wk B) (unpackArrow sums A B (packArrow sums A B receipt.2.val))) ↔
            C.compS (C.wk B) candidate = receipt.1.val
        rw [unpack_packArrow, second]

end Mettapedia.TypeTheory.CwfYoneda
