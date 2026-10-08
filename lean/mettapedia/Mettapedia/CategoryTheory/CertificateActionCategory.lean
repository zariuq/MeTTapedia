import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.Algebra.Group.Defs

/-!
# A category of current-state certificate actions with receipts

The independently supplied family may vary with the state. An arrow has
both a complete function between those certificate types and a receipt in
the supplied monoid. Composition updates the certificate and concatenates
the receipts in execution order. Forgetting the receipt is an actual
functor; it does not provide a decoder for the forgotten data.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.CategoryTheory.CertificateActionCategory

open _root_.CategoryTheory

universe u v w
variable {States : Type u}

def Objects (_family : States → Type w) (_Receipt : Type v) := States

variable (family : States → Type w) (Receipt : Type v) [Monoid Receipt]

instance : Category.{max v w} (Objects family Receipt) where
  Hom first last := Receipt × (family first → family last)
  id _ := ⟨1, id⟩
  comp first second := ⟨first.1 * second.1, second.2 ∘ first.2⟩
  id_comp arrow := by
    apply Prod.ext
    · exact one_mul arrow.1
    · rfl
  comp_id arrow := by
    apply Prod.ext
    · exact mul_one arrow.1
    · rfl
  assoc first second third := by
    apply Prod.ext
    · exact mul_assoc first.1 second.1 third.1
    · rfl

variable {family Receipt}
variable {first middle last : Objects family Receipt}

def receipt (action : first ⟶ last) : Receipt := action.1

def apply (action : first ⟶ last) (certificate : family first) : family last :=
  action.2 certificate

theorem receipt_composition (before : first ⟶ middle) (after : middle ⟶ last) :
    receipt (before ≫ after) = receipt before * receipt after := rfl

theorem certificate_composition (before : first ⟶ middle) (after : middle ⟶ last)
    (certificate : family first) :
    apply (before ≫ after) certificate = apply after (apply before certificate) := rfl

theorem identity_receipt (state : Objects family Receipt) : receipt (𝟙 state) = 1 := rfl

theorem identity_certificate (state : Objects family Receipt) (certificate : family state) :
    apply (𝟙 state) certificate = certificate := rfl

/-- The certificate action remains after erasing the independently retained receipt. -/
def erase : Objects family Receipt ⥤ Type w where
  obj state := family state
  map action := TypeCat.ofHom action.2

end Mettapedia.CategoryTheory.CertificateActionCategory
