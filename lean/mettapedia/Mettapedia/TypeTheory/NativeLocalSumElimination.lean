import Mettapedia.TypeTheory.NativeLocalTypeOperations
import Mettapedia.TypeTheory.ContextualSumComprehension

/-!
# Full motives for native local dependent pairs

The earned native local sum operations satisfy the shared beta, eta and
substitution interface. Its comprehension comparison supplies elimination
for motives over the complete pair context, including both components.
The comparison and elimination are derived from those local term laws.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.NativeLocalSumElimination

open CategoryTheory
open Mettapedia.Computability.ComputationalTrinity
open Mettapedia.GSLT.Core.ContextualLadder
open DisplayedPresheafComprehension DisplayedPresheafCwf
open ContextualLocalUniverses NativeLocalTypeFormers NativeLocalTypeOperations
open ContextualSumComprehension

universe u
variable {C : Type u} [Category.{u} C]
variable {X : Face.{u, u, u} C}

noncomputable def stableSums (C : Type u) [Category.{u} C] : StableSums (localModel C) where
  operations := sums C
  beta := sums_beta C
  eta := by intro X A B value; exact sum_eta (A := A) (B := B) value
  substitution := sums_substitution C

noncomputable def fullMotiveEquiv (A : NativeType X)
    (B : NativeType (totalSpace A.decoded))
    (M : (localModel C).Ty (sumContext (stableSums C) A B)) :
    (localModel C).Tm (tupleContext A B)
        ((localModel C).tySub M (pack (stableSums C) A B)) ≃
      (localModel C).Tm (sumContext (stableSums C) A B) M :=
  sectionEquiv (stableSums C) A B M

attribute [local irreducible] stableSums fullMotiveEquiv

theorem fullMotiveEquiv_inverse (A : NativeType X)
    (B : NativeType (totalSpace A.decoded))
    (M : (localModel C).Ty (sumContext (stableSums C) A B))
    (term : (localModel C).Tm (sumContext (stableSums C) A B) M) :
    (fullMotiveEquiv A B M).symm term =
      (localModel C).tmSub term (pack (stableSums C) A B) := by
  unfold fullMotiveEquiv sectionEquiv
  rfl

theorem full_motive_beta (A : NativeType X)
    (B : NativeType (totalSpace A.decoded))
    (M : (localModel C).Ty (sumContext (stableSums C) A B))
    (body : (localModel C).Tm (tupleContext A B)
      ((localModel C).tySub M (pack (stableSums C) A B))) :
    (localModel C).tmSub ((fullMotiveEquiv A B M) body) (pack (stableSums C) A B) = body := by
  rw [← fullMotiveEquiv_inverse]
  exact (fullMotiveEquiv A B M).symm_apply_apply body

theorem full_motive_eta (A : NativeType X)
    (B : NativeType (totalSpace A.decoded))
    (M : (localModel C).Ty (sumContext (stableSums C) A B))
    (term : (localModel C).Tm (sumContext (stableSums C) A B) M) :
    fullMotiveEquiv A B M ((localModel C).tmSub term (pack (stableSums C) A B)) = term := by
  rw [← fullMotiveEquiv_inverse]
  exact (fullMotiveEquiv A B M).apply_symm_apply term

end Mettapedia.TypeTheory.NativeLocalSumElimination
