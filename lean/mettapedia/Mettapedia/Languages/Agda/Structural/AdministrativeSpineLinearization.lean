import Mettapedia.Languages.Agda.Structural.AdministrativeEndpointRegularity

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Structural.AdministrativeStatics.CanonizationPreparation

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.FiniteRulePremiseLists
open Statics (RawTm RawTy RawContext TypeParameter TypeBody)

noncomputable def consToNested {n : Nat} {Γ : RawContext n} {A : TypeParameter n}
    {B : TypeBody n} {f u : RawTm n} {rest : Spine (scope n)} {C : RawTy n}
    (head : CoreDerivation (Statics.typed Γ f (Statics.piType A B).code))
    (argument : CoreDerivation (Statics.typed Γ u A.code))
    (tail : Action Γ (B.instantiate u).code rest C) :
    CoreDerivation (Statics.termEqual Γ (eliminate f (cons (apply u) rest))
      (eliminate (eliminate f (cons (apply u) nil)) rest) C) := by
  let initial := Derivation.cons (A := A) (B := B) argument (Derivation.nil Γ (B.instantiate u).code)
  let nested := Derivation.nestedElimination head initial tail
  let first := Derivation.appendCons (Derivation.append initial tail)
  let sameArgument := Derivation.core (.reflexivity Γ u A.code)
    (consEvidence CoreDerivation argument (noEvidence CoreDerivation))
  let second := Derivation.spineCons (A := A) (B := B) sameArgument
    (Derivation.appendEmpty (Derivation.append (Derivation.nil Γ (B.instantiate u).code) tail))
  let sameHead := Derivation.core (.reflexivity Γ f (Statics.piType A B).code)
    (consEvidence CoreDerivation head (noEvidence CoreDerivation))
  let flat := Derivation.eliminationCongruence sameHead (Derivation.spineTrans first second)
  let composite := Derivation.core (.transitivity Γ
    (eliminate (eliminate f (cons (apply u) nil)) rest)
    (eliminate f (append (cons (apply u) nil) rest)) (eliminate f (cons (apply u) rest)) C)
    (consEvidence CoreDerivation nested (consEvidence CoreDerivation flat (noEvidence CoreDerivation)))
  exact Derivation.core (.symmetry Γ (eliminate (eliminate f (cons (apply u) nil)) rest)
    (eliminate f (cons (apply u) rest)) C)
    (consEvidence CoreDerivation composite (noEvidence CoreDerivation))

end Mettapedia.Languages.Agda.Structural.AdministrativeStatics.CanonizationPreparation
