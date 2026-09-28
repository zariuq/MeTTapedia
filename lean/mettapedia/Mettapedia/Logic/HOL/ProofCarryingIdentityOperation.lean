import Mettapedia.Logic.HOL.ProofCarryingPipeline

/-!
# Identity operation on proof-carrying HOL values

For any predicate, the identity function preserves its invariant. The
retained proof is an actual HOL derivation: beta identifies the applied
identity with its argument, congruence transports that equality through the
predicate, and implication elimination consumes the incoming invariant.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.ProofCarryingIdentityOperation

open Mettapedia.Logic

universe u v

def identityOperation {Base : Type u} {Const : HOL.Ty Base → Type v}
    {Γ : HOL.Ctx Base} {Δ : List (HOL.Formula Const Γ)}
    {σ : HOL.Ty Base} (predicate : HOL.Term Const Γ (.arr σ .prop)) :
    HOL.ProofCarryingPipeline.Operation predicate Δ where
  term := .lam (.var .vz)
  evidence := by
    apply HOL.ProofSyntax.allI
    apply HOL.ProofSyntax.impI
    let point : HOL.Term Const (σ :: Γ) σ := .var .vz
    let body : HOL.Term Const (σ :: σ :: Γ) σ := .var .vz
    let identity : HOL.Term Const (σ :: Γ) (.arr σ σ) := .lam body
    let liftedPredicate : HOL.Term Const (σ :: Γ) (.arr σ .prop) :=
      HOL.weaken predicate
    change HOL.ProofSyntax Const
      (.app liftedPredicate point :: HOL.weakenHyps Δ)
      (.app liftedPredicate (.app identity point))
    have appliedIdentity : HOL.ProofSyntax Const
        (.app liftedPredicate point :: HOL.weakenHyps Δ)
        (.eq (.app identity point) point) := by
      simpa only [identity, body, HOL.instantiate_var_vz] using
        (HOL.ProofSyntax.beta (Δ :=
          .app liftedPredicate point :: HOL.weakenHyps Δ) point body)
    have predicatesEqual := HOL.ProofSyntax.eqAppArg
      liftedPredicate appliedIdentity
    exact HOL.ProofSyntax.impE
      (HOL.ProofSyntax.eqPropER predicatesEqual) (.hyp 0)

#print axioms identityOperation

end Mettapedia.Logic.HOL.ProofCarryingIdentityOperation
