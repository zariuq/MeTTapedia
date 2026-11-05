import Mettapedia.Logic.HOL.ProofSyntaxCut
import Mettapedia.Logic.HOL.WitnessedExtension

/-!
# Retained beta at a freshly opened variable

Opening a weakened abstraction at the fresh variable returns its original
body. The receipt has one inference node and needs no extensionality rule.
-/

set_option autoImplicit false
namespace Mettapedia.Logic.HOL.ProofSyntax
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base} {σ τ : Ty Base}
  {Δ : List (Formula Const (σ :: Γ))}

def betaAtFresh (body : Term Const (σ :: Γ) τ) :
    ProofSyntax Const Δ (.eq (.app (HOL.weaken (.lam body)) (.var .vz)) body) :=
  .castIndices rfl (congrArg₂ (fun left right : Term Const (σ :: Γ) τ => Term.eq left right)
    (show Term.app (.lam (HOL.rename (Rename.lift Rename.weaken) body)) (.var .vz) =
      Term.app (HOL.weaken (.lam body)) (.var .vz) from rfl)
    (instantiate_vz_rename_lift_weaken body))
    (.beta (.var .vz) (HOL.rename (Rename.lift Rename.weaken) body))

theorem betaAtFresh_free (body : Term Const (σ :: Γ) τ) :
    (betaAtFresh (Δ := Δ) body).FunctionExtensionalityFree := by
  unfold betaAtFresh
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  trivial

theorem betaAtFresh_nodeCount (body : Term Const (σ :: Γ) τ) :
    Derivation.nodeCount (betaAtFresh (Δ := Δ) body).observe = 1 := by
  unfold betaAtFresh
  rw [ProofSyntax.observe_nodeCount_castIndices]
  rfl

end Mettapedia.Logic.HOL.ProofSyntax
