import Mettapedia.Logic.HOL.ProofSyntaxStructural

/-!
# A retained cut with one supplied premise receipt

The continuation can use the premise as a hypothesis. Implication
introduction and elimination attach the supplied receipt once. The exact
proof-node count is independent of how often that hypothesis occurs.
-/

set_option autoImplicit false
namespace Mettapedia.Logic.HOL.ProofSyntax
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base}
  {Δ : List (Formula Const Γ)} {premise result : Formula Const Γ}

def cut (proof : ProofSyntax Const Δ premise) (continuation : ProofSyntax Const (premise :: Δ) result) :
    ProofSyntax Const Δ result := .impE (.impI continuation) proof

theorem cut_free (proof : ProofSyntax Const Δ premise) (continuation : ProofSyntax Const (premise :: Δ) result)
    (proofFree : proof.FunctionExtensionalityFree) (continuationFree : continuation.FunctionExtensionalityFree) :
    (cut proof continuation).FunctionExtensionalityFree := ⟨continuationFree,proofFree⟩

theorem cut_nodeCount (proof : ProofSyntax Const Δ premise) (continuation : ProofSyntax Const (premise :: Δ) result) :
    Derivation.nodeCount (cut proof continuation).observe = proof.nodeCount + continuation.nodeCount + 2 := by
  simp [cut,ProofSyntax.nodeCount,ProofSyntax.observe]
  omega

theorem observe_nodeCount_castIndices {Δ' : List (Formula Const Γ)} {result' : Formula Const Γ}
    (assumptions : Δ = Δ') (conclusion : result = result') (proof : ProofSyntax Const Δ result) :
    Derivation.nodeCount (proof.castIndices assumptions conclusion).observe = Derivation.nodeCount proof.observe :=
  nodeCount_castIndices assumptions conclusion proof

theorem observe_mono_nodeCount {Δ' : List (Formula Const Γ)} (transport : OccurrenceMap Δ Δ')
    (proof : ProofSyntax Const Δ result) :
    Derivation.nodeCount (proof.mono transport).observe = Derivation.nodeCount proof.observe :=
  mono_nodeCount transport proof

end Mettapedia.Logic.HOL.ProofSyntax
