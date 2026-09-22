import Mettapedia.Logic.HOL.Embedding.ZFSetHOLContextualInterpretation
import Mettapedia.Logic.HOL.Embedding.ZFSetHOLProofInterpretation

/-!
# Retained proof-induced maps as actual contextual function graphs

A source universal implication gives a term of the existing set-coded CwF:
an actual graph from the source refinement fibre to the target refinement
fibre. Its application agrees with the independently constructed Henkin map,
and arbitrary contextual reindexing commutes with graph construction.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.Embedding.ZFSetHOLContextualProofConsumption

open ZFSetHOLProofInterpretation ZFSetHOLTermInterpretation ZFSetDependentProducts
open ZFSetUniverseClosure ZFSetUniverseInterpretation
open ZFSetContextualInterpretation (SetFamily Section Extension piFamily piDecode)
open HenkinPredicateFamilyInterpretation

universe u

noncomputable def refinementFamily (h : CofinalInaccessibles.{u})
    {Γ : Ctx Unit} {A : Ty Unit} (hypotheses : List (Formula UniverseSymbol Γ))
    (φ : Formula UniverseSymbol (A :: Γ)) : SetFamily.{u + 1} (CodedSatisfied h hypotheses) :=
  fun ρ => refinementCode h φ ρ.1

noncomputable def mapping (h : CofinalInaccessibles.{u})
    {Γ : Ctx Unit} {A : Ty Unit} {hypotheses : List (Formula UniverseSymbol Γ)}
    {φ ψ : Formula UniverseSymbol (A :: Γ)}
    (proof : ProofSyntax UniverseSymbol hypotheses (.all (.imp φ ψ))) :
    Section (piFamily (refinementFamily h hypotheses φ)
      (fun pair => refinementFamily h hypotheses ψ pair.1)) :=
  ZFSetContextualInterpretation.lam (fun pair => refinementMap h proof pair.1 pair.2)

theorem mapping_application (h : CofinalInaccessibles.{u})
    {Γ : Ctx Unit} {A : Ty Unit} {hypotheses : List (Formula UniverseSymbol Γ)}
    {φ ψ : Formula UniverseSymbol (A :: Γ)}
    (proof : ProofSyntax UniverseSymbol hypotheses (.all (.imp φ ψ)))
    (ρ : CodedSatisfied h hypotheses) (point : Elements (refinementCode h φ ρ.1)) :
    piDecode (refinementFamily h hypotheses φ)
        (fun pair => refinementFamily h hypotheses ψ pair.1) ρ
        (mapping h proof ρ) point = refinementMap h proof ρ point :=
  congrFun ((piDecode (refinementFamily h hypotheses φ)
    (fun pair => refinementFamily h hypotheses ψ pair.1) ρ).apply_symm_apply
      (fun point => refinementMap h proof ρ point)) point

theorem mapping_decodes_to_original (h : CofinalInaccessibles.{u})
    {Γ : Ctx Unit} {A : Ty Unit} {hypotheses : List (Formula UniverseSymbol Γ)}
    {φ ψ : Formula UniverseSymbol (A :: Γ)}
    (proof : ProofSyntax UniverseSymbol hypotheses (.all (.imp φ ψ)))
    (ρ : CodedSatisfied h hypotheses) (point : Elements (refinementCode h φ ρ.1)) :
    refinementEquiv h ψ ρ.1
        (piDecode (refinementFamily h hypotheses φ)
          (fun pair => refinementFamily h hypotheses ψ pair.1) ρ (mapping h proof ρ) point) =
      refinementMapOfProof (universeModel h) (universeFunctionsRespectEqv h)
        proof (decodeSatisfied h ρ) (refinementEquiv h φ ρ.1 point) := by
  rw [mapping_application]
  exact refinementMap_square h proof ρ point

theorem mapping_preserves_value (h : CofinalInaccessibles.{u})
    {Γ : Ctx Unit} {A : Ty Unit} {hypotheses : List (Formula UniverseSymbol Γ)}
    {φ ψ : Formula UniverseSymbol (A :: Γ)}
    (proof : ProofSyntax UniverseSymbol hypotheses (.all (.imp φ ψ)))
    (ρ : CodedSatisfied h hypotheses) (point : Elements (refinementCode h φ ρ.1)) :
    (piDecode (refinementFamily h hypotheses φ)
        (fun pair => refinementFamily h hypotheses ψ pair.1) ρ
        (mapping h proof ρ) point).1 = point.1 := by
  rw [mapping_application]
  rfl

theorem mapping_reindex (h : CofinalInaccessibles.{u})
    {Γ : Ctx Unit} {A : Ty Unit} {hypotheses : List (Formula UniverseSymbol Γ)}
    {φ ψ : Formula UniverseSymbol (A :: Γ)}
    (proof : ProofSyntax UniverseSymbol hypotheses (.all (.imp φ ψ)))
    {Δ : Type (u + 2)} (θ : Δ → CodedSatisfied h hypotheses) :
    (fun δ => mapping h proof (θ δ)) =
      ZFSetContextualInterpretation.lam
        (a := refinementFamily h hypotheses φ ∘ θ)
        (b := fun pair => refinementFamily h hypotheses ψ (θ pair.1))
        (fun pair => refinementMap h proof (θ pair.1) pair.2) :=
  ZFSetContextualInterpretation.lam_substitution θ _

/-- A first-class function graph induced by the retained source proof is
applied at a genuine member of a predicate-dependent refinement fibre. -/
theorem discard_true_application (h : CofinalInaccessibles.{u}) :
    (piDecode (refinementFamily h [] (.and equalsParameter .top))
        (fun pair => refinementFamily h [] equalsParameter pair.1)
        (noHypotheses h emptyParameter) (mapping h discardTrue (noHypotheses h emptyParameter))
        (equalPoint h)).1 = ∅ :=
  mapping_preserves_value h discardTrue (noHypotheses h emptyParameter) (equalPoint h)

#print axioms mapping
#print axioms mapping_application
#print axioms mapping_decodes_to_original
#print axioms mapping_preserves_value
#print axioms mapping_reindex
#print axioms discard_true_application

end Mettapedia.Logic.HOL.Embedding.ZFSetHOLContextualProofConsumption
