import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.AwodeyButzHeytingPointModelBridge

namespace Mettapedia.AutoBooks.Codex.IntuitionisticHOL

open Mettapedia.Logic.HOL

universe u v

namespace AwodeyButzHeytingPointModelBridgeRegression

open HigherOrderPointHeytingGlobalModelBridge

variable {Base : Type u} {Const : Ty Base → Type v}
variable {M : GlobalModel Base Const}

theorem carrier_encode_decode_path
    (W : OnePointTopologicalWitness M)
    {τ : Ty Base}
    (x : M.Carrier τ) :
    W.decode (W.encode x) = x := by
  exact W.decode_encode x

theorem heyting_underlying_path
    (W : OnePointHeytingWitness M) :
    W.toHeyting.toTopologicalInterpretation = W.toTopologicalInterpretation := by
  exact W.toHeyting_toTopological

theorem concrete_witness_encode_decode_path
    {τ : Ty Base}
    (x : M.Carrier τ) :
    (concreteOnePointTopologicalWitness (M := M)).decode
        ((concreteOnePointTopologicalWitness (M := M)).encode x) = x := by
  exact (concreteOnePointTopologicalWitness (M := M)).decode_encode x

theorem concrete_witness_const_path
    {τ : Ty Base}
    (c : Const τ) :
    (concreteOnePointTopologicalWitness (M := M)).encode (M.const c) =
      (concreteOnePointTopologicalInterpretation (M := M).const c).toContinuousMap () := by
  exact concreteOnePointTopologicalWitness_const (M := M) c

theorem concrete_prop_top_path :
    (concreteOnePointPropositionWitness (M := M)).propTop.toContinuousMap () =
      (concreteOnePointPropositionWitness (M := M)).encodeProp M.topP := by
  exact concreteOnePointPropositionWitness_top (M := M)

theorem concrete_prop_meet_path
    (p q : M.Carrier .prop) :
    (concreteOnePointPropositionWitness (M := M)).fiberMeet
        ⟨((concreteOnePointPropositionWitness (M := M)).encodeProp p,
          (concreteOnePointPropositionWitness (M := M)).encodeProp q), by simp⟩ =
      (concreteOnePointPropositionWitness (M := M)).encodeProp (M.andP p q) := by
  exact concreteOnePointPropositionWitness_meet (M := M) p q

theorem concrete_formula_and_path
    {Γ : Ctx Base}
    (φ ψ : Formula Const Γ)
    (γ :
      (HigherOrderPointTopologicalGlobalModelBridge.basicInterp.ctxSpace (M := M) Γ).Carrier) :
    (concreteOnePointPropositionWitness (M := M)).fiberMeet
        ⟨((concreteOnePointPropositionWitness (M := M)).encodeProp
            (pointFormulaValue (M := M) φ γ),
          (concreteOnePointPropositionWitness (M := M)).encodeProp
            (pointFormulaValue (M := M) ψ γ)), by simp⟩ =
      (concreteOnePointPropositionWitness (M := M)).encodeProp
        (pointFormulaValue (M := M) (Term.and φ ψ) γ) := by
  exact concreteOnePointPropositionWitness_formula_and (M := M) φ ψ γ

theorem concrete_and_counterexample_consumer_path
    {Γ : Ctx Base}
    {Δ : List (Formula Const Γ)}
    (φ ψ : Formula Const Γ)
    (γ :
      (HigherOrderPointTopologicalGlobalModelBridge.basicInterp.ctxSpace (M := M) Γ).Carrier)
    (hΔ :
      HigherOrderPointTopologicalGlobalModelBridge.basicInterp.truthAntecedent
        (M := M) Δ γ = ⊤)
    (hAnd :
      M.truth
        ((concreteOnePointPropositionWitness (M := M)).decodeProp
          ((concreteOnePointPropositionWitness (M := M)).fiberMeet
            ⟨((concreteOnePointPropositionWitness (M := M)).encodeProp
                (pointFormulaValue (M := M) φ γ),
              (concreteOnePointPropositionWitness (M := M)).encodeProp
                (pointFormulaValue (M := M) ψ γ)), by simp⟩)) ≠ ⊤) :
    ¬ Derivable (Base := Base) (Const := Const) Δ (Term.and φ ψ) := by
  exact not_derivable_of_and_formula_witness_counterexample (M := M) φ ψ γ hΔ hAnd

theorem concrete_formula_or_path
    {Γ : Ctx Base}
    (φ ψ : Formula Const Γ)
    (γ :
      (HigherOrderPointTopologicalGlobalModelBridge.basicInterp.ctxSpace (M := M) Γ).Carrier) :
    (concreteOnePointPropositionWitness (M := M)).fiberJoin
        ⟨((concreteOnePointPropositionWitness (M := M)).encodeProp
            (pointFormulaValue (M := M) φ γ),
          (concreteOnePointPropositionWitness (M := M)).encodeProp
            (pointFormulaValue (M := M) ψ γ)), by simp⟩ =
      (concreteOnePointPropositionWitness (M := M)).encodeProp
        (pointFormulaValue (M := M) (Term.or φ ψ) γ) := by
  exact concreteOnePointPropositionWitness_formula_or (M := M) φ ψ γ

theorem concrete_formula_imp_path
    {Γ : Ctx Base}
    (φ ψ : Formula Const Γ)
    (γ :
      (HigherOrderPointTopologicalGlobalModelBridge.basicInterp.ctxSpace (M := M) Γ).Carrier) :
    (concreteOnePointPropositionWitness (M := M)).fiberHimp
        ⟨((concreteOnePointPropositionWitness (M := M)).encodeProp
            (pointFormulaValue (M := M) φ γ),
          (concreteOnePointPropositionWitness (M := M)).encodeProp
            (pointFormulaValue (M := M) ψ γ)), by simp⟩ =
      (concreteOnePointPropositionWitness (M := M)).encodeProp
        (pointFormulaValue (M := M) (Term.imp φ ψ) γ) := by
  exact concreteOnePointPropositionWitness_formula_imp (M := M) φ ψ γ

theorem concrete_or_counterexample_consumer_path
    {Γ : Ctx Base}
    {Δ : List (Formula Const Γ)}
    (φ ψ : Formula Const Γ)
    (γ :
      (HigherOrderPointTopologicalGlobalModelBridge.basicInterp.ctxSpace (M := M) Γ).Carrier)
    (hΔ :
      HigherOrderPointTopologicalGlobalModelBridge.basicInterp.truthAntecedent
        (M := M) Δ γ = ⊤)
    (hOr :
      M.truth
        ((concreteOnePointPropositionWitness (M := M)).decodeProp
          ((concreteOnePointPropositionWitness (M := M)).fiberJoin
            ⟨((concreteOnePointPropositionWitness (M := M)).encodeProp
                (pointFormulaValue (M := M) φ γ),
              (concreteOnePointPropositionWitness (M := M)).encodeProp
                (pointFormulaValue (M := M) ψ γ)), by simp⟩)) ≠ ⊤) :
    ¬ Derivable (Base := Base) (Const := Const) Δ (Term.or φ ψ) := by
  exact not_derivable_of_or_formula_witness_counterexample (M := M) φ ψ γ hΔ hOr

theorem concrete_imp_counterexample_consumer_path
    {Γ : Ctx Base}
    {Δ : List (Formula Const Γ)}
    (φ ψ : Formula Const Γ)
    (γ :
      (HigherOrderPointTopologicalGlobalModelBridge.basicInterp.ctxSpace (M := M) Γ).Carrier)
    (hΔ :
      HigherOrderPointTopologicalGlobalModelBridge.basicInterp.truthAntecedent
        (M := M) Δ γ = ⊤)
    (hImp :
      M.truth
        ((concreteOnePointPropositionWitness (M := M)).decodeProp
          ((concreteOnePointPropositionWitness (M := M)).fiberHimp
            ⟨((concreteOnePointPropositionWitness (M := M)).encodeProp
                (pointFormulaValue (M := M) φ γ),
              (concreteOnePointPropositionWitness (M := M)).encodeProp
                (pointFormulaValue (M := M) ψ γ)), by simp⟩)) ≠ ⊤) :
    ¬ Derivable (Base := Base) (Const := Const) Δ (Term.imp φ ψ) := by
  exact not_derivable_of_imp_formula_witness_counterexample (M := M) φ ψ γ hΔ hImp

theorem concrete_imp_coherent_top_of_derivable_path
    {Γ : Ctx Base}
    {Δ : List (Formula Const Γ)}
    (φ ψ : Formula Const Γ)
    (hder : Derivable (Base := Base) (Const := Const) Δ (Term.imp φ ψ))
    (γ :
      (HigherOrderPointTopologicalGlobalModelBridge.basicInterp.ctxSpace (M := M) Γ).Carrier)
    (hΔ :
      HigherOrderPointTopologicalGlobalModelBridge.basicInterp.truthAntecedent
        (M := M) Δ γ = ⊤) :
    M.truth
      ((concreteOnePointPropositionWitness (M := M)).decodeProp
        ((concreteOnePointPropositionWitness (M := M)).fiberHimp
          ⟨((concreteOnePointPropositionWitness (M := M)).encodeProp
              (pointFormulaValue (M := M) φ γ),
            (concreteOnePointPropositionWitness (M := M)).encodeProp
              (pointFormulaValue (M := M) ψ γ)), by simp⟩)) = ⊤ := by
  exact imp_formula_witness_coherent_top_of_derivable (M := M) φ ψ hder γ hΔ

theorem concrete_and_coherent_top_of_derivable_path
    {Γ : Ctx Base}
    {Δ : List (Formula Const Γ)}
    (φ ψ : Formula Const Γ)
    (hder : Derivable (Base := Base) (Const := Const) Δ (Term.and φ ψ))
    (γ :
      (HigherOrderPointTopologicalGlobalModelBridge.basicInterp.ctxSpace (M := M) Γ).Carrier)
    (hΔ :
      HigherOrderPointTopologicalGlobalModelBridge.basicInterp.truthAntecedent
        (M := M) Δ γ = ⊤) :
    M.truth
      ((concreteOnePointPropositionWitness (M := M)).decodeProp
        ((concreteOnePointPropositionWitness (M := M)).fiberMeet
          ⟨((concreteOnePointPropositionWitness (M := M)).encodeProp
              (pointFormulaValue (M := M) φ γ),
            (concreteOnePointPropositionWitness (M := M)).encodeProp
              (pointFormulaValue (M := M) ψ γ)), by simp⟩)) = ⊤ := by
  exact and_formula_witness_coherent_top_of_derivable (M := M) φ ψ hder γ hΔ

theorem concrete_or_coherent_top_of_derivable_path
    {Γ : Ctx Base}
    {Δ : List (Formula Const Γ)}
    (φ ψ : Formula Const Γ)
    (hder : Derivable (Base := Base) (Const := Const) Δ (Term.or φ ψ))
    (γ :
      (HigherOrderPointTopologicalGlobalModelBridge.basicInterp.ctxSpace (M := M) Γ).Carrier)
    (hΔ :
      HigherOrderPointTopologicalGlobalModelBridge.basicInterp.truthAntecedent
        (M := M) Δ γ = ⊤) :
    M.truth
      ((concreteOnePointPropositionWitness (M := M)).decodeProp
        ((concreteOnePointPropositionWitness (M := M)).fiberJoin
          ⟨((concreteOnePointPropositionWitness (M := M)).encodeProp
              (pointFormulaValue (M := M) φ γ),
            (concreteOnePointPropositionWitness (M := M)).encodeProp
              (pointFormulaValue (M := M) ψ γ)), by simp⟩)) = ⊤ := by
  exact or_formula_witness_coherent_top_of_derivable (M := M) φ ψ hder γ hΔ

theorem concrete_or_top_of_truthValidSequent_path
    {Γ : Ctx Base}
    {Δ : List (Formula Const Γ)}
    (φ ψ : Formula Const Γ)
    (hvalid :
      HigherOrderPointTopologicalGlobalModelBridge.basicInterp.TruthValidSequent
        (M := M) Δ (Term.or φ ψ))
    (γ :
      (HigherOrderPointTopologicalGlobalModelBridge.basicInterp.ctxSpace (M := M) Γ).Carrier)
    (hΔ :
      HigherOrderPointTopologicalGlobalModelBridge.basicInterp.truthAntecedent
        (M := M) Δ γ = ⊤) :
    M.truth
      ((concreteOnePointPropositionWitness (M := M)).decodeProp
        ((concreteOnePointPropositionWitness (M := M)).fiberJoin
          ⟨((concreteOnePointPropositionWitness (M := M)).encodeProp
              (pointFormulaValue (M := M) φ γ),
            (concreteOnePointPropositionWitness (M := M)).encodeProp
              (pointFormulaValue (M := M) ψ γ)), by simp⟩)) = ⊤ := by
  exact or_formula_witness_top_of_truthValidSequent (M := M) φ ψ hvalid γ hΔ

theorem concrete_and_top_of_truthValidSequent_path
    {Γ : Ctx Base}
    {Δ : List (Formula Const Γ)}
    (φ ψ : Formula Const Γ)
    (hvalid :
      HigherOrderPointTopologicalGlobalModelBridge.basicInterp.TruthValidSequent
        (M := M) Δ (Term.and φ ψ))
    (γ :
      (HigherOrderPointTopologicalGlobalModelBridge.basicInterp.ctxSpace (M := M) Γ).Carrier)
    (hΔ :
      HigherOrderPointTopologicalGlobalModelBridge.basicInterp.truthAntecedent
        (M := M) Δ γ = ⊤) :
    M.truth
      ((concreteOnePointPropositionWitness (M := M)).decodeProp
        ((concreteOnePointPropositionWitness (M := M)).fiberMeet
          ⟨((concreteOnePointPropositionWitness (M := M)).encodeProp
              (pointFormulaValue (M := M) φ γ),
            (concreteOnePointPropositionWitness (M := M)).encodeProp
              (pointFormulaValue (M := M) ψ γ)), by simp⟩)) = ⊤ := by
  exact and_formula_witness_top_of_truthValidSequent (M := M) φ ψ hvalid γ hΔ

theorem concrete_imp_top_of_truthValidSequent_path
    {Γ : Ctx Base}
    {Δ : List (Formula Const Γ)}
    (φ ψ : Formula Const Γ)
    (hvalid :
      HigherOrderPointTopologicalGlobalModelBridge.basicInterp.TruthValidSequent
        (M := M) Δ (Term.imp φ ψ))
    (γ :
      (HigherOrderPointTopologicalGlobalModelBridge.basicInterp.ctxSpace (M := M) Γ).Carrier)
    (hΔ :
      HigherOrderPointTopologicalGlobalModelBridge.basicInterp.truthAntecedent
        (M := M) Δ γ = ⊤) :
    M.truth
      ((concreteOnePointPropositionWitness (M := M)).decodeProp
        ((concreteOnePointPropositionWitness (M := M)).fiberHimp
          ⟨((concreteOnePointPropositionWitness (M := M)).encodeProp
              (pointFormulaValue (M := M) φ γ),
            (concreteOnePointPropositionWitness (M := M)).encodeProp
              (pointFormulaValue (M := M) ψ γ)), by simp⟩)) = ⊤ := by
  exact imp_formula_witness_top_of_truthValidSequent (M := M) φ ψ hvalid γ hΔ

end AwodeyButzHeytingPointModelBridgeRegression

end Mettapedia.AutoBooks.Codex.IntuitionisticHOL
