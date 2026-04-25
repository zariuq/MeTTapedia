import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.AwodeyButzHeytingPointModelBridge

namespace Mettapedia.AutoBooks.Codex.IntuitionisticHOL

open Mettapedia.Logic.HOL

universe u v w

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

theorem concrete_prop_join_path
    (p q : M.Carrier .prop) :
    (concreteOnePointPropositionWitness (M := M)).fiberJoin
        ⟨((concreteOnePointPropositionWitness (M := M)).encodeProp p,
          (concreteOnePointPropositionWitness (M := M)).encodeProp q), by simp⟩ =
      (concreteOnePointPropositionWitness (M := M)).encodeProp (M.orP p q) := by
  exact concreteOnePointPropositionWitness_join (M := M) p q

theorem concrete_heyting_algebra_meet_continuous_path
    (laws : PropCarrierHeytingLaws M) :
    Continuous (concreteOnePointHeytingAlgebraWitness (M := M) laws).fiberMeet := by
  exact (concreteOnePointHeytingAlgebraWitness (M := M) laws).fiberMeet_continuous

theorem concrete_heyting_algebra_meet_idempotent_path
    (laws : PropCarrierHeytingLaws M)
    (p :
      ((concreteOnePointHeytingAlgebraWitness (M := M) laws).toTopologicalInterpretation.propSpace).Carrier) :
    (concreteOnePointHeytingAlgebraWitness (M := M) laws).fiberMeet ⟨(p, p), rfl⟩ = p := by
  exact (concreteOnePointHeytingAlgebraWitness (M := M) laws).fiberMeet_idempotent p

theorem concrete_heyting_algebra_join_comm_path
    (laws : PropCarrierHeytingLaws M)
    (pq :
      PropFiberPair
        ((concreteOnePointHeytingAlgebraWitness (M := M) laws).toTopologicalInterpretation.propSpace)) :
    (concreteOnePointHeytingAlgebraWitness (M := M) laws).fiberJoin pq =
      (concreteOnePointHeytingAlgebraWitness (M := M) laws).fiberJoin
        ⟨(pq.val.2, pq.val.1), pq.property.symm⟩ := by
  exact (concreteOnePointHeytingAlgebraWitness (M := M) laws).fiberJoin_comm pq

theorem concrete_heyting_algebra_himp_continuous_path
    (laws : PropCarrierHeytingLaws M) :
    Continuous (concreteOnePointHeytingAlgebraWitness (M := M) laws).fiberHimp := by
  exact (concreteOnePointHeytingAlgebraWitness (M := M) laws).fiberHimp_continuous

theorem faithful_heyting_source_concrete_meet_continuous_path
    [HeytingAlgebra (M.Carrier .prop)]
    (source : PropCarrierFaithfulHeytingSource M) :
    Continuous
      (concreteOnePointHeytingAlgebraWitness (M := M)
        source.toPropCarrierHeytingLaws).fiberMeet := by
  exact
    (concreteOnePointHeytingAlgebraWitness (M := M)
      source.toPropCarrierHeytingLaws).fiberMeet_continuous

namespace LindenbaumQuotientCanary

inductive BaseSort where
  | atom

abbrev CanaryConst : Ty BaseSort → Type := fun _ => Empty

noncomputable abbrev CanonicalModel (T : ClosedTheorySet CanaryConst) :
    GlobalModel BaseSort CanaryConst :=
  LindenbaumQuotientPropGlobalModel.model
    (Base := BaseSort) (Const := CanaryConst) T

noncomputable abbrev CanonicalLaws
    (T : ClosedTheorySet CanaryConst) :
    PropCarrierHeytingLaws (CanonicalModel T) :=
  LindenbaumQuotientPropGlobalModel.sourcedHeytingLaws
    (Base := BaseSort) (Const := CanaryConst) T

noncomputable abbrev CanonicalAlgebraWitness
    (T : ClosedTheorySet CanaryConst) :
    OnePointHeytingAlgebraWitness (CanonicalModel T) :=
  concreteOnePointHeytingAlgebraWitness
    (M := CanonicalModel T) (CanonicalLaws T)

noncomputable abbrev CanonicalSectionWitness
    (T : ClosedTheorySet CanaryConst) :
    OnePointHeytingSectionWitness (CanonicalModel T) :=
  concreteOnePointHeytingSectionWitness
    (M := CanonicalModel T) (CanonicalLaws T)

theorem sourced_lindenbaum_laws_feed_one_point_algebra
    (T : ClosedTheorySet CanaryConst) :
    Continuous (CanonicalAlgebraWitness T).fiberHimp := by
  exact (CanonicalAlgebraWitness T).fiberHimp_continuous

theorem sourced_lindenbaum_laws_feed_section_algebra_himp
    (T : ClosedTheorySet CanaryConst)
    (a b : (CanonicalSectionWitness T).toTopologicalInterpretation.propSpace.GlobalSection) :
    (CanonicalSectionWitness T).propHimp a b =
      (CanonicalAlgebraWitness T).propHimpOfPoint a b := by
  exact concreteOnePointHeytingSectionWitness_propHimp_eq_propHimpOfPoint
    (M := CanonicalModel T) (CanonicalLaws T) a b

end LindenbaumQuotientCanary

theorem concrete_heyting_section_meet_comm_path
    (laws : PropCarrierHeytingLaws M)
    (a b :
      (((concreteOnePointHeytingSectionWitness (M := M) laws).toTopologicalInterpretation.propSpace).GlobalSection)) :
    (concreteOnePointHeytingSectionWitness (M := M) laws).propMeet a b =
      (concreteOnePointHeytingSectionWitness (M := M) laws).propMeet b a := by
  exact (concreteOnePointHeytingSectionWitness (M := M) laws).propMeet_comm a b

theorem concrete_heyting_section_join_bot_path
    (laws : PropCarrierHeytingLaws M)
    (a :
      (((concreteOnePointHeytingSectionWitness (M := M) laws).toTopologicalInterpretation.propSpace).GlobalSection)) :
    (concreteOnePointHeytingSectionWitness (M := M) laws).propJoin a
        (concreteOnePointHeytingSectionWitness (M := M) laws).propBot = a := by
  exact (concreteOnePointHeytingSectionWitness (M := M) laws).propJoin_bot a

theorem concrete_heyting_section_meet_join_distrib_path
    (laws : PropCarrierHeytingLaws M)
    (a b c :
      (((concreteOnePointHeytingSectionWitness (M := M) laws).toTopologicalInterpretation.propSpace).GlobalSection)) :
    (concreteOnePointHeytingSectionWitness (M := M) laws).propMeet a
        ((concreteOnePointHeytingSectionWitness (M := M) laws).propJoin b c) =
      (concreteOnePointHeytingSectionWitness (M := M) laws).propJoin
        ((concreteOnePointHeytingSectionWitness (M := M) laws).propMeet a b)
        ((concreteOnePointHeytingSectionWitness (M := M) laws).propMeet a c) := by
  exact (concreteOnePointHeytingSectionWitness (M := M) laws).propMeet_join_distrib a b c

theorem concrete_heyting_section_himp_adj_path
    (laws : PropCarrierHeytingLaws M)
    (a b c :
      (((concreteOnePointHeytingSectionWitness (M := M) laws).toTopologicalInterpretation.propSpace).GlobalSection)) :
    (concreteOnePointHeytingSectionWitness (M := M) laws).propMeet
        ((concreteOnePointHeytingSectionWitness (M := M) laws).propMeet a b) c =
        (concreteOnePointHeytingSectionWitness (M := M) laws).propMeet a b ↔
      (concreteOnePointHeytingSectionWitness (M := M) laws).propMeet a
          ((concreteOnePointHeytingSectionWitness (M := M) laws).propHimp b c) = a := by
  exact (concreteOnePointHeytingSectionWitness (M := M) laws).propHimp_adj a b c

theorem concrete_heyting_section_meet_fiber_path
    (laws : PropCarrierHeytingLaws M)
    (a b :
      (((concreteOnePointHeytingSectionWitness (M := M) laws).toTopologicalInterpretation.propSpace).GlobalSection)) :
    (concreteOnePointHeytingSectionWitness (M := M) laws).propMeet a b =
      (concreteOnePointHeytingAlgebraWitness (M := M) laws).propMeetOfPoint a b := by
  exact concreteOnePointHeytingSectionWitness_propMeet_eq_propMeetOfPoint
    (M := M) laws a b

theorem concrete_heyting_section_join_fiber_path
    (laws : PropCarrierHeytingLaws M)
    (a b :
      (((concreteOnePointHeytingSectionWitness (M := M) laws).toTopologicalInterpretation.propSpace).GlobalSection)) :
    (concreteOnePointHeytingSectionWitness (M := M) laws).propJoin a b =
      (concreteOnePointHeytingAlgebraWitness (M := M) laws).propJoinOfPoint a b := by
  exact concreteOnePointHeytingSectionWitness_propJoin_eq_propJoinOfPoint
    (M := M) laws a b

theorem concrete_heyting_section_himp_fiber_path
    (laws : PropCarrierHeytingLaws M)
    (a b :
      (((concreteOnePointHeytingSectionWitness (M := M) laws).toTopologicalInterpretation.propSpace).GlobalSection)) :
    (concreteOnePointHeytingSectionWitness (M := M) laws).propHimp a b =
      (concreteOnePointHeytingAlgebraWitness (M := M) laws).propHimpOfPoint a b := by
  exact concreteOnePointHeytingSectionWitness_propHimp_eq_propHimpOfPoint
    (M := M) laws a b

theorem equality_law_beta_shape_path
    (laws : EqualityCarrierLaws M)
    {σ τ : Ty Base}
    (f : M.Carrier σ → M.Carrier τ)
    (x : M.Carrier σ) :
    M.truth (M.eqP (M.app (M.lam f) x) (f x)) = ⊤ := by
  exact EqualityCarrierLaws.beta_top laws f x

theorem equality_law_eta_shape_path
    (laws : EqualityCarrierLaws M)
    {σ τ : Ty Base}
    (f : M.Carrier (σ ⇒ τ)) :
    M.truth (M.eqP (M.lam (fun x => M.app f x)) f) = ⊤ := by
  exact EqualityCarrierLaws.eta_top laws f

theorem canonical_extensional_equality_source_feeds_laws
    (source : CanonicalExtensionalEqualityCarrierSource M) :
    EqualityCarrierLaws M := by
  exact source.toEqualityCarrierLaws

theorem canonical_extensional_equality_source_feeds_beta
    (source : CanonicalExtensionalEqualityCarrierSource M)
    {σ τ : Ty Base}
    (f : M.Carrier σ → M.Carrier τ)
    (x : M.Carrier σ) :
    M.truth (M.eqP (M.app (M.lam f) x) (f x)) = ⊤ := by
  exact EqualityCarrierLaws.beta_top source.toEqualityCarrierLaws f x

theorem canonical_extensional_equality_source_theorem_feeds_eta
    (h : CanonicalExtensionalEqualitySourceTheorem (Base := Base) (Const := Const) M)
    {σ τ : Ty Base}
    (f : M.Carrier (σ ⇒ τ)) :
    M.truth (M.eqP (M.lam (fun x => M.app f x)) f) = ⊤ := by
  exact EqualityCarrierLaws.eta_top
    (equalityCarrierLaws_of_canonicalExtensionalEqualitySourceTheorem
      (Base := Base) (Const := Const) h) f

theorem preModelEqv_refl_source_field_canary
    (audit : PreModelEqvCarrierAudit.{u, v, w} M)
    {τ : Ty Base}
    (x : M.Carrier τ) :
    audit.Eqv τ x x := by
  exact audit.eqv_refl_source_field x

theorem preModelEqv_truth_reflection_source_field_canary
    (source : PreModelEqvTruthSource.{u, v, w} M)
    {τ : Ty Base}
    {x y : M.Carrier τ}
    (h : M.truth (M.eqP x y) = ⊤) :
    source.Eqv τ x y := by
  exact source.eqv_of_truth_eq_top_source_field h

theorem preModelEqv_truth_introduction_source_field_canary
    (source : PreModelEqvTruthSource.{u, v, w} M)
    {τ : Ty Base}
    {x y : M.Carrier τ}
    (h : source.Eqv τ x y) :
    M.truth (M.eqP x y) = ⊤ := by
  exact source.truth_eq_top_of_eqv_source_field h

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

theorem concrete_formula_eq_path
    {Γ : Ctx Base} {τ : Ty Base}
    (t u : Term Const Γ τ)
    (γ :
      (HigherOrderPointTopologicalGlobalModelBridge.basicInterp.ctxSpace (M := M) Γ).Carrier) :
    pointFormulaValue (M := M) (Term.eq t u) γ =
      M.eqP
        (SemilocalModel.eval M.toSemilocalModel
          (HigherOrderPointTopologicalGlobalModelBridge.basicInterp.decodeEnv (M := M) γ) t)
        (SemilocalModel.eval M.toSemilocalModel
          (HigherOrderPointTopologicalGlobalModelBridge.basicInterp.decodeEnv (M := M) γ) u) := by
  exact pointFormulaValue_eq (M := M) t u γ

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

theorem concrete_formula_witness_truth_eq_truthEval_path
    {Γ : Ctx Base}
    (χ : Formula Const Γ)
    (γ :
      (HigherOrderPointTopologicalGlobalModelBridge.basicInterp.ctxSpace (M := M) Γ).Carrier) :
    M.truth
        ((concreteOnePointPropositionWitness (M := M)).decodeProp
          ((concreteOnePointPropositionWitness (M := M)).encodeProp
            (pointFormulaValue (M := M) χ γ))) =
      HigherOrderPointTopologicalGlobalModelBridge.basicInterp.truthEval
        (M := M) χ γ := by
  exact formula_witness_truth_eq_truthEval (M := M) χ γ

theorem concrete_formula_witness_top_of_truthValidSequent_path
    {Γ : Ctx Base}
    {Δ : List (Formula Const Γ)}
    (χ : Formula Const Γ)
    (hvalid :
      HigherOrderPointTopologicalGlobalModelBridge.basicInterp.TruthValidSequent
        (M := M) Δ χ)
    (γ :
      (HigherOrderPointTopologicalGlobalModelBridge.basicInterp.ctxSpace (M := M) Γ).Carrier)
    (hΔ :
      HigherOrderPointTopologicalGlobalModelBridge.basicInterp.truthAntecedent
        (M := M) Δ γ = ⊤) :
    M.truth
        ((concreteOnePointPropositionWitness (M := M)).decodeProp
          ((concreteOnePointPropositionWitness (M := M)).encodeProp
            (pointFormulaValue (M := M) χ γ))) = ⊤ := by
  exact formula_witness_top_of_truthValidSequent (M := M) (χ := χ) hvalid γ hΔ

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
