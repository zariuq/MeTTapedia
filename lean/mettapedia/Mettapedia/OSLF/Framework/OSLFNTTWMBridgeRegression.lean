import Mettapedia.OSLF.Framework.OSLFNTTWMBridge
import Mettapedia.OSLF.Framework.OSLFNTTTheoryClosure
import Mettapedia.OSLF.Framework.ModalSubobjectBridge
import Mettapedia.OSLF.Framework.OSLFNTTWMCanonicalClosure

/-!
# OSLF -> NTT -> WM Bridge Regression Fixtures

Regression fixtures consuming the formula-level bridge endpoints.
-/

namespace Mettapedia.OSLF.Framework.OSLFNTTWMBridgeRegression

open CategoryTheory
open Mettapedia.OSLF.Framework.OSLFNTTWMBridge
open Mettapedia.OSLF.Framework.OSLFNTTTheoryClosure
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.Formula
open Mettapedia.CategoryTheory.PLNInstance
open Mettapedia.OSLF.Framework.ModalSubobjectBridge
open Mettapedia.OSLF.Framework.OSLFNTTWMCanonicalClosure
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.Framework.CategoryBridge
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.OSLFEvidenceSemantics
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.PLNWorldModelCategoricalBridge.WMHyperdoctrine

universe u v x

abbrev WMHyper (State : Type x) [EvidenceType State] :=
  Mettapedia.Logic.PLNWorldModelHyperdoctrine.WMHyperdoctrine.{u, v, 0, x} State

variable {State : Type x} [EvidenceType State] [WorldModel State Pattern]

/-- Formula-level regression fixture: consume the graph-triangle endpoint directly. -/
theorem formula_graph_triangle_fixture
    (relEnv : RelationEnv)
    (W : State)
    (queryOfAtom : String → Pattern → Pattern)
    (φf : OSLFFormula) (Xobj : Mettapedia.CategoryTheory.PLNInstance.PLNObj)
    {Xgr : Opposite (Mettapedia.OSLF.Framework.ConstructorCategory.ConstructorObj
      Mettapedia.OSLF.Framework.MeTTaToNTT.mettaFull)}
    (p : Pattern) :
    FormulaGraphEndpoint
      (State := State) (relEnv := relEnv) (W := W)
      (queryOfAtom := queryOfAtom) (φf := φf) (Xobj := Xobj)
      (X := Xgr) (p := p) := by
  exact oslf_formula_ntt_graph_triangle
    (relEnv := relEnv) (W := W) (queryOfAtom := queryOfAtom)
    (φf := φf) (Xobj := Xobj) (X := Xgr) (p := p)

/-- Canonical regression fixture:
consume representable BC-square transport together with the Π-facing transport
endpoint that is routed explicitly via `prop12_piSigmaPredicateRulePack`. -/
theorem representable_bc_with_prop12_pi_fixture
    (lang : LanguageDef) (s : LangSort lang)
    (seed : Pattern) (φ : Pattern → Prop)
    (hNat : languageSortPredNaturality lang s seed φ)
    {P B D : CategoryTheory.Functor (Opposite (ConstructorObj lang)) (Type _)}
    (pi1 : P ⟶ languageSortRepresentableObj lang s)
    (pi2 : P ⟶ B)
    (f : languageSortRepresentableObj lang s ⟶ D)
    (g : B ⟶ D)
    (hpb : CategoryTheory.IsPullback pi1 pi2 f g)
    (hf : CategoryTheory.Mono f) (hpi2 : CategoryTheory.Mono pi2)
    (χ : CategoryTheory.Subfunctor D) :
    (CategoryTheory.Subobject.pullback g).obj
        ((CategoryTheory.Subobject.map f).obj
          (languageSortFiber_ofPatternPred_subobject
            lang s seed φ hNat))
      =
    (CategoryTheory.Subobject.map pi2).obj
        ((CategoryTheory.Subobject.pullback pi1).obj
          (languageSortFiber_ofPatternPred_subobject
            lang s seed φ hNat))
    ∧
    (((Mettapedia.GSLT.Topos.presheafChangeOfBase (C := ConstructorObj lang)).pullback f χ
        ≤ languageSortFiber_ofPatternPred lang s seed φ hNat)
      ↔
      (χ ≤
        (Mettapedia.GSLT.Topos.presheafChangeOfBase (C := ConstructorObj lang)).universalImage f
          (languageSortFiber_ofPatternPred lang s seed φ hNat))) := by
  refine ⟨?_, ?_⟩
  · exact
      Mettapedia.OSLF.Framework.BeckChevalleyOSLF.representable_patternPred_sigma_beckChevalley
        (lang := lang) (s := s) (seed := seed) (φ := φ) (hNat := hNat)
        (pi1 := pi1) (pi2 := pi2) (f := f) (g := g)
        (hpb := hpb) (hf := hf) (hpi2 := hpi2)
  · exact
      (Mettapedia.OSLF.Framework.ToposTOGLBridge.topos_representable_patternPred_piSigma_transport_via_prop12_pack
        (lang := lang) (s := s) (seed := seed) (φ := φ) (hNat := hNat)
        (f := f) (χ := χ) (ψ := (⊤ : CategoryTheory.Subfunctor D))).2

/-- Canonical regression fixture:
consume BC-square transport together with the unified Π/Σ transport endpoint
that is routed explicitly via the Prop-12 ΠΣ pack. -/
theorem representable_bc_with_prop12_piSigma_fixture
    (lang : LanguageDef) (s : LangSort lang)
    (seed : Pattern) (φ : Pattern → Prop)
    (hNat : languageSortPredNaturality lang s seed φ)
    {P B D : CategoryTheory.Functor (Opposite (ConstructorObj lang)) (Type _)}
    (pi1 : P ⟶ languageSortRepresentableObj lang s)
    (pi2 : P ⟶ B)
    (f : languageSortRepresentableObj lang s ⟶ D)
    (g : B ⟶ D)
    (hpb : CategoryTheory.IsPullback pi1 pi2 f g)
    (hf : CategoryTheory.Mono f) (hpi2 : CategoryTheory.Mono pi2)
    (χ ψ : CategoryTheory.Subfunctor D) :
    (CategoryTheory.Subobject.pullback g).obj
        ((CategoryTheory.Subobject.map f).obj
          (languageSortFiber_ofPatternPred_subobject
            lang s seed φ hNat))
      =
    (CategoryTheory.Subobject.map pi2).obj
        ((CategoryTheory.Subobject.pullback pi1).obj
          (languageSortFiber_ofPatternPred_subobject
            lang s seed φ hNat))
    ∧
    ((((Mettapedia.GSLT.Topos.presheafChangeOfBase (C := ConstructorObj lang)).directImage f)
        ((languageSortFiber_ofPatternPred lang s seed φ hNat :
          CategoryTheory.Subfunctor (languageSortRepresentableObj lang s)))
      ≤ ψ)
      ↔
      ((show CategoryTheory.Subfunctor (languageSortRepresentableObj lang s)
          from languageSortFiber_ofPatternPred lang s seed φ hNat)
        ≤ ((Mettapedia.GSLT.Topos.presheafChangeOfBase (C := ConstructorObj lang)).pullback f) ψ))
    ∧
    ((((Mettapedia.GSLT.Topos.presheafChangeOfBase (C := ConstructorObj lang)).pullback f) χ
      ≤ languageSortFiber_ofPatternPred lang s seed φ hNat)
      ↔
      (χ ≤
        (Mettapedia.GSLT.Topos.presheafChangeOfBase (C := ConstructorObj lang)).universalImage f
          (languageSortFiber_ofPatternPred lang s seed φ hNat))) := by
  let pack :
      Mettapedia.OSLF.Framework.BeckChevalleyOSLF.RepresentablePiSigmaTransportPack
        (lang := lang) (s := s) (seed := seed) (φ := φ) (hNat := hNat) (f := f) :=
    Mettapedia.OSLF.Framework.ToposTOGLBridge.topos_representable_patternPred_piSigma_transport_pack_via_prop12
      (lang := lang) (s := s) (seed := seed) (φ := φ) (hNat := hNat) (f := f)
  refine ⟨?_, ?_, ?_⟩
  · exact pack.sigma_beckChevalley pi1 pi2 g hpb hf hpi2
  · exact (pack.piSigma_transport χ ψ).1
  · exact (pack.piSigma_transport χ ψ).2

/-- Canonical regression fixture: consume the packaged representable Π/Σ
transport API directly (Σ-BC + Σ/Π transport). -/
theorem representable_transport_pack_fixture
    (lang : LanguageDef) (s : LangSort lang)
    (seed : Pattern) (φ : Pattern → Prop)
    (hNat : languageSortPredNaturality lang s seed φ)
    {P B D : CategoryTheory.Functor (Opposite (ConstructorObj lang)) (Type _)}
    (pi1 : P ⟶ languageSortRepresentableObj lang s)
    (pi2 : P ⟶ B)
    (f : languageSortRepresentableObj lang s ⟶ D)
    (g : B ⟶ D)
    (hpb : CategoryTheory.IsPullback pi1 pi2 f g)
    (hf : CategoryTheory.Mono f) (hpi2 : CategoryTheory.Mono pi2)
    (χ ψ : CategoryTheory.Subfunctor D) :
    ((CategoryTheory.Subobject.pullback g).obj
        ((CategoryTheory.Subobject.map f).obj
          (languageSortFiber_ofPatternPred_subobject lang s seed φ hNat))
      =
      (CategoryTheory.Subobject.map pi2).obj
        ((CategoryTheory.Subobject.pullback pi1).obj
          (languageSortFiber_ofPatternPred_subobject lang s seed φ hNat)))
    ∧
    ((((Mettapedia.GSLT.Topos.presheafChangeOfBase (C := ConstructorObj lang)).directImage f)
        ((languageSortFiber_ofPatternPred lang s seed φ hNat :
          CategoryTheory.Subfunctor (languageSortRepresentableObj lang s)))
      ≤ ψ)
      ↔
      ((show CategoryTheory.Subfunctor (languageSortRepresentableObj lang s)
          from languageSortFiber_ofPatternPred lang s seed φ hNat)
        ≤ ((Mettapedia.GSLT.Topos.presheafChangeOfBase (C := ConstructorObj lang)).pullback f) ψ))
    ∧
    ((((Mettapedia.GSLT.Topos.presheafChangeOfBase (C := ConstructorObj lang)).pullback f) χ
      ≤ languageSortFiber_ofPatternPred lang s seed φ hNat)
      ↔
      (χ ≤
        (Mettapedia.GSLT.Topos.presheafChangeOfBase (C := ConstructorObj lang)).universalImage f
          (languageSortFiber_ofPatternPred lang s seed φ hNat))) := by
  let pack :
      Mettapedia.OSLF.Framework.BeckChevalleyOSLF.RepresentablePiSigmaTransportPack
        (lang := lang) (s := s) (seed := seed) (φ := φ) (hNat := hNat) (f := f) :=
    Mettapedia.OSLF.Framework.ToposTOGLBridge.topos_representable_patternPred_piSigma_transport_pack_via_prop12
      (lang := lang) (s := s) (seed := seed) (φ := φ) (hNat := hNat) (f := f)
  refine ⟨?_, ?_, ?_⟩
  · exact pack.sigma_beckChevalley pi1 pi2 g hpb hf hpi2
  · exact pack.sigma_transport ψ
  · exact pack.pi_transport χ

/-- Canonical regression fixture: consume the Topos-facing representable Π/Σ
transport-pack endpoint directly (not just the Beck-Chevalley layer). -/
theorem topos_representable_transport_pack_fixture
    (lang : LanguageDef) (s : LangSort lang)
    (seed : Pattern) (φ : Pattern → Prop)
    (hNat : languageSortPredNaturality lang s seed φ)
    {D : CategoryTheory.Functor (Opposite (ConstructorObj lang)) (Type _)}
    (f : languageSortRepresentableObj lang s ⟶ D) :
    Mettapedia.OSLF.Framework.BeckChevalleyOSLF.RepresentablePiSigmaTransportPack
      (lang := lang) (s := s) (seed := seed) (φ := φ) (hNat := hNat) (f := f) := by
  exact
    Mettapedia.OSLF.Framework.ToposTOGLBridge.topos_representable_patternPred_piSigma_transport_pack_via_prop12
      (lang := lang) (s := s) (seed := seed) (φ := φ) (hNat := hNat) (f := f)

/-- Categorical regression fixture: consume the unified formula endpoint that
combines graph-witness transport with the WM institution+Beck-Chevalley
endpoint statement. -/
theorem formula_graph_triangle_categorical_fixture
    (H : Mettapedia.Logic.PLNWorldModelHyperdoctrine.WMHyperdoctrine State)
    {P Aobj Bobj D : H.Obj}
    (pi1 : P ⟶ Aobj) (pi2 : P ⟶ Bobj) (fcat : Aobj ⟶ D) (gcat : Bobj ⟶ D)
    (hpb : CategoryTheory.IsPullback pi1 pi2 fcat gcat)
    (hmfcat : CategoryTheory.Mono fcat) (hmpi2 : CategoryTheory.Mono pi2)
    (relEnv : RelationEnv)
    (W : State)
    (queryOfAtom : String → Pattern → Pattern)
    (φf : OSLFFormula) (Xobj : Mettapedia.CategoryTheory.PLNInstance.PLNObj)
    {Xgr : Opposite (Mettapedia.OSLF.Framework.ConstructorCategory.ConstructorObj
      Mettapedia.OSLF.Framework.MeTTaToNTT.mettaFull)}
    (p : Pattern)
    (φcat : H.query Bobj) :
    FormulaGraphEndpoint
      (State := State) (relEnv := relEnv) (W := W)
      (queryOfAtom := queryOfAtom) (φf := φf) (Xobj := Xobj)
      (X := Xgr) (p := p)
    ∧
    Mettapedia.Logic.PLNWorldModelCategoricalBridge.WMHyperdoctrine.EndpointStatement
      (H := H) pi1 pi2 fcat gcat W φcat := by
  simpa using
    (oslf_formula_ntt_graph_triangle_categorical
      (H := H) (pi1 := pi1) (pi2 := pi2) (fcat := fcat) (gcat := gcat)
      (hpb := hpb) (hmfcat := hmfcat) (hmpi2 := hmpi2)
      (relEnv := relEnv) (W := W) (queryOfAtom := queryOfAtom)
      (φf := φf) (Xobj := Xobj) (X := Xgr) (p := p) (φcat := φcat))

/-- Closure regression fixture: consume the closure-level formula endpoint wrapper
directly. -/
theorem formula_endpoint_bridge_fixture
    (relEnv : RelationEnv)
    (W : State)
    (queryOfAtom : String → Pattern → Pattern)
    (φf : OSLFFormula) (Xobj : Mettapedia.CategoryTheory.PLNInstance.PLNObj)
    {Xgr : Opposite (Mettapedia.OSLF.Framework.ConstructorCategory.ConstructorObj
      Mettapedia.OSLF.Framework.MeTTaToNTT.mettaFull)} :
    FormulaEndpointBridge
      (State := State) (relEnv := relEnv) (W := W)
      (queryOfAtom := queryOfAtom) (φf := φf) (Xobj := Xobj)
      (X := Xgr) := by
  exact formulaEndpointBridge_of_oslf_formula_ntt_graph_triangle
    (State := State)
    (relEnv := relEnv) (W := W) (queryOfAtom := queryOfAtom)
    (φf := φf) (Xobj := Xobj) (X := Xgr)

/-- Closure regression fixture: star-closure packaging yields a directly usable
state-indexed WM consequence rule. -/
theorem oslf_stepStar_rule_sound_fixture
    {relEnv : RelationEnv}
    (I : OSLFNTTWMInterface relEnv State Pattern)
    {p q : Pattern}
    (hstar : OSLFTheoryStepStar relEnv p q)
    {W : State}
    (hW : I.side W) :
    let r : WMConsequenceRuleOn State Pattern :=
      wmConsequenceRuleOn_of_oslfTheoryStepStar (State := State) (Query := Pattern)
        (I := I) hstar
    WorldModel.queryStrength (State := State) (Query := Pattern) W r.premise ≤
      WorldModel.queryStrength (State := State) (Query := Pattern) W r.conclusion := by
  intro r
  exact r.sound hW

/-- Concrete pointwise model fixture (positive): when the side-condition holds,
the canonical pointwise interface discharges one-step OSLF obligations. -/
theorem pointwise_interface_step_fixture
    {relEnv : RelationEnv}
    {W : StepState}
    (hW : pointwiseStepSide relEnv W)
    {p q : Pattern}
    (hstep : OSLFTheoryStep relEnv p q) :
    let I := pointwiseStepInterface relEnv
    WorldModel.queryStrength (State := StepState) (Query := StepQuery) W (I.encode p) ≤
      WorldModel.queryStrength (State := StepState) (Query := StepQuery) W (I.encode q) := by
  intro I
  simpa using (I.step_sound (W := W) (p := p) (q := q) hW hstep)

/-- Concrete pointwise model fixture (negative): step-soundness is not automatic
without the side-condition. -/
theorem pointwise_interface_side_not_auto_fixture
    (relEnv : RelationEnv)
    {p q : Pattern}
    (hneq : p ≠ q)
    (hstep : OSLFTheoryStep relEnv p q) :
    ∃ W : StepState, ¬ (pointwiseStepInterface relEnv).side W := by
  simpa [pointwiseStepInterface] using
    (pointwiseStepSide_not_automatic (relEnv := relEnv) (p := p) (q := q)
      hneq hstep)

/-- SemE fragment fixture: the canonical evidence-level interface generated from
atom step-monotonicity discharges one-step obligations on the induced semantic
state. -/
theorem semE_fragment_interface_step_fixture
    (relEnv : RelationEnv)
    (Iatom : EvidenceAtomSem)
    (hAtom :
      ∀ (a : String) {p q : Pattern},
        OSLFTheoryStep relEnv p q →
        Iatom a p ≤ Iatom a q)
    (φ : OSLFFormula)
    (hφ : StepEvidenceMonotoneFragment φ)
    {p q : Pattern}
    (hstep : OSLFTheoryStep relEnv p q) :
    let Iev := semEFragmentEvidenceInterface
      (relEnv := relEnv) (I := Iatom) (hAtom := hAtom)
      (φ := φ) hφ
    WMEvidenceObligation SemEState SemEQuery
      (semEState relEnv Iatom φ) (Iev.encode p) (Iev.encode q) := by
  intro Iev
  have hSide : Iev.side (semEState relEnv Iatom φ) := rfl
  simpa using (Iev.step_sound (W := semEState relEnv Iatom φ) (p := p) (q := q) hSide hstep)

/-- SemE fragment fixture: consume the unified semE categorical endpoint and
project the institution/Beck-Chevalley endpoint together with one-step evidence
closure. -/
theorem semE_fragment_categorical_endpoint_step_fixture
    (H : Mettapedia.Logic.PLNWorldModelHyperdoctrine.WMHyperdoctrine SemEState)
    {P Aobj Bobj D : H.Obj}
    (pi1 : P ⟶ Aobj) (pi2 : P ⟶ Bobj) (fcat : Aobj ⟶ D) (gcat : Bobj ⟶ D)
    (hpb : CategoryTheory.IsPullback pi1 pi2 fcat gcat)
    (hmfcat : CategoryTheory.Mono fcat) (hmpi2 : CategoryTheory.Mono pi2)
    (relEnv : RelationEnv)
    (queryOfAtom : String → Pattern → Pattern)
    (Iatom : EvidenceAtomSem)
    (hAtom :
      ∀ (a : String) {p q : Pattern},
        OSLFTheoryStep relEnv p q →
        Iatom a p ≤ Iatom a q)
    (φ : OSLFFormula)
    (hφ : StepEvidenceMonotoneFragment φ)
    (Xobj : Mettapedia.CategoryTheory.PLNInstance.PLNObj)
    {Xgr : Opposite (Mettapedia.OSLF.Framework.ConstructorCategory.ConstructorObj
      Mettapedia.OSLF.Framework.MeTTaToNTT.mettaFull)}
    (p q : Pattern)
    (hstep : OSLFTheoryStep relEnv p q)
    (φcat : H.query Bobj) :
    Mettapedia.Logic.PLNWorldModelCategoricalBridge.WMHyperdoctrine.EndpointStatement
      (H := H) pi1 pi2 fcat gcat (semEState relEnv Iatom φ) φcat
    ∧
    WMEvidenceObligation SemEState SemEQuery
      (semEState relEnv Iatom φ) p q := by
  rcases semE_fragment_formulaCategoricalEndpoint_step
      (H := H)
      (pi1 := pi1) (pi2 := pi2) (fcat := fcat) (gcat := gcat)
      (hpb := hpb) (hmfcat := hmfcat) (hmpi2 := hmpi2)
      (relEnv := relEnv) (queryOfAtom := queryOfAtom)
      (I := Iatom) (hAtom := hAtom) (φ := φ) (hφ := hφ)
      (Xobj := Xobj) (X := Xgr)
      (p := p) (q := q) hstep (φcat := φcat)
    with ⟨hPack, hEv⟩
  exact ⟨(hPack p).2, hEv⟩

/-- SemE fragment fixture (star): consume the star-closure categorical endpoint
and project endpoint statement + evidence obligation. -/
theorem semE_fragment_categorical_endpoint_stepStar_fixture
    (H : Mettapedia.Logic.PLNWorldModelHyperdoctrine.WMHyperdoctrine SemEState)
    {P Aobj Bobj D : H.Obj}
    (pi1 : P ⟶ Aobj) (pi2 : P ⟶ Bobj) (fcat : Aobj ⟶ D) (gcat : Bobj ⟶ D)
    (hpb : CategoryTheory.IsPullback pi1 pi2 fcat gcat)
    (hmfcat : CategoryTheory.Mono fcat) (hmpi2 : CategoryTheory.Mono pi2)
    (relEnv : RelationEnv)
    (queryOfAtom : String → Pattern → Pattern)
    (Iatom : EvidenceAtomSem)
    (hAtom :
      ∀ (a : String) {p q : Pattern},
        OSLFTheoryStep relEnv p q →
        Iatom a p ≤ Iatom a q)
    (φ : OSLFFormula)
    (hφ : StepEvidenceMonotoneFragment φ)
    (Xobj : Mettapedia.CategoryTheory.PLNInstance.PLNObj)
    {Xgr : Opposite (Mettapedia.OSLF.Framework.ConstructorCategory.ConstructorObj
      Mettapedia.OSLF.Framework.MeTTaToNTT.mettaFull)}
    (p q : Pattern)
    (hstar : OSLFTheoryStepStar relEnv p q)
    (φcat : H.query Bobj) :
    Mettapedia.Logic.PLNWorldModelCategoricalBridge.WMHyperdoctrine.EndpointStatement
      (H := H) pi1 pi2 fcat gcat (semEState relEnv Iatom φ) φcat
    ∧
    WMEvidenceObligation SemEState SemEQuery
      (semEState relEnv Iatom φ) p q := by
  rcases semE_fragment_formulaCategoricalEndpoint_stepStar
      (H := H)
      (pi1 := pi1) (pi2 := pi2) (fcat := fcat) (gcat := gcat)
      (hpb := hpb) (hmfcat := hmfcat) (hmpi2 := hmpi2)
      (relEnv := relEnv) (queryOfAtom := queryOfAtom)
      (I := Iatom) (hAtom := hAtom) (φ := φ) (hφ := hφ)
      (Xobj := Xobj) (X := Xgr)
      (p := p) (q := q) (hstar := hstar) (φcat := φcat)
    with ⟨hPack, hEv⟩
  exact ⟨(hPack p).2, hEv⟩

/-- SemE fragment fixture (policy star): consume the policy-indexed star
categorical endpoint wrapper directly (no ad-hoc atom/modal assumptions). -/
theorem semE_fragment_categorical_endpoint_policy_stepStar_fixture
    (H : Mettapedia.Logic.PLNWorldModelHyperdoctrine.WMHyperdoctrine SemEState)
    {P Aobj Bobj D : H.Obj}
    (pi1 : P ⟶ Aobj) (pi2 : P ⟶ Bobj) (fcat : Aobj ⟶ D) (gcat : Bobj ⟶ D)
    (hpb : CategoryTheory.IsPullback pi1 pi2 fcat gcat)
    (hmfcat : CategoryTheory.Mono fcat) (hmpi2 : CategoryTheory.Mono pi2)
    (relEnv : RelationEnv)
    (queryOfAtom : String → Pattern → Pattern)
    (Iatom : EvidenceAtomSem)
    (policy : ControlledStepPolicy relEnv Iatom)
    (φ : OSLFFormula)
    (hφ : StepEvidenceControlledByPolicy policy φ)
    (Xobj : Mettapedia.CategoryTheory.PLNInstance.PLNObj)
    {Xgr : Opposite (Mettapedia.OSLF.Framework.ConstructorCategory.ConstructorObj
      Mettapedia.OSLF.Framework.MeTTaToNTT.mettaFull)}
    (p q : Pattern)
    (hstar : OSLFTheoryStepStar relEnv p q)
    (φcat : H.query Bobj) :
    Mettapedia.Logic.PLNWorldModelCategoricalBridge.WMHyperdoctrine.EndpointStatement
      (H := H) pi1 pi2 fcat gcat (semEState relEnv Iatom φ) φcat
    ∧
    WMEvidenceObligation SemEState SemEQuery
      (semEState relEnv Iatom φ) p q := by
  rcases semE_fragment_formulaCategoricalEndpoint_stepStar_of_policy
      (H := H)
      (pi1 := pi1) (pi2 := pi2) (fcat := fcat) (gcat := gcat)
      (hpb := hpb) (hmfcat := hmfcat) (hmpi2 := hmpi2)
      (relEnv := relEnv) (queryOfAtom := queryOfAtom)
      (I := Iatom) (policy := policy) (φ := φ) (hφ := hφ)
      (Xobj := Xobj) (X := Xgr)
      (p := p) (q := q) (hstar := hstar) (φcat := φcat)
    with ⟨hPack, hEv⟩
  exact ⟨(hPack p).2, hEv⟩

/-- SemE fragment fixture (star-rule): consume the dedicated evidence-rule
constructor generated from the star categorical endpoint package. -/
theorem semE_fragment_evidence_rule_stepStar_fixture
    (H : Mettapedia.Logic.PLNWorldModelHyperdoctrine.WMHyperdoctrine SemEState)
    {P Aobj Bobj D : H.Obj}
    (pi1 : P ⟶ Aobj) (pi2 : P ⟶ Bobj) (fcat : Aobj ⟶ D) (gcat : Bobj ⟶ D)
    (hpb : CategoryTheory.IsPullback pi1 pi2 fcat gcat)
    (hmfcat : CategoryTheory.Mono fcat) (hmpi2 : CategoryTheory.Mono pi2)
    (relEnv : RelationEnv)
    (queryOfAtom : String → Pattern → Pattern)
    (Iatom : EvidenceAtomSem)
    (hAtom :
      ∀ (a : String) {p q : Pattern},
        OSLFTheoryStep relEnv p q →
        Iatom a p ≤ Iatom a q)
    (φ : OSLFFormula)
    (hφ : StepEvidenceMonotoneFragment φ)
    (Xobj : Mettapedia.CategoryTheory.PLNInstance.PLNObj)
    {Xgr : Opposite (Mettapedia.OSLF.Framework.ConstructorCategory.ConstructorObj
      Mettapedia.OSLF.Framework.MeTTaToNTT.mettaFull)}
    {p q : Pattern}
    (hstar : OSLFTheoryStepStar relEnv p q)
    (φcat : H.query Bobj) :
    let r :=
      semE_fragment_evidenceRuleOn_of_formulaCategoricalEndpoint_stepStar
        (H := H)
        (pi1 := pi1) (pi2 := pi2) (fcat := fcat) (gcat := gcat)
        (hpb := hpb) (hmfcat := hmfcat) (hmpi2 := hmpi2)
        (relEnv := relEnv) (queryOfAtom := queryOfAtom)
        (I := Iatom) (hAtom := hAtom) (φ := φ) (hφ := hφ)
        (Xobj := Xobj) (X := Xgr)
        (hstar := hstar) (φcat := φcat)
    WMEvidenceObligation SemEState SemEQuery
      (semEState relEnv Iatom φ) r.premise r.conclusion := by
  intro r
  have hSide : r.side (semEState relEnv Iatom φ) := rfl
  exact r.sound hSide

/-- SemE fragment fixture (policy star-rule): consume the dedicated
policy-indexed evidence-rule constructor. -/
theorem semE_fragment_evidence_rule_policy_stepStar_fixture
    (H : Mettapedia.Logic.PLNWorldModelHyperdoctrine.WMHyperdoctrine SemEState)
    {P Aobj Bobj D : H.Obj}
    (pi1 : P ⟶ Aobj) (pi2 : P ⟶ Bobj) (fcat : Aobj ⟶ D) (gcat : Bobj ⟶ D)
    (hpb : CategoryTheory.IsPullback pi1 pi2 fcat gcat)
    (hmfcat : CategoryTheory.Mono fcat) (hmpi2 : CategoryTheory.Mono pi2)
    (relEnv : RelationEnv)
    (queryOfAtom : String → Pattern → Pattern)
    (Iatom : EvidenceAtomSem)
    (policy : ControlledStepPolicy relEnv Iatom)
    (φ : OSLFFormula)
    (hφ : StepEvidenceControlledByPolicy policy φ)
    (Xobj : Mettapedia.CategoryTheory.PLNInstance.PLNObj)
    {Xgr : Opposite (Mettapedia.OSLF.Framework.ConstructorCategory.ConstructorObj
      Mettapedia.OSLF.Framework.MeTTaToNTT.mettaFull)}
    {p q : Pattern}
    (hstar : OSLFTheoryStepStar relEnv p q)
    (φcat : H.query Bobj) :
    let r :=
      semE_fragment_evidenceRuleOn_of_formulaCategoricalEndpoint_stepStar_of_policy
        (H := H)
        (pi1 := pi1) (pi2 := pi2) (fcat := fcat) (gcat := gcat)
        (hpb := hpb) (hmfcat := hmfcat) (hmpi2 := hmpi2)
        (relEnv := relEnv) (queryOfAtom := queryOfAtom)
        (I := Iatom) (policy := policy) (φ := φ) (hφ := hφ)
        (Xobj := Xobj) (X := Xgr)
        (hstar := hstar) (φcat := φcat)
    WMEvidenceObligation SemEState SemEQuery
      (semEState relEnv Iatom φ) r.premise r.conclusion := by
  intro r
  have hSide : r.side (semEState relEnv Iatom φ) := rfl
  exact r.sound hSide

/-- Canonical closure regression fixture: consume the formula-level path-order
star wrapper directly and project the endpoint + evidence obligations. -/
theorem formula_pathOrder_star_endpoint_projection_fixture
    (lang : LanguageDef) (s : LangSort lang)
    (seed qComm : Pattern) (φpred : Pattern → Prop)
    (relEnv : RelationEnv)
    (I : EvidenceAtomSem)
    (hPathOrder :
      ∀ {a b : LangSort lang}
        (g : SortPath lang a b) (h : SortPath lang b s),
          pathSem lang g (pathSem lang h seed) = pathSem lang (g.comp h) seed)
    (hSemEPolicy : ControlledStepPolicy relEnv I)
    {Pm Bm Dm : CategoryTheory.Functor (Opposite (ConstructorObj lang)) (Type _)}
    (pi1m : Pm ⟶ (languageSortRepresentableObj lang s))
    (pi2m : Pm ⟶ Bm)
    (fm : (languageSortRepresentableObj lang s) ⟶ Dm)
    (gm : Bm ⟶ Dm)
    (hpbm : CategoryTheory.IsPullback pi1m pi2m fm gm)
    (hfm : CategoryTheory.Mono fm) (hpi2m : CategoryTheory.Mono pi2m)
    {Xmodal : Opposite (ConstructorObj lang)}
    (pmodal : Pattern)
    (H : Mettapedia.Logic.PLNWorldModelHyperdoctrine.WMHyperdoctrine SemEState)
    {P Aobj Bobj D : H.Obj}
    (pi1 : P ⟶ Aobj) (pi2 : P ⟶ Bobj) (fcat : Aobj ⟶ D) (gcat : Bobj ⟶ D)
    (hpb : CategoryTheory.IsPullback pi1 pi2 fcat gcat)
    (hmfcat : CategoryTheory.Mono fcat) (hmpi2 : CategoryTheory.Mono pi2)
    (queryOfAtom : String → Pattern → Pattern)
    (φf : OSLFFormula)
    (hφ : StepEvidenceControlledByPolicy hSemEPolicy φf)
    (Xobj : Mettapedia.CategoryTheory.PLNInstance.PLNObj)
    {Xgr : Opposite (Mettapedia.OSLF.Framework.ConstructorCategory.ConstructorObj
      Mettapedia.OSLF.Framework.MeTTaToNTT.mettaFull)}
    (p q : Pattern)
    (hstar : OSLFTheoryStepStar relEnv p q)
    (φcat : H.query Bobj) :
    Mettapedia.Logic.PLNWorldModelCategoricalBridge.WMHyperdoctrine.EndpointStatement
      (H := H) pi1 pi2 fcat gcat (semEState relEnv I φf) φcat
    ∧
    WMEvidenceObligation SemEState SemEQuery
      (semEState relEnv I φf) p q := by
  have hPack :=
    oslf_formula_ntt_wm_star_sound_of_pathOrder
      (lang := lang) (s := s)
      (seed := seed) (qComm := qComm) (φpred := φpred)
      (relEnv := relEnv)
      (I := I)
      (hPathOrder := hPathOrder)
      (hSemEPolicy := hSemEPolicy)
      (pi1m := pi1m) (pi2m := pi2m) (fm := fm) (gm := gm)
      (hpbm := hpbm) (hfm := hfm) (hpi2m := hpi2m)
      (Xmodal := Xmodal) (pmodal := pmodal)
      (H := H)
      (pi1 := pi1) (pi2 := pi2) (fcat := fcat) (gcat := gcat)
      (hpb := hpb) (hmfcat := hmfcat) (hmpi2 := hmpi2)
      (queryOfAtom := queryOfAtom)
      (φf := φf) (hφ := hφ)
      (Xobj := Xobj) (Xgr := Xgr)
      (p := p) (q := q) (hstar := hstar) (φcat := φcat)
  exact ⟨hPack.2.2.2.1, hPack.2.2.2.2⟩

/-- Canonical-closure regression fixture: consume `CanonicalClosureContext`
directly at the fixpoint endpoint surface. -/
theorem canonical_context_fixpoint_endpoint_fixture
    (ctx : CanonicalClosureContext)
    {Pm Bm Dm : CategoryTheory.Functor (Opposite (ConstructorObj ctx.lang)) (Type _)}
    (pi1m : Pm ⟶ (languageSortRepresentableObj ctx.lang ctx.s))
    (pi2m : Pm ⟶ Bm)
    (fm : (languageSortRepresentableObj ctx.lang ctx.s) ⟶ Dm)
    (gm : Bm ⟶ Dm)
    (hpbm : CategoryTheory.IsPullback pi1m pi2m fm gm)
    (hfm : CategoryTheory.Mono fm) (hpi2m : CategoryTheory.Mono pi2m)
    {Xmodal : Opposite (ConstructorObj ctx.lang)}
    (pmodal : Pattern)
    (H : Mettapedia.Logic.PLNWorldModelHyperdoctrine.WMHyperdoctrine SemEState)
    {P Aobj Bobj D : H.Obj}
    (pi1 : P ⟶ Aobj) (pi2 : P ⟶ Bobj) (fcat : Aobj ⟶ D) (gcat : Bobj ⟶ D)
    (hpb : CategoryTheory.IsPullback pi1 pi2 fcat gcat)
    (hmfcat : CategoryTheory.Mono fcat) (hmpi2 : CategoryTheory.Mono pi2)
    (queryOfAtom : String → Pattern → Pattern)
    (φf : OSLFFormula)
    (hφ : StepEvidenceControlledByPolicy ctx.hSemEPolicy φf)
    (Xobj : Mettapedia.CategoryTheory.PLNInstance.PLNObj)
    {Xgr : Opposite (Mettapedia.OSLF.Framework.ConstructorCategory.ConstructorObj
      Mettapedia.OSLF.Framework.MeTTaToNTT.mettaFull)}
    (p q : Pattern)
    (hstar : OSLFTheoryStepStar ctx.relEnv p q)
    (φcat : H.query Bobj)
    (hStrengthFromEvidence :
      WMEvidenceObligation SemEState SemEQuery
        (semEState ctx.relEnv ctx.I φf) p q →
      WMStrengthObligation SemEState SemEQuery
        (semEState ctx.relEnv ctx.I φf) p q) :
    let W0 : SemEState := semEState ctx.relEnv ctx.I φf
    let r : WMConsequenceRuleOn SemEState SemEQuery :=
      { side := fun W => W = W0
        premise := p
        conclusion := q
        sound := by
          intro W hW
          subst hW
          have hCore :=
            oslf_formula_ntt_wm_star_sound_ctx
              (ctx := ctx)
              (pi1m := pi1m) (pi2m := pi2m) (fm := fm) (gm := gm)
              (hpbm := hpbm) (hfm := hfm) (hpi2m := hpi2m)
              (Xmodal := Xmodal) (pmodal := pmodal)
              (H := H)
              (pi1 := pi1) (pi2 := pi2) (fcat := fcat) (gcat := gcat)
              (hpb := hpb) (hmfcat := hmfcat) (hmpi2 := hmpi2)
              (queryOfAtom := queryOfAtom)
              (φf := φf) (hφ := hφ)
              (Xobj := Xobj) (Xgr := Xgr)
              (p := p) (q := q) (hstar := hstar) (φcat := φcat)
          rcases hCore with ⟨_hFormula, hRest⟩
          rcases hRest with ⟨_hModal, hRest⟩
          rcases hRest with ⟨_hDia, hRest⟩
          rcases hRest with ⟨_hEndpoint, hEv⟩
          exact hStrengthFromEvidence hEv }
    let R : Mettapedia.Logic.PLNWorldModelFixpointClosure.RuleSet SemEState SemEQuery := ({r} : Set _)
    p ∈ Mettapedia.Logic.PLNWorldModelFixpointClosure.immediateIter R W0 ({p} : Set SemEQuery) 0
      ∧ q ∈ Mettapedia.Logic.PLNWorldModelFixpointClosure.immediateIter R W0 ({p} : Set SemEQuery) 1
      ∧ q ∈ Mettapedia.Logic.PLNWorldModelFixpointClosure.leastRuleClosure R W0 ({p} : Set SemEQuery) := by
  simpa using
    (canonical_star_to_fixpoint_endpoint
      (ctx := ctx)
      (pi1m := pi1m) (pi2m := pi2m) (fm := fm) (gm := gm)
      (hpbm := hpbm) (hfm := hfm) (hpi2m := hpi2m)
      (Xmodal := Xmodal) (pmodal := pmodal)
      (H := H)
      (pi1 := pi1) (pi2 := pi2) (fcat := fcat) (gcat := gcat)
      (hpb := hpb) (hmfcat := hmfcat) (hmpi2 := hmpi2)
      (queryOfAtom := queryOfAtom)
      (φf := φf) (hφ := hφ)
      (Xobj := Xobj) (Xgr := Xgr)
      (p := p) (q := q) (hstar := hstar) (φcat := φcat)
      (hStrengthFromEvidence := hStrengthFromEvidence))

/-- Canonical-closure regression fixture:
consume the explicit rule-pack transport surface and the fixpoint closure
endpoint from one shared `CanonicalClosureContext`. -/
theorem canonical_context_rulePack_fixpoint_endpoint_fixture
    (ctx : CanonicalClosureContext)
    (hφTop :
      languageSortPredNaturality ctx.lang ctx.s ctx.seed ctx.φpred)
    {Pm Bm Dm : CategoryTheory.Functor (Opposite (ConstructorObj ctx.lang)) (Type _)}
    (pi1m : Pm ⟶ (languageSortRepresentableObj ctx.lang ctx.s))
    (pi2m : Pm ⟶ Bm)
    (fm : (languageSortRepresentableObj ctx.lang ctx.s) ⟶ Dm)
    (gm : Bm ⟶ Dm)
    (hpbm : CategoryTheory.IsPullback pi1m pi2m fm gm)
    (hfm : CategoryTheory.Mono fm) (hpi2m : CategoryTheory.Mono pi2m)
    {Xmodal : Opposite (ConstructorObj ctx.lang)}
    (pmodal : Pattern)
    (H : Mettapedia.Logic.PLNWorldModelHyperdoctrine.WMHyperdoctrine SemEState)
    {P Aobj Bobj D : H.Obj}
    (pi1 : P ⟶ Aobj) (pi2 : P ⟶ Bobj) (fcat : Aobj ⟶ D) (gcat : Bobj ⟶ D)
    (hpb : CategoryTheory.IsPullback pi1 pi2 fcat gcat)
    (hmfcat : CategoryTheory.Mono fcat) (hmpi2 : CategoryTheory.Mono pi2)
    (queryOfAtom : String → Pattern → Pattern)
    (φf : OSLFFormula)
    (hφ : StepEvidenceControlledByPolicy ctx.hSemEPolicy φf)
    (Xobj : Mettapedia.CategoryTheory.PLNInstance.PLNObj)
    {Xgr : Opposite (Mettapedia.OSLF.Framework.ConstructorCategory.ConstructorObj
      Mettapedia.OSLF.Framework.MeTTaToNTT.mettaFull)}
    (p q : Pattern)
    (hstar : OSLFTheoryStepStar ctx.relEnv p q)
    (φcat : H.query Bobj)
    (χ ψ : CategoryTheory.Subfunctor Dm)
    (hStrengthFromEvidence :
      WMEvidenceObligation SemEState SemEQuery
        (semEState ctx.relEnv ctx.I φf) p q →
      WMStrengthObligation SemEState SemEQuery
        (semEState ctx.relEnv ctx.I φf) p q) :
    ((((Mettapedia.GSLT.Topos.presheafChangeOfBase
        (C := ConstructorObj ctx.lang)).directImage fm)
        ((languageSortFiber_ofPatternPred ctx.lang ctx.s ctx.seed ctx.φpred hφTop :
          CategoryTheory.Subfunctor (languageSortRepresentableObj ctx.lang ctx.s)))
      ≤ ψ)
      ↔
      ((show CategoryTheory.Subfunctor (languageSortRepresentableObj ctx.lang ctx.s)
          from languageSortFiber_ofPatternPred ctx.lang ctx.s ctx.seed ctx.φpred hφTop)
        ≤ ((Mettapedia.GSLT.Topos.presheafChangeOfBase
          (C := ConstructorObj ctx.lang)).pullback fm) ψ))
    ∧
    ((((Mettapedia.GSLT.Topos.presheafChangeOfBase
        (C := ConstructorObj ctx.lang)).pullback fm) χ
      ≤ languageSortFiber_ofPatternPred ctx.lang ctx.s ctx.seed ctx.φpred hφTop)
      ↔
      (χ ≤
        ((Mettapedia.GSLT.Topos.presheafChangeOfBase
          (C := ConstructorObj ctx.lang)).universalImage fm)
          (languageSortFiber_ofPatternPred ctx.lang ctx.s ctx.seed ctx.φpred hφTop)))
    ∧
    (let W0 : SemEState := semEState ctx.relEnv ctx.I φf
      let r : WMConsequenceRuleOn SemEState SemEQuery :=
        { side := fun W => W = W0
          premise := p
          conclusion := q
          sound := by
            intro W hW
            subst hW
            have hCore :=
              oslf_formula_ntt_wm_star_sound_ctx
                (ctx := ctx)
                (pi1m := pi1m) (pi2m := pi2m) (fm := fm) (gm := gm)
                (hpbm := hpbm) (hfm := hfm) (hpi2m := hpi2m)
                (Xmodal := Xmodal) (pmodal := pmodal)
                (H := H)
                (pi1 := pi1) (pi2 := pi2) (fcat := fcat) (gcat := gcat)
                (hpb := hpb) (hmfcat := hmfcat) (hmpi2 := hmpi2)
                (queryOfAtom := queryOfAtom)
                (φf := φf) (hφ := hφ)
                (Xobj := Xobj) (Xgr := Xgr)
                (p := p) (q := q) (hstar := hstar) (φcat := φcat)
            rcases hCore with ⟨_hFormula, hRest⟩
            rcases hRest with ⟨_hModal, hRest⟩
            rcases hRest with ⟨_hDia, hRest⟩
            rcases hRest with ⟨_hEndpoint, hEv⟩
            exact hStrengthFromEvidence hEv }
      let R : Mettapedia.Logic.PLNWorldModelFixpointClosure.RuleSet SemEState SemEQuery := ({r} : Set _)
      p ∈ Mettapedia.Logic.PLNWorldModelFixpointClosure.immediateIter R W0 ({p} : Set SemEQuery) 0
        ∧ q ∈ Mettapedia.Logic.PLNWorldModelFixpointClosure.immediateIter R W0 ({p} : Set SemEQuery) 1
        ∧ q ∈ Mettapedia.Logic.PLNWorldModelFixpointClosure.leastRuleClosure R W0 ({p} : Set SemEQuery)) := by
  let modal : CanonicalModalSquare ctx := {
    Pm := Pm
    Bm := Bm
    Dm := Dm
    pi1m := pi1m
    pi2m := pi2m
    fm := fm
    gm := gm
    hpbm := hpbm
    hfm := hfm
    hpi2m := hpi2m
    Xmodal := Xmodal
    pmodal := pmodal
  }
  let cat : CanonicalHyperSquare ctx := {
    H := H
    P := P
    Aobj := Aobj
    Bobj := Bobj
    D := D
    pi1 := pi1
    pi2 := pi2
    fcat := fcat
    gcat := gcat
    hpb := hpb
    hmfcat := hmfcat
    hmpi2 := hmpi2
  }
  let fa : CanonicalFormulaArgs ctx := {
    queryOfAtom := queryOfAtom
    φf := φf
    hφ := hφ
    Xobj := Xobj
    Xgr := Xgr
  }
  let goal : CanonicalGoalArgs ctx cat fa := {
    p := p
    q := q
    hstar := hstar
    φcat := φcat
    hStrengthFromEvidence := hStrengthFromEvidence
  }
  let transportGoal : CanonicalTransportGoalArgs ctx modal cat fa := {
    hφTop := hφTop
    χ := χ
    ψ := ψ
    goal := goal
  }
  simpa [modal, cat, fa, goal, transportGoal] using
    canonical_rulePack_transport_piSigma_and_fixpoint_of_transportGoal
      (ctx := ctx) (modal := modal) (cat := cat) (fa := fa)
      (hPiSigmaPack := Mettapedia.OSLF.NativeType.prop12_piSigmaPredicateRulePack
        (C := ConstructorObj ctx.lang))
      (transportGoal := transportGoal)

/-- Canonical-closure regression fixture:
transport-goal bundled variant consuming the explicit Prop-12 Π/Σ transport-pack
compatibility endpoint together with WM fixpoint closure. -/
theorem canonical_context_transportGoal_rulePack_fixpoint_endpoint_fixture_via_rulePack
    (ctx : CanonicalClosureContext)
    (modal : CanonicalModalSquare ctx)
    (cat : CanonicalHyperSquare ctx)
    (fa : CanonicalFormulaArgs ctx)
    (hPiSigmaPack :
      Mettapedia.OSLF.NativeType.PiSigmaPredicateRulePack
        (C := ConstructorObj ctx.lang))
    (transportGoal : CanonicalTransportGoalArgs ctx modal cat fa) :
    ((((Mettapedia.GSLT.Topos.presheafChangeOfBase
        (C := ConstructorObj ctx.lang)).directImage modal.fm)
        ((languageSortFiber_ofPatternPred ctx.lang ctx.s ctx.seed ctx.φpred transportGoal.hφTop :
          CategoryTheory.Subfunctor (languageSortRepresentableObj ctx.lang ctx.s)))
      ≤ transportGoal.ψ)
      ↔
      ((show CategoryTheory.Subfunctor (languageSortRepresentableObj ctx.lang ctx.s)
          from languageSortFiber_ofPatternPred
            ctx.lang ctx.s ctx.seed ctx.φpred transportGoal.hφTop)
        ≤ ((Mettapedia.GSLT.Topos.presheafChangeOfBase
          (C := ConstructorObj ctx.lang)).pullback modal.fm) transportGoal.ψ))
    ∧
    ((((Mettapedia.GSLT.Topos.presheafChangeOfBase
        (C := ConstructorObj ctx.lang)).pullback modal.fm) transportGoal.χ
      ≤ languageSortFiber_ofPatternPred
          ctx.lang ctx.s ctx.seed ctx.φpred transportGoal.hφTop)
      ↔
      (transportGoal.χ ≤
        ((Mettapedia.GSLT.Topos.presheafChangeOfBase
          (C := ConstructorObj ctx.lang)).universalImage modal.fm)
          (languageSortFiber_ofPatternPred
            ctx.lang ctx.s ctx.seed ctx.φpred transportGoal.hφTop)))
    ∧
    (let W0 : SemEState := semEState ctx.relEnv ctx.I fa.φf
      let r : WMConsequenceRuleOn SemEState SemEQuery :=
        canonicalConsequenceRuleOn_compact_of_goal
          (ctx := ctx) (modal := modal) (cat := cat) (fa := fa)
          (goal := transportGoal.goal)
      let R : Mettapedia.Logic.PLNWorldModelFixpointClosure.RuleSet SemEState SemEQuery := ({r} : Set _)
      transportGoal.goal.p ∈ Mettapedia.Logic.PLNWorldModelFixpointClosure.immediateIter R W0 ({transportGoal.goal.p} : Set SemEQuery) 0
        ∧ transportGoal.goal.q ∈ Mettapedia.Logic.PLNWorldModelFixpointClosure.immediateIter R W0 ({transportGoal.goal.p} : Set SemEQuery) 1
        ∧ transportGoal.goal.q ∈ Mettapedia.Logic.PLNWorldModelFixpointClosure.leastRuleClosure R W0 ({transportGoal.goal.p} : Set SemEQuery)) := by
  simpa using canonical_rulePack_transport_piSigma_and_fixpoint_of_transportGoal
    (ctx := ctx) (modal := modal) (cat := cat) (fa := fa)
    (hPiSigmaPack := hPiSigmaPack)
    (transportGoal := transportGoal)

/-- Canonical-closure regression fixture:
transport-goal bundled Prop-12 compatibility route over the rule-pack-first
transport-goal endpoint. -/
theorem canonical_context_transportGoal_rulePack_fixpoint_endpoint_fixture
    (ctx : CanonicalClosureContext)
    (modal : CanonicalModalSquare ctx)
    (cat : CanonicalHyperSquare ctx)
    (fa : CanonicalFormulaArgs ctx)
    (transportGoal : CanonicalTransportGoalArgs ctx modal cat fa) :
    ((((Mettapedia.GSLT.Topos.presheafChangeOfBase
        (C := ConstructorObj ctx.lang)).directImage modal.fm)
        ((languageSortFiber_ofPatternPred ctx.lang ctx.s ctx.seed ctx.φpred transportGoal.hφTop :
          CategoryTheory.Subfunctor (languageSortRepresentableObj ctx.lang ctx.s)))
      ≤ transportGoal.ψ)
      ↔
      ((show CategoryTheory.Subfunctor (languageSortRepresentableObj ctx.lang ctx.s)
          from languageSortFiber_ofPatternPred
            ctx.lang ctx.s ctx.seed ctx.φpred transportGoal.hφTop)
        ≤ ((Mettapedia.GSLT.Topos.presheafChangeOfBase
          (C := ConstructorObj ctx.lang)).pullback modal.fm) transportGoal.ψ))
    ∧
    ((((Mettapedia.GSLT.Topos.presheafChangeOfBase
        (C := ConstructorObj ctx.lang)).pullback modal.fm) transportGoal.χ
      ≤ languageSortFiber_ofPatternPred
          ctx.lang ctx.s ctx.seed ctx.φpred transportGoal.hφTop)
      ↔
      (transportGoal.χ ≤
        ((Mettapedia.GSLT.Topos.presheafChangeOfBase
          (C := ConstructorObj ctx.lang)).universalImage modal.fm)
          (languageSortFiber_ofPatternPred
            ctx.lang ctx.s ctx.seed ctx.φpred transportGoal.hφTop)))
    ∧
    (let W0 : SemEState := semEState ctx.relEnv ctx.I fa.φf
      let r : WMConsequenceRuleOn SemEState SemEQuery :=
        canonicalConsequenceRuleOn_compact_of_goal
          (ctx := ctx) (modal := modal) (cat := cat) (fa := fa)
          (goal := transportGoal.goal)
      let R : Mettapedia.Logic.PLNWorldModelFixpointClosure.RuleSet SemEState SemEQuery := ({r} : Set _)
      transportGoal.goal.p ∈ Mettapedia.Logic.PLNWorldModelFixpointClosure.immediateIter R W0 ({transportGoal.goal.p} : Set SemEQuery) 0
        ∧ transportGoal.goal.q ∈ Mettapedia.Logic.PLNWorldModelFixpointClosure.immediateIter R W0 ({transportGoal.goal.p} : Set SemEQuery) 1
        ∧ transportGoal.goal.q ∈ Mettapedia.Logic.PLNWorldModelFixpointClosure.leastRuleClosure R W0 ({transportGoal.goal.p} : Set SemEQuery)) := by
  simpa using canonical_context_transportGoal_rulePack_fixpoint_endpoint_fixture_via_rulePack
    (ctx := ctx) (modal := modal) (cat := cat) (fa := fa)
    (hPiSigmaPack := Mettapedia.OSLF.NativeType.prop12_piSigmaPredicateRulePack
      (C := ConstructorObj ctx.lang))
    (transportGoal := transportGoal)

/-- Canonical compact fixture:
consume the compact bundled canonical consequence-rule constructor directly. -/
theorem canonical_compact_rule_constructor_fixture
    (ctx : CanonicalClosureContext)
    (modal : CanonicalModalSquare ctx)
    (cat : CanonicalHyperSquare ctx)
    (fa : CanonicalFormulaArgs ctx)
    (p q : Pattern)
    (hstar : OSLFTheoryStepStar ctx.relEnv p q)
    (φcat : cat.H.query cat.Bobj)
    (hStrengthFromEvidence :
      WMEvidenceObligation SemEState SemEQuery
        (semEState ctx.relEnv ctx.I fa.φf) p q →
      WMStrengthObligation SemEState SemEQuery
        (semEState ctx.relEnv ctx.I fa.φf) p q) :
    let r : WMConsequenceRuleOn SemEState SemEQuery :=
      canonicalConsequenceRuleOn_compact
        (ctx := ctx) (modal := modal) (cat := cat) (fa := fa)
        (p := p) (q := q) (hstar := hstar) (φcat := φcat)
        (hStrengthFromEvidence := hStrengthFromEvidence)
    WorldModel.queryStrength (State := SemEState) (Query := SemEQuery)
      (semEState ctx.relEnv ctx.I fa.φf) r.premise ≤
    WorldModel.queryStrength (State := SemEState) (Query := SemEQuery)
      (semEState ctx.relEnv ctx.I fa.φf) r.conclusion := by
  intro r
  let goal : CanonicalGoalArgs ctx cat fa := {
    p := p
    q := q
    hstar := hstar
    φcat := φcat
    hStrengthFromEvidence := hStrengthFromEvidence
  }
  change WorldModel.queryStrength (State := SemEState) (Query := SemEQuery)
      (semEState ctx.relEnv ctx.I fa.φf)
      ((canonicalConsequenceRuleOn_compact_of_goal
        (ctx := ctx) (modal := modal) (cat := cat) (fa := fa) (goal := goal)).premise)
    ≤ WorldModel.queryStrength (State := SemEState) (Query := SemEQuery)
      (semEState ctx.relEnv ctx.I fa.φf)
      ((canonicalConsequenceRuleOn_compact_of_goal
        (ctx := ctx) (modal := modal) (cat := cat) (fa := fa) (goal := goal)).conclusion)
  have hSide :
      (canonicalConsequenceRuleOn_compact_of_goal
        (ctx := ctx) (modal := modal) (cat := cat) (fa := fa) (goal := goal)).side
        (semEState ctx.relEnv ctx.I fa.φf) := rfl
  simpa [r, goal] using
    (canonicalConsequenceRuleOn_compact_of_goal
      (ctx := ctx) (modal := modal) (cat := cat) (fa := fa) (goal := goal)).sound hSide

/-- Canonical compact fixture:
goal-bundled rule-constructor canary using `CanonicalGoalArgs` directly. -/
theorem canonical_compact_goal_rule_constructor_fixture
    (ctx : CanonicalClosureContext)
    (modal : CanonicalModalSquare ctx)
    (cat : CanonicalHyperSquare ctx)
    (fa : CanonicalFormulaArgs ctx)
    (goal : CanonicalGoalArgs ctx cat fa) :
    let r : WMConsequenceRuleOn SemEState SemEQuery :=
      canonicalConsequenceRuleOn_compact_of_goal
        (ctx := ctx) (modal := modal) (cat := cat) (fa := fa) (goal := goal)
    WorldModel.queryStrength (State := SemEState) (Query := SemEQuery)
      (semEState ctx.relEnv ctx.I fa.φf) r.premise ≤
    WorldModel.queryStrength (State := SemEState) (Query := SemEQuery)
      (semEState ctx.relEnv ctx.I fa.φf) r.conclusion := by
  intro r
  have hSide : r.side (semEState ctx.relEnv ctx.I fa.φf) := rfl
  exact r.sound hSide

/-- Canonical compact fixture:
the compact bundled canonical consequence rule is directly consumable by
`immediateIter/leastRuleClosure` without unpacking tuple endpoints. -/
theorem canonical_compact_rule_fixpoint_fixture
    (ctx : CanonicalClosureContext)
    (modal : CanonicalModalSquare ctx)
    (cat : CanonicalHyperSquare ctx)
    (fa : CanonicalFormulaArgs ctx)
    (p q : Pattern)
    (hstar : OSLFTheoryStepStar ctx.relEnv p q)
    (φcat : cat.H.query cat.Bobj)
    (hStrengthFromEvidence :
      WMEvidenceObligation SemEState SemEQuery
        (semEState ctx.relEnv ctx.I fa.φf) p q →
      WMStrengthObligation SemEState SemEQuery
        (semEState ctx.relEnv ctx.I fa.φf) p q) :
    let W0 : SemEState := semEState ctx.relEnv ctx.I fa.φf
    let r : WMConsequenceRuleOn SemEState SemEQuery :=
      canonicalConsequenceRuleOn_compact
        (ctx := ctx) (modal := modal) (cat := cat) (fa := fa)
        (p := p) (q := q) (hstar := hstar) (φcat := φcat)
        (hStrengthFromEvidence := hStrengthFromEvidence)
    let R : Mettapedia.Logic.PLNWorldModelFixpointClosure.RuleSet SemEState SemEQuery := ({r} : Set _)
    p ∈ Mettapedia.Logic.PLNWorldModelFixpointClosure.immediateIter R W0 ({p} : Set SemEQuery) 0
      ∧ q ∈ Mettapedia.Logic.PLNWorldModelFixpointClosure.immediateIter R W0 ({p} : Set SemEQuery) 1
      ∧ q ∈ Mettapedia.Logic.PLNWorldModelFixpointClosure.leastRuleClosure R W0 ({p} : Set SemEQuery) := by
  let goal : CanonicalGoalArgs ctx cat fa := {
    p := p
    q := q
    hstar := hstar
    φcat := φcat
    hStrengthFromEvidence := hStrengthFromEvidence
  }
  simpa [goal] using canonicalConsequenceRuleOn_compact_fixpoint_of_goal
    (ctx := ctx) (modal := modal) (cat := cat) (fa := fa) (goal := goal)

/-- Canonical compact fixture:
consume the combined Π/Σ transport-pack + WM fixpoint endpoint through the
bundled canonical context/square arguments. -/
theorem canonical_compact_rulePack_transport_fixpoint_fixture
    (ctx : CanonicalClosureContext)
    (modal : CanonicalModalSquare ctx)
    (cat : CanonicalHyperSquare ctx)
    (fa : CanonicalFormulaArgs ctx)
    (hφTop :
      languageSortPredNaturality ctx.lang ctx.s ctx.seed ctx.φpred)
    (p q : Pattern)
    (hstar : OSLFTheoryStepStar ctx.relEnv p q)
    (φcat : cat.H.query cat.Bobj)
    (hStrengthFromEvidence :
      WMEvidenceObligation SemEState SemEQuery
        (semEState ctx.relEnv ctx.I fa.φf) p q →
      WMStrengthObligation SemEState SemEQuery
        (semEState ctx.relEnv ctx.I fa.φf) p q) :
    Mettapedia.OSLF.Framework.BeckChevalleyOSLF.RepresentablePiSigmaTransportPack
      (lang := ctx.lang) (s := ctx.s) (seed := ctx.seed) (φ := ctx.φpred)
      (hNat := hφTop) (f := modal.fm)
    ∧
    (let W0 : SemEState := semEState ctx.relEnv ctx.I fa.φf
      let r : WMConsequenceRuleOn SemEState SemEQuery :=
        canonicalConsequenceRuleOn_compact
          (ctx := ctx) (modal := modal) (cat := cat) (fa := fa)
          (p := p) (q := q) (hstar := hstar) (φcat := φcat)
          (hStrengthFromEvidence := hStrengthFromEvidence)
      let R : Mettapedia.Logic.PLNWorldModelFixpointClosure.RuleSet SemEState SemEQuery := ({r} : Set _)
      p ∈ Mettapedia.Logic.PLNWorldModelFixpointClosure.immediateIter R W0 ({p} : Set SemEQuery) 0
        ∧ q ∈ Mettapedia.Logic.PLNWorldModelFixpointClosure.immediateIter R W0 ({p} : Set SemEQuery) 1
        ∧ q ∈ Mettapedia.Logic.PLNWorldModelFixpointClosure.leastRuleClosure R W0 ({p} : Set SemEQuery)) := by
  simpa using canonical_prop12_transport_pack_and_fixpoint_endpoint_compact
    (ctx := ctx) (modal := modal) (cat := cat) (fa := fa)
    (hφTop := hφTop)
    (p := p) (q := q) (hstar := hstar) (φcat := φcat)
    (hStrengthFromEvidence := hStrengthFromEvidence)

/-- Canonical compact fixture:
same combined Π/Σ transport + WM fixpoint endpoint, but through a single
goal-bundle argument to avoid high-arity theorem tails in callers. -/
theorem canonical_compact_goal_endpoint_fixture
    (ctx : CanonicalClosureContext)
    (modal : CanonicalModalSquare ctx)
    (cat : CanonicalHyperSquare ctx)
    (fa : CanonicalFormulaArgs ctx)
    (hφTop :
      languageSortPredNaturality ctx.lang ctx.s ctx.seed ctx.φpred)
    (goal : CanonicalGoalArgs ctx cat fa) :
    Mettapedia.OSLF.Framework.BeckChevalleyOSLF.RepresentablePiSigmaTransportPack
      (lang := ctx.lang) (s := ctx.s) (seed := ctx.seed) (φ := ctx.φpred)
      (hNat := hφTop) (f := modal.fm)
    ∧
    (let W0 : SemEState := semEState ctx.relEnv ctx.I fa.φf
      let r : WMConsequenceRuleOn SemEState SemEQuery :=
        canonicalConsequenceRuleOn_compact_of_goal
          (ctx := ctx) (modal := modal) (cat := cat) (fa := fa) (goal := goal)
      let R : Mettapedia.Logic.PLNWorldModelFixpointClosure.RuleSet SemEState SemEQuery := ({r} : Set _)
      goal.p ∈ Mettapedia.Logic.PLNWorldModelFixpointClosure.immediateIter R W0 ({goal.p} : Set SemEQuery) 0
        ∧ goal.q ∈ Mettapedia.Logic.PLNWorldModelFixpointClosure.immediateIter R W0 ({goal.p} : Set SemEQuery) 1
        ∧ goal.q ∈ Mettapedia.Logic.PLNWorldModelFixpointClosure.leastRuleClosure R W0 ({goal.p} : Set SemEQuery)) := by
  simpa using canonical_prop12_transport_pack_and_fixpoint_endpoint_of_goal
    (ctx := ctx) (modal := modal) (cat := cat) (fa := fa)
    (hφTop := hφTop) (goal := goal)

/-- Policy-object fixture: consume `modalSubobject_policy_semE_step_mono`
directly on an atom formula, using a shared modal-subobject/controlled policy. -/
theorem modal_policy_semE_step_mono_atom_fixture
    (relEnv : RelationEnv)
    (Iatom : EvidenceAtomSem)
    (hAtom :
      ∀ (a : String) {p q : Pattern},
        OSLFTheoryStep relEnv p q →
        Iatom a p ≤ Iatom a q)
    (hDia :
      ∀ {p q u : Pattern},
        OSLFTheoryStep relEnv p q →
        OSLFTheoryStep relEnv p u →
        OSLFTheoryStep relEnv q u)
    (hBox :
      ∀ {p q u : Pattern},
        OSLFTheoryStep relEnv p q →
        OSLFTheoryStep relEnv u q →
        OSLFTheoryStep relEnv u p)
    (seed commArg : Pattern)
    (a : String)
    {p qStep : Pattern}
    (hstep : OSLFTheoryStep relEnv p qStep) :
    semE (OSLFTheoryStep relEnv) Iatom (.atom a) p ≤
      semE (OSLFTheoryStep relEnv) Iatom (.atom a) qStep := by
  let semPolicy : ControlledStepPolicy relEnv Iatom := {
    atom_step_mono := hAtom
    impAnte := fun _ => False
    imp_step_antitone := by
      intro φ p q hFalse
      exact (False.elim hFalse)
    dia_successor_closed := hDia
    box_predecessor_closed := hBox
  }
  let policy :
      ModalSubobjectControlledPolicy
        Mettapedia.OSLF.Framework.MeTTaFullInstance.mettaFull
        Mettapedia.OSLF.Framework.MeTTaFullInstance.mettaState
        seed commArg relEnv Iatom := {
    pathLiftPkg :=
      Mettapedia.OSLF.Framework.CategoryBridge.commDiPathSemLiftPkg_of_pathSem_comm_subst_and_path_order
        Mettapedia.OSLF.Framework.MeTTaFullInstance.mettaFull
        Mettapedia.OSLF.Framework.MeTTaFullInstance.mettaState
        seed commArg
        (Mettapedia.OSLF.Framework.MeTTaFullInstance.mettaFull_pathOrder seed)
    semEPolicy := semPolicy
  }
  have hFrag : StepEvidenceControlledByPolicy policy.semEPolicy (.atom a) :=
    StepEvidenceControlledByPolicy.atom a
  exact modalSubobject_policy_semE_step_mono
    (lang := Mettapedia.OSLF.Framework.MeTTaFullInstance.mettaFull)
    (s := Mettapedia.OSLF.Framework.MeTTaFullInstance.mettaState)
    (seed := seed) (q := commArg)
    (relEnv := relEnv) (I := Iatom)
    (policy := policy)
    (hφf := hFrag)
    (hstep := hstep)

end Mettapedia.OSLF.Framework.OSLFNTTWMBridgeRegression
