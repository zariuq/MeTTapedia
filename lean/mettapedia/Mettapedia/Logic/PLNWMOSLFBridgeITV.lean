import Mettapedia.Logic.PLNWMOSLFBridge
import Mettapedia.Logic.PLNWorldModelITV
import Mettapedia.OSLF.Framework.QuantaleCoherence

/-!
# PLN ↔ WMΣ ↔ OSLF Bridge (Typed Queries, ITV Layer)

Typed ITV bridge above the typed WM and OSLF layers:

- atom-level ITV semantics from typed WM queries
- threshold-Prop atom semantics for ITV coordinates
- rewrite-rule soundness lifted to ITV atoms
- transport/coherence bundle connecting ITV atom thresholds to
  `Framework.QuantaleCoherence.language_quantale_coherence_bundle`
-/

namespace Mettapedia.Logic.PLNWMOSLFBridgeITVTyped

open Mettapedia.OSLF.Formula
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.OSLFEvidenceSemantics
open Mettapedia.Algebra.QuantaleWeakness
open Mettapedia.OSLF.Framework.LangMorphism
open Mettapedia.OSLF.Framework.QuantaleCoherence

/-! ## Core ITV Atom Bridge -/

section CoreBridge

variable {State Srt Ctx : Type*} {Query : Srt → Type*}
variable [EvidenceType State] [WorldModelSigma State Srt Query]

/-- Coordinate projection from an ITV to a real quantity. -/
abbrev ITVCoord := PLNIndefiniteTruth.ITV → ℝ

/-- Atom-indexed ITV semantics from typed WM queries. -/
noncomputable def wmITVAtomSemQSigma
    (itvSem : ITVSemantics Ctx) (ctx : Ctx)
    (W : State) (queryOfAtom : String → Pattern → Sigma Query) :
    String → Pattern → PLNIndefiniteTruth.ITV :=
  fun a p =>
    WorldModelSigma.queryITV
      (State := State) (Srt := Srt) (Query := Query) (Ctx := Ctx)
      itvSem ctx W (queryOfAtom a p)

/-- Generic threshold atom semantics over an ITV coordinate. -/
noncomputable def thresholdAtomSemOfWMITVQSigma
    (itvSem : ITVSemantics Ctx) (ctx : Ctx)
    (W : State) (tau : ℝ) (coord : ITVCoord)
    (queryOfAtom : String → Pattern → Sigma Query) : AtomSem :=
  fun a p => tau ≤ coord (wmITVAtomSemQSigma
    (State := State) (Srt := Srt) (Query := Query) (Ctx := Ctx)
    itvSem ctx W queryOfAtom a p)

/-- Lower-bound threshold atom semantics from ITV values. -/
noncomputable def lowerAtomSemOfWMITVQSigma
    (itvSem : ITVSemantics Ctx) (ctx : Ctx)
    (W : State) (tau : ℝ)
    (queryOfAtom : String → Pattern → Sigma Query) : AtomSem :=
  thresholdAtomSemOfWMITVQSigma
    (State := State) (Srt := Srt) (Query := Query) (Ctx := Ctx)
    itvSem ctx W tau (fun itv => itv.lower) queryOfAtom

/-- Upper-bound threshold atom semantics from ITV values. -/
noncomputable def upperAtomSemOfWMITVQSigma
    (itvSem : ITVSemantics Ctx) (ctx : Ctx)
    (W : State) (tau : ℝ)
    (queryOfAtom : String → Pattern → Sigma Query) : AtomSem :=
  thresholdAtomSemOfWMITVQSigma
    (State := State) (Srt := Srt) (Query := Query) (Ctx := Ctx)
    itvSem ctx W tau (fun itv => itv.upper) queryOfAtom

/-- Credibility-threshold atom semantics from ITV values. -/
noncomputable def credibilityAtomSemOfWMITVQSigma
    (itvSem : ITVSemantics Ctx) (ctx : Ctx)
    (W : State) (tau : ℝ)
    (queryOfAtom : String → Pattern → Sigma Query) : AtomSem :=
  thresholdAtomSemOfWMITVQSigma
    (State := State) (Srt := Srt) (Query := Query) (Ctx := Ctx)
    itvSem ctx W tau (fun itv => itv.credibility) queryOfAtom

/-- Width-threshold atom semantics from ITV values. -/
noncomputable def widthAtomSemOfWMITVQSigma
    (itvSem : ITVSemantics Ctx) (ctx : Ctx)
    (W : State) (tau : ℝ)
    (queryOfAtom : String → Pattern → Sigma Query) : AtomSem :=
  thresholdAtomSemOfWMITVQSigma
    (State := State) (Srt := Srt) (Query := Query) (Ctx := Ctx)
    itvSem ctx W tau (fun itv => itv.width) queryOfAtom

/-- Midpoint-strength-threshold atom semantics from ITV values. -/
noncomputable def strengthAtomSemOfWMITVQSigma
    (itvSem : ITVSemantics Ctx) (ctx : Ctx)
    (W : State) (tau : ℝ)
    (queryOfAtom : String → Pattern → Sigma Query) : AtomSem :=
  thresholdAtomSemOfWMITVQSigma
    (State := State) (Srt := Srt) (Query := Query) (Ctx := Ctx)
    itvSem ctx W tau (fun itv => itv.strength) queryOfAtom

@[simp] theorem wmITVAtomSemQSigma_atom
    (itvSem : ITVSemantics Ctx) (ctx : Ctx)
    (W : State) (queryOfAtom : String → Pattern → Sigma Query)
    (a : String) (p : Pattern) :
    wmITVAtomSemQSigma
      (State := State) (Srt := Srt) (Query := Query) (Ctx := Ctx)
      itvSem ctx W queryOfAtom a p =
      WorldModelSigma.queryITV
        (State := State) (Srt := Srt) (Query := Query) (Ctx := Ctx)
        itvSem ctx W (queryOfAtom a p) := rfl

/-- Typed WM rewrite soundness transferred to ITV atom equality. -/
theorem wmRewriteRuleSigma_itv_atom_eq_derive
    (itvSem : ITVSemantics Ctx) (ctx : Ctx)
    (r : WorldModelSigma.WMRewriteRuleSigma State Srt Query)
    (hSide : r.side) (W : State)
    (queryOfAtom : String → Pattern → Sigma Query)
    (a : String) (p : Pattern)
    (hEnc : queryOfAtom a p = r.conclusion) :
    wmITVAtomSemQSigma
      (State := State) (Srt := Srt) (Query := Query) (Ctx := Ctx)
      itvSem ctx W queryOfAtom a p
      = itvSem.eval ctx (r.derive W) := by
  unfold wmITVAtomSemQSigma
  calc
    WorldModelSigma.queryITV
      (State := State) (Srt := Srt) (Query := Query) (Ctx := Ctx)
      itvSem ctx W (queryOfAtom a p)
        =
      WorldModelSigma.queryITV
        (State := State) (Srt := Srt) (Query := Query) (Ctx := Ctx)
        itvSem ctx W r.conclusion := by simp [hEnc]
    _ = itvSem.eval ctx (r.derive W) := by
      simpa using
        (WorldModelSigma.WMRewriteRuleSigma.itv_eval_eq_queryITV
          (State := State) (Srt := Srt) (Query := Query) (Ctx := Ctx)
          (sem := itvSem) (ctx := ctx) (r := r) hSide W).symm

/-- Generic ITV-coordinate threshold consequence from a typed WM rewrite rule. -/
theorem wmRewriteRuleSigma_itv_threshold_atom
    (R : Pattern → Pattern → Prop)
    (itvSem : ITVSemantics Ctx) (ctx : Ctx)
    (tau : ℝ) (coord : ITVCoord)
    (r : WorldModelSigma.WMRewriteRuleSigma State Srt Query)
    (hSide : r.side) (W : State)
    (queryOfAtom : String → Pattern → Sigma Query)
    (a : String) (p : Pattern)
    (hEnc : queryOfAtom a p = r.conclusion)
    (hTau : tau ≤ coord (itvSem.eval ctx (r.derive W))) :
    sem R
      (thresholdAtomSemOfWMITVQSigma
        (State := State) (Srt := Srt) (Query := Query) (Ctx := Ctx)
        itvSem ctx W tau coord queryOfAtom)
      (.atom a) p := by
  change tau ≤ coord
    (wmITVAtomSemQSigma
      (State := State) (Srt := Srt) (Query := Query) (Ctx := Ctx)
      itvSem ctx W queryOfAtom a p)
  rw [wmRewriteRuleSigma_itv_atom_eq_derive
    (State := State) (Srt := Srt) (Query := Query) (Ctx := Ctx)
    itvSem ctx r hSide W queryOfAtom a p hEnc]
  exact hTau

/-- Lower-threshold consequence from a typed WM rewrite rule. -/
theorem wmRewriteRuleSigma_lower_threshold_atom
    (R : Pattern → Pattern → Prop)
    (itvSem : ITVSemantics Ctx) (ctx : Ctx)
    (tau : ℝ)
    (r : WorldModelSigma.WMRewriteRuleSigma State Srt Query)
    (hSide : r.side) (W : State)
    (queryOfAtom : String → Pattern → Sigma Query)
    (a : String) (p : Pattern)
    (hEnc : queryOfAtom a p = r.conclusion)
    (hTau : tau ≤ (itvSem.eval ctx (r.derive W)).lower) :
    sem R
      (lowerAtomSemOfWMITVQSigma
        (State := State) (Srt := Srt) (Query := Query) (Ctx := Ctx)
        itvSem ctx W tau queryOfAtom)
      (.atom a) p :=
  wmRewriteRuleSigma_itv_threshold_atom
    (State := State) (Srt := Srt) (Query := Query) (Ctx := Ctx)
    R itvSem ctx tau (fun itv => itv.lower) r hSide W queryOfAtom a p hEnc hTau

/-- Credibility-threshold consequence from a typed WM rewrite rule. -/
theorem wmRewriteRuleSigma_credibility_threshold_atom
    (R : Pattern → Pattern → Prop)
    (itvSem : ITVSemantics Ctx) (ctx : Ctx)
    (tau : ℝ)
    (r : WorldModelSigma.WMRewriteRuleSigma State Srt Query)
    (hSide : r.side) (W : State)
    (queryOfAtom : String → Pattern → Sigma Query)
    (a : String) (p : Pattern)
    (hEnc : queryOfAtom a p = r.conclusion)
    (hTau : tau ≤ (itvSem.eval ctx (r.derive W)).credibility) :
    sem R
      (credibilityAtomSemOfWMITVQSigma
        (State := State) (Srt := Srt) (Query := Query) (Ctx := Ctx)
        itvSem ctx W tau queryOfAtom)
      (.atom a) p :=
  wmRewriteRuleSigma_itv_threshold_atom
    (State := State) (Srt := Srt) (Query := Query) (Ctx := Ctx)
    R itvSem ctx tau (fun itv => itv.credibility) r hSide W queryOfAtom a p hEnc hTau

/-- Upper-threshold consequence from a typed WM rewrite rule. -/
theorem wmRewriteRuleSigma_upper_threshold_atom
    (R : Pattern → Pattern → Prop)
    (itvSem : ITVSemantics Ctx) (ctx : Ctx)
    (tau : ℝ)
    (r : WorldModelSigma.WMRewriteRuleSigma State Srt Query)
    (hSide : r.side) (W : State)
    (queryOfAtom : String → Pattern → Sigma Query)
    (a : String) (p : Pattern)
    (hEnc : queryOfAtom a p = r.conclusion)
    (hTau : tau ≤ (itvSem.eval ctx (r.derive W)).upper) :
    sem R
      (upperAtomSemOfWMITVQSigma
        (State := State) (Srt := Srt) (Query := Query) (Ctx := Ctx)
        itvSem ctx W tau queryOfAtom)
      (.atom a) p :=
  wmRewriteRuleSigma_itv_threshold_atom
    (State := State) (Srt := Srt) (Query := Query) (Ctx := Ctx)
    R itvSem ctx tau (fun itv => itv.upper) r hSide W queryOfAtom a p hEnc hTau

/-- Width-threshold consequence from a typed WM rewrite rule. -/
theorem wmRewriteRuleSigma_width_threshold_atom
    (R : Pattern → Pattern → Prop)
    (itvSem : ITVSemantics Ctx) (ctx : Ctx)
    (tau : ℝ)
    (r : WorldModelSigma.WMRewriteRuleSigma State Srt Query)
    (hSide : r.side) (W : State)
    (queryOfAtom : String → Pattern → Sigma Query)
    (a : String) (p : Pattern)
    (hEnc : queryOfAtom a p = r.conclusion)
    (hTau : tau ≤ (itvSem.eval ctx (r.derive W)).width) :
    sem R
      (widthAtomSemOfWMITVQSigma
        (State := State) (Srt := Srt) (Query := Query) (Ctx := Ctx)
        itvSem ctx W tau queryOfAtom)
      (.atom a) p :=
  wmRewriteRuleSigma_itv_threshold_atom
    (State := State) (Srt := Srt) (Query := Query) (Ctx := Ctx)
    R itvSem ctx tau (fun itv => itv.width) r hSide W queryOfAtom a p hEnc hTau

/-- Midpoint-strength-threshold consequence from a typed WM rewrite rule. -/
theorem wmRewriteRuleSigma_strength_threshold_atom
    (R : Pattern → Pattern → Prop)
    (itvSem : ITVSemantics Ctx) (ctx : Ctx)
    (tau : ℝ)
    (r : WorldModelSigma.WMRewriteRuleSigma State Srt Query)
    (hSide : r.side) (W : State)
    (queryOfAtom : String → Pattern → Sigma Query)
    (a : String) (p : Pattern)
    (hEnc : queryOfAtom a p = r.conclusion)
    (hTau : tau ≤ (itvSem.eval ctx (r.derive W)).strength) :
    sem R
      (strengthAtomSemOfWMITVQSigma
        (State := State) (Srt := Srt) (Query := Query) (Ctx := Ctx)
        itvSem ctx W tau queryOfAtom)
      (.atom a) p :=
  wmRewriteRuleSigma_itv_threshold_atom
    (State := State) (Srt := Srt) (Query := Query) (Ctx := Ctx)
    R itvSem ctx tau (fun itv => itv.strength) r hSide W queryOfAtom a p hEnc hTau

end CoreBridge

/-! ## Quantale/Language Coherence Bundles for ITV Atom Thresholds -/

section CoherenceBundle

variable {State Srt Ctx₁ Ctx₂ : Type*} {Query : Srt → Type*}
variable {Q Q' : Type*}
variable {L₁ L₂ : LanguageDef}
variable [EvidenceType State] [WorldModelSigma State Srt Query]
variable [Monoid Q] [CompleteLattice Q]
variable [Monoid Q'] [CompleteLattice Q']

/-- Pattern valuation obtained from a typed WM atom encoder and state. -/
noncomputable def wmPatternValuation
    (W : State) (queryOfAtom : String → Pattern → Sigma Query)
    (a : String) : Pattern → BinaryEvidence :=
  fun p =>
    WorldModelSigma.evidence
      (State := State) (Srt := Srt) (Query := Query) W (queryOfAtom a p)

/-- Quantale/language coherence specialized to typed WM atom evidence valuations. -/
theorem language_quantale_coherence_wm_atomEvidence
    (m : LanguageMorphism L₁ L₂ Eq)
    (f : QuantaleHom Q Q')
    (srcVal : Pattern → Q) (dstVal : Pattern → Q')
    (hVal : ∀ p, dstVal (m.mapTerm p) = f (srcVal p))
    {U : Type*} [Fintype U]
    (pick : U → Pattern) {p₀ : Pattern}
    (hReach : ∀ u, LangReducesStar L₁ p₀ (pick u))
    (H : Finset (U × U)) :
    (∀ u, LangReducesStar L₂ (m.mapTerm p₀) (m.mapTerm (pick u))) ∧
    f (weakness (sourceWeight srcVal pick) H) =
      weakness (targetWeight dstVal m.mapTerm pick) H :=
  language_quantale_coherence_bundle
    (m := m) (f := f) (srcVal := srcVal) (dstVal := dstVal)
    (hVal := hVal) (pick := pick) (hReach := hReach) (H := H)

/-- Bundle theorem connecting:
1) quantale/language coherence on atom valuations, and
2) ITV-threshold atom truth transport under pointwise ITV compatibility. -/
theorem language_quantale_coherence_wmITV_threshold_atom
    (R : Pattern → Pattern → Prop)
    (m : LanguageMorphism L₁ L₂ Eq)
    (f : QuantaleHom Q Q')
    (srcVal : Pattern → Q) (dstVal : Pattern → Q')
    (hVal : ∀ p, dstVal (m.mapTerm p) = f (srcVal p))
    (itvSem₁ : ITVSemantics Ctx₁) (ctx₁ : Ctx₁)
    (itvSem₂ : ITVSemantics Ctx₂) (ctx₂ : Ctx₂)
    (itvOfSrc : Q → BinaryEvidence) (itvOfDst : Q' → BinaryEvidence)
    (coord : ITVCoord) (tau : ℝ)
    (a0 : String)
    (hITV : ∀ p, itvSem₂.eval ctx₂ (itvOfDst (dstVal (m.mapTerm p))) =
      itvSem₁.eval ctx₁ (itvOfSrc (srcVal p)))
    {U : Type*} [Fintype U]
    (pick : U → Pattern) {p₀ : Pattern}
    (hReach : ∀ u, LangReducesStar L₁ p₀ (pick u))
    (H : Finset (U × U))
    (hTau : ∀ u, tau ≤ coord (itvSem₁.eval ctx₁ (itvOfSrc (srcVal (pick u))))) :
    (∀ u, LangReducesStar L₂ (m.mapTerm p₀) (m.mapTerm (pick u))) ∧
    f (weakness (sourceWeight srcVal pick) H) =
      weakness (targetWeight dstVal m.mapTerm pick) H ∧
    (∀ u, sem R
      (fun a p => a = a0 ∧
        tau ≤ coord (itvSem₂.eval ctx₂ (itvOfDst (dstVal p))))
      (.atom a0) (m.mapTerm (pick u))) := by
  rcases language_quantale_coherence_wm_atomEvidence
      (m := m) (f := f) (srcVal := srcVal) (dstVal := dstVal)
      (hVal := hVal) (pick := pick) (hReach := hReach) (H := H)
    with ⟨hForward, hWeak⟩
  refine ⟨hForward, hWeak, ?_⟩
  intro u
  change (a0 = a0 ∧
      tau ≤ coord (itvSem₂.eval ctx₂ (itvOfDst (dstVal (m.mapTerm (pick u))))))
  refine ⟨rfl, ?_⟩
  have hEq : itvSem₂.eval ctx₂ (itvOfDst (dstVal (m.mapTerm (pick u)))) =
      itvSem₁.eval ctx₁ (itvOfSrc (srcVal (pick u))) := hITV (pick u)
  simpa [hEq] using hTau u

/-- Typed WM/query-encoder specialization of
`language_quantale_coherence_wmITV_threshold_atom`, expressed directly with
`wmPatternValuation` and `thresholdAtomSemOfWMITVQSigma`. -/
theorem language_quantale_coherence_wmITV_threshold_atom_of_queryEncoders
    (R : Pattern → Pattern → Prop)
    (m : LanguageMorphism L₁ L₂ Eq)
    (f : QuantaleHom BinaryEvidence BinaryEvidence)
    (itvSem₁ : ITVSemantics Ctx₁) (ctx₁ : Ctx₁)
    (itvSem₂ : ITVSemantics Ctx₂) (ctx₂ : Ctx₂)
    (W₁ W₂ : State)
    (queryOfAtom₁ queryOfAtom₂ : String → Pattern → Sigma Query)
    (a0 : String)
    (coord : ITVCoord) (tau : ℝ)
    (hVal : ∀ p,
      wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₂ queryOfAtom₂ a0 (m.mapTerm p) =
      f (wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0 p))
    (hITV : ∀ p,
      itvSem₂.eval ctx₂
        (wmPatternValuation
          (State := State) (Srt := Srt) (Query := Query) W₂ queryOfAtom₂ a0 (m.mapTerm p)) =
      itvSem₁.eval ctx₁
        (wmPatternValuation
          (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0 p))
    {U : Type*} [Fintype U]
    (pick : U → Pattern) {p₀ : Pattern}
    (hReach : ∀ u, LangReducesStar L₁ p₀ (pick u))
    (H : Finset (U × U))
    (hTau : ∀ u,
      tau ≤ coord (itvSem₁.eval ctx₁
        (wmPatternValuation
          (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0 (pick u)))) :
    (∀ u, LangReducesStar L₂ (m.mapTerm p₀) (m.mapTerm (pick u))) ∧
    f (weakness
      (sourceWeight
        (wmPatternValuation
          (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0) pick) H) =
      weakness
        (targetWeight
          (wmPatternValuation
            (State := State) (Srt := Srt) (Query := Query) W₂ queryOfAtom₂ a0) m.mapTerm pick) H ∧
    (∀ u, sem R
      (thresholdAtomSemOfWMITVQSigma
        (State := State) (Srt := Srt) (Query := Query) (Ctx := Ctx₂)
        itvSem₂ ctx₂ W₂ tau coord queryOfAtom₂)
      (.atom a0) (m.mapTerm (pick u))) := by
  rcases language_quantale_coherence_wmITV_threshold_atom
      (R := R) (m := m) (f := f)
      (srcVal :=
        wmPatternValuation
          (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0)
      (dstVal :=
        wmPatternValuation
          (State := State) (Srt := Srt) (Query := Query) W₂ queryOfAtom₂ a0)
      (hVal := hVal)
      (itvSem₁ := itvSem₁) (ctx₁ := ctx₁)
      (itvSem₂ := itvSem₂) (ctx₂ := ctx₂)
      (itvOfSrc := id) (itvOfDst := id)
      (coord := coord) (tau := tau) (a0 := a0)
      (hITV := hITV)
      (pick := pick) (hReach := hReach) (H := H) (hTau := hTau)
    with ⟨hForward, hWeak, hThresh⟩
  refine ⟨hForward, hWeak, ?_⟩
  intro u
  have hAtom := hThresh u
  have hPair :
      a0 = a0 ∧
        tau ≤ coord
          (itvSem₂.eval ctx₂
            (wmPatternValuation
              (State := State) (Srt := Srt) (Query := Query) W₂ queryOfAtom₂ a0
                (m.mapTerm (pick u)))) := by
    simpa [Mettapedia.OSLF.Formula.sem, wmPatternValuation] using hAtom
  change tau ≤ coord
    (wmITVAtomSemQSigma
      (State := State) (Srt := Srt) (Query := Query) (Ctx := Ctx₂)
      itvSem₂ ctx₂ W₂ queryOfAtom₂ a0 (m.mapTerm (pick u)))
  simpa [wmITVAtomSemQSigma, wmPatternValuation] using hPair.2

/-- Lower-coordinate specialization of the typed WM/query-encoder coherence bundle. -/
theorem language_quantale_coherence_wmITV_lower_threshold_atom_of_queryEncoders
    (R : Pattern → Pattern → Prop)
    (m : LanguageMorphism L₁ L₂ Eq)
    (f : QuantaleHom BinaryEvidence BinaryEvidence)
    (itvSem₁ : ITVSemantics Ctx₁) (ctx₁ : Ctx₁)
    (itvSem₂ : ITVSemantics Ctx₂) (ctx₂ : Ctx₂)
    (W₁ W₂ : State)
    (queryOfAtom₁ queryOfAtom₂ : String → Pattern → Sigma Query)
    (a0 : String) (tau : ℝ)
    (hVal : ∀ p,
      wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₂ queryOfAtom₂ a0 (m.mapTerm p) =
      f (wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0 p))
    (hITV : ∀ p,
      itvSem₂.eval ctx₂
        (wmPatternValuation
          (State := State) (Srt := Srt) (Query := Query) W₂ queryOfAtom₂ a0 (m.mapTerm p)) =
      itvSem₁.eval ctx₁
        (wmPatternValuation
          (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0 p))
    {U : Type*} [Fintype U]
    (pick : U → Pattern) {p₀ : Pattern}
    (hReach : ∀ u, LangReducesStar L₁ p₀ (pick u))
    (H : Finset (U × U))
    (hTau : ∀ u,
      tau ≤ (itvSem₁.eval ctx₁
        (wmPatternValuation
          (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0 (pick u))).lower) :
    (∀ u, LangReducesStar L₂ (m.mapTerm p₀) (m.mapTerm (pick u))) ∧
    f (weakness
      (sourceWeight
        (wmPatternValuation
          (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0) pick) H) =
      weakness
        (targetWeight
          (wmPatternValuation
            (State := State) (Srt := Srt) (Query := Query) W₂ queryOfAtom₂ a0) m.mapTerm pick) H ∧
    (∀ u, sem R
      (lowerAtomSemOfWMITVQSigma
        (State := State) (Srt := Srt) (Query := Query) (Ctx := Ctx₂)
        itvSem₂ ctx₂ W₂ tau queryOfAtom₂)
      (.atom a0) (m.mapTerm (pick u))) := by
  simpa [lowerAtomSemOfWMITVQSigma, thresholdAtomSemOfWMITVQSigma] using
    (language_quantale_coherence_wmITV_threshold_atom_of_queryEncoders
      (R := R) (m := m) (f := f)
      (itvSem₁ := itvSem₁) (ctx₁ := ctx₁)
      (itvSem₂ := itvSem₂) (ctx₂ := ctx₂)
      (W₁ := W₁) (W₂ := W₂)
      (queryOfAtom₁ := queryOfAtom₁) (queryOfAtom₂ := queryOfAtom₂)
      (a0 := a0) (coord := fun itv => itv.lower) (tau := tau)
      (hVal := hVal) (hITV := hITV)
      (pick := pick) (hReach := hReach) (H := H) (hTau := hTau))

/-- Upper-coordinate specialization of the typed WM/query-encoder coherence bundle. -/
theorem language_quantale_coherence_wmITV_upper_threshold_atom_of_queryEncoders
    (R : Pattern → Pattern → Prop)
    (m : LanguageMorphism L₁ L₂ Eq)
    (f : QuantaleHom BinaryEvidence BinaryEvidence)
    (itvSem₁ : ITVSemantics Ctx₁) (ctx₁ : Ctx₁)
    (itvSem₂ : ITVSemantics Ctx₂) (ctx₂ : Ctx₂)
    (W₁ W₂ : State)
    (queryOfAtom₁ queryOfAtom₂ : String → Pattern → Sigma Query)
    (a0 : String) (tau : ℝ)
    (hVal : ∀ p,
      wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₂ queryOfAtom₂ a0 (m.mapTerm p) =
      f (wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0 p))
    (hITV : ∀ p,
      itvSem₂.eval ctx₂
        (wmPatternValuation
          (State := State) (Srt := Srt) (Query := Query) W₂ queryOfAtom₂ a0 (m.mapTerm p)) =
      itvSem₁.eval ctx₁
        (wmPatternValuation
          (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0 p))
    {U : Type*} [Fintype U]
    (pick : U → Pattern) {p₀ : Pattern}
    (hReach : ∀ u, LangReducesStar L₁ p₀ (pick u))
    (H : Finset (U × U))
    (hTau : ∀ u,
      tau ≤ (itvSem₁.eval ctx₁
        (wmPatternValuation
          (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0 (pick u))).upper) :
    (∀ u, LangReducesStar L₂ (m.mapTerm p₀) (m.mapTerm (pick u))) ∧
    f (weakness
      (sourceWeight
        (wmPatternValuation
          (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0) pick) H) =
      weakness
        (targetWeight
          (wmPatternValuation
            (State := State) (Srt := Srt) (Query := Query) W₂ queryOfAtom₂ a0) m.mapTerm pick) H ∧
    (∀ u, sem R
      (upperAtomSemOfWMITVQSigma
        (State := State) (Srt := Srt) (Query := Query) (Ctx := Ctx₂)
        itvSem₂ ctx₂ W₂ tau queryOfAtom₂)
      (.atom a0) (m.mapTerm (pick u))) := by
  simpa [upperAtomSemOfWMITVQSigma, thresholdAtomSemOfWMITVQSigma] using
    (language_quantale_coherence_wmITV_threshold_atom_of_queryEncoders
      (R := R) (m := m) (f := f)
      (itvSem₁ := itvSem₁) (ctx₁ := ctx₁)
      (itvSem₂ := itvSem₂) (ctx₂ := ctx₂)
      (W₁ := W₁) (W₂ := W₂)
      (queryOfAtom₁ := queryOfAtom₁) (queryOfAtom₂ := queryOfAtom₂)
      (a0 := a0) (coord := fun itv => itv.upper) (tau := tau)
      (hVal := hVal) (hITV := hITV)
      (pick := pick) (hReach := hReach) (H := H) (hTau := hTau))

/-- Credibility-coordinate specialization of the typed WM/query-encoder coherence bundle. -/
theorem language_quantale_coherence_wmITV_credibility_threshold_atom_of_queryEncoders
    (R : Pattern → Pattern → Prop)
    (m : LanguageMorphism L₁ L₂ Eq)
    (f : QuantaleHom BinaryEvidence BinaryEvidence)
    (itvSem₁ : ITVSemantics Ctx₁) (ctx₁ : Ctx₁)
    (itvSem₂ : ITVSemantics Ctx₂) (ctx₂ : Ctx₂)
    (W₁ W₂ : State)
    (queryOfAtom₁ queryOfAtom₂ : String → Pattern → Sigma Query)
    (a0 : String) (tau : ℝ)
    (hVal : ∀ p,
      wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₂ queryOfAtom₂ a0 (m.mapTerm p) =
      f (wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0 p))
    (hITV : ∀ p,
      itvSem₂.eval ctx₂
        (wmPatternValuation
          (State := State) (Srt := Srt) (Query := Query) W₂ queryOfAtom₂ a0 (m.mapTerm p)) =
      itvSem₁.eval ctx₁
        (wmPatternValuation
          (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0 p))
    {U : Type*} [Fintype U]
    (pick : U → Pattern) {p₀ : Pattern}
    (hReach : ∀ u, LangReducesStar L₁ p₀ (pick u))
    (H : Finset (U × U))
    (hTau : ∀ u,
      tau ≤ (itvSem₁.eval ctx₁
        (wmPatternValuation
          (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0 (pick u))).credibility) :
    (∀ u, LangReducesStar L₂ (m.mapTerm p₀) (m.mapTerm (pick u))) ∧
    f (weakness
      (sourceWeight
        (wmPatternValuation
          (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0) pick) H) =
      weakness
        (targetWeight
          (wmPatternValuation
            (State := State) (Srt := Srt) (Query := Query) W₂ queryOfAtom₂ a0) m.mapTerm pick) H ∧
    (∀ u, sem R
      (credibilityAtomSemOfWMITVQSigma
        (State := State) (Srt := Srt) (Query := Query) (Ctx := Ctx₂)
        itvSem₂ ctx₂ W₂ tau queryOfAtom₂)
      (.atom a0) (m.mapTerm (pick u))) := by
  simpa [credibilityAtomSemOfWMITVQSigma, thresholdAtomSemOfWMITVQSigma] using
    (language_quantale_coherence_wmITV_threshold_atom_of_queryEncoders
      (R := R) (m := m) (f := f)
      (itvSem₁ := itvSem₁) (ctx₁ := ctx₁)
      (itvSem₂ := itvSem₂) (ctx₂ := ctx₂)
      (W₁ := W₁) (W₂ := W₂)
      (queryOfAtom₁ := queryOfAtom₁) (queryOfAtom₂ := queryOfAtom₂)
      (a0 := a0) (coord := fun itv => itv.credibility) (tau := tau)
      (hVal := hVal) (hITV := hITV)
      (pick := pick) (hReach := hReach) (H := H) (hTau := hTau))

/-- Width-coordinate specialization of the typed WM/query-encoder coherence bundle. -/
theorem language_quantale_coherence_wmITV_width_threshold_atom_of_queryEncoders
    (R : Pattern → Pattern → Prop)
    (m : LanguageMorphism L₁ L₂ Eq)
    (f : QuantaleHom BinaryEvidence BinaryEvidence)
    (itvSem₁ : ITVSemantics Ctx₁) (ctx₁ : Ctx₁)
    (itvSem₂ : ITVSemantics Ctx₂) (ctx₂ : Ctx₂)
    (W₁ W₂ : State)
    (queryOfAtom₁ queryOfAtom₂ : String → Pattern → Sigma Query)
    (a0 : String) (tau : ℝ)
    (hVal : ∀ p,
      wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₂ queryOfAtom₂ a0 (m.mapTerm p) =
      f (wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0 p))
    (hITV : ∀ p,
      itvSem₂.eval ctx₂
        (wmPatternValuation
          (State := State) (Srt := Srt) (Query := Query) W₂ queryOfAtom₂ a0 (m.mapTerm p)) =
      itvSem₁.eval ctx₁
        (wmPatternValuation
          (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0 p))
    {U : Type*} [Fintype U]
    (pick : U → Pattern) {p₀ : Pattern}
    (hReach : ∀ u, LangReducesStar L₁ p₀ (pick u))
    (H : Finset (U × U))
    (hTau : ∀ u,
      tau ≤ (itvSem₁.eval ctx₁
        (wmPatternValuation
          (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0 (pick u))).width) :
    (∀ u, LangReducesStar L₂ (m.mapTerm p₀) (m.mapTerm (pick u))) ∧
    f (weakness
      (sourceWeight
        (wmPatternValuation
          (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0) pick) H) =
      weakness
        (targetWeight
          (wmPatternValuation
            (State := State) (Srt := Srt) (Query := Query) W₂ queryOfAtom₂ a0) m.mapTerm pick) H ∧
    (∀ u, sem R
      (widthAtomSemOfWMITVQSigma
        (State := State) (Srt := Srt) (Query := Query) (Ctx := Ctx₂)
        itvSem₂ ctx₂ W₂ tau queryOfAtom₂)
      (.atom a0) (m.mapTerm (pick u))) := by
  simpa [widthAtomSemOfWMITVQSigma, thresholdAtomSemOfWMITVQSigma] using
    (language_quantale_coherence_wmITV_threshold_atom_of_queryEncoders
      (R := R) (m := m) (f := f)
      (itvSem₁ := itvSem₁) (ctx₁ := ctx₁)
      (itvSem₂ := itvSem₂) (ctx₂ := ctx₂)
      (W₁ := W₁) (W₂ := W₂)
      (queryOfAtom₁ := queryOfAtom₁) (queryOfAtom₂ := queryOfAtom₂)
      (a0 := a0) (coord := fun itv => itv.width) (tau := tau)
      (hVal := hVal) (hITV := hITV)
      (pick := pick) (hReach := hReach) (H := H) (hTau := hTau))

/-- Strength-coordinate specialization of the typed WM/query-encoder coherence bundle. -/
theorem language_quantale_coherence_wmITV_strength_threshold_atom_of_queryEncoders
    (R : Pattern → Pattern → Prop)
    (m : LanguageMorphism L₁ L₂ Eq)
    (f : QuantaleHom BinaryEvidence BinaryEvidence)
    (itvSem₁ : ITVSemantics Ctx₁) (ctx₁ : Ctx₁)
    (itvSem₂ : ITVSemantics Ctx₂) (ctx₂ : Ctx₂)
    (W₁ W₂ : State)
    (queryOfAtom₁ queryOfAtom₂ : String → Pattern → Sigma Query)
    (a0 : String) (tau : ℝ)
    (hVal : ∀ p,
      wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₂ queryOfAtom₂ a0 (m.mapTerm p) =
      f (wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0 p))
    (hITV : ∀ p,
      itvSem₂.eval ctx₂
        (wmPatternValuation
          (State := State) (Srt := Srt) (Query := Query) W₂ queryOfAtom₂ a0 (m.mapTerm p)) =
      itvSem₁.eval ctx₁
        (wmPatternValuation
          (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0 p))
    {U : Type*} [Fintype U]
    (pick : U → Pattern) {p₀ : Pattern}
    (hReach : ∀ u, LangReducesStar L₁ p₀ (pick u))
    (H : Finset (U × U))
    (hTau : ∀ u,
      tau ≤ (itvSem₁.eval ctx₁
        (wmPatternValuation
          (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0 (pick u))).strength) :
    (∀ u, LangReducesStar L₂ (m.mapTerm p₀) (m.mapTerm (pick u))) ∧
    f (weakness
      (sourceWeight
        (wmPatternValuation
          (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0) pick) H) =
      weakness
        (targetWeight
          (wmPatternValuation
            (State := State) (Srt := Srt) (Query := Query) W₂ queryOfAtom₂ a0) m.mapTerm pick) H ∧
    (∀ u, sem R
      (strengthAtomSemOfWMITVQSigma
        (State := State) (Srt := Srt) (Query := Query) (Ctx := Ctx₂)
        itvSem₂ ctx₂ W₂ tau queryOfAtom₂)
      (.atom a0) (m.mapTerm (pick u))) := by
  simpa [strengthAtomSemOfWMITVQSigma, thresholdAtomSemOfWMITVQSigma] using
    (language_quantale_coherence_wmITV_threshold_atom_of_queryEncoders
      (R := R) (m := m) (f := f)
      (itvSem₁ := itvSem₁) (ctx₁ := ctx₁)
      (itvSem₂ := itvSem₂) (ctx₂ := ctx₂)
      (W₁ := W₁) (W₂ := W₂)
      (queryOfAtom₁ := queryOfAtom₁) (queryOfAtom₂ := queryOfAtom₂)
      (a0 := a0) (coord := fun itv => itv.strength) (tau := tau)
      (hVal := hVal) (hITV := hITV)
      (pick := pick) (hReach := hReach) (H := H) (hTau := hTau))

end CoherenceBundle

/-! ## Selector-Specialized Coherence (Internalized ITV-Compatibility) -/

section SelectorCoherence

variable {State Srt : Type*} {Query : Srt → Type*}
variable {L₁ L₂ : LanguageDef}
variable [EvidenceType State] [WorldModelSigma State Srt Query]

/-- `id`-quantale specialization of typed WM/query-encoder coherence.
This internalizes the ITV-compatibility side condition (`hITV`) by reducing it
to pointwise valuation equality under the same semantics/context. -/
theorem language_quantale_coherence_wmITV_threshold_atom_of_queryEncoders_id
    (R : Pattern → Pattern → Prop)
    (m : LanguageMorphism L₁ L₂ Eq)
    (itvSem : ITVSemantics Ctx)
    (ctx : Ctx)
    (W₁ W₂ : State)
    (queryOfAtom₁ queryOfAtom₂ : String → Pattern → Sigma Query)
    (a0 : String)
    (coord : ITVCoord) (tau : ℝ)
    (hVal : ∀ p,
      wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₂ queryOfAtom₂ a0 (m.mapTerm p) =
      wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0 p)
    {U : Type*} [Fintype U]
    (pick : U → Pattern) {p₀ : Pattern}
    (hReach : ∀ u, LangReducesStar L₁ p₀ (pick u))
    (H : Finset (U × U))
    (hTau : ∀ u,
      tau ≤ coord (itvSem.eval ctx
        (wmPatternValuation
          (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0 (pick u)))) :
    (∀ u, LangReducesStar L₂ (m.mapTerm p₀) (m.mapTerm (pick u))) ∧
    weakness
      (sourceWeight
        (wmPatternValuation
          (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0) pick) H =
      weakness
        (targetWeight
          (wmPatternValuation
            (State := State) (Srt := Srt) (Query := Query) W₂ queryOfAtom₂ a0) m.mapTerm pick) H ∧
    (∀ u, sem R
      (thresholdAtomSemOfWMITVQSigma
        (State := State) (Srt := Srt) (Query := Query) (Ctx := Ctx)
        itvSem ctx W₂ tau coord queryOfAtom₂)
      (.atom a0) (m.mapTerm (pick u))) := by
  simpa using
    (language_quantale_coherence_wmITV_threshold_atom_of_queryEncoders
      (State := State) (Srt := Srt) (Query := Query)
      (R := R) (m := m) (f := QuantaleHom.id (Q := BinaryEvidence))
      (itvSem₁ := itvSem) (ctx₁ := ctx)
      (itvSem₂ := itvSem) (ctx₂ := ctx)
      (W₁ := W₁) (W₂ := W₂)
      (queryOfAtom₁ := queryOfAtom₁) (queryOfAtom₂ := queryOfAtom₂)
      (a0 := a0) (coord := coord) (tau := tau)
      (hVal := by simpa using hVal)
      (hITV := by
        intro p
        simp [hVal p])
      (pick := pick) (hReach := hReach) (H := H) (hTau := hTau))

/-- Bayes-exact selector specialization with internalized ITV-compatibility. -/
theorem language_quantale_coherence_wmITV_threshold_atom_of_queryEncoders_bayesNormal_id
    (R : Pattern → Pattern → Prop)
    (m : LanguageMorphism L₁ L₂ Eq)
    (ctx : BinaryContext)
    (W₁ W₂ : State)
    (queryOfAtom₁ queryOfAtom₂ : String → Pattern → Sigma Query)
    (a0 : String)
    (coord : ITVCoord) (tau : ℝ)
    (hVal : ∀ p,
      wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₂ queryOfAtom₂ a0 (m.mapTerm p) =
      wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0 p)
    {U : Type*} [Fintype U]
    (pick : U → Pattern) {p₀ : Pattern}
    (hReach : ∀ u, LangReducesStar L₁ p₀ (pick u))
    (H : Finset (U × U))
    (hTau : ∀ u,
      tau ≤ coord (ITVSemantics.bayesCredible95.eval ctx
        (wmPatternValuation
          (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0 (pick u)))) :
    (∀ u, LangReducesStar L₂ (m.mapTerm p₀) (m.mapTerm (pick u))) ∧
    weakness
      (sourceWeight
        (wmPatternValuation
          (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0) pick) H =
      weakness
        (targetWeight
          (wmPatternValuation
            (State := State) (Srt := Srt) (Query := Query) W₂ queryOfAtom₂ a0) m.mapTerm pick) H ∧
    (∀ u, sem R
      (thresholdAtomSemOfWMITVQSigma
        (State := State) (Srt := Srt) (Query := Query) (Ctx := BinaryContext)
        ITVSemantics.bayesCredible95 ctx W₂ tau coord queryOfAtom₂)
      (.atom a0) (m.mapTerm (pick u))) := by
  exact language_quantale_coherence_wmITV_threshold_atom_of_queryEncoders_id
    (State := State) (Srt := Srt) (Query := Query)
    (R := R) (m := m)
    (itvSem := ITVSemantics.bayesCredible95) (ctx := ctx)
    (W₁ := W₁) (W₂ := W₂)
    (queryOfAtom₁ := queryOfAtom₁) (queryOfAtom₂ := queryOfAtom₂)
    (a0 := a0) (coord := coord) (tau := tau)
    (hVal := hVal)
    (pick := pick) (hReach := hReach) (H := H) (hTau := hTau)

/-- Bayes-exact selector specialization with internalized ITV-compatibility. -/
theorem language_quantale_coherence_wmITV_threshold_atom_of_queryEncoders_bayesExact_id
    (R : Pattern → Pattern → Prop)
    (m : LanguageMorphism L₁ L₂ Eq)
    (ctx : BinaryContext)
    (W₁ W₂ : State)
    (queryOfAtom₁ queryOfAtom₂ : String → Pattern → Sigma Query)
    (a0 : String)
    (coord : ITVCoord) (tau : ℝ)
    (hVal : ∀ p,
      wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₂ queryOfAtom₂ a0 (m.mapTerm p) =
      wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0 p)
    {U : Type*} [Fintype U]
    (pick : U → Pattern) {p₀ : Pattern}
    (hReach : ∀ u, LangReducesStar L₁ p₀ (pick u))
    (H : Finset (U × U))
    (hTau : ∀ u,
      tau ≤ coord (ITVSemantics.bayesCredibleExact95.eval ctx
        (wmPatternValuation
          (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0 (pick u)))) :
    (∀ u, LangReducesStar L₂ (m.mapTerm p₀) (m.mapTerm (pick u))) ∧
    weakness
      (sourceWeight
        (wmPatternValuation
          (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0) pick) H =
      weakness
        (targetWeight
          (wmPatternValuation
            (State := State) (Srt := Srt) (Query := Query) W₂ queryOfAtom₂ a0) m.mapTerm pick) H ∧
    (∀ u, sem R
      (thresholdAtomSemOfWMITVQSigma
        (State := State) (Srt := Srt) (Query := Query) (Ctx := BinaryContext)
        ITVSemantics.bayesCredibleExact95 ctx W₂ tau coord queryOfAtom₂)
      (.atom a0) (m.mapTerm (pick u))) := by
  exact language_quantale_coherence_wmITV_threshold_atom_of_queryEncoders_id
    (State := State) (Srt := Srt) (Query := Query)
    (R := R) (m := m)
    (itvSem := ITVSemantics.bayesCredibleExact95) (ctx := ctx)
    (W₁ := W₁) (W₂ := W₂)
    (queryOfAtom₁ := queryOfAtom₁) (queryOfAtom₂ := queryOfAtom₂)
    (a0 := a0) (coord := coord) (tau := tau)
    (hVal := hVal)
    (pick := pick) (hReach := hReach) (H := H) (hTau := hTau)

/-- Walley-IDM selector specialization with internalized ITV-compatibility. -/
theorem language_quantale_coherence_wmITV_threshold_atom_of_queryEncoders_walley_id
    (R : Pattern → Pattern → Prop)
    (m : LanguageMorphism L₁ L₂ Eq)
    (ctx : IDMPredictiveContext)
    (W₁ W₂ : State)
    (queryOfAtom₁ queryOfAtom₂ : String → Pattern → Sigma Query)
    (a0 : String)
    (coord : ITVCoord) (tau : ℝ)
    (hVal : ∀ p,
      wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₂ queryOfAtom₂ a0 (m.mapTerm p) =
      wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0 p)
    {U : Type*} [Fintype U]
    (pick : U → Pattern) {p₀ : Pattern}
    (hReach : ∀ u, LangReducesStar L₁ p₀ (pick u))
    (H : Finset (U × U))
    (hTau : ∀ u,
      tau ≤ coord (ITVSemantics.walleyIDMPredictive.eval ctx
        (wmPatternValuation
          (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0 (pick u)))) :
    (∀ u, LangReducesStar L₂ (m.mapTerm p₀) (m.mapTerm (pick u))) ∧
    weakness
      (sourceWeight
        (wmPatternValuation
          (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0) pick) H =
      weakness
        (targetWeight
          (wmPatternValuation
            (State := State) (Srt := Srt) (Query := Query) W₂ queryOfAtom₂ a0) m.mapTerm pick) H ∧
    (∀ u, sem R
      (thresholdAtomSemOfWMITVQSigma
        (State := State) (Srt := Srt) (Query := Query) (Ctx := IDMPredictiveContext)
        ITVSemantics.walleyIDMPredictive ctx W₂ tau coord queryOfAtom₂)
      (.atom a0) (m.mapTerm (pick u))) := by
  exact language_quantale_coherence_wmITV_threshold_atom_of_queryEncoders_id
    (State := State) (Srt := Srt) (Query := Query)
    (R := R) (m := m)
    (itvSem := ITVSemantics.walleyIDMPredictive) (ctx := ctx)
    (W₁ := W₁) (W₂ := W₂)
    (queryOfAtom₁ := queryOfAtom₁) (queryOfAtom₂ := queryOfAtom₂)
    (a0 := a0) (coord := coord) (tau := tau)
    (hVal := hVal)
    (pick := pick) (hReach := hReach) (H := H) (hTau := hTau)

/-- Bayes-exact lower-coordinate selector coherence (internalized ITV-compatibility). -/
theorem language_quantale_coherence_wmITV_lower_threshold_atom_of_queryEncoders_bayesNormal_id
    (R : Pattern → Pattern → Prop)
    (m : LanguageMorphism L₁ L₂ Eq)
    (ctx : BinaryContext)
    (W₁ W₂ : State)
    (queryOfAtom₁ queryOfAtom₂ : String → Pattern → Sigma Query)
    (a0 : String) (tau : ℝ)
    (hVal : ∀ p,
      wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₂ queryOfAtom₂ a0 (m.mapTerm p) =
      wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0 p)
    {U : Type*} [Fintype U]
    (pick : U → Pattern) {p₀ : Pattern}
    (hReach : ∀ u, LangReducesStar L₁ p₀ (pick u))
    (H : Finset (U × U))
    (hTau : ∀ u,
      tau ≤ (ITVSemantics.bayesCredible95.eval ctx
        (wmPatternValuation
          (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0 (pick u))).lower) :
    (∀ u, LangReducesStar L₂ (m.mapTerm p₀) (m.mapTerm (pick u))) ∧
    weakness
      (sourceWeight
        (wmPatternValuation
          (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0) pick) H =
      weakness
        (targetWeight
          (wmPatternValuation
            (State := State) (Srt := Srt) (Query := Query) W₂ queryOfAtom₂ a0) m.mapTerm pick) H ∧
    (∀ u, sem R
      (lowerAtomSemOfWMITVQSigma
        (State := State) (Srt := Srt) (Query := Query) (Ctx := BinaryContext)
        ITVSemantics.bayesCredible95 ctx W₂ tau queryOfAtom₂)
      (.atom a0) (m.mapTerm (pick u))) := by
  simpa [lowerAtomSemOfWMITVQSigma, thresholdAtomSemOfWMITVQSigma] using
    (language_quantale_coherence_wmITV_threshold_atom_of_queryEncoders_bayesNormal_id
      (State := State) (Srt := Srt) (Query := Query)
      (R := R) (m := m) (ctx := ctx)
      (W₁ := W₁) (W₂ := W₂)
      (queryOfAtom₁ := queryOfAtom₁) (queryOfAtom₂ := queryOfAtom₂)
      (a0 := a0) (coord := fun itv => itv.lower) (tau := tau)
      (hVal := hVal)
      (pick := pick) (hReach := hReach) (H := H) (hTau := hTau))

/-- Bayes-exact lower-coordinate selector coherence (internalized ITV-compatibility). -/
theorem language_quantale_coherence_wmITV_lower_threshold_atom_of_queryEncoders_bayesExact_id
    (R : Pattern → Pattern → Prop)
    (m : LanguageMorphism L₁ L₂ Eq)
    (ctx : BinaryContext)
    (W₁ W₂ : State)
    (queryOfAtom₁ queryOfAtom₂ : String → Pattern → Sigma Query)
    (a0 : String) (tau : ℝ)
    (hVal : ∀ p,
      wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₂ queryOfAtom₂ a0 (m.mapTerm p) =
      wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0 p)
    {U : Type*} [Fintype U]
    (pick : U → Pattern) {p₀ : Pattern}
    (hReach : ∀ u, LangReducesStar L₁ p₀ (pick u))
    (H : Finset (U × U))
    (hTau : ∀ u,
      tau ≤ (ITVSemantics.bayesCredibleExact95.eval ctx
        (wmPatternValuation
          (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0 (pick u))).lower) :
    (∀ u, LangReducesStar L₂ (m.mapTerm p₀) (m.mapTerm (pick u))) ∧
    weakness
      (sourceWeight
        (wmPatternValuation
          (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0) pick) H =
      weakness
        (targetWeight
          (wmPatternValuation
            (State := State) (Srt := Srt) (Query := Query) W₂ queryOfAtom₂ a0) m.mapTerm pick) H ∧
    (∀ u, sem R
      (lowerAtomSemOfWMITVQSigma
        (State := State) (Srt := Srt) (Query := Query) (Ctx := BinaryContext)
        ITVSemantics.bayesCredibleExact95 ctx W₂ tau queryOfAtom₂)
      (.atom a0) (m.mapTerm (pick u))) := by
  simpa [lowerAtomSemOfWMITVQSigma, thresholdAtomSemOfWMITVQSigma] using
    (language_quantale_coherence_wmITV_threshold_atom_of_queryEncoders_bayesExact_id
      (State := State) (Srt := Srt) (Query := Query)
      (R := R) (m := m) (ctx := ctx)
      (W₁ := W₁) (W₂ := W₂)
      (queryOfAtom₁ := queryOfAtom₁) (queryOfAtom₂ := queryOfAtom₂)
      (a0 := a0) (coord := fun itv => itv.lower) (tau := tau)
      (hVal := hVal)
      (pick := pick) (hReach := hReach) (H := H) (hTau := hTau))

/-- Walley lower-coordinate selector coherence (internalized ITV-compatibility). -/
theorem language_quantale_coherence_wmITV_lower_threshold_atom_of_queryEncoders_walley_id
    (R : Pattern → Pattern → Prop)
    (m : LanguageMorphism L₁ L₂ Eq)
    (ctx : IDMPredictiveContext)
    (W₁ W₂ : State)
    (queryOfAtom₁ queryOfAtom₂ : String → Pattern → Sigma Query)
    (a0 : String) (tau : ℝ)
    (hVal : ∀ p,
      wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₂ queryOfAtom₂ a0 (m.mapTerm p) =
      wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0 p)
    {U : Type*} [Fintype U]
    (pick : U → Pattern) {p₀ : Pattern}
    (hReach : ∀ u, LangReducesStar L₁ p₀ (pick u))
    (H : Finset (U × U))
    (hTau : ∀ u,
      tau ≤ (ITVSemantics.walleyIDMPredictive.eval ctx
        (wmPatternValuation
          (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0 (pick u))).lower) :
    (∀ u, LangReducesStar L₂ (m.mapTerm p₀) (m.mapTerm (pick u))) ∧
    weakness
      (sourceWeight
        (wmPatternValuation
          (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0) pick) H =
      weakness
        (targetWeight
          (wmPatternValuation
            (State := State) (Srt := Srt) (Query := Query) W₂ queryOfAtom₂ a0) m.mapTerm pick) H ∧
    (∀ u, sem R
      (lowerAtomSemOfWMITVQSigma
        (State := State) (Srt := Srt) (Query := Query) (Ctx := IDMPredictiveContext)
        ITVSemantics.walleyIDMPredictive ctx W₂ tau queryOfAtom₂)
      (.atom a0) (m.mapTerm (pick u))) := by
  simpa [lowerAtomSemOfWMITVQSigma, thresholdAtomSemOfWMITVQSigma] using
    (language_quantale_coherence_wmITV_threshold_atom_of_queryEncoders_walley_id
      (State := State) (Srt := Srt) (Query := Query)
      (R := R) (m := m) (ctx := ctx)
      (W₁ := W₁) (W₂ := W₂)
      (queryOfAtom₁ := queryOfAtom₁) (queryOfAtom₂ := queryOfAtom₂)
      (a0 := a0) (coord := fun itv => itv.lower) (tau := tau)
      (hVal := hVal)
      (pick := pick) (hReach := hReach) (H := H) (hTau := hTau))

/-- Bayes-exact upper-coordinate selector coherence (internalized ITV-compatibility). -/
theorem language_quantale_coherence_wmITV_upper_threshold_atom_of_queryEncoders_bayesNormal_id
    (R : Pattern → Pattern → Prop)
    (m : LanguageMorphism L₁ L₂ Eq)
    (ctx : BinaryContext)
    (W₁ W₂ : State)
    (queryOfAtom₁ queryOfAtom₂ : String → Pattern → Sigma Query)
    (a0 : String) (tau : ℝ)
    (hVal : ∀ p,
      wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₂ queryOfAtom₂ a0 (m.mapTerm p) =
      wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0 p)
    {U : Type*} [Fintype U]
    (pick : U → Pattern) {p₀ : Pattern}
    (hReach : ∀ u, LangReducesStar L₁ p₀ (pick u))
    (H : Finset (U × U))
    (hTau : ∀ u,
      tau ≤ (ITVSemantics.bayesCredible95.eval ctx
        (wmPatternValuation
          (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0 (pick u))).upper) :
    (∀ u, LangReducesStar L₂ (m.mapTerm p₀) (m.mapTerm (pick u))) ∧
    weakness
      (sourceWeight
        (wmPatternValuation
          (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0) pick) H =
      weakness
        (targetWeight
          (wmPatternValuation
            (State := State) (Srt := Srt) (Query := Query) W₂ queryOfAtom₂ a0) m.mapTerm pick) H ∧
    (∀ u, sem R
      (upperAtomSemOfWMITVQSigma
        (State := State) (Srt := Srt) (Query := Query) (Ctx := BinaryContext)
        ITVSemantics.bayesCredible95 ctx W₂ tau queryOfAtom₂)
      (.atom a0) (m.mapTerm (pick u))) := by
  simpa [upperAtomSemOfWMITVQSigma, thresholdAtomSemOfWMITVQSigma] using
    (language_quantale_coherence_wmITV_threshold_atom_of_queryEncoders_bayesNormal_id
      (State := State) (Srt := Srt) (Query := Query)
      (R := R) (m := m) (ctx := ctx)
      (W₁ := W₁) (W₂ := W₂)
      (queryOfAtom₁ := queryOfAtom₁) (queryOfAtom₂ := queryOfAtom₂)
      (a0 := a0) (coord := fun itv => itv.upper) (tau := tau)
      (hVal := hVal)
      (pick := pick) (hReach := hReach) (H := H) (hTau := hTau))

/-- Bayes-exact upper-coordinate selector coherence (internalized ITV-compatibility). -/
theorem language_quantale_coherence_wmITV_upper_threshold_atom_of_queryEncoders_bayesExact_id
    (R : Pattern → Pattern → Prop)
    (m : LanguageMorphism L₁ L₂ Eq)
    (ctx : BinaryContext)
    (W₁ W₂ : State)
    (queryOfAtom₁ queryOfAtom₂ : String → Pattern → Sigma Query)
    (a0 : String) (tau : ℝ)
    (hVal : ∀ p,
      wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₂ queryOfAtom₂ a0 (m.mapTerm p) =
      wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0 p)
    {U : Type*} [Fintype U]
    (pick : U → Pattern) {p₀ : Pattern}
    (hReach : ∀ u, LangReducesStar L₁ p₀ (pick u))
    (H : Finset (U × U))
    (hTau : ∀ u,
      tau ≤ (ITVSemantics.bayesCredibleExact95.eval ctx
        (wmPatternValuation
          (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0 (pick u))).upper) :
    (∀ u, LangReducesStar L₂ (m.mapTerm p₀) (m.mapTerm (pick u))) ∧
    weakness
      (sourceWeight
        (wmPatternValuation
          (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0) pick) H =
      weakness
        (targetWeight
          (wmPatternValuation
            (State := State) (Srt := Srt) (Query := Query) W₂ queryOfAtom₂ a0) m.mapTerm pick) H ∧
    (∀ u, sem R
      (upperAtomSemOfWMITVQSigma
        (State := State) (Srt := Srt) (Query := Query) (Ctx := BinaryContext)
        ITVSemantics.bayesCredibleExact95 ctx W₂ tau queryOfAtom₂)
      (.atom a0) (m.mapTerm (pick u))) := by
  simpa [upperAtomSemOfWMITVQSigma, thresholdAtomSemOfWMITVQSigma] using
    (language_quantale_coherence_wmITV_threshold_atom_of_queryEncoders_bayesExact_id
      (State := State) (Srt := Srt) (Query := Query)
      (R := R) (m := m) (ctx := ctx)
      (W₁ := W₁) (W₂ := W₂)
      (queryOfAtom₁ := queryOfAtom₁) (queryOfAtom₂ := queryOfAtom₂)
      (a0 := a0) (coord := fun itv => itv.upper) (tau := tau)
      (hVal := hVal)
      (pick := pick) (hReach := hReach) (H := H) (hTau := hTau))

/-- Walley upper-coordinate selector coherence (internalized ITV-compatibility). -/
theorem language_quantale_coherence_wmITV_upper_threshold_atom_of_queryEncoders_walley_id
    (R : Pattern → Pattern → Prop)
    (m : LanguageMorphism L₁ L₂ Eq)
    (ctx : IDMPredictiveContext)
    (W₁ W₂ : State)
    (queryOfAtom₁ queryOfAtom₂ : String → Pattern → Sigma Query)
    (a0 : String) (tau : ℝ)
    (hVal : ∀ p,
      wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₂ queryOfAtom₂ a0 (m.mapTerm p) =
      wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0 p)
    {U : Type*} [Fintype U]
    (pick : U → Pattern) {p₀ : Pattern}
    (hReach : ∀ u, LangReducesStar L₁ p₀ (pick u))
    (H : Finset (U × U))
    (hTau : ∀ u,
      tau ≤ (ITVSemantics.walleyIDMPredictive.eval ctx
        (wmPatternValuation
          (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0 (pick u))).upper) :
    (∀ u, LangReducesStar L₂ (m.mapTerm p₀) (m.mapTerm (pick u))) ∧
    weakness
      (sourceWeight
        (wmPatternValuation
          (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0) pick) H =
      weakness
        (targetWeight
          (wmPatternValuation
            (State := State) (Srt := Srt) (Query := Query) W₂ queryOfAtom₂ a0) m.mapTerm pick) H ∧
    (∀ u, sem R
      (upperAtomSemOfWMITVQSigma
        (State := State) (Srt := Srt) (Query := Query) (Ctx := IDMPredictiveContext)
        ITVSemantics.walleyIDMPredictive ctx W₂ tau queryOfAtom₂)
      (.atom a0) (m.mapTerm (pick u))) := by
  simpa [upperAtomSemOfWMITVQSigma, thresholdAtomSemOfWMITVQSigma] using
    (language_quantale_coherence_wmITV_threshold_atom_of_queryEncoders_walley_id
      (State := State) (Srt := Srt) (Query := Query)
      (R := R) (m := m) (ctx := ctx)
      (W₁ := W₁) (W₂ := W₂)
      (queryOfAtom₁ := queryOfAtom₁) (queryOfAtom₂ := queryOfAtom₂)
      (a0 := a0) (coord := fun itv => itv.upper) (tau := tau)
      (hVal := hVal)
      (pick := pick) (hReach := hReach) (H := H) (hTau := hTau))

/-- Bayes-exact credibility-coordinate selector coherence (internalized ITV-compatibility). -/
theorem language_quantale_coherence_wmITV_credibility_threshold_atom_of_queryEncoders_bayesNormal_id
    (R : Pattern → Pattern → Prop)
    (m : LanguageMorphism L₁ L₂ Eq)
    (ctx : BinaryContext)
    (W₁ W₂ : State)
    (queryOfAtom₁ queryOfAtom₂ : String → Pattern → Sigma Query)
    (a0 : String) (tau : ℝ)
    (hVal : ∀ p,
      wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₂ queryOfAtom₂ a0 (m.mapTerm p) =
      wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0 p)
    {U : Type*} [Fintype U]
    (pick : U → Pattern) {p₀ : Pattern}
    (hReach : ∀ u, LangReducesStar L₁ p₀ (pick u))
    (H : Finset (U × U))
    (hTau : ∀ u,
      tau ≤ (ITVSemantics.bayesCredible95.eval ctx
        (wmPatternValuation
          (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0 (pick u))).credibility) :
    (∀ u, LangReducesStar L₂ (m.mapTerm p₀) (m.mapTerm (pick u))) ∧
    weakness
      (sourceWeight
        (wmPatternValuation
          (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0) pick) H =
      weakness
        (targetWeight
          (wmPatternValuation
            (State := State) (Srt := Srt) (Query := Query) W₂ queryOfAtom₂ a0) m.mapTerm pick) H ∧
    (∀ u, sem R
      (credibilityAtomSemOfWMITVQSigma
        (State := State) (Srt := Srt) (Query := Query) (Ctx := BinaryContext)
        ITVSemantics.bayesCredible95 ctx W₂ tau queryOfAtom₂)
      (.atom a0) (m.mapTerm (pick u))) := by
  simpa [credibilityAtomSemOfWMITVQSigma, thresholdAtomSemOfWMITVQSigma] using
    (language_quantale_coherence_wmITV_threshold_atom_of_queryEncoders_bayesNormal_id
      (State := State) (Srt := Srt) (Query := Query)
      (R := R) (m := m) (ctx := ctx)
      (W₁ := W₁) (W₂ := W₂)
      (queryOfAtom₁ := queryOfAtom₁) (queryOfAtom₂ := queryOfAtom₂)
      (a0 := a0) (coord := fun itv => itv.credibility) (tau := tau)
      (hVal := hVal)
      (pick := pick) (hReach := hReach) (H := H) (hTau := hTau))

/-- Bayes-exact credibility-coordinate selector coherence (internalized ITV-compatibility). -/
theorem language_quantale_coherence_wmITV_credibility_threshold_atom_of_queryEncoders_bayesExact_id
    (R : Pattern → Pattern → Prop)
    (m : LanguageMorphism L₁ L₂ Eq)
    (ctx : BinaryContext)
    (W₁ W₂ : State)
    (queryOfAtom₁ queryOfAtom₂ : String → Pattern → Sigma Query)
    (a0 : String) (tau : ℝ)
    (hVal : ∀ p,
      wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₂ queryOfAtom₂ a0 (m.mapTerm p) =
      wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0 p)
    {U : Type*} [Fintype U]
    (pick : U → Pattern) {p₀ : Pattern}
    (hReach : ∀ u, LangReducesStar L₁ p₀ (pick u))
    (H : Finset (U × U))
    (hTau : ∀ u,
      tau ≤ (ITVSemantics.bayesCredibleExact95.eval ctx
        (wmPatternValuation
          (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0 (pick u))).credibility) :
    (∀ u, LangReducesStar L₂ (m.mapTerm p₀) (m.mapTerm (pick u))) ∧
    weakness
      (sourceWeight
        (wmPatternValuation
          (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0) pick) H =
      weakness
        (targetWeight
          (wmPatternValuation
            (State := State) (Srt := Srt) (Query := Query) W₂ queryOfAtom₂ a0) m.mapTerm pick) H ∧
    (∀ u, sem R
      (credibilityAtomSemOfWMITVQSigma
        (State := State) (Srt := Srt) (Query := Query) (Ctx := BinaryContext)
        ITVSemantics.bayesCredibleExact95 ctx W₂ tau queryOfAtom₂)
      (.atom a0) (m.mapTerm (pick u))) := by
  simpa [credibilityAtomSemOfWMITVQSigma, thresholdAtomSemOfWMITVQSigma] using
    (language_quantale_coherence_wmITV_threshold_atom_of_queryEncoders_bayesExact_id
      (State := State) (Srt := Srt) (Query := Query)
      (R := R) (m := m) (ctx := ctx)
      (W₁ := W₁) (W₂ := W₂)
      (queryOfAtom₁ := queryOfAtom₁) (queryOfAtom₂ := queryOfAtom₂)
      (a0 := a0) (coord := fun itv => itv.credibility) (tau := tau)
      (hVal := hVal)
      (pick := pick) (hReach := hReach) (H := H) (hTau := hTau))

/-- Walley credibility-coordinate selector coherence (internalized ITV-compatibility). -/
theorem language_quantale_coherence_wmITV_credibility_threshold_atom_of_queryEncoders_walley_id
    (R : Pattern → Pattern → Prop)
    (m : LanguageMorphism L₁ L₂ Eq)
    (ctx : IDMPredictiveContext)
    (W₁ W₂ : State)
    (queryOfAtom₁ queryOfAtom₂ : String → Pattern → Sigma Query)
    (a0 : String) (tau : ℝ)
    (hVal : ∀ p,
      wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₂ queryOfAtom₂ a0 (m.mapTerm p) =
      wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0 p)
    {U : Type*} [Fintype U]
    (pick : U → Pattern) {p₀ : Pattern}
    (hReach : ∀ u, LangReducesStar L₁ p₀ (pick u))
    (H : Finset (U × U))
    (hTau : ∀ u,
      tau ≤ (ITVSemantics.walleyIDMPredictive.eval ctx
        (wmPatternValuation
          (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0 (pick u))).credibility) :
    (∀ u, LangReducesStar L₂ (m.mapTerm p₀) (m.mapTerm (pick u))) ∧
    weakness
      (sourceWeight
        (wmPatternValuation
          (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0) pick) H =
      weakness
        (targetWeight
          (wmPatternValuation
            (State := State) (Srt := Srt) (Query := Query) W₂ queryOfAtom₂ a0) m.mapTerm pick) H ∧
    (∀ u, sem R
      (credibilityAtomSemOfWMITVQSigma
        (State := State) (Srt := Srt) (Query := Query) (Ctx := IDMPredictiveContext)
        ITVSemantics.walleyIDMPredictive ctx W₂ tau queryOfAtom₂)
      (.atom a0) (m.mapTerm (pick u))) := by
  simpa [credibilityAtomSemOfWMITVQSigma, thresholdAtomSemOfWMITVQSigma] using
    (language_quantale_coherence_wmITV_threshold_atom_of_queryEncoders_walley_id
      (State := State) (Srt := Srt) (Query := Query)
      (R := R) (m := m) (ctx := ctx)
      (W₁ := W₁) (W₂ := W₂)
      (queryOfAtom₁ := queryOfAtom₁) (queryOfAtom₂ := queryOfAtom₂)
      (a0 := a0) (coord := fun itv => itv.credibility) (tau := tau)
      (hVal := hVal)
      (pick := pick) (hReach := hReach) (H := H) (hTau := hTau))

/-- Bayes-exact width-coordinate selector coherence (internalized ITV-compatibility). -/
theorem language_quantale_coherence_wmITV_width_threshold_atom_of_queryEncoders_bayesNormal_id
    (R : Pattern → Pattern → Prop)
    (m : LanguageMorphism L₁ L₂ Eq)
    (ctx : BinaryContext)
    (W₁ W₂ : State)
    (queryOfAtom₁ queryOfAtom₂ : String → Pattern → Sigma Query)
    (a0 : String) (tau : ℝ)
    (hVal : ∀ p,
      wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₂ queryOfAtom₂ a0 (m.mapTerm p) =
      wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0 p)
    {U : Type*} [Fintype U]
    (pick : U → Pattern) {p₀ : Pattern}
    (hReach : ∀ u, LangReducesStar L₁ p₀ (pick u))
    (H : Finset (U × U))
    (hTau : ∀ u,
      tau ≤ (ITVSemantics.bayesCredible95.eval ctx
        (wmPatternValuation
          (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0 (pick u))).width) :
    (∀ u, LangReducesStar L₂ (m.mapTerm p₀) (m.mapTerm (pick u))) ∧
    weakness
      (sourceWeight
        (wmPatternValuation
          (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0) pick) H =
      weakness
        (targetWeight
          (wmPatternValuation
            (State := State) (Srt := Srt) (Query := Query) W₂ queryOfAtom₂ a0) m.mapTerm pick) H ∧
    (∀ u, sem R
      (widthAtomSemOfWMITVQSigma
        (State := State) (Srt := Srt) (Query := Query) (Ctx := BinaryContext)
        ITVSemantics.bayesCredible95 ctx W₂ tau queryOfAtom₂)
      (.atom a0) (m.mapTerm (pick u))) := by
  simpa [widthAtomSemOfWMITVQSigma, thresholdAtomSemOfWMITVQSigma] using
    (language_quantale_coherence_wmITV_threshold_atom_of_queryEncoders_bayesNormal_id
      (State := State) (Srt := Srt) (Query := Query)
      (R := R) (m := m) (ctx := ctx)
      (W₁ := W₁) (W₂ := W₂)
      (queryOfAtom₁ := queryOfAtom₁) (queryOfAtom₂ := queryOfAtom₂)
      (a0 := a0) (coord := fun itv => itv.width) (tau := tau)
      (hVal := hVal)
      (pick := pick) (hReach := hReach) (H := H) (hTau := hTau))

/-- Bayes-exact width-coordinate selector coherence (internalized ITV-compatibility). -/
theorem language_quantale_coherence_wmITV_width_threshold_atom_of_queryEncoders_bayesExact_id
    (R : Pattern → Pattern → Prop)
    (m : LanguageMorphism L₁ L₂ Eq)
    (ctx : BinaryContext)
    (W₁ W₂ : State)
    (queryOfAtom₁ queryOfAtom₂ : String → Pattern → Sigma Query)
    (a0 : String) (tau : ℝ)
    (hVal : ∀ p,
      wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₂ queryOfAtom₂ a0 (m.mapTerm p) =
      wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0 p)
    {U : Type*} [Fintype U]
    (pick : U → Pattern) {p₀ : Pattern}
    (hReach : ∀ u, LangReducesStar L₁ p₀ (pick u))
    (H : Finset (U × U))
    (hTau : ∀ u,
      tau ≤ (ITVSemantics.bayesCredibleExact95.eval ctx
        (wmPatternValuation
          (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0 (pick u))).width) :
    (∀ u, LangReducesStar L₂ (m.mapTerm p₀) (m.mapTerm (pick u))) ∧
    weakness
      (sourceWeight
        (wmPatternValuation
          (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0) pick) H =
      weakness
        (targetWeight
          (wmPatternValuation
            (State := State) (Srt := Srt) (Query := Query) W₂ queryOfAtom₂ a0) m.mapTerm pick) H ∧
    (∀ u, sem R
      (widthAtomSemOfWMITVQSigma
        (State := State) (Srt := Srt) (Query := Query) (Ctx := BinaryContext)
        ITVSemantics.bayesCredibleExact95 ctx W₂ tau queryOfAtom₂)
      (.atom a0) (m.mapTerm (pick u))) := by
  simpa [widthAtomSemOfWMITVQSigma, thresholdAtomSemOfWMITVQSigma] using
    (language_quantale_coherence_wmITV_threshold_atom_of_queryEncoders_bayesExact_id
      (State := State) (Srt := Srt) (Query := Query)
      (R := R) (m := m) (ctx := ctx)
      (W₁ := W₁) (W₂ := W₂)
      (queryOfAtom₁ := queryOfAtom₁) (queryOfAtom₂ := queryOfAtom₂)
      (a0 := a0) (coord := fun itv => itv.width) (tau := tau)
      (hVal := hVal)
      (pick := pick) (hReach := hReach) (H := H) (hTau := hTau))

/-- Walley width-coordinate selector coherence (internalized ITV-compatibility). -/
theorem language_quantale_coherence_wmITV_width_threshold_atom_of_queryEncoders_walley_id
    (R : Pattern → Pattern → Prop)
    (m : LanguageMorphism L₁ L₂ Eq)
    (ctx : IDMPredictiveContext)
    (W₁ W₂ : State)
    (queryOfAtom₁ queryOfAtom₂ : String → Pattern → Sigma Query)
    (a0 : String) (tau : ℝ)
    (hVal : ∀ p,
      wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₂ queryOfAtom₂ a0 (m.mapTerm p) =
      wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0 p)
    {U : Type*} [Fintype U]
    (pick : U → Pattern) {p₀ : Pattern}
    (hReach : ∀ u, LangReducesStar L₁ p₀ (pick u))
    (H : Finset (U × U))
    (hTau : ∀ u,
      tau ≤ (ITVSemantics.walleyIDMPredictive.eval ctx
        (wmPatternValuation
          (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0 (pick u))).width) :
    (∀ u, LangReducesStar L₂ (m.mapTerm p₀) (m.mapTerm (pick u))) ∧
    weakness
      (sourceWeight
        (wmPatternValuation
          (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0) pick) H =
      weakness
        (targetWeight
          (wmPatternValuation
            (State := State) (Srt := Srt) (Query := Query) W₂ queryOfAtom₂ a0) m.mapTerm pick) H ∧
    (∀ u, sem R
      (widthAtomSemOfWMITVQSigma
        (State := State) (Srt := Srt) (Query := Query) (Ctx := IDMPredictiveContext)
        ITVSemantics.walleyIDMPredictive ctx W₂ tau queryOfAtom₂)
      (.atom a0) (m.mapTerm (pick u))) := by
  simpa [widthAtomSemOfWMITVQSigma, thresholdAtomSemOfWMITVQSigma] using
    (language_quantale_coherence_wmITV_threshold_atom_of_queryEncoders_walley_id
      (State := State) (Srt := Srt) (Query := Query)
      (R := R) (m := m) (ctx := ctx)
      (W₁ := W₁) (W₂ := W₂)
      (queryOfAtom₁ := queryOfAtom₁) (queryOfAtom₂ := queryOfAtom₂)
      (a0 := a0) (coord := fun itv => itv.width) (tau := tau)
      (hVal := hVal)
      (pick := pick) (hReach := hReach) (H := H) (hTau := hTau))

/-- Bayes-exact strength-coordinate selector coherence (internalized ITV-compatibility). -/
theorem language_quantale_coherence_wmITV_strength_threshold_atom_of_queryEncoders_bayesNormal_id
    (R : Pattern → Pattern → Prop)
    (m : LanguageMorphism L₁ L₂ Eq)
    (ctx : BinaryContext)
    (W₁ W₂ : State)
    (queryOfAtom₁ queryOfAtom₂ : String → Pattern → Sigma Query)
    (a0 : String) (tau : ℝ)
    (hVal : ∀ p,
      wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₂ queryOfAtom₂ a0 (m.mapTerm p) =
      wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0 p)
    {U : Type*} [Fintype U]
    (pick : U → Pattern) {p₀ : Pattern}
    (hReach : ∀ u, LangReducesStar L₁ p₀ (pick u))
    (H : Finset (U × U))
    (hTau : ∀ u,
      tau ≤ (ITVSemantics.bayesCredible95.eval ctx
        (wmPatternValuation
          (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0 (pick u))).strength) :
    (∀ u, LangReducesStar L₂ (m.mapTerm p₀) (m.mapTerm (pick u))) ∧
    weakness
      (sourceWeight
        (wmPatternValuation
          (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0) pick) H =
      weakness
        (targetWeight
          (wmPatternValuation
            (State := State) (Srt := Srt) (Query := Query) W₂ queryOfAtom₂ a0) m.mapTerm pick) H ∧
    (∀ u, sem R
      (strengthAtomSemOfWMITVQSigma
        (State := State) (Srt := Srt) (Query := Query) (Ctx := BinaryContext)
        ITVSemantics.bayesCredible95 ctx W₂ tau queryOfAtom₂)
      (.atom a0) (m.mapTerm (pick u))) := by
  simpa [strengthAtomSemOfWMITVQSigma, thresholdAtomSemOfWMITVQSigma] using
    (language_quantale_coherence_wmITV_threshold_atom_of_queryEncoders_bayesNormal_id
      (State := State) (Srt := Srt) (Query := Query)
      (R := R) (m := m) (ctx := ctx)
      (W₁ := W₁) (W₂ := W₂)
      (queryOfAtom₁ := queryOfAtom₁) (queryOfAtom₂ := queryOfAtom₂)
      (a0 := a0) (coord := fun itv => itv.strength) (tau := tau)
      (hVal := hVal)
      (pick := pick) (hReach := hReach) (H := H) (hTau := hTau))

/-- Bayes-exact strength-coordinate selector coherence (internalized ITV-compatibility). -/
theorem language_quantale_coherence_wmITV_strength_threshold_atom_of_queryEncoders_bayesExact_id
    (R : Pattern → Pattern → Prop)
    (m : LanguageMorphism L₁ L₂ Eq)
    (ctx : BinaryContext)
    (W₁ W₂ : State)
    (queryOfAtom₁ queryOfAtom₂ : String → Pattern → Sigma Query)
    (a0 : String) (tau : ℝ)
    (hVal : ∀ p,
      wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₂ queryOfAtom₂ a0 (m.mapTerm p) =
      wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0 p)
    {U : Type*} [Fintype U]
    (pick : U → Pattern) {p₀ : Pattern}
    (hReach : ∀ u, LangReducesStar L₁ p₀ (pick u))
    (H : Finset (U × U))
    (hTau : ∀ u,
      tau ≤ (ITVSemantics.bayesCredibleExact95.eval ctx
        (wmPatternValuation
          (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0 (pick u))).strength) :
    (∀ u, LangReducesStar L₂ (m.mapTerm p₀) (m.mapTerm (pick u))) ∧
    weakness
      (sourceWeight
        (wmPatternValuation
          (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0) pick) H =
      weakness
        (targetWeight
          (wmPatternValuation
            (State := State) (Srt := Srt) (Query := Query) W₂ queryOfAtom₂ a0) m.mapTerm pick) H ∧
    (∀ u, sem R
      (strengthAtomSemOfWMITVQSigma
        (State := State) (Srt := Srt) (Query := Query) (Ctx := BinaryContext)
        ITVSemantics.bayesCredibleExact95 ctx W₂ tau queryOfAtom₂)
      (.atom a0) (m.mapTerm (pick u))) := by
  simpa [strengthAtomSemOfWMITVQSigma, thresholdAtomSemOfWMITVQSigma] using
    (language_quantale_coherence_wmITV_threshold_atom_of_queryEncoders_bayesExact_id
      (State := State) (Srt := Srt) (Query := Query)
      (R := R) (m := m) (ctx := ctx)
      (W₁ := W₁) (W₂ := W₂)
      (queryOfAtom₁ := queryOfAtom₁) (queryOfAtom₂ := queryOfAtom₂)
      (a0 := a0) (coord := fun itv => itv.strength) (tau := tau)
      (hVal := hVal)
      (pick := pick) (hReach := hReach) (H := H) (hTau := hTau))

/-- Walley strength-coordinate selector coherence (internalized ITV-compatibility). -/
theorem language_quantale_coherence_wmITV_strength_threshold_atom_of_queryEncoders_walley_id
    (R : Pattern → Pattern → Prop)
    (m : LanguageMorphism L₁ L₂ Eq)
    (ctx : IDMPredictiveContext)
    (W₁ W₂ : State)
    (queryOfAtom₁ queryOfAtom₂ : String → Pattern → Sigma Query)
    (a0 : String) (tau : ℝ)
    (hVal : ∀ p,
      wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₂ queryOfAtom₂ a0 (m.mapTerm p) =
      wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0 p)
    {U : Type*} [Fintype U]
    (pick : U → Pattern) {p₀ : Pattern}
    (hReach : ∀ u, LangReducesStar L₁ p₀ (pick u))
    (H : Finset (U × U))
    (hTau : ∀ u,
      tau ≤ (ITVSemantics.walleyIDMPredictive.eval ctx
        (wmPatternValuation
          (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0 (pick u))).strength) :
    (∀ u, LangReducesStar L₂ (m.mapTerm p₀) (m.mapTerm (pick u))) ∧
    weakness
      (sourceWeight
        (wmPatternValuation
          (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0) pick) H =
      weakness
        (targetWeight
          (wmPatternValuation
            (State := State) (Srt := Srt) (Query := Query) W₂ queryOfAtom₂ a0) m.mapTerm pick) H ∧
    (∀ u, sem R
      (strengthAtomSemOfWMITVQSigma
        (State := State) (Srt := Srt) (Query := Query) (Ctx := IDMPredictiveContext)
        ITVSemantics.walleyIDMPredictive ctx W₂ tau queryOfAtom₂)
      (.atom a0) (m.mapTerm (pick u))) := by
  simpa [strengthAtomSemOfWMITVQSigma, thresholdAtomSemOfWMITVQSigma] using
    (language_quantale_coherence_wmITV_threshold_atom_of_queryEncoders_walley_id
      (State := State) (Srt := Srt) (Query := Query)
      (R := R) (m := m) (ctx := ctx)
      (W₁ := W₁) (W₂ := W₂)
      (queryOfAtom₁ := queryOfAtom₁) (queryOfAtom₂ := queryOfAtom₂)
      (a0 := a0) (coord := fun itv => itv.strength) (tau := tau)
      (hVal := hVal)
      (pick := pick) (hReach := hReach) (H := H) (hTau := hTau))

end SelectorCoherence

end Mettapedia.Logic.PLNWMOSLFBridgeITVTyped
