import Mettapedia.Languages.GF.HandCrafted.English.InterfaceContrast
import Mettapedia.Languages.GF.Examples.ScopeAmbiguity
import Mettapedia.Languages.GF.WorldModelVisibleBridge
import Mettapedia.Languages.GF.VisibleLayer
import Mettapedia.Languages.GF.WorldModelSemantics
import Mettapedia.OSLF.Formula
import Mettapedia.OSLF.MeTTaIL.Syntax
import Mettapedia.OSLF.QuantifiedFormula2
import Mettapedia.Logic.EvidenceQuantale

/-!
# GF English Semantic Highlights

Paper-facing aliases for high-value theorem endpoints in the current
GF/English fragment.
-/

namespace Mettapedia.Languages.GF.HandCrafted.English.SemanticHighlights

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.QuantifiedFormula2
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Languages.GF.VisibleLayer
open Mettapedia.Languages.GF.WorldModelSemantics
open Mettapedia.Languages.GF.WorldModelVisibleBridge
open Mettapedia.OSLF.Formula

/-- Scope ambiguity ordering on the EMLA witness (`∃∀ ≤ ∀∃`). -/
theorem emla_scope_inverse_le_surface
    (R : Pattern → Pattern → Prop) (I : QEvidenceAtomSem) (Dom : Domain2)
    (env : VarEnv2) (p : Pattern) :
    qsemE2 R I Dom env
      (.qexists "q2" (.qforall "q1"
        (.qimp (.qatom ⟨"man_N", [.var "q1"]⟩)
          (.qand (.qatom ⟨"woman_N", [.var "q2"]⟩)
                 (.qatom ⟨"love_V2", [.var "q1", .var "q2"]⟩))))) p ≤
    qsemE2 R I Dom env
      (.qforall "q1" (.qexists "q2"
        (.qimp (.qatom ⟨"man_N", [.var "q1"]⟩)
          (.qand (.qatom ⟨"woman_N", [.var "q2"]⟩)
                 (.qatom ⟨"love_V2", [.var "q1", .var "q2"]⟩))))) p :=
  Mettapedia.Languages.GF.Examples.ScopeAmbiguity.emla_scope_ordering R I Dom env p

/-- Pronoun-binding locality: V4 preserves formulas that do not mention
the bound pronoun free. -/
theorem v4_preserves_unmentioned_formula
    {cfg : VisibleCfg} {π : TemporalPolicy}
    (pr r : String) (pos : Pattern) (s : GrammarState)
    (href_pos : StoreAtom.ref r pos ∈ s.store)
    (hfresh : ∀ r', StoreAtom.bind pr r' ∉ s.store)
    (hfb : functionalBind s.store) (hur : uniqueRef s.store)
    (I : QEvidenceAtomSem) (Dom : Domain2) (φ : QFormula2)
    (hnotfree : pr ∉ freeVarsQF2 φ) :
    let s' : GrammarState := ⟨s.term, s.store + {StoreAtom.bind pr r}⟩
    gfReducesFull cfg π s s' ∧
    gsemE2Full cfg π I Dom φ s = gsemE2Full cfg π I Dom φ s' :=
  Mettapedia.Languages.GF.WorldModelVisibleBridge.V4_preserves_unmentioned_formula
    (cfg := cfg) (π := π)
    pr r pos s href_pos hfresh hfb hur I Dom φ hnotfree

/-- Store-to-environment invariance under bind/ref equivalence and
functional-bind/unique-ref invariants. -/
theorem store_env_invariant_equiv
    (σ₁ σ₂ : Multiset StoreAtom)
    (hfb₁ : functionalBind σ₁) (hur₁ : uniqueRef σ₁)
    (hfb₂ : functionalBind σ₂) (hur₂ : uniqueRef σ₂)
    (hbind : ∀ pr r, StoreAtom.bind pr r ∈ σ₁ ↔ StoreAtom.bind pr r ∈ σ₂)
    (href : ∀ r pos, StoreAtom.ref r pos ∈ σ₁ ↔ StoreAtom.ref r pos ∈ σ₂) :
    storeToEnv σ₁ = storeToEnv σ₂ :=
  Mettapedia.Languages.GF.WorldModelVisibleBridge.storeToEnv_invariant_equiv
    σ₁ σ₂ hfb₁ hur₁ hfb₂ hur₂ hbind href

/-! ## Modal theorem family wrappers -/

/-- Positive-fragment monotonicity in the accessibility relation. -/
theorem modal_positive_monotone
    {R1 R2 : Pattern → Pattern → Prop}
    (hR : ∀ p q, R1 p q → R2 p q)
    (I : AtomSem) {φ : OSLFFormula} (hpos : positiveFormula φ)
    {p : Pattern} (h : sem R1 I φ p) :
    sem R2 I φ p :=
  sem_mono_rel_positive hR I hpos h

/-- Modal-free formulas are relation-independent (`R`-invariant semantics). -/
theorem modal_free_relation_irrelevant
    {R1 R2 : Pattern → Pattern → Prop}
    (I : AtomSem) {φ : OSLFFormula} (hmf : modalFree φ)
    {p : Pattern} :
    sem R1 I φ p ↔ sem R2 I φ p :=
  sem_modalFree_irrel I hmf

/-- `□` is anti-monotone in the relation (for modal-free payloads). -/
theorem modal_box_antitone
    {R1 R2 : Pattern → Pattern → Prop}
    (hR : ∀ p q, R2 p q → R1 p q)
    (I : AtomSem) {φ : OSLFFormula} (hmf : modalFree φ)
    {p : Pattern} (h : sem R1 I (.box φ) p) :
    sem R2 I (.box φ) p :=
  sem_antitone_box hR I hmf h

/-- Any positive theorem over syntax reductions lifts to temporal policies. -/
theorem modal_syntax_lifts_to_temporal
    (π : TemporalPolicy)
    (I : AtomSem) {φ : OSLFFormula} (hpos : positiveFormula φ)
    {p : Pattern}
    (h : sem (Mettapedia.OSLF.Framework.TypeSynthesis.langReduces
      Mettapedia.Languages.GF.OSLFBridge.gfRGLLanguageDef) I φ p) :
    sem (gfReducesTemporal π) I φ p :=
  sem_syntax_lifts_to_temporal π I hpos h

/-! ## Temporal asymmetry wrappers -/

/-- Under `syntaxOnly`, present temporal nodes have no `◇`-progress. -/
theorem temporal_asymmetry_syntaxOnly
    (cl : Pattern) (I : AtomSem) (φ : OSLFFormula) :
    ¬ sem (gfReducesTemporal .syntaxOnly) I (.dia φ)
      (.apply "⊛temporal" [cl, .apply "0" []]) :=
  present_not_entail_past_syntaxOnly cl I φ

/-- Policy-conditioned positive counterpart: if present→past edge exists, progress holds. -/
theorem temporal_progress_with_policy_edge
    (step : Pattern → Pattern → Prop)
    (cl : Pattern)
    (hstep : step
      (.apply "⊛temporal" [cl, .apply "0" []])
      (.apply "⊛temporal" [cl, .apply "-1" []]))
    (I : AtomSem) :
    sem (gfReducesTemporal (.withStep step)) I
      (.dia .top)
      (.apply "⊛temporal" [cl, .apply "0" []]) :=
  present_can_progress_of_temporalStep step cl hstep I

end Mettapedia.Languages.GF.HandCrafted.English.SemanticHighlights
