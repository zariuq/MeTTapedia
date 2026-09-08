import Mettapedia.OSLF.Framework.HypercubeGSLTFunctor
import Mettapedia.OSLF.Framework.VertexTemporalRewriteRules

/-!
# Temporal/Event Hypercube GSLT Functor

Extends the selector-only hypercube/GSLT transport with temporal/event rewrites.

Source category:
- `ProbabilityVertex` ordered by weakness (`v ≤ w` means `w` is weaker).

Target family:
- `vertexTemporalLanguageDef v` from `VertexTemporalRewriteRules`.

Core result:
- Any reduction in a weaker temporal/event vertex language transports forward
  to every stronger vertex language.
-/

namespace Mettapedia.OSLF.Framework.HypercubeTemporalGSLTFunctor

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.LangMorphism
open Mettapedia.ProbabilityTheory.Hypercube
open Mettapedia.OSLF.Framework.VertexTemporalRewriteRules
open Mettapedia.OSLF.Framework.HypercubeGSLTFunctor

/-! ## Reduction Monotonicity -/

theorem langReduces_mono_vertex_temporal {v w : ProbabilityVertex} (h : v ≤ w)
    {p q : Pattern}
    (hred : langReduces (vertexTemporalLanguageDef w) p q) :
    langReduces (vertexTemporalLanguageDef v) p q := by
  unfold langReduces langReducesUsing at hred ⊢
  exact contextualStep_mono_rules
    (activeRulesWithTemporal_subset_of_le h)
    hred

/-- The canonical step modulo equations is monotone along the temporal
hypercube.  These presentations have no equation generators, so the proof is
the identity-equivalence specialization of the one semantic relation. -/
theorem langSemanticReduces_mono_vertex_temporal
    {v w : ProbabilityVertex} (h : v ≤ w) {p q : Pattern}
    (hred : langSemanticReduces (vertexTemporalLanguageDef w) p q) :
    langSemanticReduces (vertexTemporalLanguageDef v) p q := by
  apply langReduces_to_semantic
  apply langReduces_mono_vertex_temporal h
  have raw :=
    (langSemanticReducesUsing_iff_langReducesUsing_of_equation_free
      RelationEnv.empty (lang := vertexTemporalLanguageDef w) (by rfl) p q).mp
      (by simpa [langSemanticReduces] using hred)
  simpa [langReduces] using raw

theorem langReducesStar_mono_vertex_temporal {v w : ProbabilityVertex} (h : v ≤ w)
    {p q : Pattern}
    (hred : LangReducesStar (vertexTemporalLanguageDef w) p q) :
    LangReducesStar (vertexTemporalLanguageDef v) p q := by
  induction hred with
  | refl _ => exact .refl _
  | step h_pq _ ih =>
    exact .step (langSemanticReduces_mono_vertex_temporal h h_pq) ih

/-! ## Forward Morphism and Fiber -/

def weaknessForwardMorphism_temporal {v w : ProbabilityVertex} (h : v ≤ w) :
    ForwardMorphism (vertexTemporalLanguageDef w) (vertexTemporalLanguageDef v) where
  mapTerm := id
  map_equiv := by
    intro left right equivalent
    have equal : left = right :=
      (langGSLT_equiv_iff_eq_of_equation_free
        (lang := vertexTemporalLanguageDef w) (by rfl) left right).mp equivalent
    subst right
    exact (langGSLT (vertexTemporalLanguageDef v)).equations.refl _
  forward_sim _ q hred :=
    ⟨q, .single (langSemanticReduces_mono_vertex_temporal h hred), rfl⟩

def gsltTemporalForwardFiber : ForwardFiber ProbabilityVertex where
  lang := vertexTemporalLanguageDef
  morph h := weaknessForwardMorphism_temporal h

theorem gslt_temporal_forward_transport {v w : ProbabilityVertex} (h : v ≤ w)
    {p q : Pattern}
    (hred : LangReducesStar (vertexTemporalLanguageDef w) p q) :
    LangReducesStar (vertexTemporalLanguageDef v) p q := by
  exact langReducesStar_mono_vertex_temporal h hred

/-! ## OSLF Pipeline per Vertex -/

noncomputable def vertexTemporalOSLF (v : ProbabilityVertex) :
    OSLFTypeSystem (langRewriteSystem (vertexTemporalLanguageDef v)) :=
  langOSLF (vertexTemporalLanguageDef v)

noncomputable def vertexTemporalGalois (v : ProbabilityVertex) :=
  langGalois (vertexTemporalLanguageDef v)

/-! ## Diamond Monotonicity -/

theorem diamond_mono_vertex_temporal {v w : ProbabilityVertex} (h : v ≤ w)
    {φ : Pattern → Prop} {p : Pattern}
    (hdiam : langDiamond (vertexTemporalLanguageDef w)
      (equationPredicateOfEquationFree (by rfl) φ) p) :
    langDiamond (vertexTemporalLanguageDef v)
      (equationPredicateOfEquationFree (by rfl) φ) p := by
  rw [langDiamond_spec] at hdiam ⊢
  obtain ⟨q, hred, hphi⟩ := hdiam
  exact ⟨q, langSemanticReduces_mono_vertex_temporal h hred, hphi⟩

/-! ## Examples -/

theorem example_transport_quantum_to_kolmogorov_temporal
    {p q : Pattern}
    (hred : LangReducesStar (vertexTemporalLanguageDef quantum) p q) :
    LangReducesStar (vertexTemporalLanguageDef kolmogorov) p q :=
  gslt_temporal_forward_transport (by decide : kolmogorov ≤ quantum) hred

theorem example_transport_mostGeneral_to_classical_temporal
    {p q : Pattern}
    (hred : LangReducesStar (vertexTemporalLanguageDef mostGeneralVertex) p q) :
    LangReducesStar (vertexTemporalLanguageDef classicalLogic) p q :=
  gslt_temporal_forward_transport (by decide : classicalLogic ≤ mostGeneralVertex) hred

end Mettapedia.OSLF.Framework.HypercubeTemporalGSLTFunctor
