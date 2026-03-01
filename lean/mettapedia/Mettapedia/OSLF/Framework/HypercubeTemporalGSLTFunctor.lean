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
  exact declReduces_mono
    (activeRulesWithTemporal_subset_of_le h)
    (by rfl)
    hred

theorem langReducesStar_mono_vertex_temporal {v w : ProbabilityVertex} (h : v ≤ w)
    {p q : Pattern}
    (hred : LangReducesStar (vertexTemporalLanguageDef w) p q) :
    LangReducesStar (vertexTemporalLanguageDef v) p q := by
  induction hred with
  | refl _ => exact .refl _
  | step h_pq _ ih =>
    exact .step (langReduces_mono_vertex_temporal h h_pq) ih

/-! ## Forward Morphism and Fiber -/

def weaknessForwardMorphism_temporal {v w : ProbabilityVertex} (h : v ≤ w) :
    ForwardMorphism (vertexTemporalLanguageDef w) (vertexTemporalLanguageDef v) where
  mapTerm := id
  forward_sim _ q hred := ⟨q, .single (langReduces_mono_vertex_temporal h hred), rfl⟩

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
    (hdiam : ∃ q, langReduces (vertexTemporalLanguageDef w) p q ∧ φ q) :
    ∃ q, langReduces (vertexTemporalLanguageDef v) p q ∧ φ q := by
  obtain ⟨q, hred, hphi⟩ := hdiam
  exact ⟨q, langReduces_mono_vertex_temporal h hred, hphi⟩

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
