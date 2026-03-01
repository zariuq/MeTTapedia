import Mettapedia.OSLF.Framework.VertexRewriteRules
import Mettapedia.OSLF.Framework.LanguageMorphism
import Mettapedia.ProbabilityTheory.Hypercube.WeaknessOrder

/-!
# GSLT Hypercube Functor: ProbabilityVertex → LanguageDef → OSLF

This module connects the 13-axis probability hypercube to the OSLF pipeline:

1. Each `ProbabilityVertex` determines a `LanguageDef` (via `vertexLanguageDef`)
2. Weakness morphisms (v ≤ w, i.e. w is weaker) induce **forward simulation**:
   reductions in the weaker language lift to reductions in the stronger language
3. Each vertex gets a full OSLF type system (`vertexOSLF`) with Galois connection

## Forward Transport Theorem

The core result: if a term reduces in a weaker (more general) theory, it also
reduces in any stronger (more specific) theory.  This is the **monotonicity of
computational power** along the hypercube weakness order.

## References

- Stay & Wells, "Generating Hypercubes of Type Systems"
- Meredith & Stay, "Operational Semantics in Logical Form"
- Gorla (2010), "Towards a Unified Approach to Encodability and Separation Results"
-/

namespace Mettapedia.OSLF.Framework.HypercubeGSLTFunctor

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match (Bindings applyBindings)
open Mettapedia.OSLF.MeTTaIL.DeclReducesPremises
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.LangMorphism
open Mettapedia.OSLF.Framework.VertexRewriteRules
open Mettapedia.ProbabilityTheory.Hypercube

/-! ## §1: Reduction Monotonicity

The key structural lemma: if a term reduces in a weaker vertex's language,
it also reduces in a stronger vertex's language.  This follows from rule
monotonicity (`activeRules_subset_of_le`). -/

/-- Declarative one-step reduction is monotone in the rule set
    (general version: no restriction on premises). -/
theorem declReduces_mono
    {lang₁ lang₂ : LanguageDef}
    (hrules : ∀ r, r ∈ lang₁.rewrites → r ∈ lang₂.rewrites)
    (hcong : lang₁.congruenceCollections = lang₂.congruenceCollections)
    {p q : Pattern}
    (hred : DeclReducesWithPremises RelationEnv.empty lang₁ p q) :
    DeclReducesWithPremises RelationEnv.empty lang₂ p q := by
  induction hred with
  | topRule r hr bs0 hbs0 bs hprem hq =>
    exact .topRule r (hrules r hr) bs0 hbs0 bs
      (applyPremisesWithEnv_mono hrules hcong RelationEnv.empty r.premises bs0 bs hprem) hq
  | @congElem _ ct _ hct i hi r hr bs0 hbs0 bs hprem _ hq =>
    have hct₂ : lang₂.allowsCongruenceIn ct := by
      simp only [LanguageDef.allowsCongruenceIn] at hct ⊢; rw [← hcong]; exact hct
    exact .congElem hct₂ i hi r (hrules r hr) bs0 hbs0 bs
      (applyPremisesWithEnv_mono hrules hcong RelationEnv.empty r.premises bs0 bs hprem) hq

/-- Reduction is monotone along the hypercube weakness order. -/
theorem langReduces_mono_vertex {v w : ProbabilityVertex} (h : v ≤ w)
    {p q : Pattern}
    (hred : langReduces (vertexLanguageDef w) p q) :
    langReduces (vertexLanguageDef v) p q := by
  unfold langReduces langReducesUsing at hred ⊢
  exact declReduces_mono
    (activeRules_subset_of_le h)
    (by rfl)  -- congruenceCollections are both default
    hred

/-! ## §2: Multi-Step Reduction Transport

Lift the single-step monotonicity to multi-step (reflexive-transitive closure). -/

/-- Multi-step reduction is monotone along the weakness order. -/
theorem langReducesStar_mono_vertex {v w : ProbabilityVertex} (h : v ≤ w)
    {p q : Pattern}
    (hred : LangReducesStar (vertexLanguageDef w) p q) :
    LangReducesStar (vertexLanguageDef v) p q := by
  induction hred with
  | refl _ => exact .refl _
  | step h_pq _ ih =>
    exact .step (langReduces_mono_vertex h h_pq) ih

/-! ## §3: Forward Morphism

A `ForwardMorphism` captures forward simulation without requiring backward
simulation.  This is the correct notion for sub-language embeddings where
the target language has strictly more rewrite rules. -/

/-- A forward simulation morphism between two languages.
    Weaker notion than `LanguageMorphism` — only forward simulation required. -/
structure ForwardMorphism (L₁ L₂ : LanguageDef) where
  /-- Maps L₁ terms to L₂ terms -/
  mapTerm : Pattern → Pattern
  /-- Every L₁ single-step reduction is matched by L₂ multi-step reduction -/
  forward_sim : ∀ p q, langReduces L₁ p q →
    ∃ T, LangReducesStar L₂ (mapTerm p) T ∧ T = mapTerm q

/-- Multi-step forward simulation -/
theorem ForwardMorphism.forward_multi
    (m : ForwardMorphism L₁ L₂)
    {p q : Pattern} (h : LangReducesStar L₁ p q) :
    ∃ T, LangReducesStar L₂ (m.mapTerm p) T ∧ T = m.mapTerm q := by
  induction h with
  | refl p => exact ⟨m.mapTerm p, .refl _, rfl⟩
  | step h_pq _ ih =>
    obtain ⟨_, h_star1, rfl⟩ := m.forward_sim _ _ h_pq
    obtain ⟨T₂, h_star2, h_eq2⟩ := ih
    exact ⟨T₂, h_star1.trans h_star2, h_eq2⟩

/-- The identity forward morphism from a weaker to a stronger language. -/
def weaknessForwardMorphism {v w : ProbabilityVertex} (h : v ≤ w) :
    ForwardMorphism (vertexLanguageDef w) (vertexLanguageDef v) where
  mapTerm := id
  forward_sim _ q hred := ⟨q, .single (langReduces_mono_vertex h hred), rfl⟩

/-! ## §4: Forward Fiber over the Hypercube

A `ForwardFiber` assigns a LanguageDef to each vertex and provides forward
morphisms along weakness edges.  Unlike `LanguageFiber`, it does not
require backward simulation. -/

/-- A family of LanguageDefs indexed by a preorder with forward morphisms. -/
structure ForwardFiber (V : Type*) [Preorder V] where
  /-- Language at each vertex -/
  lang : V → LanguageDef
  /-- Forward morphism along each weakness step -/
  morph : ∀ {v w : V}, v ≤ w → ForwardMorphism (lang w) (lang v)

/-- Map a term along a weakness relation (identity for our instantiation). -/
def ForwardFiber.mapTerm {V : Type*} [Preorder V]
    (F : ForwardFiber V) {v w : V} (h : v ≤ w) (p : Pattern) : Pattern :=
  (F.morph h).mapTerm p

/-- Forward transport: multi-step reductions transport along weakness relations. -/
theorem ForwardFiber.transport_forward {V : Type*} [Preorder V]
    (F : ForwardFiber V) {v w : V} (h : v ≤ w)
    {p q : Pattern}
    (hred : LangReducesStar (F.lang w) p q) :
    ∃ q', LangReducesStar (F.lang v) (F.mapTerm h p) q' ∧
      q' = F.mapTerm h q :=
  (F.morph h).forward_multi hred

/-! ## §5: The GSLT Hypercube Forward Fiber -/

/-- The GSLT forward fiber over the 13-axis probability hypercube. -/
def gsltForwardFiber : ForwardFiber ProbabilityVertex where
  lang := vertexLanguageDef
  morph h := weaknessForwardMorphism h

/-- Forward transport along the hypercube weakness order:
    if a term multi-step reduces in a weaker theory, it multi-step reduces
    in any stronger theory (since `mapTerm = id`, terms are unchanged). -/
theorem gslt_forward_transport {v w : ProbabilityVertex} (h : v ≤ w)
    {p q : Pattern}
    (hred : LangReducesStar (vertexLanguageDef w) p q) :
    LangReducesStar (vertexLanguageDef v) p q := by
  -- Directly from langReducesStar_mono_vertex (no need for ForwardFiber detour)
  exact langReducesStar_mono_vertex h hred

/-! ## §6: OSLF Pipeline Per Vertex

Each vertex gets the full OSLF type system with proven Galois connection. -/

/-- The OSLF-generated type system at a hypercube vertex. -/
noncomputable def vertexOSLF (v : ProbabilityVertex) :
    OSLFTypeSystem (langRewriteSystem (vertexLanguageDef v)) :=
  langOSLF (vertexLanguageDef v)

/-- The Galois connection at a hypercube vertex. -/
noncomputable def vertexGalois (v : ProbabilityVertex) :=
  langGalois (vertexLanguageDef v)

/-! ## §7: Diamond Modality Transport

If a formula involving ◇ (step-future) is satisfied at a weaker vertex,
it is also satisfied at any stronger vertex. -/

/-- Diamond modality is monotone along the weakness order:
    if there exists a reduct satisfying φ in the weaker theory,
    there exists a reduct satisfying φ in the stronger theory. -/
theorem diamond_mono_vertex {v w : ProbabilityVertex} (h : v ≤ w)
    {φ : Pattern → Prop} {p : Pattern}
    (hdiam : ∃ q, langReduces (vertexLanguageDef w) p q ∧ φ q) :
    ∃ q, langReduces (vertexLanguageDef v) p q ∧ φ q := by
  obtain ⟨q, hred, hphi⟩ := hdiam
  exact ⟨q, langReduces_mono_vertex h hred, hphi⟩

/-! ## §8: Concrete Examples -/

/-- Kolmogorov is stronger than quantum (quantum is weaker/more general). -/
example : kolmogorov ≤ quantum := by decide

/-- Classical logic is the strongest (most specific) vertex. -/
example : classicalLogic ≤ kolmogorov := by decide

/-- Most general vertex is the weakest. -/
example : kolmogorov ≤ mostGeneralVertex := by decide

/-- Forward transport instantiation: any reduction at `mostGeneralVertex`
    (only ExtBayes2) also works at `kolmogorov` (all 3 rules). -/
theorem example_transport_mostGeneral_to_kolmogorov
    {p q : Pattern}
    (hred : LangReducesStar (vertexLanguageDef mostGeneralVertex) p q) :
    LangReducesStar (vertexLanguageDef kolmogorov) p q :=
  gslt_forward_transport (by decide : kolmogorov ≤ mostGeneralVertex) hred

/-- Forward transport: any reduction at `quantum` also works at `kolmogorov`. -/
theorem example_transport_quantum_to_kolmogorov
    {p q : Pattern}
    (hred : LangReducesStar (vertexLanguageDef quantum) p q) :
    LangReducesStar (vertexLanguageDef kolmogorov) p q :=
  gslt_forward_transport (by decide : kolmogorov ≤ quantum) hred

/-- The vertexLanguageDef at classicalLogic has the same rules as plnSelectorLanguageDef
    (both commutative + precise → all 3 rules). -/
theorem classicalLogic_rules_eq :
    (vertexLanguageDef classicalLogic).rewrites =
      [PLNSelectorLanguageDef.ruleExtBayes2,
       PLNSelectorLanguageDef.ruleExtBayesFamily,
       PLNSelectorLanguageDef.ruleNormalizeStrength] := by rfl

end Mettapedia.OSLF.Framework.HypercubeGSLTFunctor
