import Mettapedia.OSLF.Framework.WMCalculusLanguageDef
import Mettapedia.OSLF.Framework.WMProbabilityEmbedding

/-!
# WM Calculus as GSLT Vertex Family

This module packages the WM calculus `LanguageDef` family as GSLT vertices,
providing:

1. A `WMLanguageFiber` over the 4-axis WM hypercube (`WMVertex`), with
   identity-on-terms forward/backward simulation along weakness edges.

2. Connection to the 13-axis probability hypercube via `wmToProbabilityVertex`.

3. Automatic OSLF per vertex via `langOSLF`.

## Key Structural Insight

For the 4-axis case, all WM vertices produce the *same* `LanguageDef`
(since the axis-dependent rules are currently semantic/predicate-level
differences, not syntactic rewrite differences).  The fiber morphisms
are therefore identity morphisms.

For the 6-axis extended case (with overlap and forgetting axes), weaker
vertices have strictly fewer rewrite rules, so forward simulation is
by rule-subset containment with `mapTerm = id`.

## References

- `PLNWMHypercubeBasis.lean` — `WMVertex`, `AxisBundle`, `LanguageFiber`, transport
- `WMProbabilityEmbedding.lean` — `wmToProbabilityVertex`, monotonicity
- `WMCalculusLanguageDef.lean` — `wmVertexLanguageDef`, `wmExtVertexLanguageDef`
-/

namespace Mettapedia.OSLF.Framework.WMCalculusGSLTVertex

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.LangMorphism
open Mettapedia.OSLF.Framework.PLNWMHypercubeBasis
open Mettapedia.OSLF.Framework.WMProbabilityEmbedding
open Mettapedia.OSLF.Framework.WMCalculusLanguageDef
open Mettapedia.ProbabilityTheory.Hypercube

/-! ## 4-Axis WM Language Equality -/

/-- All 4-axis WM vertices produce the same LanguageDef, because the
    axis-dependent rule lists are all empty (the differences between
    boolean/heyting, point/bounds, etc. are semantic, not syntactic). -/
theorem wmVertexLanguageDef_eq (v w : WMVertex) :
    wmVertexLanguageDef v = wmVertexLanguageDef w := by
  simp only [wmVertexLanguageDef, wmExtVertexLanguageDef, wmTypes]
  -- All axis-dependent rule lists are [], so rewrites = coreRules ++ [] ++ ... ++ []
  -- and types = ["State", "Query", "Evidence"] for both
  cases hL : v .logic <;> cases hL' : w .logic <;>
    cases hT : v .truthValue <;> cases hT' : w .truthValue <;>
    cases hI : v .interval <;> cases hI' : w .interval <;>
    cases hQ : v .typing <;> cases hQ' : w .typing <;>
    simp [logicRules, tvRules, intervalRules, typingRules,
          overlapRules, forgettingRules]

/-! ## 4-Axis WM Language Fiber -/

/-- Identity-on-terms language morphism between any two WM vertices.
    Since both vertices produce the same LanguageDef, this is trivially
    a full bidirectional simulation. -/
def wmVertexIdMorphism (v w : WMVertex) :
    LanguageMorphism (wmVertexLanguageDef v) (wmVertexLanguageDef w) Eq where
  mapTerm := id
  forward_sim := by
    intro p q h
    refine ⟨q, LangReducesStar.single ?_, rfl⟩
    rw [← wmVertexLanguageDef_eq v w]
    exact h
  backward_sim := by
    intro p t h
    refine ⟨t, LangReducesStar.single ?_, rfl⟩
    rw [wmVertexLanguageDef_eq v w]
    exact h

/-- The 4-axis WM calculus as a `WMLanguageFiber`.
    Each vertex gets the same LanguageDef with identity morphisms. -/
def wmLanguageFiber : WMLanguageFiber where
  lang := wmVertexLanguageDef
  morph := fun _ => wmVertexIdMorphism _ _

/-! ## Connection to Probability Hypercube -/

/-- LanguageDef at a probability vertex, via the WM embedding projection. -/
def wmAtProbabilityVertex (pv : ProbabilityVertex) : LanguageDef :=
  wmVertexLanguageDef (probabilityToWMVertex pv)

/-- Any two probability vertices yield the same WM LanguageDef
    (since all 4-axis WM vertices are equal). -/
theorem wmAtProbabilityVertex_eq (pv₁ pv₂ : ProbabilityVertex) :
    wmAtProbabilityVertex pv₁ = wmAtProbabilityVertex pv₂ := by
  simp only [wmAtProbabilityVertex]
  exact wmVertexLanguageDef_eq _ _

/-! ## Transport Theorems -/

/-- The WM fiber's mapAlongPath is always `id` (identity morphisms). -/
@[simp] theorem wmLanguageFiber_mapAlongPath_eq_id
    {v w : WMVertex} (π : CubePath wmAxes v w) (p : Pattern) :
    mapAlongPath (A := wmAxes) wmLanguageFiber π p = p := by
  induction π with
  | refl _ => rfl
  | cons _ _ ih =>
    simp [mapAlongPath, wmLanguageFiber, wmVertexIdMorphism] at ih ⊢
    exact ih

/-- Reductions at one WM vertex are reductions at any other WM vertex. -/
theorem wmCalc_transport {v w : WMVertex} {p q : Pattern}
    (hred : LangReducesStar (wmVertexLanguageDef v) p q) :
    LangReducesStar (wmVertexLanguageDef w) p q := by
  rw [← wmVertexLanguageDef_eq v w]
  exact hred

/-- Canonical path transport from classical-fast to general-exact. -/
theorem wmCalc_transport_canonical {p q : Pattern}
    (hred : LangReducesStar (wmVertexLanguageDef wmVertexClassicalFast) p q) :
    LangReducesStar (wmVertexLanguageDef wmVertexGeneralExact) p q :=
  wmCalc_transport hred

/-- Transport via the WM language fiber's generic path theorem. -/
theorem wmCalc_transport_path {v w : WMVertex}
    (π : CubePath wmAxes v w) {p q : Pattern}
    (hred : LangReducesStar (wmVertexLanguageDef v) p q) :
    ∃ q', LangReducesStar (wmVertexLanguageDef w)
      (mapAlongPath (A := wmAxes) wmLanguageFiber π p) q' ∧
      q' = mapAlongPath (A := wmAxes) wmLanguageFiber π q :=
  transport_path_forward (A := wmAxes) (F := wmLanguageFiber) π hred

/-! ## OSLF Per Vertex -/

/-- OSLF type system for any WM vertex (automatic via TypeSynthesis). -/
noncomputable def wmVertexOSLF (v : WMVertex) :=
  langOSLF (wmVertexLanguageDef v)

/-- All WM vertices produce the same OSLF type system. -/
theorem wmVertexOSLF_eq (v w : WMVertex) :
    wmVertexLanguageDef v = wmVertexLanguageDef w :=
  wmVertexLanguageDef_eq v w

/-! ## Extended 6-Axis Vertex LanguageDef -/

/-- OSLF type system for any extended WM vertex. -/
noncomputable def wmExtVertexOSLF (v : WMExtVertex) :=
  langOSLF (wmExtVertexLanguageDef v)

/-! ## Full 13-Axis Vertex Family -/

/-- All logic axis rules are empty. -/
private theorem logicRules_nil (l : WMLogic) : logicRules l = [] := by cases l <;> rfl
/-- All truth-value axis rules are empty. -/
private theorem tvRules_nil (t : WMTruthValue) : tvRules t = [] := by cases t <;> rfl
/-- All interval axis rules are empty. -/
private theorem intervalRules_nil (i : WMIntervalSemantics) : intervalRules i = [] := by
  cases i <;> rfl
/-- All typing axis rules are empty. -/
private theorem typingRules_nil (q : WMQueryTyping) : typingRules q = [] := by cases q <;> rfl

theorem wmFullVertexLanguageDef_base_eq (v w : WMFullVertex)
    (hov : v.overlap = w.overlap) (hfg : v.forgetting = w.forgetting)
    (hpv : v.provenance = w.provenance) (hfp : v.fixpoint = w.fixpoint)
    (hco : v.cost = w.cost) (hcn : v.conservation = w.conservation)
    (hex : v.experiment = w.experiment) (hkr : v.kripke = w.kripke)
    (hca : v.carrier = w.carrier) :
    wmFullVertexLanguageDef v = wmFullVertexLanguageDef w := by
  simp only [wmFullVertexLanguageDef, wmFullTypes,
             hov, hfg, hpv, hfp, hco, hcn, hex, hkr, hca,
             logicRules_nil, tvRules_nil, intervalRules_nil, typingRules_nil]

/-- Identity-on-terms language morphism between full vertices with the same
    extension axes (where only the base 4 axes differ). -/
def wmFullVertexIdMorphism (v w : WMFullVertex)
    (heq : wmFullVertexLanguageDef v = wmFullVertexLanguageDef w) :
    LanguageMorphism (wmFullVertexLanguageDef v) (wmFullVertexLanguageDef w) Eq where
  mapTerm := id
  forward_sim := by
    intro p q h
    refine ⟨q, LangReducesStar.single ?_, rfl⟩
    rw [← heq]; exact h
  backward_sim := by
    intro p t h
    refine ⟨t, LangReducesStar.single ?_, rfl⟩
    rw [heq]; exact h

/-- The minimal full vertex has the same rewrite rules as the core WM calculus. -/
theorem wmFullVertexMinimal_rewrites_eq_core :
    (wmFullVertexLanguageDef wmFullVertexMinimal).rewrites =
    coreRules := by
  simp [wmFullVertexLanguageDef, wmFullVertexMinimal,
        logicRules_nil, tvRules_nil, intervalRules_nil, typingRules_nil,
        overlapRules, forgettingRules, supportTrackedRules,
        provenanceRules, fixpointRules, costRules,
        conservationRules, experimentRules, kripkeRules, carrierRules]

/-- Reductions at one full vertex transfer to any other with the same LanguageDef. -/
theorem wmFullCalc_transport {v w : WMFullVertex} {p q : Pattern}
    (heq : wmFullVertexLanguageDef v = wmFullVertexLanguageDef w)
    (hred : LangReducesStar (wmFullVertexLanguageDef v) p q) :
    LangReducesStar (wmFullVertexLanguageDef w) p q := by
  rw [← heq]; exact hred

/-- The full vertex embedding from WMExtVertex preserves rewrite rules
    (when the forgetting mode is not supportTracked). -/
theorem wmExtToFull_transport_rewrites {v : WMExtVertex}
    (hf : v.forgetting ≠ .supportTracked) :
    (wmFullVertexLanguageDef (wmExtToFull v)).rewrites =
    (wmExtVertexLanguageDef v).rewrites :=
  wmExtToFull_rewrites_eq v hf

/-! ## Full Vertex OSLF -/

/-- OSLF type system for any full 13-axis WM vertex. -/
noncomputable def wmFullVertexOSLF' (v : WMFullVertex) :=
  langOSLF (wmFullVertexLanguageDef v)

/-- The maximal vertex OSLF (all extensions enabled). -/
noncomputable def wmMaximalOSLF :=
  langOSLF (wmFullVertexLanguageDef wmFullVertexMaximal)

/-! ## Extension Axis Rule Counts -/

/-- Total number of rewrite rules at a given full vertex. -/
def wmFullVertexRuleCount (v : WMFullVertex) : Nat :=
  (wmFullVertexLanguageDef v).rewrites.length

/-- The minimal vertex has exactly the 5 core rules. -/
theorem wmFullVertexMinimal_ruleCount :
    wmFullVertexRuleCount wmFullVertexMinimal = 5 := by
  simp [wmFullVertexRuleCount, wmFullVertexLanguageDef, wmFullVertexMinimal,
        coreRules, logicRules_nil, tvRules_nil, intervalRules_nil, typingRules_nil,
        overlapRules, forgettingRules, supportTrackedRules,
        provenanceRules, fixpointRules, costRules,
        conservationRules, experimentRules, kripkeRules, carrierRules]

/-- The maximal vertex has 5 core + 1 overlap + 2 forgetting + 1 support +
    6 provenance + 4 fixpoint + 3 cost + 2 conservation + 7 experiment +
    3 kripke + 2 generic = 36 rules. -/
theorem wmFullVertexMaximal_ruleCount :
    wmFullVertexRuleCount wmFullVertexMaximal = 36 := by
  simp [wmFullVertexRuleCount, wmFullVertexLanguageDef, wmFullVertexMaximal,
        coreRules, logicRules_nil, tvRules_nil, intervalRules_nil, typingRules_nil,
        overlapRules, forgettingRules, supportTrackedRules,
        provenanceRules, fixpointRules, costRules,
        conservationRules, experimentRules, kripkeRules, carrierRules]

end Mettapedia.OSLF.Framework.WMCalculusGSLTVertex
