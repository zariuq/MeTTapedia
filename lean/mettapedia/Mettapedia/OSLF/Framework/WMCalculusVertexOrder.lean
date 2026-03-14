import Mettapedia.OSLF.Framework.WMCalculusLanguageDef
import Mettapedia.OSLF.Framework.WMCalculusContextClosure
import Mettapedia.OSLF.Framework.HypercubeGSLTFunctor

/-!
# WM Calculus — Vertex Preorder and Forward Fiber

The 9 extension axes of `WMFullVertex` each define a monotone chain of
rewrite rule lists (more expressive mode ⊇ less expressive mode).
This file proves:

1. Per-axis rule subset monotonicity
2. Full vertex rule subset theorem
3. `ForwardMorphism` and `ForwardFiber` instances
4. `BoundedOrder` with `⊥ = wmFullVertexMaximal` and `⊤ = wmFullVertexMinimal`

Convention: `v ≤ w` means `v` is at least as expressive as `w`
(i.e. `v` has at least as many rules as `w`), following the
`ProbabilityVertex` convention in `HypercubeGSLTFunctor.lean`.
-/

namespace Mettapedia.OSLF.Framework.WMCalculusVertexOrder

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.DeclReducesPremises
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.WMCalculusLanguageDef
open Mettapedia.OSLF.Framework.WMCalculusContextClosure
open Mettapedia.OSLF.Framework.HypercubeGSLTFunctor
open Mettapedia.OSLF.Framework.LangMorphism
open Mettapedia.OSLF.Framework.PLNWMHypercubeBasis

/-! ## §1: Per-Axis Rule Subset Monotonicity -/

theorem overlapRules_subset_of_le {a b : WMOverlapMode} (h : a ≤ b) :
    ∀ r ∈ overlapRules b, r ∈ overlapRules a := by
  cases a <;> cases b <;> simp_all [LE.le, overlapRules]

theorem forgettingRules_subset_of_le {a b : WMForgettingMode} (h : a ≤ b) :
    ∀ r ∈ forgettingRules b, r ∈ forgettingRules a := by
  cases a <;> cases b <;> simp_all [LE.le, forgettingRules]

theorem supportTrackedRules_subset_of_le {a b : WMForgettingMode} (h : a ≤ b) :
    ∀ r ∈ supportTrackedRules b, r ∈ supportTrackedRules a := by
  cases a <;> cases b <;> simp_all [LE.le, supportTrackedRules]

theorem provenanceRules_subset_of_le {a b : WMProvenanceMode} (h : a ≤ b) :
    ∀ r ∈ provenanceRules b, r ∈ provenanceRules a := by
  cases a <;> cases b <;> simp_all [LE.le, provenanceRules]

theorem fixpointRules_subset_of_le {a b : WMFixpointMode} (h : a ≤ b) :
    ∀ r ∈ fixpointRules b, r ∈ fixpointRules a := by
  cases a <;> cases b <;> simp_all [LE.le, fixpointRules]

theorem costRules_subset_of_le {a b : WMCostMode} (h : a ≤ b) :
    ∀ r ∈ costRules b, r ∈ costRules a := by
  cases a <;> cases b <;> simp_all [LE.le, costRules]

theorem conservationRules_subset_of_le {a b : WMConservationMode} (h : a ≤ b) :
    ∀ r ∈ conservationRules b, r ∈ conservationRules a := by
  cases a <;> cases b <;> simp_all [LE.le, conservationRules]

theorem experimentRules_subset_of_le {a b : WMExperimentMode} (h : a ≤ b) :
    ∀ r ∈ experimentRules b, r ∈ experimentRules a := by
  cases a <;> cases b <;> simp_all [LE.le, experimentRules]

theorem kripkeRules_subset_of_le {a b : WMKripkeMode} (h : a ≤ b) :
    ∀ r ∈ kripkeRules b, r ∈ kripkeRules a := by
  cases a <;> cases b <;> simp_all [LE.le, kripkeRules]

theorem carrierRules_subset_of_le {a b : WMCarrierMode} (h : a ≤ b) :
    ∀ r ∈ carrierRules b, r ∈ carrierRules a := by
  cases a <;> cases b <;> simp_all [LE.le, carrierRules]

/-! ## §2: Base Axis Vacuity -/

private theorem logicRules_nil (x : WMLogic) : logicRules x = [] := by cases x <;> rfl
private theorem tvRules_nil (x : WMTruthValue) : tvRules x = [] := by cases x <;> rfl
private theorem intervalRules_nil (x : WMIntervalSemantics) : intervalRules x = [] := by
  cases x <;> rfl
private theorem typingRules_nil (x : WMQueryTyping) : typingRules x = [] := by cases x <;> rfl

/-! ## §3: Full Vertex Rule Subset Theorem -/

/-- Rewrite rules of a weaker full vertex are a subset of a stronger one.
    `v ≤ w` means `v` has at least as many rules as `w`. -/
theorem wmFullVertexRules_subset_of_le {v w : WMFullVertex} (h : v ≤ w) :
    ∀ r ∈ (wmFullVertexLanguageDef w).rewrites,
      r ∈ (wmFullVertexLanguageDef v).rewrites := by
  intro r hr
  simp only [wmFullVertexLanguageDef,
    logicRules_nil, tvRules_nil, intervalRules_nil, typingRules_nil,
    List.mem_append] at hr ⊢
  obtain ⟨ho, hf, hp, hfp, hco, hcon, he, hk, hca⟩ := h
  -- Split the left-nested 11-disjunct Or stepwise
  rcases hr with hr | hcar
  · rcases hr with hr | hkri
    · rcases hr with hr | hexp
      · rcases hr with hr | hcons
        · rcases hr with hr | hcost
          · rcases hr with hr | hfix
            · rcases hr with hr | hprov
              · rcases hr with hr | hsup
                · rcases hr with hr | hfgt
                  · rcases hr with hcore | hovr
                    · exact .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl hcore)))))))))
                    · exact .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl
                        (.inr (overlapRules_subset_of_le ho r hovr))))))))))
                  · exact .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl
                      (.inr (forgettingRules_subset_of_le hf r hfgt)))))))))
                · exact .inl (.inl (.inl (.inl (.inl (.inl (.inl
                    (.inr (supportTrackedRules_subset_of_le hf r hsup))))))))
              · exact .inl (.inl (.inl (.inl (.inl (.inl
                  (.inr (provenanceRules_subset_of_le hp r hprov)))))))
            · exact .inl (.inl (.inl (.inl (.inl
                (.inr (fixpointRules_subset_of_le hfp r hfix))))))
          · exact .inl (.inl (.inl (.inl
              (.inr (costRules_subset_of_le hco r hcost)))))
        · exact .inl (.inl (.inl
            (.inr (conservationRules_subset_of_le hcon r hcons))))
      · exact .inl (.inl (.inr (experimentRules_subset_of_le he r hexp)))
    · exact .inl (.inr (kripkeRules_subset_of_le hk r hkri))
  · exact .inr (carrierRules_subset_of_le hca r hcar)

/-- Rewrite rules subset for extended (6-axis) vertex. -/
theorem wmExtVertexRules_subset_of_le {v w : WMExtVertex} (h : v ≤ w) :
    ∀ r ∈ (wmExtVertexLanguageDef w).rewrites,
      r ∈ (wmExtVertexLanguageDef v).rewrites := by
  intro r hr
  simp only [wmExtVertexLanguageDef,
    logicRules_nil, tvRules_nil, intervalRules_nil, typingRules_nil,
    List.mem_append] at hr ⊢
  obtain ⟨ho, hf⟩ := h
  rcases hr with ((hcore | hovr) | hfgt)
  · exact .inl (.inl hcore)
  · exact .inl (.inr (overlapRules_subset_of_le ho r hovr))
  · exact .inr (forgettingRules_subset_of_le hf r hfgt)

/-! ## §3: Reduction Monotonicity -/

/-- Single-step reduction is monotone along the WM full vertex weakness order. -/
theorem wmLangReduces_mono_fullVertex {v w : WMFullVertex} (h : v ≤ w)
    {p q : Pattern}
    (hred : langReduces (wmFullVertexLanguageDef w) p q) :
    langReduces (wmFullVertexLanguageDef v) p q := by
  unfold langReduces langReducesUsing at hred ⊢
  exact declReduces_mono (wmFullVertexRules_subset_of_le h) rfl hred

/-- Multi-step reduction is monotone along the WM full vertex weakness order. -/
theorem wmLangReducesStar_mono_fullVertex {v w : WMFullVertex} (h : v ≤ w)
    {p q : Pattern}
    (hred : LangReducesStar (wmFullVertexLanguageDef w) p q) :
    LangReducesStar (wmFullVertexLanguageDef v) p q := by
  induction hred with
  | refl _ => exact .refl _
  | step h_pq _ ih => exact .step (wmLangReduces_mono_fullVertex h h_pq) ih

/-- Single-step reduction monotonicity for 6-axis vertex. -/
theorem wmLangReduces_mono_extVertex {v w : WMExtVertex} (h : v ≤ w)
    {p q : Pattern}
    (hred : langReduces (wmExtVertexLanguageDef w) p q) :
    langReduces (wmExtVertexLanguageDef v) p q := by
  unfold langReduces langReducesUsing at hred ⊢
  exact declReduces_mono (wmExtVertexRules_subset_of_le h) rfl hred

/-- Multi-step reduction monotonicity for 6-axis vertex. -/
theorem wmLangReducesStar_mono_extVertex {v w : WMExtVertex} (h : v ≤ w)
    {p q : Pattern}
    (hred : LangReducesStar (wmExtVertexLanguageDef w) p q) :
    LangReducesStar (wmExtVertexLanguageDef v) p q := by
  induction hred with
  | refl _ => exact .refl _
  | step h_pq _ ih => exact .step (wmLangReduces_mono_extVertex h h_pq) ih

/-! ## §4: Forward Morphism and Forward Fiber -/

/-- Identity forward morphism along WM full vertex weakness edges.
    Since `v ≤ w` means `v` has at least as many rules, reductions in `w`
    (fewer rules) are valid in `v` (more rules), so `mapTerm = id`. -/
def wmWeaknessForwardMorphism_full {v w : WMFullVertex} (h : v ≤ w) :
    ForwardMorphism (wmFullVertexLanguageDef w) (wmFullVertexLanguageDef v) where
  mapTerm := id
  forward_sim _ q hred := ⟨q, .single (wmLangReduces_mono_fullVertex h hred), rfl⟩

/-- The WM forward fiber over the full vertex preorder.
    Each vertex gets its `LanguageDef`; weakness edges induce identity
    forward morphisms via rule-set monotonicity. -/
def wmFullForwardFiber : ForwardFiber WMFullVertex where
  lang := wmFullVertexLanguageDef
  morph h := wmWeaknessForwardMorphism_full h

/-- Forward transport along the WM full vertex weakness order. -/
theorem wm_full_forward_transport {v w : WMFullVertex} (h : v ≤ w)
    {p q : Pattern}
    (hred : LangReducesStar (wmFullVertexLanguageDef w) p q) :
    LangReducesStar (wmFullVertexLanguageDef v) p q :=
  wmLangReducesStar_mono_fullVertex h hred

/-- Identity forward morphism for 6-axis vertex. -/
def wmWeaknessForwardMorphism_ext {v w : WMExtVertex} (h : v ≤ w) :
    ForwardMorphism (wmExtVertexLanguageDef w) (wmExtVertexLanguageDef v) where
  mapTerm := id
  forward_sim _ q hred := ⟨q, .single (wmLangReduces_mono_extVertex h hred), rfl⟩

/-- The WM forward fiber over the ext vertex preorder. -/
def wmExtForwardFiber : ForwardFiber WMExtVertex where
  lang := wmExtVertexLanguageDef
  morph h := wmWeaknessForwardMorphism_ext h

/-- Forward transport for 6-axis vertex. -/
theorem wm_ext_forward_transport {v w : WMExtVertex} (h : v ≤ w)
    {p q : Pattern}
    (hred : LangReducesStar (wmExtVertexLanguageDef w) p q) :
    LangReducesStar (wmExtVertexLanguageDef v) p q :=
  wmLangReducesStar_mono_extVertex h hred

/-! ## §5: Bounded Order -/

/-- The maximal full vertex (36 rules) is the bottom of the weakness order. -/
theorem wmFullVertexMaximal_le (w : WMFullVertex) : wmFullVertexMaximal ≤ w := by
  simp only [LE.le, wmFullVertexMaximal]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (cases w; rename_i _ o f p fp co con e k ca) <;>
    first | (cases o <;> trivial) | (cases f <;> trivial) | (cases p <;> trivial) |
            (cases fp <;> trivial) | (cases co <;> trivial) | (cases con <;> trivial) |
            (cases e <;> trivial) | (cases k <;> trivial) | (cases ca <;> trivial)

/-- The minimal full vertex (5 rules, core only) is the top of the weakness order. -/
theorem wmFullVertex_le_minimal (v : WMFullVertex) : v ≤ wmFullVertexMinimal := by
  simp only [LE.le, wmFullVertexMinimal]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (cases v; rename_i _ o f p fp co con e k ca) <;>
    first | (cases o <;> trivial) | (cases f <;> trivial) | (cases p <;> trivial) |
            (cases fp <;> trivial) | (cases co <;> trivial) | (cases con <;> trivial) |
            (cases e <;> trivial) | (cases k <;> trivial) | (cases ca <;> trivial)

end Mettapedia.OSLF.Framework.WMCalculusVertexOrder
