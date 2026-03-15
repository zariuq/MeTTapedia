import Mettapedia.OSLF.Framework.HypercubeGSLTFunctor

/-!
# Bisimulation Morphisms and Fibers

Extends the forward-only GSLT morphism infrastructure with backward
simulation, giving full bisimulation morphisms and fibers.

## Relation to Meredith's Framework

In Lucius Gregory Meredith's "Computation, Causality, and Consciousness" (2026),
GSLT morphisms preserve bisimulation (Def 2.2).  Here we provide:
- `BackwardMorphism`: target reductions lift back to source
- `BisimulationMorphism`: both forward and backward
- `BisimulationFiber`: preorder-indexed family with bisimulation along edges
-/

namespace Mettapedia.OSLF.Framework.BisimulationFiber

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.LangMorphism
open Mettapedia.OSLF.Framework.HypercubeGSLTFunctor

/-! ## Backward Morphism -/

/-- A backward simulation morphism between two languages. -/
structure BackwardMorphism (L₁ L₂ : LanguageDef) where
  mapTerm : Pattern → Pattern
  backward_sim : ∀ p q, langReduces L₂ (mapTerm p) q →
    ∃ p', LangReducesStar L₁ p p' ∧ q = mapTerm p'

/-! ## Bisimulation Morphism -/

/-- A bisimulation morphism: both forward and backward simulation.
    The strict (`Eq`-based) variant of `LanguageMorphism`. -/
structure BisimulationMorphism (L₁ L₂ : LanguageDef) where
  mapTerm : Pattern → Pattern
  forward_sim : ∀ p q, langReduces L₁ p q →
    ∃ T, LangReducesStar L₂ (mapTerm p) T ∧ T = mapTerm q
  backward_sim : ∀ p q, langReduces L₂ (mapTerm p) q →
    ∃ p', LangReducesStar L₁ p p' ∧ q = mapTerm p'

/-- Extract the forward half. -/
def BisimulationMorphism.toForward (m : BisimulationMorphism L₁ L₂) :
    ForwardMorphism L₁ L₂ where
  mapTerm := m.mapTerm
  forward_sim := m.forward_sim

/-- Extract the backward half. -/
def BisimulationMorphism.toBackward (m : BisimulationMorphism L₁ L₂) :
    BackwardMorphism L₁ L₂ where
  mapTerm := m.mapTerm
  backward_sim := m.backward_sim

/-- Multi-step forward simulation. -/
theorem BisimulationMorphism.forward_multi
    (m : BisimulationMorphism L₁ L₂)
    {p q : Pattern} (h : LangReducesStar L₁ p q) :
    ∃ T, LangReducesStar L₂ (m.mapTerm p) T ∧ T = m.mapTerm q :=
  m.toForward.forward_multi h

/-- Multi-step backward simulation. -/
theorem BisimulationMorphism.backward_multi
    (m : BisimulationMorphism L₁ L₂)
    {p q : Pattern} (h : LangReducesStar L₂ (m.mapTerm p) q) :
    ∃ p', LangReducesStar L₁ p p' ∧ q = m.mapTerm p' := by
  generalize hstart : m.mapTerm p = mp at h
  induction h generalizing p with
  | refl _ => exact ⟨p, .refl _, hstart.symm⟩
  | step h_step _ ih =>
    subst hstart
    obtain ⟨p₁, h_star1, rfl⟩ := m.backward_sim _ _ h_step
    obtain ⟨p₂, h_star2, h_eq⟩ := @ih p₁ rfl
    exact ⟨p₂, h_star1.trans h_star2, h_eq⟩

/-! ## Identity Morphism -/

/-- The identity bisimulation morphism. -/
def BisimulationMorphism.idMorph (L : LanguageDef) :
    BisimulationMorphism L L where
  mapTerm := fun x => x
  forward_sim _ q h := ⟨q, .single h, rfl⟩
  backward_sim _ q h := ⟨q, .single h, rfl⟩

/-! ## Bisimulation Fiber -/

/-- A family of LanguageDefs indexed by a preorder with bisimulation morphisms
    along all weakness edges.  Full-strength version of `ForwardFiber`. -/
structure BisimulationFiber (V : Type*) [Preorder V] where
  lang : V → LanguageDef
  morph : ∀ {v w : V}, v ≤ w → BisimulationMorphism (lang w) (lang v)

/-- Every BisimulationFiber gives a ForwardFiber by forgetting backward sim. -/
def BisimulationFiber.toForwardFiber {V : Type*} [Preorder V]
    (F : BisimulationFiber V) : ForwardFiber V where
  lang := F.lang
  morph h := (F.morph h).toForward

/-- Forward transport via bisimulation fiber. -/
theorem BisimulationFiber.transport_forward {V : Type*} [Preorder V]
    (F : BisimulationFiber V) {v w : V} (h : v ≤ w)
    {p q : Pattern}
    (hred : LangReducesStar (F.lang w) p q) :
    ∃ q', LangReducesStar (F.lang v) ((F.morph h).mapTerm p) q' ∧
      q' = (F.morph h).mapTerm q :=
  (F.morph h).forward_multi hred

/-- Backward transport via bisimulation fiber. -/
theorem BisimulationFiber.transport_backward {V : Type*} [Preorder V]
    (F : BisimulationFiber V) {v w : V} (h : v ≤ w)
    {p : Pattern} {q : Pattern}
    (hred : LangReducesStar (F.lang v) ((F.morph h).mapTerm p) q) :
    ∃ p', LangReducesStar (F.lang w) p p' ∧
      q = (F.morph h).mapTerm p' :=
  (F.morph h).backward_multi hred

end Mettapedia.OSLF.Framework.BisimulationFiber
