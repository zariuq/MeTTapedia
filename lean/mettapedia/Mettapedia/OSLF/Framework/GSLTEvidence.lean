import Mettapedia.OSLF.Framework.TypeSynthesis
import Mettapedia.Logic.EvidenceQuantale

/-!
# GSLT BinaryEvidence Assignment: The Universal Bridge

A GSLT (graph-structured lambda theory) equipped with parallel composition
has a natural evidence framework: count how many processes in an ensemble
satisfy or refute a given observable property.  This file defines the
abstract bridge structure that connects any GSLT to the WM evidence
framework.

## The Key Insight

`BinaryWorldModel(State, Query) ≅ AddMonoidHom(State, Query → BinaryEvidence)`

A world model is a single additive morphism into evidence profiles.
This holds for any value monoid V, not just BinaryEvidence:

- V = BinaryEvidence (ℝ≥0∞ × ℝ≥0∞): Bayesian counting (our WM-PLN case)
- V = ℂ: quantum amplitudes (L. Gregory Meredith's weight map)
- V = ℝ≥0: classical probability (Born rule shadow)

The `GSLTEvidenceAssignment` structure captures this uniformly.

## References

- L. Gregory Meredith, "Computation, Causality, and Consciousness" (2026)
  §6: The Weight Map and Lagrangian Structure
- GPT-5.4 Pro review: BinaryWorldModel ≅ AddMonoidHom(State, Query → BinaryEvidence)
-/

namespace Mettapedia.OSLF.Framework.GSLTEvidence

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Logic.EvidenceQuantale

/-! ## GSLT BinaryEvidence Assignment -/

/-- A GSLT evidence assignment: an additive morphism from process ensembles
    to value profiles, indexed by observable properties.

    This generalizes `BinaryWorldModel` from `BinaryEvidence` to any additive monoid V.
    When V = BinaryEvidence, this is exactly the WM-PLN evidence extraction.
    When V = ℂ, this is L. Gregory Meredith's weight map.

    The two axioms say:
    1. BinaryEvidence is additive over parallel composition (ensemble union).
    2. The empty ensemble has zero evidence for every query. -/
structure GSLTEvidenceAssignment (State : Type*) (Query : Type*) (V : Type*)
    [AddCommMonoid State] [AddCommMonoid V] where
  /-- Extract a value for a query from a state -/
  extract : State → Query → V
  /-- Extraction is additive over state composition -/
  extract_add : ∀ W₁ W₂ q, extract (W₁ + W₂) q = extract W₁ q + extract W₂ q
  /-- Zero state has zero value for every query -/
  extract_zero : ∀ q, extract 0 q = 0

/-- The bundled additive morphism: extract as an AddMonoidHom into profiles.
    This is GPT-5.4's key recasting:
    BinaryWorldModel(State, Query) ≅ AddMonoidHom(State, Query → V). -/
def GSLTEvidenceAssignment.toProfileHom
    {State Query V : Type*} [AddCommMonoid State] [AddCommMonoid V]
    (ea : GSLTEvidenceAssignment State Query V) :
    AddMonoidHom State (Query → V) where
  toFun W q := ea.extract W q
  map_zero' := by funext q; exact ea.extract_zero q
  map_add' W₁ W₂ := by funext q; exact ea.extract_add W₁ W₂ q

/-- Recover a GSLTEvidenceAssignment from a profile hom.
    This is the inverse direction of the equivalence. -/
def GSLTEvidenceAssignment.ofProfileHom
    {State Query V : Type*} [AddCommMonoid State] [AddCommMonoid V]
    (f : AddMonoidHom State (Query → V)) :
    GSLTEvidenceAssignment State Query V where
  extract W q := f W q
  extract_add W₁ W₂ q := by
    have := f.map_add W₁ W₂
    exact congrFun this q
  extract_zero q := by
    have := f.map_zero
    exact congrFun this q

/-! ## Terminal BinaryEvidence Profile

For any query type Q, the "joint evidence" profile `Q → V` is itself
a state type (with pointwise addition).  The identity extraction from
this state is the terminal evidence assignment: every other assignment
factors through it. -/

/-- The joint evidence profile: the terminal extensional world model.
    Every evidence assignment factors through this via its profile hom. -/
abbrev JointProfile (Query V : Type*) [AddCommMonoid V] := Query → V

/-- The canonical (identity) evidence assignment on the profile itself. -/
def canonicalAssignment (Query V : Type*) [AddCommMonoid V] :
    GSLTEvidenceAssignment (JointProfile Query V) Query V where
  extract f q := f q
  extract_add _ _ _ := rfl
  extract_zero _ := rfl

/-- Every evidence assignment factors through the canonical one via
    its profile hom.  This is the universal property:
    JointProfile is terminal in the category of evidence assignments. -/
theorem factors_through_canonical
    {State Query V : Type*} [AddCommMonoid State] [AddCommMonoid V]
    (ea : GSLTEvidenceAssignment State Query V)
    (W : State) (q : Query) :
    ea.extract W q = (canonicalAssignment Query V).extract (ea.toProfileHom W) q :=
  rfl

end Mettapedia.OSLF.Framework.GSLTEvidence
