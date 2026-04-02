import Mettapedia.Languages.GF.OSLFBridge
import Mettapedia.Languages.GF.WorldModelVisibleBridge
import Mettapedia.Languages.GF.SemanticKernelConfluence
import Mettapedia.OSLF.Framework.CategoryBridge
import Mettapedia.OSLF.QuantifiedFormula2

/-!
# OSLF ◇ Composes with Quantifier Scope Ordering

The deep Tier 4 result: the OSLF modal operator ◇ (diamond) preserves
quantifier scope ordering via monotonicity of the Galois connection.

## Two independently-built systems

1. **OSLF semantic kernel** (44 rewrites in 11 families): ◇/□ via Galois connection
2. **VisibleLayer scope pipeline** (V1-V4): `scope_ordering_qsemE2` (∃∀ ≤ ∀∃)

## The composition theorem

If predicate φ ⊆ ψ pointwise (scope ordering), then ◇φ ⊆ ◇ψ (modal preserves ordering).

## Council

- Meredith, Stay: hypercube ◇ composes with quantifier semantics via monotonicity
- de Paiva: ◇ is a left adjoint, preserves ⊔, transports lattice inequalities
- Martin-Löf: quantifier scope is a type-theoretic choice; reduction preserves the ordering
- Bateson, Alexander: the pattern that connects operational theory to logical form
-/

namespace Mettapedia.Languages.GF.OSLFScopeComposition

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.CategoryBridge
open Mettapedia.OSLF.QuantifiedFormula2
open Mettapedia.Languages.GF.WorldModelVisibleBridge
open Mettapedia.Languages.GF.SemanticKernelConfluence

-- ═══════════════════════════════════════════════════════════════════
-- Section 1: ◇ preserves predicate entailment (monotonicity)
-- ═══════════════════════════════════════════════════════════════════

/-- ◇ preserves predicate entailment: if φ ⊆ ψ then ◇φ ⊆ ◇ψ. -/
theorem diamond_preserves_entailment (lang : LanguageDef)
    {φ ψ : Pattern → Prop} (h : ∀ p, φ p → ψ p) :
    ∀ p, langDiamond lang φ p → langDiamond lang ψ p :=
  langDiamond_monotone lang h

/-- □ preserves predicate entailment: if φ ⊆ ψ then □φ ⊆ □ψ. -/
theorem box_preserves_entailment (lang : LanguageDef)
    {φ ψ : Pattern → Prop} (h : ∀ p, φ p → ψ p) :
    ∀ p, langBox lang φ p → langBox lang ψ p :=
  langBox_monotone lang h

-- ═══════════════════════════════════════════════════════════════════
-- Section 2: ◇ composes with scope ordering (the deep result)
-- ═══════════════════════════════════════════════════════════════════

/-- **The composition theorem**: scope ordering lifts through ◇.

    If `scopeInverse p → scopeSurface p` for all p (the scope ordering),
    then `◇(scopeInverse) p → ◇(scopeSurface) p`.

    This means: when a scope-ambiguous sentence is embedded via EmbedS (◇),
    the evidence ordering of the two readings is preserved. The modal
    operator doesn't collapse or invert the scope preference. -/
theorem diamond_scope_composition (lang : LanguageDef)
    (scopeInverse scopeSurface : Pattern → Prop)
    (h_ordering : ∀ p, scopeInverse p → scopeSurface p) :
    ∀ p, langDiamond lang scopeInverse p → langDiamond lang scopeSurface p :=
  diamond_preserves_entailment lang h_ordering

/-- □ also composes with scope ordering. -/
theorem box_scope_composition (lang : LanguageDef)
    (scopeInverse scopeSurface : Pattern → Prop)
    (h_ordering : ∀ p, scopeInverse p → scopeSurface p) :
    ∀ p, langBox lang scopeInverse p → langBox lang scopeSurface p :=
  box_preserves_entailment lang h_ordering

-- ═══════════════════════════════════════════════════════════════════
-- Section 3: Concrete instantiation with QFormula2 evidence
-- ═══════════════════════════════════════════════════════════════════

/-- Scope ordering on evidence lifts through ◇ via threshold predicates.

    `scope_ordering_qsemE2` gives: `qsemE2(∃y.∀x.φ)(p) ≤ qsemE2(∀x.∃y.φ)(p)`.
    Combined with `diamond_scope_composition`, any scope-dependent property
    that holds at the inverse scope also holds at the surface scope,
    even after modal embedding via ◇. -/
theorem diamond_scope_evidence_monotone
    (lang : LanguageDef)
    (R : Pattern → Pattern → Prop) (I : QEvidenceAtomSem)
    (Dom : Domain2) (env : VarEnv2)
    {x y : String} (hne : x ≠ y) (φ : QFormula2)
    (P : _root_.Mettapedia.Logic.EvidenceQuantale.BinaryEvidence → Prop)
    (hP : Monotone P) :
    let invPred := fun p => P (qsemE2 R I Dom env (.qexists y (.qforall x φ)) p)
    let surfPred := fun p => P (qsemE2 R I Dom env (.qforall x (.qexists y φ)) p)
    ∀ p, langDiamond lang invPred p → langDiamond lang surfPred p := by
  intro invPred surfPred
  apply diamond_scope_composition
  intro p h_inv
  exact hP (scope_ordering_qsemE2 R I Dom env hne φ p) h_inv

-- ═══════════════════════════════════════════════════════════════════
-- Section 4: OSLF rewrites and V1 target disjoint subtrees
-- ═══════════════════════════════════════════════════════════════════

/-- Non-quantifier OSLF rewrites never touch DetCN nodes.

    V1 recognizes NP constructors (DetCN, UsePN, MassNP, UsePron).
    OSLF rewrites target non-NP constructors (UseCl, PredVP, UseN, EmbedS, etc.).
    No non-quantifier rewrite creates or destroys a DetCN node. -/
theorem non_quantifier_rewrites_preserve_detcn
    (ℓ : GFRewriteLabel)
    (hfam : labelFamily ℓ ≠ GFRewriteFamily.quantifier)
    (src tgt : Pattern)
    (hstep : GFTopStep ℓ src tgt) :
    ¬ (∃ det cn, src = .apply "DetCN" [det, cn]) := by
  intro ⟨det, cn, heq⟩
  cases hstep <;> simp [labelFamily] at hfam heq

/-- Quantifier rewrites target exactly DetCN heads. -/
theorem quantifier_rewrites_target_detcn
    (src tgt : Pattern)
    (h : ∃ ℓ, labelFamily ℓ = GFRewriteFamily.quantifier ∧ GFTopStep ℓ src tgt) :
    ∃ det cn, src = .apply "DetCN" [det, cn] := by
  obtain ⟨ℓ, hfam, hstep⟩ := h
  cases hstep <;> simp [labelFamily] at hfam <;> exact ⟨_, _, rfl⟩

end Mettapedia.Languages.GF.OSLFScopeComposition
