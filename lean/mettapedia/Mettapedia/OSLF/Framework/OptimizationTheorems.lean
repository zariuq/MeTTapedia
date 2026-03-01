import Mettapedia.OSLF.Framework.TypeSynthesis
import Mettapedia.OSLF.Framework.HypercubeGSLTFunctor
import Mettapedia.OSLF.Framework.BeckChevalleyOSLF

/-!
# OSLF Optimization Theorems

Formally verified theorems that justify engine optimization decisions for
mettail-rust.  Each theorem certifies that a specific optimization preserves
the semantics of the OSLF type system.

## Theorems

| Theorem | Optimization |
|---------|-------------|
| `diamond_false_early_termination` | Skip successor exploration when ¬◇φ |
| `box_memoization_safe` | Memoize □-typed predecessors |
| `deterministic_diamond_collapse` | Direct-dispatch when reduction is unique |
| `specialization_preserves_reduction` | Specialize rules to stronger fragments (all languages, incl. premise-driven) |
| `substitution_reduction_fusion` | Fuse substitution + reduction passes (Beck-Chevalley) |

## References

- Meredith & Stay, "Operational Semantics in Logical Form" §4, §6
- Williams & Stay, "Native Type Theory" (ACT 2021) §3
-/

namespace Mettapedia.OSLF.Framework.OptimizationTheorems

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.DeclReducesPremises (DeclReducesWithPremises)
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.HypercubeGSLTFunctor

/-! ## §1: Early Termination via Diamond Falsity

If `¬ ◇φ p` (no successor of `p` satisfies `φ`), the engine can prune the
entire search subtree rooted at `p` without exploring any successors. -/

/-- If no reduction of `p` satisfies `φ`, every individual successor fails `φ`.
    The engine can skip exploring `p`'s successors for `φ`. -/
theorem diamond_false_early_termination (relEnv : RelationEnv) (lang : LanguageDef)
    (φ : Pattern → Prop) (p : Pattern)
    (h : ¬ langDiamondUsing relEnv lang φ p) :
    ∀ q, langReducesUsing relEnv lang p q → ¬ φ q := by
  intro q hred hφ
  exact h ((langDiamondUsing_spec relEnv lang φ p).mpr ⟨q, hred, hφ⟩)

/-! ## §2: Box Memoization Safety

If `□φ p` holds (all predecessors of `p` satisfy `φ`), the engine can
memoize this fact: any term reducing TO `p` is guaranteed to satisfy `φ`.
No re-checking needed. -/

/-- If all predecessors of `p` satisfy `φ`, any specific predecessor satisfies `φ`.
    The engine can safely memoize `□φ` results. -/
theorem box_memoization_safe (relEnv : RelationEnv) (lang : LanguageDef)
    (φ : Pattern → Prop) (p : Pattern)
    (h : langBoxUsing relEnv lang φ p) :
    ∀ q, langReducesUsing relEnv lang q p → φ q :=
  (langBoxUsing_spec relEnv lang φ p).mp h

/-! ## §3: Deterministic Reduction Collapse

When reduction at `p` is deterministic (unique successor `q`), the modal
diamond collapses: `◇φ p ↔ φ q`. The engine can use direct-dispatch
instead of search. -/

/-- If reduction at `p` is deterministic (unique successor `q`), then
    `◇φ p ↔ φ q`. The engine can skip search and direct-dispatch to `q`. -/
theorem deterministic_diamond_collapse (relEnv : RelationEnv) (lang : LanguageDef)
    (φ : Pattern → Prop) (p q : Pattern)
    (hred : langReducesUsing relEnv lang p q)
    (hdet : ∀ q', langReducesUsing relEnv lang p q' → q' = q) :
    langDiamondUsing relEnv lang φ p ↔ φ q := by
  rw [langDiamondUsing_spec]
  constructor
  · rintro ⟨q', hred', hφ⟩
    exact hdet q' hred' ▸ hφ
  · intro hφ
    exact ⟨q, hred, hφ⟩

/-- Corollary: deterministic reduction also collapses □.
    `□φ p ↔ (∀ q, langReducesUsing relEnv lang q p → φ q)` is already the
    spec, but in the deterministic-predecessor case we get a simpler form. -/
theorem deterministic_box_collapse (relEnv : RelationEnv) (lang : LanguageDef)
    (φ : Pattern → Prop) (p q : Pattern)
    (hred : langReducesUsing relEnv lang q p)
    (hdet : ∀ q', langReducesUsing relEnv lang q' p → q' = q) :
    langBoxUsing relEnv lang φ p ↔ φ q := by
  rw [langBoxUsing_spec]
  constructor
  · intro h; exact h q hred
  · intro hφ q' hred'
    exact hdet q' hred' ▸ hφ

/-! ## §4: Specialization Preserves Reduction (Monotonicity)

If a term reduces in a weaker language (fewer rules), it reduces in any
stronger language (more rules). The engine can specialize rules to stronger
fragments without re-checking reductions established in weaker fragments. -/

/-- Reduction is monotone in the rule set: if `lang₁`'s rules are a subset
    of `lang₂`'s rules (with matching congruence collections), then any
    reduction in `lang₁` is also a reduction in `lang₂`.

    The engine can safely specialize rules to stronger fragments.
    This holds for ALL languages, including those with premise-driven rules
    (eqnLookup, typeOf, cast, groundedCall). -/
theorem specialization_preserves_reduction
    {lang₁ lang₂ : LanguageDef}
    (hrules : ∀ r, r ∈ lang₁.rewrites → r ∈ lang₂.rewrites)
    (hcong : lang₁.congruenceCollections = lang₂.congruenceCollections)
    {p q : Pattern}
    (hred : langReducesUsing RelationEnv.empty lang₁ p q) :
    langReducesUsing RelationEnv.empty lang₂ p q :=
  declReduces_mono hrules hcong hred

/-- Diamond is monotone in the rule set: if `lang₁ ⊆ lang₂` (with matching
    congruence collections), then `◇₁φ ≤ ◇₂φ`.

    The engine can lift diamond-witnesses from weaker fragments. -/
theorem diamond_mono_rules
    {lang₁ lang₂ : LanguageDef}
    (hrules : ∀ r, r ∈ lang₁.rewrites → r ∈ lang₂.rewrites)
    (hcong : lang₁.congruenceCollections = lang₂.congruenceCollections)
    (φ : Pattern → Prop) (p : Pattern)
    (h : langDiamondUsing RelationEnv.empty lang₁ φ p) :
    langDiamondUsing RelationEnv.empty lang₂ φ p := by
  rw [langDiamondUsing_spec] at h ⊢
  obtain ⟨q, hred, hφ⟩ := h
  exact ⟨q, specialization_preserves_reduction hrules hcong hred, hφ⟩

/-- Box is contravariant in the rule set: `◇₁ ≤ ◇₂` implies `□₂ ≤ □₁`.

    This follows from the Galois connection: if the left adjoint grows,
    the right adjoint shrinks.  The engine can weaken box-guarantees when
    moving to a stronger language. -/
theorem box_contra_rules
    {lang₁ lang₂ : LanguageDef}
    (hrules : ∀ r, r ∈ lang₁.rewrites → r ∈ lang₂.rewrites)
    (hcong : lang₁.congruenceCollections = lang₂.congruenceCollections)
    (φ : Pattern → Prop) (p : Pattern)
    (h : langBoxUsing RelationEnv.empty lang₂ φ p) :
    langBoxUsing RelationEnv.empty lang₁ φ p := by
  rw [langBoxUsing_spec] at h ⊢
  intro q hred
  exact h q (specialization_preserves_reduction hrules hcong hred)

/-! ## §5: Substitution-Reduction Fusion (Beck-Chevalley)

The COMM substitution and reduction compose via Beck-Chevalley:
`∃_σ ∘ ◇ ⊣ □ ∘ σ*`. This means the engine can fuse substitution and
reduction passes into a single traversal. -/

/-- Substitution-reduction fusion: the Galois connection `∃_σ ∘ ◇ ⊣ □ ∘ σ*`
    is formally established for the COMM substitution.

    This justifies fusing substitution + reduction passes in the engine:
    instead of (1) substitute then (2) search for diamond, the engine can
    process both in a single traversal.

    Re-exported from BeckChevalleyOSLF for the optimization-theorem API. -/
theorem substitution_reduction_fusion (lang : LanguageDef) (q : Pattern) :
    GaloisConnection
      (BeckChevalleyOSLF.commDi q ∘ langDiamond lang)
      (langBox lang ∘ BeckChevalleyOSLF.commPb q) :=
  BeckChevalleyOSLF.commDi_diamond_galois lang q

/-! ## §6: Galois Connection Composition

The general theorem: composing two Galois connections yields a Galois
connection. This is the workhorse behind substitution-reduction fusion
and any future adjoint-based optimizations.

Re-exported from BeckChevalleyOSLF for the optimization-theorem API. -/

/-- Composing Galois connections: if `l₁ ⊣ u₁` and `l₂ ⊣ u₂`, then
    `l₂ ∘ l₁ ⊣ u₁ ∘ u₂`.  The engine can chain any sequence of
    adjoint-based passes without breaking the overall Galois connection. -/
theorem galois_composition [Preorder α] [Preorder β] [Preorder γ]
    {l₁ : α → β} {u₁ : β → α} {l₂ : β → γ} {u₂ : γ → β}
    (gc₁ : GaloisConnection l₁ u₁) (gc₂ : GaloisConnection l₂ u₂) :
    GaloisConnection (l₂ ∘ l₁) (u₁ ∘ u₂) :=
  BeckChevalleyOSLF.galoisConnection_comp gc₁ gc₂

/-! ## Summary

**0 sorries. 0 axioms.**

All theorems follow from existing proven infrastructure:
- `langDiamondUsing_spec` / `langBoxUsing_spec` (TypeSynthesis.lean)
- `declReduces_mono` (HypercubeGSLTFunctor.lean)
- `commDi_diamond_galois` / `galoisConnection_comp` (BeckChevalleyOSLF.lean)

**Engine optimization contracts:**
1. Early termination: skip search when ¬◇φ
2. Memoization: cache □-typed results
3. Direct-dispatch: skip search for deterministic reductions
4. Rule specialization: lift reductions across sub-languages
5. Pass fusion: fuse substitution + reduction via Beck-Chevalley
-/

end Mettapedia.OSLF.Framework.OptimizationTheorems
