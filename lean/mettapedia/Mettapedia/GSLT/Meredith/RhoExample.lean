import Mettapedia.GSLT.Meredith.GSLT
import Mettapedia.GSLT.Meredith.LambdaTheory
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence

/-!
# The ρ-Calculus as a GSLT Instance

This file exhibits the ρ-calculus as a concrete GSLT (Def 2.1) and sketches its
lambda theory (Def 4.1), connecting to the formalization in
`Mettapedia.Languages.ProcessCalculi.RhoCalculus`.

## The ρ-Calculus GSLT

- **Terms T**: MeTTaIL `Pattern` (covering processes and names)
- **Equations E**: Structural congruence `StructuralCongruence` (a ≡ relation
  with refl/symm/trans + commutative monoid laws for parallel composition)
- **Rewrites R**: Squashed `Reduces` (COMM + DROP + EQUIV), `Prop`-valued

## Key Rewrite Rules (§4.2)

- **COMM**: `{n!(q) | for(<-n){p} | rest} ⇝ {p[@q/x] | rest}`
- **DROP**: `*(@ p) ⇝ p`
- **EQUIV**: rewriting modulo structural congruence

## Connection to Lambda Theory (Def 4.1)

The λ-theory Tρ has (paper §4.2):
- Base types Pr, Nm
- Operations: 0, |, @, *, outₖ, inₖ
- Equations: (Pr, |, 0) commutative monoid + @(*n) = n
- Rewrite proposition: (⇝) ↪ Pr × Pr with COMM and DROP as base rewrites
- Rewrite operations: congruence for |

## References

- Stay, Meredith & Wells, "Generating Hypercubes of Type Systems" (2026), §4.2
- Meredith & Radestock, "A Reflective Higher-Order Calculus" (2005)
- Meredith, "Computation, Causality, and Consciousness" (2026), §2
-/

namespace Mettapedia.GSLT.Meredith.RhoExample

open Mettapedia.GSLT
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction
open Mettapedia.OSLF.MeTTaIL.Syntax

/-! ## Step 1: StructuralCongruence as a Setoid -/

/-- Structural congruence is an equivalence relation.

    `StructuralCongruence` has explicit `refl`, `symm`, `trans` constructors,
    so it is an equivalence by construction.
-/
def rhoEquivSetoid : Setoid Pattern where
  r     := StructuralCongruence
  iseqv := {
    refl  := StructuralCongruence.refl
    symm  := fun h => StructuralCongruence.symm _ _ h
    trans := fun h1 h2 => StructuralCongruence.trans _ _ _ h1 h2
  }

/-! ## Step 2: The Rewrite Relation -/

/-- The one-step rewrite relation on ρ-calculus patterns.

    `Reduces` is `Type`-valued (data), so we squash to `Prop` via `Nonempty`.
    `p ⇝ q` holds iff there exists a `Reduces p q` derivation.
-/
def rhoRewrites (p q : Pattern) : Prop := Nonempty (Reduces p q)

/-! ## Step 3: Coherence Conditions -/

/-- Rewrite respects structural congruence on the left.

    If `t ≡ t'` (StructuralCongruence t t') and `t ⇝ u`, then `∃ u', t' ⇝ u' ∧ u ≡ u'`.

    Proof: use `u' = u`. Construct `Reduces t' u` via the `equiv` constructor:
      `Reduces.equiv (SC.symm h) (r : Reduces t u) (SC.refl u) : Reduces t' u`.
    The witness `u ≡ u` holds by `SC.refl`.
-/
theorem rhoRewrites_resp_left :
    ∀ {t t' u : Pattern},
      rhoEquivSetoid.r t t' → rhoRewrites t u →
      ∃ u', rhoRewrites t' u' ∧ rhoEquivSetoid.r u u' := by
  intro t t' u htt' ⟨r⟩
  exact ⟨u,
    ⟨Reduces.equiv (StructuralCongruence.symm _ _ htt') r (StructuralCongruence.refl _)⟩,
    StructuralCongruence.refl _⟩

/-- Rewrite respects structural congruence on the right.

    If `t ⇝ u` and `u ≡ u'`, then `t ⇝ u'`.

    Proof: `Reduces.equiv (SC.refl t) r huu' : Reduces t u'`.
-/
theorem rhoRewrites_resp_right :
    ∀ {t u u' : Pattern},
      rhoRewrites t u → rhoEquivSetoid.r u u' → rhoRewrites t u' := by
  intro t u u' ⟨r⟩ huu'
  exact ⟨Reduces.equiv (StructuralCongruence.refl _) r huu'⟩

/-! ## Step 4: The GSLT Instance -/

/-- The ρ-calculus as a GSLT.

    Definition 2.1 (Meredith 2026): S = (T, E, R) where:
    - T = `Pattern` (MeTTaIL patterns: processes, names, and quoted processes)
    - E = `StructuralCongruence` (commutative monoid for |, plus @(*n) = n)
    - R = `Nonempty (Reduces · ·)` (squashed COMM + DROP + EQUIV)

    The coherence conditions `rewrites_resp_left` and `rewrites_resp_right`
    are proved above using the `Reduces.equiv` constructor.
-/
def rhoGSLT : GSLT where
  Term              := Pattern
  equations         := rhoEquivSetoid
  rewrites          := rhoRewrites
  rewrites_resp_left  := rhoRewrites_resp_left
  rewrites_resp_right := rhoRewrites_resp_right

/-! ## Step 5: Key Terms and Reductions -/

/-- The nil process 0 : Pattern. -/
def nilProcess : Pattern := .apply "PZero" []

/-- A one-step COMM reduction (example).
    `{n!(q) | for(<-n){p}} ⇝ {commSubst p q}` -/
example (n q p : Pattern) :
    rhoGSLT.Step
      (.collection .hashBag [.apply "POutput" [n, q], .apply "PInput" [n, .lambda none p]] none)
      (.collection .hashBag [Mettapedia.OSLF.MeTTaIL.Substitution.commSubst p q] none) :=
  ⟨Reduces.comm⟩

/-- A DROP reduction example: `*(@ p) ⇝ p`. -/
example (p : Pattern) :
    rhoGSLT.Step (.apply "PDrop" [.apply "NQuote" [p]]) p :=
  ⟨Reduces.drop⟩

/-! ## Step 6: Connection to the Lambda Theory -/

/-- The rewrite relation of the rho GSLT as a GSLTHom-compatible type.
    This shows rhoGSLT participates in the GSLTHom category. -/
def rhoIdHom : GSLTHom rhoGSLT rhoGSLT := GSLTHom.id rhoGSLT

/-!
## Remark: Lambda Theory Connection (§4.2)

A full `LambdaTheory` instance for the ρ-calculus would require:
1. A category T with CCC structure whose objects include Pr (processes) and Nm (names)
2. A rewrite relation `T.rewriteRel` derived from `Reduces`
3. Naturality: `rewriteRel_nat` — the rewrite relation is stable under substitution

The flat GSLT `rhoGSLT` above captures the term-level dynamics.
The categorical lambda theory `Tρ` (§4.2) lives over the CCC of the ρ-calculus.
A full formalization of `Tρ` is left as future work.
-- TODO: construct LambdaTheory instance once CCC of rho-calculus is formalized
-/

end Mettapedia.GSLT.Meredith.RhoExample
