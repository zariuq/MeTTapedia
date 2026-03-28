import Mettapedia.GSLT.Dynamics.WeightCost
import Mathlib.Data.Complex.Basic

/-!
# Finite-Support Path Integrals over GSLTs

This file formalizes the finite-support path-integral layer of Meredith's
"Computation, Causality, and Consciousness" (2026), Part I, §9.

## Main Definitions

* `AmplitudeWeightedGSLT` — Definition 9.1 specialized to complex amplitudes
* `rewritePathAppend` — concatenation of rewrite paths
* `FinitePathFamily` — a finite family of rewrite paths between two terms
* `transitionAmplitude` — finite-support transition amplitude (Definition 9.2)

## Design Note

The paper writes the transition amplitude as a sum over all paths from `P` to `Q`.
Constructively, that requires either a finite path space or an independent
summability theory.  This file therefore formalizes the finite-support version
first: amplitudes over an explicitly chosen finite family of rewrite paths.

This is the right small kernel for later work:
- global sums can be added once finiteness/summability hypotheses are explicit
- composition and multiplicativity are already available at the finite level

## References

- Meredith, "Computation, Causality, and Consciousness" (2026), §9
- Feynman & Hibbs, "Quantum Mechanics and Path Integrals"
-/

namespace Mettapedia.GSLT

/-- Definition 9.1: an amplitude-weighted GSLT is a weighted GSLT whose
    amplitude values are complex numbers. -/
abbrev AmplitudeWeightedGSLT (A : Type*) (k : Nat) := WeightedGSLT Complex A k

/-- Concatenation of rewrite paths. -/
def rewritePathAppend {S : GSLT} {t u v : S.Term} :
    S.RewritePath t u → S.RewritePath u v → S.RewritePath t v
  | .nil _, q => q
  | .cons h rest, q => .cons h (rewritePathAppend rest q)

/-- Path length is additive under concatenation. -/
theorem rewritePathLength_append {S : GSLT} {t u v : S.Term}
    (p : S.RewritePath t u) (q : S.RewritePath u v) :
    (rewritePathAppend p q).length = p.length + q.length := by
  induction p with
  | nil _ =>
      simp [rewritePathAppend, GSLT.RewritePath.length]
  | cons _ rest ih =>
      simp [rewritePathAppend, GSLT.RewritePath.length, ih, Nat.add_assoc]

/-- A finite family of rewrite paths from `t` to `u`.

    This is the constructive stand-in for the formal sum over all paths
    appearing in Definition 9.2. -/
abbrev FinitePathFamily (S : GSLT) (t u : S.Term) := List (S.RewritePath t u)

namespace FinitePathFamily

variable {S : GSLT}

/-- The empty path family. -/
def empty {t u : S.Term} : FinitePathFamily S t u := []

/-- A singleton path family. -/
def singleton {t u : S.Term} (p : S.RewritePath t u) : FinitePathFamily S t u := [p]

/-- Union of two finite path families is list concatenation. -/
def union {t u : S.Term}
    (Γ Δ : FinitePathFamily S t u) : FinitePathFamily S t u :=
  Γ ++ Δ

/-- Composition of path families by concatenating every left path with every right path. -/
def compose {t u v : S.Term}
    (Γ : FinitePathFamily S t u) (Δ : FinitePathFamily S u v) :
    FinitePathFamily S t v :=
  Γ.foldr (fun p acc => (Δ.map fun q => rewritePathAppend p q) ++ acc) []

end FinitePathFamily

/-- Definition 9.2: the finite-support transition amplitude is the sum of the
    amplitudes of all paths in the chosen finite support. -/
def transitionAmplitude {S : GSLT} {W : Type*} [Semiring W] (wm : WeightMap S W)
    {t u : S.Term} (Γ : FinitePathFamily S t u) : W :=
  (Γ.map (pathAmplitude wm)).sum

theorem pathAmplitude_append {W : Type*} [Monoid W] (wm : WeightMap S W)
    {t u v : S.Term} (p : S.RewritePath t u) (q : S.RewritePath u v) :
    pathAmplitude wm (rewritePathAppend p q) = pathAmplitude wm p * pathAmplitude wm q := by
  induction p with
  | nil _ =>
      simp [rewritePathAppend, pathAmplitude]
  | cons h rest ih =>
      simp [rewritePathAppend, pathAmplitude, ih, mul_assoc]

theorem transitionAmplitude_empty {W : Type*} [Semiring W] (wm : WeightMap S W)
    {t u : S.Term} :
    transitionAmplitude (S := S) wm (FinitePathFamily.empty (S := S) (t := t) (u := u)) = 0 := by
  simp [transitionAmplitude, FinitePathFamily.empty]

theorem transitionAmplitude_singleton {W : Type*} [Semiring W] (wm : WeightMap S W)
    {t u : S.Term} (p : S.RewritePath t u) :
    transitionAmplitude (S := S) wm (FinitePathFamily.singleton (S := S) p) = pathAmplitude wm p := by
  simp [transitionAmplitude, FinitePathFamily.singleton]

theorem transitionAmplitude_union {W : Type*} [Semiring W] (wm : WeightMap S W)
    {t u : S.Term} (Γ Δ : FinitePathFamily S t u) :
    transitionAmplitude (S := S) wm (FinitePathFamily.union Γ Δ) =
      transitionAmplitude (S := S) wm Γ + transitionAmplitude (S := S) wm Δ := by
  simp [transitionAmplitude, FinitePathFamily.union, List.map_append, List.sum_append]

/-! ## Summary

This file establishes:

1. **AmplitudeWeightedGSLT**: Definition 9.1 specialized to `Complex`
2. **rewritePathAppend**: Concatenation of rewrite paths
3. **pathAmplitude_append**: Path amplitudes multiply under concatenation
4. **FinitePathFamily**: Finite supports for constructive path sums
5. **transitionAmplitude**: Finite-support version of Definition 9.2
6. **transitionAmplitude_union**: Additivity under finite-support union

**Paper Coverage**: Definition 9.1; Definition 9.2 (finite-support form)

**No sorry statements** — everything is definitionally conservative over the
existing path and weight infrastructure.

**Next**: strengthen from finite supports to explicit summability hypotheses, or
move to the Theorem 10.1 conservation/interface layer.
-/

end Mettapedia.GSLT
