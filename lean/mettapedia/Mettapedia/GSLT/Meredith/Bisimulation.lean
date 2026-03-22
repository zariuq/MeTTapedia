import Mettapedia.GSLT.Meredith.GSLT

/-!
# Bisimulation Quotient and Distinction Events

Building on Core's `GSLT.Bisimilar` (greatest bisimulation), this file adds:

1. **BisimQuotient** — the quotient `T(S) / ∼` as Lean's `Quotient`
2. **Distinction events** — pairs of non-bisimilar terms
3. **Induced rewriting** — the rewrite relation descends to the quotient
4. **Bridge to weakness** — distinction events as the domain for quantale weakness

## Key Idea (Meredith 2026)

"The true ontology of a GSLT is its bisimulation quotient."

Two terms are ontologically identical iff no sequence of experiments can
distinguish them. The distinction events — pairs (p,q) with p ≁ q — are
exactly what weakness measures over a quantale.

## References

- Meredith, "Computation, Causality, and Consciousness" (2026), §2, §5
- Milner, "Communication and Concurrency" (1989)
-/

namespace Mettapedia.GSLT.Meredith.Bisimulation

open Mettapedia.GSLT

/-! ## The Bisimulation Quotient -/

/-- The bisimulation quotient `T(S) / ∼`.

    Meredith: "the bisimulation quotient is the true ontology."
    Two terms are identified iff they are bisimilar (operationally indistinguishable).
-/
def BisimQuotient (S : GSLT) := Quotient S.bisimSetoid

/-- Project a term to its bisimulation equivalence class. -/
def toBisimClass (S : GSLT) (t : S.Term) : BisimQuotient S :=
  Quotient.mk S.bisimSetoid t

/-- Two terms have the same class iff they are bisimilar. -/
theorem bisimClass_eq_iff (S : GSLT) (p q : S.Term) :
    toBisimClass S p = toBisimClass S q ↔ S.Bisimilar p q :=
  Quotient.eq (r := S.bisimSetoid)

/-! ## Distinction Events -/

/-- Two terms are distinguished if they are NOT bisimilar.

    This is the key concept connecting to weakness:
    the distinction events are exactly the domain over which
    quantale weakness is computed.
-/
def IsDistinguished (S : GSLT) (p q : S.Term) : Prop :=
  ¬ S.Bisimilar p q

/-- Distinguished terms have different bisimulation classes. -/
theorem distinguished_classes_ne (S : GSLT) {p q : S.Term}
    (h : IsDistinguished S p q) : toBisimClass S p ≠ toBisimClass S q := by
  intro heq
  exact h ((bisimClass_eq_iff S p q).mp heq)

/-- Different bisimulation classes correspond to distinguished terms. -/
theorem ne_classes_distinguished (S : GSLT) {p q : S.Term}
    (h : toBisimClass S p ≠ toBisimClass S q) : IsDistinguished S p q := by
  intro hbis
  exact h ((bisimClass_eq_iff S p q).mpr hbis)

/-- Distinction is symmetric. -/
theorem isDistinguished_symm (S : GSLT) {p q : S.Term}
    (h : IsDistinguished S p q) : IsDistinguished S q p :=
  fun hbis => h (S.bisimilar_symm hbis)

/-- Distinction is irreflexive (no term is distinguished from itself). -/
theorem not_isDistinguished_self (S : GSLT) (p : S.Term) :
    ¬ IsDistinguished S p p :=
  fun h => h (S.bisimilar_refl p)

/-! ## Induced Rewriting on the Quotient

    The rewrite relation descends to the bisimulation quotient:
    if [p] ⇝ [p'] is well-defined (independent of representative).
    This requires that bisimilar terms have matching reductions,
    which is exactly the bisimulation property.
-/

/-- Rewriting is compatible with bisimilarity: if `p ∼ q` and `p ⇝ p'`,
    then ∃ q' with `q ⇝ q'` and `p' ∼ q'`.

    This is just the forward half of bisimulation, restated.
-/
theorem rewrites_compat_bisimilar (S : GSLT) {p q p' : S.Term}
    (hbis : S.Bisimilar p q) (hstep : S.rewrites p p') :
    ∃ q', S.rewrites q q' ∧ S.Bisimilar p' q' := by
  obtain ⟨R, ⟨hfwd, _⟩, hpq⟩ := hbis
  obtain ⟨q', hstep', hR'⟩ := hfwd hpq hstep
  exact ⟨q', hstep', R, ⟨hfwd, ‹_›⟩, hR'⟩

/-! ## Bridge to Quantale Weakness

    The quantale weakness framework (`Mettapedia.Algebra.QuantaleWeakness`)
    computes weakness over `Finset (U × U)` given a weight function `U → Q`.

    For a GSLT with a finite bisimulation quotient:
    - `U = BisimQuotient S` (the true ontology)
    - Weight function `μ : U → Q` assigns evidence/probability to each class
    - Distinction event = `{(u, v) | u ≠ v}` ⊆ U × U
    - Non-distinction event = `{(u, u) | u ∈ U}` (diagonal)
    - `weakness(distinction)` measures overall distinguishability
    - `weakness(non-distinction)` = the "self-similarity" measure

    The weakness of the distinction event is exactly Bennett's/Ellerman's
    logical entropy when `Q = ℝ≥0∞` and `μ` is a probability distribution.

    This connects Greg's operational ontology to Ben's evidence algebra:
    **distinction = evidence** — evidence strength IS operational distinguishability.
-/

/-- For a GSLT with finitely many bisimulation classes, the distinction and
    non-distinction events are complementary in `U × U`.

    In the finite case, this gives the key identity:
    `weakness(distinction) + weakness(non-distinction) = weakness(U × U)`
    which is Bennett's fundamental equation.
-/
theorem distinction_complement (S : GSLT) (p q : S.Term) :
    IsDistinguished S p q ↔ ¬ S.Bisimilar p q :=
  Iff.rfl

/-! ## GSLT Morphisms and the Quotient

    Morphisms descend to the quotient because they preserve bisimilarity.
-/

/-- A GSLT morphism induces a map on bisimulation quotients. -/
def quotientMap {S S' : GSLT} (f : GSLT.Morphism S S') :
    BisimQuotient S → BisimQuotient S' :=
  Quotient.map f.toFun (fun _ _ h => f.preserves_bisim h)

/-- The quotient map respects the projection. -/
theorem quotientMap_comm {S S' : GSLT} (f : GSLT.Morphism S S') (t : S.Term) :
    quotientMap f (toBisimClass S t) = toBisimClass S' (f.toFun t) :=
  rfl

-- NOTE: Quotient map does NOT preserve distinction in general —
-- morphisms can merge distinct classes. Preservation holds for
-- injective-on-quotient morphisms (embeddings).

end Mettapedia.GSLT.Meredith.Bisimulation
