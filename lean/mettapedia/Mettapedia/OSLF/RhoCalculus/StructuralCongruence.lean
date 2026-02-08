import Mettapedia.OSLF.MeTTaIL.Syntax
import Mettapedia.OSLF.MeTTaIL.Substitution

/-!
# Structural Congruence for ρ-Calculus (Locally Nameless)

This file defines structural congruence for ρ-calculus processes,
following Meredith & Radestock (2005), "A Reflective Higher-order Calculus", page 4:

> "The structural congruence of processes, noted ≡, is the least congruence,
> **containing α-equivalence, ≡α**"

## Locally Nameless Simplification

In locally nameless representation, α-equivalence is **syntactic equality**.
Patterns that differ only in bound variable names are literally the same object
(de Bruijn indices have no names). This eliminates:
- `alphaRename` function (not needed)
- `allVars` / `isGloballyFresh` (not needed)
- Variable capture bugs (impossible by construction)

## Key Properties

1. **α-equivalence** (≡α): Syntactic equality in locally nameless
2. **Structural congruence** (≡): Equality + parallel composition laws
3. **Quote respects structural equivalence** (page 7, STRUCT-EQUIV rule)

## References

- Meredith & Radestock (2005), pages 4-7
- Meredith & Stay, "Operational Semantics in Logical Form"
- Aydemir et al., "Engineering Formal Metatheory" (POPL 2008)
-/

namespace Mettapedia.OSLF.RhoCalculus

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution

/-! ## α-Equivalence

In locally nameless representation, α-equivalence is syntactic equality.
Bound variables use de Bruijn indices (no names), so patterns that differ
only in bound variable names are literally identical.
-/

/-- α-equivalence for ρ-calculus processes.

In locally nameless, this is just `Eq`. Kept as an abbreviation for
documentation and compatibility with the paper's notation. -/
abbrev AlphaEquiv (p q : Pattern) : Prop := p = q

notation:50 p " ≡α " q => AlphaEquiv p q

/-! ## Structural Congruence

Structural congruence includes equality (α-equivalence in LN) plus laws for
parallel composition.

From Meredith & Radestock (2005), page 4:
```
P | 0 ≡ P ≡ 0 | P
P | Q ≡ Q | P
(P | Q) | R ≡ P | (Q | R)
```

In our MeTTaIL representation, parallel composition is:
`.collection .hashBag [P, Q, ...] none`
-/

/-- Structural congruence for ρ-calculus processes.

This is the least congruence containing α-equivalence (2005 paper, page 4).
In locally nameless, α-equivalence is Eq, so the `alpha` constructor takes `p = q`.
-/
inductive StructuralCongruence : Pattern → Pattern → Prop where
  | alpha (p q : Pattern) :
      p = q →
      StructuralCongruence p q

  | refl (p : Pattern) :
      StructuralCongruence p p

  | symm (p q : Pattern) :
      StructuralCongruence p q →
      StructuralCongruence q p

  | trans (p q r : Pattern) :
      StructuralCongruence p q →
      StructuralCongruence q r →
      StructuralCongruence p r

  | par_singleton (p : Pattern) :
      StructuralCongruence
        (.collection .hashBag [p] none)
        p

  | par_nil_left (p : Pattern) :
      StructuralCongruence
        (.collection .hashBag [.apply "PZero" [], p] none)
        p

  | par_nil_right (p : Pattern) :
      StructuralCongruence
        (.collection .hashBag [p, .apply "PZero" []] none)
        p

  | par_comm (p q : Pattern) :
      StructuralCongruence
        (.collection .hashBag [p, q] none)
        (.collection .hashBag [q, p] none)

  | par_assoc (p q r : Pattern) :
      StructuralCongruence
        (.collection .hashBag [.collection .hashBag [p, q] none, r] none)
        (.collection .hashBag [p, .collection .hashBag [q, r] none] none)

  | par_cong (ps qs : List Pattern) :
      (ps.length = qs.length) →
      (∀ i h₁ h₂, StructuralCongruence (ps.get ⟨i, h₁⟩) (qs.get ⟨i, h₂⟩)) →
      StructuralCongruence
        (.collection .hashBag ps none)
        (.collection .hashBag qs none)

  /-- Flattening: [ps..., [qs...]] ≡ [ps..., qs...]

      Derived from the paper's associativity law. In our flat representation,
      a nested parallel composition can always be flattened.
      Reference: Meredith & Radestock (2005), page 4, (P | Q) | R ≡ P | (Q | R)
  -/
  | par_flatten (ps qs : List Pattern) :
      StructuralCongruence
        (.collection .hashBag (ps ++ [.collection .hashBag qs none]) none)
        (.collection .hashBag (ps ++ qs) none)

  /-- Permutation: any reordering of parallel components preserves congruence.

      Paper justification: | is commutative and associative (page 4),
      so arbitrary permutations are valid. This subsumes par_comm.
  -/
  | par_perm (elems₁ elems₂ : List Pattern) :
      elems₁.Perm elems₂ →
      StructuralCongruence
        (.collection .hashBag elems₁ none)
        (.collection .hashBag elems₂ none)

  /-- Set permutation: any reordering of set elements preserves congruence.

      Paper justification: sets are unordered by definition.
      Parallel to `par_perm` for bags.
  -/
  | set_perm (elems₁ elems₂ : List Pattern) :
      elems₁.Perm elems₂ →
      StructuralCongruence
        (.collection .hashSet elems₁ none)
        (.collection .hashSet elems₂ none)

  /-- Set congruence: element-wise structural congruence.

      Parallel to `par_cong` for bags.
  -/
  | set_cong (elems₁ elems₂ : List Pattern) :
      (elems₁.length = elems₂.length) →
      (∀ i h₁ h₂, StructuralCongruence (elems₁.get ⟨i, h₁⟩) (elems₂.get ⟨i, h₂⟩)) →
      StructuralCongruence
        (.collection .hashSet elems₁ none)
        (.collection .hashSet elems₂ none)

  | lambda_cong (p q : Pattern) :
      StructuralCongruence p q →
      StructuralCongruence (.lambda p) (.lambda q)

  | apply_cong (f : String) (args₁ args₂ : List Pattern) :
      (args₁.length = args₂.length) →
      (∀ i h₁ h₂, StructuralCongruence (args₁.get ⟨i, h₁⟩) (args₂.get ⟨i, h₂⟩)) →
      StructuralCongruence (.apply f args₁) (.apply f args₂)

  /-- General collection congruence: element-wise SC for any collection type/guard.

      Subsumes par_cong (hashBag none) and set_cong (hashSet none) for the
      general case. Needed for rhoSubstitute_SC_arg on non-hashBag-none patterns.
  -/
  | collection_general_cong (ct : CollType) (elems₁ elems₂ : List Pattern)
      (g : Option String) :
      (elems₁.length = elems₂.length) →
      (∀ i h₁ h₂, StructuralCongruence (elems₁.get ⟨i, h₁⟩) (elems₂.get ⟨i, h₂⟩)) →
      StructuralCongruence (.collection ct elems₁ g) (.collection ct elems₂ g)

  | multiLambda_cong (n : Nat) (p q : Pattern) :
      StructuralCongruence p q →
      StructuralCongruence (.multiLambda n p) (.multiLambda n q)

  | subst_cong (p₁ p₂ : Pattern) (a₁ a₂ : Pattern) :
      StructuralCongruence p₁ p₂ →
      StructuralCongruence a₁ a₂ →
      StructuralCongruence (.subst p₁ a₁) (.subst p₂ a₂)

  /-- QuoteDrop: @(*n) ≡ n
      MeTTaIL equation: (NQuote (PDrop N)) = N
      Reference: MeTTaIL spec, Section "equations"
  -/
  | quote_drop (n : Pattern) :
      StructuralCongruence (.apply "NQuote" [.apply "PDrop" [n]]) n

notation:50 p " ≡ " q => StructuralCongruence p q

/-! ## Derived Structural Rules -/

/-- Flattening lemma: nested 2-element bag can be flattened.

    [p, [q, r]] ≡ [p, q, r]
-/
theorem par_flatten_two (p q r : Pattern) :
    StructuralCongruence
      (.collection .hashBag [p, .collection .hashBag [q, r] none] none)
      (.collection .hashBag [p, q, r] none) :=
  StructuralCongruence.par_flatten [p] [q, r]

/-! ## Name Equivalence

From Meredith & Radestock (2005), page 7:

Names are quoted processes. Name equivalence is defined by:
```
⌜x⌝ ≡N x         (QUOTE-DROP)

P ≡ Q
─────────────    (STRUCT-EQUIV)
⌜P⌝ ≡N ⌜Q⌝
```
-/

/-- Name equivalence for ρ-calculus.

This respects structural congruence, including α-equivalence.
-/
inductive NameEquiv : Pattern → Pattern → Prop where
  /-- QuoteDrop for names: @(*n) ≡N n -/
  | quote_drop (n : Pattern) :
      NameEquiv (.apply "NQuote" [.apply "PDrop" [n]]) n

  /-- Reflexivity -/
  | refl (n : Pattern) :
      NameEquiv n n

  | struct_equiv (p q : Pattern) :
      StructuralCongruence p q →
      NameEquiv (.apply "NQuote" [p]) (.apply "NQuote" [q])

  | symm (x y : Pattern) :
      NameEquiv x y →
      NameEquiv y x

  | trans (x y z : Pattern) :
      NameEquiv x y →
      NameEquiv y z →
      NameEquiv x z

notation:50 x " ≡N " y => NameEquiv x y

/-! ## Key Theorems -/

/-- Structural congruence is an equivalence relation -/
theorem structuralCongruence_equivalence : Equivalence StructuralCongruence where
  refl := @StructuralCongruence.refl
  symm := @StructuralCongruence.symm
  trans := @StructuralCongruence.trans

/-- α-equivalence (= Eq in LN) implies structural congruence -/
theorem alpha_implies_struct {p q : Pattern} :
    p = q → StructuralCongruence p q :=
  fun h => StructuralCongruence.alpha p q h

/-- Quote respects structural congruence.

This is the STRUCT-EQUIV rule from page 7 of the 2005 paper.
-/
theorem quote_respects_structural {p q : Pattern} :
    StructuralCongruence p q → NameEquiv (.apply "NQuote" [p]) (.apply "NQuote" [q]) :=
  NameEquiv.struct_equiv p q

/-- Quote respects α-equivalence (trivial in LN since α-equiv = Eq) -/
theorem quote_respects_alpha {p q : Pattern} :
    p = q → NameEquiv (.apply "NQuote" [p]) (.apply "NQuote" [q]) :=
  fun h => quote_respects_structural (alpha_implies_struct h)

end Mettapedia.OSLF.RhoCalculus
