import Mettapedia.OSLF.MeTTaIL.Syntax
import Mettapedia.OSLF.MeTTaIL.Substitution

/-!
# Structural Congruence for ρ-Calculus (Locally Nameless)

This file defines structural congruence for ρ-calculus processes,
following Meredith & Radestock (2005), "A Reflective Higher-order Calculus", page 4:

> "The structural congruence of processes, noted ≡, is the least congruence,
> **containing α-equivalence, ≡α**"

## Locally Nameless semantic boundary

Source patterns retain binder display names for diagnostics.  The generic
`LanguageDef` semantic boundary erases that metadata while de Bruijn indices
carry binding, so α-equivalence is **syntactic equality on admitted terms**.
This eliminates:
- `alphaRename` function (not needed)
- `allVars` / `isGloballyFresh` (not needed)
- Variable capture bugs (impossible by construction)

## Key Properties

1. **α-equivalence** (≡α): equality after generic binder-metadata erasure;
   syntactic equality on the admitted locally nameless carrier
2. **Structural congruence** (≡): Equality + parallel composition laws
3. **Quote respects structural equivalence** (page 7, STRUCT-EQUIV rule)

## References

- Meredith & Radestock (2005), pages 4-7
- Meredith & Stay, "Operational Semantics in Logical Form"
- Aydemir et al., "Engineering Formal Metatheory" (POPL 2008)
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution

/-! ## α-Equivalence

Bound variables use de Bruijn indices.  Raw patterns may retain source display
names, so generic α-equivalence compares their canonical erasures; admitted
semantic patterns already are those erasures.
-/

/-- α-equivalence for ρ-calculus processes.

This is the language-independent locally nameless alpha relation. -/
abbrev AlphaEquiv (p q : Pattern) : Prop := Pattern.AlphaEquiv p q

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

This is the least congruence containing semantic α-equivalence (2005 paper,
page 4).  Its carrier is the canonical locally nameless representation, where
the generic alpha relation is equality; the `alpha` constructor therefore
takes `p = q`.
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

  | lambda_cong (nm : Option String) (p q : Pattern) :
      StructuralCongruence p q →
      StructuralCongruence (.lambda nm p) (.lambda nm q)

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

  | multiLambda_cong (n : Nat) (nms : List String) (p q : Pattern) :
      StructuralCongruence p q →
      StructuralCongruence (.multiLambda n nms p) (.multiLambda n nms q)

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

  /-- ParEmpty: the empty parallel composition is nil.
      `[] ≡ PZero` — the missing base case of the `par_nil` family; an empty
      `hashBag` carries no process, so it is structurally congruent to `PZero`.
      This is the standard process-calculus law `0 | 0 | ... ≡ 0` at arity zero,
      and it is exactly what `stripSCWrappers` already assumes when it collapses
      an all-`PZero` bag to `PZero`. -/
  | par_empty :
      StructuralCongruence (.collection .hashBag [] none) (.apply "PZero" [])

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

/-- Generic alpha-equivalence implies structural congruence once both terms
have crossed the canonical semantic boundary. -/
theorem alpha_implies_struct {p q : Pattern}
    (pCanonical : p.hasCanonicalBinderMetadata = true)
    (qCanonical : q.hasCanonicalBinderMetadata = true) :
    (p ≡α q) → StructuralCongruence p q :=
  fun equivalent => StructuralCongruence.alpha p q
    ((Pattern.alphaEquiv_iff_eq_of_canonical pCanonical qCanonical).mp
      equivalent)

/-- Surface alpha-equivalence becomes structural congruence after selecting
the generic canonical representatives. -/
theorem alpha_implies_struct_after_erasure {p q : Pattern} :
    (p ≡α q) →
      StructuralCongruence p.eraseBinderMetadata q.eraseBinderMetadata :=
  fun equivalent => StructuralCongruence.alpha _ _ equivalent

/-- Quote respects structural congruence.

This is the STRUCT-EQUIV rule from page 7 of the 2005 paper.
-/
theorem quote_respects_structural {p q : Pattern} :
    StructuralCongruence p q → NameEquiv (.apply "NQuote" [p]) (.apply "NQuote" [q]) :=
  NameEquiv.struct_equiv p q

/-- Quote respects α-equivalence on admitted canonical terms. -/
theorem quote_respects_alpha {p q : Pattern}
    (pCanonical : p.hasCanonicalBinderMetadata = true)
    (qCanonical : q.hasCanonicalBinderMetadata = true) :
    (p ≡α q) → NameEquiv (.apply "NQuote" [p]) (.apply "NQuote" [q]) :=
  fun equivalent => quote_respects_structural
    (alpha_implies_struct pCanonical qCanonical equivalent)

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
