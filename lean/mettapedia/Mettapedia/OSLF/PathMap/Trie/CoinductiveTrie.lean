/-!
# Coinductive Trie — Canonical Semantics for PathMap

A `CTrie V` is the coinductive (infinite, lazy) semantic model for byte-indexed
tries, represented as its lookup function `List UInt8 → Option V`.  This is the
coalgebraic encoding: a CTrie IS its semantic content.

Operations (union, inter, diff, restrict) are defined pointwise and satisfy
algebraic laws up to **bisimilarity** (`Bisim`), which is extensional equality
on lookup.

This module is the *canonical truth* layer.  The finite inductive trie
(`FTrie`) is a refinement that embeds into `CTrie` via a structure-preserving
map (see `TrieRefinement.lean`).

## References

- Traytel et al., "Formal Languages, Formally and Coinductively" (FSCD 2016)
- Abel, "Formal Languages, Coinductively Formalized in Agda" (Ljubljana 2017)
- Brzozowski, "Derivatives of Regular Expressions" (1964)
-/

namespace Mettapedia.OSLF.PathMap.Trie

universe u

/-! ## §1: Core Type

The coalgebraic encoding: a CTrie IS its lookup function. -/

/-- A coinductive byte-indexed trie, represented as its lookup function.
    This is the Traytel/Abel coalgebraic encoding: a trie IS its membership
    predicate (lifted from `Bool` to `Option V`). -/
def CTrie (V : Type u) := List UInt8 → Option V

namespace CTrie

variable {V : Type u}

/-! ## §2: Basic Operations -/

/-- The everywhere-empty trie: no values anywhere. -/
def empty : CTrie V := fun _ => none

/-- Whether a path has any value (Bool-level membership). -/
def accepts (t : CTrie V) (p : List UInt8) : Bool := (t p).isSome

/-- The value at the root (empty path). -/
def val (t : CTrie V) : Option V := t []

/-- Brzozowski derivative: the subtrie at byte `b`. -/
def deriv (t : CTrie V) (b : UInt8) : CTrie V := fun p => t (b :: p)

/-! ## §3: Bisimilarity -/

/-- Two CTries are bisimilar when they agree on lookup at every path.
    Extensional equality — equivalent to coinductive bisimulation. -/
def Bisim (t₁ t₂ : CTrie V) : Prop := ∀ p, t₁ p = t₂ p

/-- Bisimilarity restricted to `accepts` (ignores which value is stored
    when both nodes have one — relevant for left-biased union). -/
def AcceptsBisim (t₁ t₂ : CTrie V) : Prop := ∀ p, t₁.accepts p = t₂.accepts p

theorem Bisim.refl (t : CTrie V) : Bisim t t := fun _ => rfl

theorem Bisim.symm {t₁ t₂ : CTrie V} (h : Bisim t₁ t₂) : Bisim t₂ t₁ :=
  fun p => (h p).symm

theorem Bisim.trans {t₁ t₂ t₃ : CTrie V} (h₁₂ : Bisim t₁ t₂) (h₂₃ : Bisim t₂ t₃) :
    Bisim t₁ t₃ := fun p => (h₁₂ p).trans (h₂₃ p)

theorem Bisim.to_acceptsBisim {t₁ t₂ : CTrie V} (h : Bisim t₁ t₂) :
    AcceptsBisim t₁ t₂ := fun p => by simp [accepts, h p]

/-! ## §4: Algebraic Operations -/

/-- Pointwise union.  Left-biased when both have values at the same path. -/
def union (t₁ t₂ : CTrie V) : CTrie V := fun p => t₁ p <|> t₂ p

/-- Pointwise intersection.  Keeps the left value when both are present. -/
def inter (t₁ t₂ : CTrie V) : CTrie V := fun p =>
  match t₁ p, t₂ p with | some v, some _ => some v | _, _ => none

/-- Pointwise difference.  Keeps left value only if right has none. -/
def diff (t₁ t₂ : CTrie V) : CTrie V := fun p =>
  match t₁ p, t₂ p with | some v, none => some v | _, _ => none

/-- Check if any prefix of `p` (including `[]`) maps to a value in `t`. -/
def hasPrefix (t : CTrie V) : List UInt8 → Bool
  | []      => (t []).isSome
  | b :: bs => (t []).isSome || hasPrefix (fun p => t (b :: p)) bs

/-- Prefix restriction: keep paths from `t₁` where some prefix is in `t₂`. -/
def restrict (t₁ t₂ : CTrie V) : CTrie V := fun p =>
  if t₂.hasPrefix p then t₁ p else none

/-! ## §5: Lookup Characterization

Operations are transparent (defined on the function representation),
so characterization is by `rfl` or simple case analysis. -/

theorem lookup_empty (p : List UInt8) : (empty : CTrie V) p = none := rfl

theorem accepts_empty (p : List UInt8) : (empty : CTrie V).accepts p = false := rfl

theorem lookup_union (t₁ t₂ : CTrie V) (p : List UInt8) :
    (union t₁ t₂) p = (t₁ p <|> t₂ p) := rfl

theorem lookup_inter (t₁ t₂ : CTrie V) (p : List UInt8) :
    (inter t₁ t₂) p =
      (match t₁ p, t₂ p with | some v, some _ => some v | _, _ => none) := rfl

theorem lookup_diff (t₁ t₂ : CTrie V) (p : List UInt8) :
    (diff t₁ t₂) p =
      (match t₁ p, t₂ p with | some v, none => some v | _, _ => none) := rfl

theorem deriv_eq (t : CTrie V) (b : UInt8) (p : List UInt8) :
    (t.deriv b) p = t (b :: p) := rfl

/-! ## §6: Algebraic Laws (up to Bisim)

All reduce to pointwise `Option` identities. -/

-- Union laws
theorem union_idem (t : CTrie V) : Bisim (union t t) t := by
  intro p; unfold union; cases t p <;> rfl

theorem union_empty_left (t : CTrie V) : Bisim (union empty t) t := fun _ => rfl

theorem union_empty_right (t : CTrie V) : Bisim (union t empty) t := by
  intro p; unfold union empty; cases t p <;> rfl

theorem union_assoc (t₁ t₂ t₃ : CTrie V) :
    Bisim (union (union t₁ t₂) t₃) (union t₁ (union t₂ t₃)) := by
  intro p; unfold union; cases t₁ p <;> rfl

theorem union_comm_accepts (t₁ t₂ : CTrie V) :
    AcceptsBisim (union t₁ t₂) (union t₂ t₁) := by
  intro p; simp [accepts, union]; cases t₁ p <;> cases t₂ p <;> rfl

-- Intersection laws
theorem inter_idem (t : CTrie V) : Bisim (inter t t) t := by
  intro p; unfold inter; cases t p <;> rfl

theorem inter_comm_accepts (t₁ t₂ : CTrie V) :
    AcceptsBisim (inter t₁ t₂) (inter t₂ t₁) := by
  intro p; simp [accepts, inter]; cases t₁ p <;> cases t₂ p <;> rfl

theorem inter_assoc (t₁ t₂ t₃ : CTrie V) :
    Bisim (inter (inter t₁ t₂) t₃) (inter t₁ (inter t₂ t₃)) := by
  intro p; unfold inter; cases t₁ p <;> cases t₂ p <;> cases t₃ p <;> rfl

theorem inter_empty_left (t : CTrie V) : Bisim (inter empty t) empty := fun _ => rfl

theorem inter_empty_right (t : CTrie V) : Bisim (inter t empty) empty := by
  intro p; unfold inter empty; cases t p <;> rfl

-- Absorption
theorem absorption (t s : CTrie V) : Bisim (union t (inter t s)) t := by
  intro p; unfold union inter; cases t p <;> rfl

-- Difference laws
theorem diff_empty_right (t : CTrie V) : Bisim (diff t empty) t := by
  intro p; unfold diff empty; cases t p <;> rfl

theorem diff_empty_left (t : CTrie V) : Bisim (diff empty t) empty := by
  intro p; unfold diff empty; cases t p <;> rfl

theorem diff_self (t : CTrie V) : Bisim (diff t t) empty := by
  intro p; unfold diff empty; cases t p <;> rfl

-- Restrict laws

/-- Helper: `hasPrefix` of a constant-none function is always false. -/
private theorem hasPrefix_const_none : ∀ (p : List UInt8),
    hasPrefix (fun (_ : List UInt8) => (none : Option V)) p = false := by
  intro p; induction p with
  | nil => rfl
  | cons _ _ ih => simp [hasPrefix, ih]

theorem restrict_empty_right (t : CTrie V) : Bisim (restrict t empty) empty := by
  intro p; unfold restrict empty
  have : hasPrefix (fun _ => (none : Option V)) p = false := hasPrefix_const_none p
  simp [this]

theorem restrict_empty_left (t : CTrie V) : Bisim (restrict empty t) empty := by
  intro p; unfold restrict empty; split <;> rfl

/-! ## §7: Distributivity -/

theorem inter_union_distrib (t₁ t₂ t₃ : CTrie V) :
    Bisim (inter t₁ (union t₂ t₃))
          (union (inter t₁ t₂) (inter t₁ t₃)) := by
  intro p; simp only [inter, union]
  cases t₁ p <;> cases t₂ p <;> cases t₃ p <;> rfl

/-! ## §8: Derivative Compatibility -/

theorem deriv_union (t₁ t₂ : CTrie V) (b : UInt8) :
    Bisim ((union t₁ t₂).deriv b) (union (t₁.deriv b) (t₂.deriv b)) :=
  fun _ => rfl

theorem deriv_inter (t₁ t₂ : CTrie V) (b : UInt8) :
    Bisim ((inter t₁ t₂).deriv b) (inter (t₁.deriv b) (t₂.deriv b)) :=
  fun _ => rfl

theorem deriv_diff (t₁ t₂ : CTrie V) (b : UInt8) :
    Bisim ((diff t₁ t₂).deriv b) (diff (t₁.deriv b) (t₂.deriv b)) :=
  fun _ => rfl

/-! ## §9: Summary

**0 sorries. 0 axioms.**

`CTrie V` provides the canonical coinductive semantics for byte-indexed tries.
All algebraic laws are proven up to `Bisim` (or `AcceptsBisim` for left-biased
operations).  The finite trie `FTrie` (see `FiniteTrie.lean`) embeds into
`CTrie` via a structure-preserving map.

The coalgebraic encoding (`CTrie V := List UInt8 → Option V`) makes all proofs
trivially pointwise — most are 1-2 lines of case analysis on `Option`.
-/

end CTrie

end Mettapedia.OSLF.PathMap.Trie
