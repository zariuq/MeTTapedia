import Mettapedia.OSLF.MeTTaIL.Substitution
import Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts
import Provenance.Util.ValueTypeString
import Init.Data.List.Lemmas

/-!
# CeTTa Explicit Substitution Bridge

Builds a Pattern-side support model for a future relation between CeTTa's
runtime representation (skeleton + slot_env) and explicit-substitution
closures.

Proved here, on the Pattern-side model:
- `applySubst_untouched`: a substitution whose domain misses every free
  variable of a subst-free pattern is the identity on it. This is the
  general-environment form of `applySubst_fresh_single`.
- `materialize_untouched` / `materialize_trivial`: the closure-level
  corollaries.
- slot-name injectivity and the `enumFrom` support lemmas.

No Lean/C correspondence theorem is claimed anywhere in this file; the C
runtime names below are comparison targets only.

## CeTTa Runtime Analogy

CeTTa factors open terms into two parts:
- **skeleton**: A pattern with slot variables (de Bruijn-style private tags)
- **slot_env**: A substitution mapping slot ordinals to concrete terms

This has the shape of an **explicit substitution closure** ⟨M, σ⟩ from
Abadi et al. (1991). The analogy is not yet a proved correspondence between
the C representation and `Pattern`.

## Candidate Correspondences

| CeTTa (C runtime)       | Explicit-substitution analogy | This file           |
|-------------------------|-----------------------------|---------------------|
| `skeleton`              | M in ⟨M, σ⟩                 | `ExplicitClosure.skeleton` |
| `slot_env`              | σ (substitution)            | `ExplicitClosure.env`      |
| `materialize()`         | M[σ] (application)          | `materialize`              |
| `canonicalize()`        | closure creation            | `canonicalize`             |
| `VariantBank`           | canonical quotient          | (hash-consing, not here)   |

## References

- Abadi et al., "Explicit Substitutions", JFP 1991
- CeTTa: `hyperon/CeTTa/src/variant_shape.h`
- Roadmap: `../../../../papers/cetta_roadmap.tex` §8 (Dual-Target Architecture)
-/

namespace Mettapedia.Bridge.CeTTaExplicitSubst

open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.OSLF.MeTTaIL.Substitution
  (SubstEnv applySubst freeVars noExplicitSubst allNoExplicitSubst
   allNoExplicitSubst_mem subst_empty)

/-! ## §1: Explicit Closure (Layer 3 Representation)

An explicit closure pairs a skeleton pattern with a substitution environment.
It is the Pattern-side candidate used for comparison with CeTTa's
`VariantShape` struct. -/

/-- A Pattern-side **explicit closure** ⟨M, σ⟩. -/
structure ExplicitClosure where
  /-- The skeleton pattern with slot variables (de Bruijn-style). -/
  skeleton : Pattern
  /-- The substitution environment mapping slot names to terms. -/
  env : SubstEnv
  deriving Repr

namespace ExplicitClosure

/-- Create a trivial closure with empty environment. -/
def trivial (p : Pattern) : ExplicitClosure :=
  ⟨p, SubstEnv.empty⟩

/-- Check if the closure has an empty environment. -/
def isGround (c : ExplicitClosure) : Bool :=
  c.env.isEmpty

end ExplicitClosure

/-! ## §2: Materialize (Substitution Application)

Materialization applies the model's environment to its skeleton.

CeTTa's `variant_shape_materialize()` is the intended comparison target; no
Lean/C correspondence theorem is claimed here. -/

/-- **Materialize** an explicit closure by applying the substitution.
    `materialize(⟨M, σ⟩) = M[σ]`

    This is the core operation that connects Layer 3 to concrete terms. -/
def materialize (c : ExplicitClosure) : Pattern :=
  applySubst c.env c.skeleton

private theorem list_map_eq_self' {α : Type*} {f : α → α} {l : List α}
    (h : ∀ a ∈ l, f a = a) : l.map f = l := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    simp only [List.map_cons]
    rw [h a (List.mem_cons.mpr (Or.inl rfl)),
        ih fun b hb => h b (List.mem_cons.mpr (Or.inr hb))]

/-- **A substitution that touches none of a pattern's free variables is the
    identity on it** (for subst-free patterns).

    This is the general-environment form of `applySubst_fresh_single`, and it
    is the Pattern-side statement of the "does σ touch M?" rejection test: if
    a conservative variable-summary intersection is empty, the substitution
    walk may be skipped and the original shared node returned.

    `noExplicitSubst` is required because `applySubst` executes `.subst`
    nodes via binder-eliminating `instantiateBVar`, changing term structure
    even when the environment has no effect. -/
theorem applySubst_untouched {env : SubstEnv} {p : Pattern}
    (hnes : noExplicitSubst p = true)
    (hdisj : ∀ name ∈ freeVars p, env.find name = none) :
    applySubst env p = p := by
  induction p using Pattern.inductionOn with
  | hbvar _ => simp [applySubst]
  | hfvar name =>
    simp only [applySubst, hdisj name (by simp [freeVars])]
  | happly c args ih =>
    simp only [applySubst]; congr 1
    exact list_map_eq_self' fun a ha =>
      ih a ha (allNoExplicitSubst_mem (by exact hnes) ha)
        (fun name hn => hdisj name
          (by simp only [freeVars]; exact List.mem_flatMap.mpr ⟨a, ha, hn⟩))
  | hlambda _ body ih =>
    simp only [applySubst]; congr 1
    simp only [freeVars] at hdisj
    exact ih (by exact hnes) hdisj
  | hmultiLambda _ _ body ih =>
    simp only [applySubst]; congr 1
    simp only [freeVars] at hdisj
    exact ih (by exact hnes) hdisj
  | hsubst body repl _ _ =>
    have : noExplicitSubst (.subst body repl) = false := rfl
    rw [this] at hnes; exact absurd hnes Bool.false_ne_true
  | hcollection ct elems rest ih =>
    simp only [applySubst]; congr 1
    exact list_map_eq_self' fun a ha =>
      ih a ha (allNoExplicitSubst_mem (by exact hnes) ha)
        (fun name hn => hdisj name
          (by simp only [freeVars]; exact List.mem_flatMap.mpr ⟨a, ha, hn⟩))

/-- Closure-level corollary: a closure whose environment misses every free
    variable of its (subst-free) skeleton materializes to the skeleton
    itself — the shared original node, unchanged. -/
theorem materialize_untouched {c : ExplicitClosure}
    (hnes : noExplicitSubst c.skeleton = true)
    (hdisj : ∀ name ∈ freeVars c.skeleton, c.env.find name = none) :
    materialize c = c.skeleton :=
  applySubst_untouched hnes hdisj

/-- Materializing the trivial closure of a subst-free pattern is the
    identity. The `noExplicitSubst` hypothesis is necessary: with a `.subst`
    node present, even the empty environment changes term structure. -/
theorem materialize_trivial (p : Pattern) (hnes : noExplicitSubst p = true) :
    materialize (ExplicitClosure.trivial p) = p :=
  subst_empty p hnes

/-! ## §3: Canonicalize (Closure Creation)

Canonicalization extracts free variables from a term, replacing them with
slot variables and building the corresponding environment.

CeTTa's `variant_shape_from_atom()` is the intended comparison target; the
construction below remains a Pattern-side candidate. -/

/-- Pattern-side slot variable naming convention: `_slot_0`, `_slot_1`, etc.
    CeTTa uses private variable identifiers; relating the two namespaces is a
    separate bridge obligation. -/
def slotName (ordinal : Nat) : String := s!"_slot_{ordinal}"

/-! ### Slot Name Injectivity

The key insight: `Nat.repr` is injective because `natStringValue ∘ Nat.repr = id`.
This uses infrastructure from `Provenance.Util.ValueTypeString`. -/

/-- `Nat.repr` is injective: distinct naturals produce distinct decimal strings.
    Proof: `natStringValue` is a left inverse of `Nat.repr`. -/
theorem Nat.repr_injective : Function.Injective Nat.repr := fun i j h => by
  have hi := natStringValue_repr i
  have hj := natStringValue_repr j
  rw [h] at hi
  exact hi.symm.trans hj

/-- Slot names are injective: `slotName i = slotName j → i = j`.

    **CeTTa correspondence**: Private slot ordinals are canonical identifiers.
    Two different ordinals always produce different slot names. -/
theorem slotName_injective : Function.Injective slotName := by
  intro i j h
  simp only [slotName] at h
  have h' : ("_slot_" ++ toString i).toList = ("_slot_" ++ toString j).toList := by
    rw [String.ext_iff] at h
    exact h
  simp only [String.toList_append] at h'
  have hcancel : (toString i).toList = (toString j).toList :=
    List.append_cancel_left h'
  have hstr : toString i = toString j := by
    apply String.ext_iff.mpr
    exact hcancel
  exact Nat.repr_injective hstr

/-- Enumerate a list with indices starting from n. -/
def enumFrom (n : Nat) : List α → List (Nat × α)
  | [] => []
  | x :: xs => (n, x) :: enumFrom (n + 1) xs

/-- Length of enumFrom equals length of input. -/
theorem enumFrom_length (n : Nat) (xs : List α) :
    (enumFrom n xs).length = xs.length := by
  induction xs generalizing n with
  | nil => rfl
  | cons x xs ih => simp [enumFrom, ih]

/-- If x is at index i in xs, then (n+i, x) is in enumFrom n xs. -/
theorem mem_enumFrom (n : Nat) (xs : List α) (x : α) (i : Nat) (hi : i < xs.length)
    (hx : xs.get ⟨i, hi⟩ = x) :
    (n + i, x) ∈ enumFrom n xs := by
  induction xs generalizing n i with
  | nil => exact absurd hi (Nat.not_lt_zero i)
  | cons y ys ih =>
    simp only [enumFrom, List.mem_cons]
    cases i with
    | zero =>
      simp only [List.get] at hx
      left
      rw [Nat.add_zero, hx]
    | succ j =>
      right
      have hj : j < ys.length := Nat.lt_of_succ_lt_succ hi
      have hx' : ys.get ⟨j, hj⟩ = x := hx
      have hmem := ih (n + 1) j hj hx'
      convert hmem using 2
      omega

/-- If x is in xs, then (i, x) is in enumFrom 0 xs for some i < length. -/
theorem mem_enumFrom_of_mem (xs : List α) (x : α) (hx : x ∈ xs) :
    ∃ i, i < xs.length ∧ (i, x) ∈ enumFrom 0 xs := by
  rw [List.mem_iff_get] at hx
  obtain ⟨⟨i, hi⟩, hget⟩ := hx
  have hmem := mem_enumFrom 0 xs x i hi hget
  simp only [Nat.zero_add] at hmem
  exact ⟨i, hi, hmem⟩

/-- Build a canonicalization map from a list of free variable names.
    Returns (slotEnv, reverseMap) where:
    - slotEnv maps slot names to original free variables
    - reverseMap maps original names to slot names -/
def buildSlotMaps (fvars : List String) : SubstEnv × SubstEnv :=
  let indexed := enumFrom 0 fvars
  let slotEnv := indexed.map fun (i, v) => (slotName i, Pattern.fvar v)
  let reverseMap := indexed.map fun (i, v) => (v, Pattern.fvar (slotName i))
  (slotEnv, reverseMap)

/-- **Canonicalize** a pattern into an explicit closure candidate.
    Extracts free variables, replaces them with slots, builds slot_env.

    `canonicalize(t) = ⟨skeleton, slot_env⟩`; the intended round-trip law
    `materialize(⟨skeleton, slot_env⟩) = t` remains to be proved.

    No theorem in this file identifies this traversal or ordering policy with
    `variant_shape_from_atom()` in `variant_shape.c`. -/
def canonicalize (p : Pattern) : ExplicitClosure :=
  let fvars := (freeVars p).eraseDups
  let (slotEnv, reverseMap) := buildSlotMaps fvars
  let skeleton := applySubst reverseMap p
  ⟨skeleton, slotEnv⟩

/-! ## §4: Candidate Skeleton Relation

The relation below classifies patterns by equality of the candidate
canonical skeleton. Its equivalence laws follow from equality. This section
does not prove an alpha-equivalence theorem or a `VariantBank` correspondence. -/

/-- Two patterns are **skeleton-equivalent** in this candidate model when
    their deterministically named canonical skeletons are equal. -/
def skeletonEquiv (p q : Pattern) : Prop :=
  (canonicalize p).skeleton = (canonicalize q).skeleton

/-- Skeleton equivalence is reflexive. -/
theorem skeletonEquiv_refl (p : Pattern) : skeletonEquiv p p := rfl

/-- Skeleton equivalence is symmetric. -/
theorem skeletonEquiv_symm (p q : Pattern) (h : skeletonEquiv p q) : skeletonEquiv q p := h.symm

/-- Skeleton equivalence is transitive. -/
theorem skeletonEquiv_trans (p q r : Pattern)
    (hpq : skeletonEquiv p q) (hqr : skeletonEquiv q r) : skeletonEquiv p r :=
  hpq.trans hqr

/-! ## §5: Internal Model Facts -/

/-- Ground patterns (no free variables) canonicalize to trivial closures. -/
theorem canonicalize_ground (p : Pattern) (h : freeVars p = []) :
    (canonicalize p).env = SubstEnv.empty := by
  simp only [canonicalize, buildSlotMaps, h, List.eraseDups_nil, enumFrom, List.map_nil]
  rfl

/-! ## §6: Deferred Bridge Theorems

Intentionally omitted until actually proved:

- the round-trip law `materialize (canonicalize p) = p` (needs subst-free and
  slot-name-freshness hypotheses: it is false if `p` contains a `.subst` node
  or a free variable literally named `_slot_i`);
- a substitution-composition operator and its law. A previous `composeEnv`
  defined as `env2.map (fun (x, t) => (x, applySubst env1 t))` was removed:
  it drops `env1`'s bindings outside `dom env2`, so the intended law
  `applySubst (composeEnv e1 e2) p = applySubst e1 (applySubst e2 p)` is
  false for it (take `x ∈ dom e1 \ dom e2`). A correct operator must append
  `env1`'s residual bindings;
- any correspondence statement tying these definitions to CeTTa's C
  implementation contracts.
-/

end Mettapedia.Bridge.CeTTaExplicitSubst
