import Mettapedia.OSLF.MeTTaIL.Substitution
import Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts
import Provenance.Util.ValueTypeString
import Init.Data.List.Lemmas

/-!
# CeTTa Explicit Substitution Bridge

Builds the support layer for relating CeTTa's Layer 3 term representation
(skeleton + slot_env) to explicit-substitution closures.

This file currently proves the carrier definitions and several key support
lemmas, including slot-name injectivity. The full bridge theorems
(`materialize (canonicalize p) = p`, substitution-composition laws, and the
strongest runtime correspondence statements) still need to be completed.

## CeTTa Layer 3 Architecture

CeTTa factors open terms into two parts:
- **skeleton**: A pattern with slot variables (de Bruijn-style private tags)
- **slot_env**: A substitution mapping slot ordinals to concrete terms

This is exactly an **explicit substitution closure** ⟨M, σ⟩ from Abadi et al. (1991).

## Key Correspondences

| CeTTa (C runtime)       | Lambda-Sigma (λσ)           | This file           |
|-------------------------|-----------------------------|---------------------|
| `skeleton`              | M in ⟨M, σ⟩                 | `ExplicitClosure.skeleton` |
| `slot_env`              | σ (substitution)            | `ExplicitClosure.env`      |
| `materialize()`         | M[σ] (application)          | `materialize`              |
| `canonicalize()`        | closure creation            | `canonicalize`             |
| `VariantBank`           | canonical quotient          | (hash-consing, not here)   |

## References

- Abadi et al., "Explicit Substitutions", JFP 1991
- CeTTa: `/home/zar/claude/c-projects/CeTTa-TermUniverse/src/variant_shape.h`
- Roadmap: `../../../../papers/cetta_roadmap.tex` §8 (Dual-Target Architecture)
-/

namespace Mettapedia.Bridge.CeTTaExplicitSubst

open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.OSLF.MeTTaIL.Substitution
  (SubstEnv applySubst openBVar closeFVar freeVars noExplicitSubst)

/-! ## §1: Explicit Closure (Layer 3 Representation)

An explicit closure pairs a skeleton pattern with a substitution environment.
This mirrors CeTTa's `VariantShape` struct from `variant_shape.h`. -/

/-- An **explicit closure** ⟨M, σ⟩ in the lambda-sigma calculus.
    Corresponds to CeTTa's `VariantShape { skeleton, slot_env }`. -/
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

Materialization applies the slot_env to the skeleton, producing a concrete term.
This is exactly `applySubst` from the locally nameless infrastructure.

**CeTTa correspondence**: `variant_shape_materialize()` in `variant_shape.c` -/

/-- **Materialize** an explicit closure by applying the substitution.
    `materialize(⟨M, σ⟩) = M[σ]`

    This is the core operation that connects Layer 3 to concrete terms. -/
def materialize (c : ExplicitClosure) : Pattern :=
  applySubst c.env c.skeleton

/-- **Theorem**: Materialize IS applySubst.
    This is definitionally true by construction — the key insight is that
    CeTTa's materialize operation exactly matches lambda-sigma substitution.

    **CeTTa contract**: `variant_shape_materialize()` computes `applySubst`. -/
theorem materialize_eq_applySubst (c : ExplicitClosure) :
    materialize c = applySubst c.env c.skeleton := rfl

/-- Materialize with empty env is identity on skeleton. -/
theorem materialize_trivial (p : Pattern) :
    materialize (ExplicitClosure.trivial p) = applySubst SubstEnv.empty p := rfl

/-! ## §3: Canonicalize (Closure Creation)

Canonicalization extracts free variables from a term, replacing them with
slot variables and building the corresponding environment.

**CeTTa correspondence**: `variant_shape_from_atom()` in `variant_shape.c` -/

/-- Slot variable naming convention: `_slot_0`, `_slot_1`, etc.
    Mirrors CeTTa's private slot tag 0xFFFFA11A with ordinal suffix. -/
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

/-- **Canonicalize** a pattern into an explicit closure.
    Extracts free variables, replaces them with slots, builds slot_env.

    `canonicalize(t) = ⟨skeleton, slot_env⟩` where `materialize(⟨skeleton, slot_env⟩) = t`

    **CeTTa contract**: `variant_shape_from_atom()` in `variant_shape.c` -/
def canonicalize (p : Pattern) : ExplicitClosure :=
  let fvars := (freeVars p).eraseDups
  let (slotEnv, reverseMap) := buildSlotMaps fvars
  let skeleton := applySubst reverseMap p
  ⟨skeleton, slotEnv⟩

/-! ## §4: Substitution Composition

Layer 3 operations compose: applying one closure's env, then another's,
is equivalent to composing the environments. -/

/-- Compose two substitution environments.
    `(σ₁ ∘ σ₂)(x) = σ₁(σ₂(x))` -/
def composeEnv (env1 env2 : SubstEnv) : SubstEnv :=
  env2.map fun (x, t) => (x, applySubst env1 t)

/-! ## §5: Alpha-Canonicity

Canonicalization respects alpha-equivalence: alpha-equivalent terms
produce the same skeleton (up to slot renaming).

**CeTTa correspondence**: `VariantBank` hash-consing in `variant_shape.c` -/

/-- Two patterns are **skeleton-equivalent** if their canonical skeletons
    are equal (ignoring the specific slot naming). -/
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

/-! ## §6: CeTTa Runtime Contracts

These theorems map directly to CeTTa's C implementation contracts. -/

/-- **Contract**: Empty environment materialization is identity.
    `materialize(⟨p, ∅⟩) = applySubst ∅ p`

    **CeTTa risk**: Empty slot_env special case handling. -/
theorem materialize_empty_env (p : Pattern) :
    materialize ⟨p, SubstEnv.empty⟩ = applySubst SubstEnv.empty p := rfl

/-- Ground patterns (no free variables) canonicalize to trivial closures. -/
theorem canonicalize_ground (p : Pattern) (h : freeVars p = []) :
    (canonicalize p).env = SubstEnv.empty := by
  simp only [canonicalize, buildSlotMaps, h, List.eraseDups_nil, enumFrom, List.map_nil]
  rfl

/-- Trivial closure materialization is just the skeleton. -/
theorem materialize_trivial_closure (p : Pattern) :
    materialize (ExplicitClosure.trivial p) = applySubst SubstEnv.empty p := rfl

/-! ## §7: Deferred Bridge Theorems

The full bridge theorems are intentionally omitted until they are actually
proved. In particular, this file does not yet claim:

- `materialize (canonicalize p) = p`
- substitution-composition compatibility for `composeEnv`
- the strongest runtime correspondence statements tying these definitions back
  to CeTTa's C implementation contracts

What remains here is the support layer that already compiles cleanly:
carrier definitions, materialization/canonicalization functions, slot-name
injectivity, and basic structural contracts. -/

end Mettapedia.Bridge.CeTTaExplicitSubst
