import Mettapedia.Languages.MeTTa.HE.Matching

/-!
# Binding Composition: Monotonic Extension Under Pattern Matching

Proves that `simpleMatch` **extends** seed bindings monotonically: the result
bindings contain all seed entries plus new ones from the match. This is the
correct abstraction — not individual lookup preservation, but a general
extension relation.

## Architecture

Ported from the translation proof at `HEPeTTaSound.lean:491-714` where
`HEBindingsExtends` + `simpleMatch_extends` were proved as private lemmas.
Now promoted to HE core infrastructure for reuse by:
- candidate selection correctness
- cache/materialization preservation
- co-reference preservation under rematch

## Key Results

- `Bindings.Extends` — monotonicity: all seed lookups preserved
- `extends_refl` / `extends_trans` — preorder
- `extends_assign_of_lookup_none` — assigning a fresh var extends
- `simpleMatch_extends` — THE mutual induction: simpleMatch extends bindings
- `simpleMatch_preserves_seed` — corollary: seed lookup preserved

## Connection to CeTTa

Maps to `space_match_backend.c`: seed bindings from prior context survive rematch.
Maps to `table_store.c`: goal bindings survive materialization.
-/

namespace Mettapedia.Languages.MeTTa.HE

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)

/-! ## §1: The extension relation -/

/-- `result` **extends** `seed`: every lookup in `seed` is preserved in `result`.
    This is the monotonicity invariant for pattern matching. -/
def Bindings.Extends (seed result : Bindings) : Prop :=
  ∀ x a, seed.lookup x = some a → result.lookup x = some a

/-- Extension is reflexive. -/
theorem Bindings.extends_refl (b : Bindings) : b.Extends b :=
  fun _ _ h => h

/-- Extension is transitive. -/
theorem Bindings.extends_trans {b₁ b₂ b₃ : Bindings}
    (h₁₂ : b₁.Extends b₂) (h₂₃ : b₂.Extends b₃) : b₁.Extends b₃ :=
  fun x a hx => h₂₃ x a (h₁₂ x a hx)

/-! ## §2: Assignment extends when variable is fresh -/

theorem isBound_false_of_lookup_none {b : Bindings} {v : String}
    (h : b.lookup v = none) : b.isBound v = false := by
  simp [Bindings.isBound, h]

theorem lookup_assign_of_lookup_none
    (b : Bindings) (v : String) (a : Atom)
    (hnone : b.lookup v = none) :
    (b.assign v a).lookup v = some a := by
  have hnotbound := isBound_false_of_lookup_none hnone
  simp only [Bindings.assign, Bindings.lookup, hnotbound, Bool.false_eq_true, ↓reduceIte,
    List.lookup_append, Bindings.lookup] at hnone ⊢
  simp [hnone]

/-- Assigning to a fresh variable extends the bindings. -/
theorem extends_assign_of_lookup_none
    (b : Bindings) (v : String) (a : Atom)
    (hnone : b.lookup v = none) :
    b.Extends (b.assign v a) := by
  intro x val hx
  have hnotbound := isBound_false_of_lookup_none hnone
  simp only [Bindings.assign, Bindings.lookup, hnotbound, Bool.false_eq_true, ↓reduceIte,
    List.lookup_append] at hx ⊢
  simp [hx]

/-- Assigning to a fresh variable doesn't affect other lookups. -/
theorem assign_lookup_ne (b : Bindings) (v : String) (a : Atom)
    (w : String) (hne : w ≠ v) (hnone : b.lookup v = none) :
    (b.assign v a).lookup w = b.lookup w := by
  have hnotbound := isBound_false_of_lookup_none hnone
  simp only [Bindings.assign, Bindings.lookup, hnotbound, Bool.false_eq_true,
    ↓reduceIte, List.lookup_append]
  cases hw : (b.assignments.lookup w) with
  | some val => rfl
  | none => simp [hne]

/-! ## §3: simpleMatch extends — the mutual induction

Ported from `HEPeTTaSound.lean:656-714`. The proof is by induction on fuel,
with mutual cases for `simpleMatch` and `simpleMatchList`. -/

/-- **THE theorem**: `simpleMatch` and `simpleMatchList` both extend their
    input bindings. Proved by mutual induction on fuel. -/
theorem simpleMatch_extends (fuel : Nat) :
    (∀ lhs target b qb,
      simpleMatch lhs target b fuel = some qb →
      b.Extends qb) ∧
    (∀ ps ts b qb,
      simpleMatch.simpleMatchList ps ts b fuel = some qb →
      b.Extends qb) := by
  induction fuel with
  | zero =>
    exact ⟨fun _ _ _ _ h => by simp [simpleMatch] at h,
           fun ps ts b qb h => by
             cases ps <;> cases ts <;>
               simp [simpleMatch.simpleMatchList, simpleMatch] at h
             subst h; exact Bindings.extends_refl _⟩
  | succ n ih =>
    obtain ⟨ih_match, ih_list⟩ := ih
    have hpat : ∀ lhs target b qb,
        simpleMatch lhs target b (n + 1) = some qb →
        b.Extends qb := by
      intro lhs target b qb hmatch
      cases lhs with
      | var v =>
        cases hlookup : b.lookup v <;>
          simp [simpleMatch, hlookup] at hmatch
        · subst hmatch; exact extends_assign_of_lookup_none b v target hlookup
        · obtain ⟨_, rfl⟩ := hmatch; exact Bindings.extends_refl _
      | symbol s =>
        cases target <;> simp [simpleMatch] at hmatch
        obtain ⟨_, rfl⟩ := hmatch; exact Bindings.extends_refl _
      | grounded g =>
        cases target <;> simp [simpleMatch] at hmatch
        obtain ⟨_, rfl⟩ := hmatch; exact Bindings.extends_refl _
      | expression ps =>
        cases target <;> simp [simpleMatch] at hmatch
        exact ih_list ps _ b qb hmatch.2
    have hlist : ∀ ps ts b qb,
        simpleMatch.simpleMatchList ps ts b (n + 1) = some qb →
        b.Extends qb := by
      intro ps'
      induction ps' with
      | nil =>
        intro ts' b' qb' h'
        cases ts' <;>
          simp [simpleMatch.simpleMatchList] at h'
        subst h'; exact Bindings.extends_refl _
      | cons p' ps' ihps =>
        intro ts' b' qb' h'
        cases ts' with
        | nil => simp [simpleMatch.simpleMatchList] at h'
        | cons t' ts' =>
          unfold simpleMatch.simpleMatchList at h'
          cases hhd : simpleMatch p' t' b' (n + 1) with
          | none => simp [hhd] at h'
          | some b'' =>
            simp [hhd] at h'
            exact Bindings.extends_trans (hpat p' t' b' b'' hhd) (ihps ts' b'' qb' h')
    exact ⟨hpat, hlist⟩

/-! ## §4: Corollaries -/

/-- **Seed preservation**: if `simpleMatch` succeeds, every seed binding
    is preserved in the result. This is a direct corollary of `simpleMatch_extends`. -/
theorem simpleMatch_preserves_seed (pattern target : Atom) (seed : Bindings)
    (fuel : Nat) (result : Bindings)
    (hmatch : simpleMatch pattern target seed fuel = some result)
    (v : String) (val : Atom) (hseed : seed.lookup v = some val) :
    result.lookup v = some val :=
  (simpleMatch_extends fuel).1 pattern target seed result hmatch v val hseed

/-- Seed preservation for `simpleMatchList`. -/
theorem simpleMatchList_preserves_seed (ps ts : List Atom) (seed : Bindings)
    (fuel : Nat) (result : Bindings)
    (hmatch : simpleMatch.simpleMatchList ps ts seed fuel = some result)
    (v : String) (val : Atom) (hseed : seed.lookup v = some val) :
    result.lookup v = some val :=
  (simpleMatch_extends fuel).2 ps ts seed result hmatch v val hseed

/-! ## §5: Interpretation

### 0 sorries

The entire file is sorry-free. The key insight (from Codex): define
`Bindings.Extends` as the primary invariant, prove the mutual induction
ONCE at that level, then derive all pointwise properties as corollaries.

The proof was ported from `HEPeTTaSound.lean:491-714` where it existed as
private lemmas. Now it's promoted to HE core infrastructure.

### What this gives CeTTa

**`simpleMatch_extends`** guarantees that CeTTa's native pattern matcher
never drops bindings. The two-phase architecture (PathMap candidates → native
rematch with seed bindings) is correct because:
1. `simpleMatch` extends the seed (this file)
2. PathMap candidates are sound (CandidateArchitecture.lean)
3. Therefore: rematch preserves seed AND finds correct matches

**`Bindings.Extends`** is the right foundation for:
- `mergeBindings_extends` (future: bindings merge preserves extension)
- Cache materialization preservation
- Store/reload round-trip correctness
-/

end Mettapedia.Languages.MeTTa.HE
