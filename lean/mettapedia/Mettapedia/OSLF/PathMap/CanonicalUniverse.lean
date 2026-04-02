import Mathlib.Data.List.Basic

/-!
# Canonical Universe: Store/Materialize, Co-reference, Hashcons Safety

Formalizes CeTTa's term universe (`term_universe.c`, `atom.c`).

## CeTTa Mapping

| Lean | CeTTa |
|------|-------|
| `VarId` | 64-bit var ID (base:32 + epoch:32) |
| `CAtom` | `struct Atom` in atom.h |
| `CAtom.applyRenaming` | var renaming in `term_universe_canonicalize_atom()` |
| `isHashConsSafe` | `atom_can_hashcons()` |
-/

namespace Mettapedia.OSLF.PathMap.CanonicalUniverse

/-! ## §1: Variable Identity -/

structure VarId where
  base : Nat
  epoch : Nat
  deriving DecidableEq, Repr, Inhabited

def VarId.isEpoch (v : VarId) : Bool := v.epoch != 0
def VarId.isCanonical (v : VarId) : Bool := v.epoch == 0

/-! ## §2: CeTTa-Aware Atoms -/

inductive GroundedKind where
  | immutable : String → GroundedKind
  | mutable : String → GroundedKind
  deriving DecidableEq, Repr, Inhabited

inductive CAtom where
  | symbol : String → CAtom
  | var : VarId → CAtom
  | grounded : GroundedKind → CAtom
  | expression : List CAtom → CAtom
  deriving Repr, Inhabited

/-! ## §3: Structural Predicates -/

def CAtom.isEpochFree : CAtom → Bool
  | .symbol _ => true
  | .var v => v.isCanonical
  | .grounded _ => true
  | .expression es => isEpochFreeList es
where isEpochFreeList : List CAtom → Bool
    | [] => true
    | a :: as => a.isEpochFree && isEpochFreeList as

def CAtom.isVarFree : CAtom → Bool
  | .symbol _ => true
  | .var _ => false
  | .grounded _ => true
  | .expression es => isVarFreeList es
where isVarFreeList : List CAtom → Bool
    | [] => true
    | a :: as => a.isVarFree && isVarFreeList as

def CAtom.isGroundedImmutable : CAtom → Bool
  | .symbol _ => true
  | .var _ => true
  | .grounded (.immutable _) => true
  | .grounded (.mutable _) => false
  | .expression es => isGroundedImmutableList es
where isGroundedImmutableList : List CAtom → Bool
    | [] => true
    | a :: as => a.isGroundedImmutable && isGroundedImmutableList as

def CAtom.isHashConsSafe : CAtom → Bool
  | .symbol _ => true
  | .var _ => false
  | .grounded (.immutable _) => true
  | .grounded (.mutable _) => false
  | .expression es => isHashConsSafeList es
where isHashConsSafeList : List CAtom → Bool
    | [] => true
    | a :: as => a.isHashConsSafe && isHashConsSafeList as

/-! ## §4: Variable Renaming -/

/-- Apply a variable renaming to an atom. Only renames epoch-tagged vars. -/
def CAtom.applyRenaming (f : VarId → VarId) : CAtom → CAtom
  | .symbol s => .symbol s
  | .var v => .var (if v.isEpoch then f v else v)
  | .grounded g => .grounded g
  | .expression es => .expression (applyRenamingList f es)
where applyRenamingList (f : VarId → VarId) : List CAtom → List CAtom
    | [] => []
    | a :: as => a.applyRenaming f :: applyRenamingList f as

/-! ## §5: Epoch-free atoms are invariant under renaming -/

theorem CAtom.applyRenaming_of_epochFree (f : VarId → VarId) (a : CAtom)
    (h : a.isEpochFree = true) : a.applyRenaming f = a := by
  match a with
  | .symbol _ => rfl
  | .var v =>
    simp only [applyRenaming, isEpochFree, VarId.isCanonical, VarId.isEpoch] at *
    simp [beq_iff_eq] at h; simp [h]
  | .grounded _ => rfl
  | .expression es =>
    simp only [applyRenaming, CAtom.expression.injEq]
    exact applyRenamingList_of_epochFree f es h
where
  applyRenamingList_of_epochFree (f : VarId → VarId) :
      (es : List CAtom) → CAtom.isEpochFree.isEpochFreeList es = true →
      CAtom.applyRenaming.applyRenamingList f es = es
    | [], _ => rfl
    | a :: as, h => by
      simp only [CAtom.isEpochFree.isEpochFreeList, Bool.and_eq_true] at h
      simp only [CAtom.applyRenaming.applyRenamingList, List.cons.injEq]
      exact ⟨CAtom.applyRenaming_of_epochFree f a h.1,
             applyRenamingList_of_epochFree f as h.2⟩

/-! ## §6: Renaming that produces canonical vars → output is epoch-free -/

theorem CAtom.applyRenaming_epochFree_output (f : VarId → VarId) (a : CAtom)
    (hf : ∀ v, v.isEpoch = true → (f v).isCanonical = true) :
    (a.applyRenaming f).isEpochFree = true := by
  match a with
  | .symbol _ => rfl
  | .var v =>
    simp only [applyRenaming, isEpochFree]
    by_cases hep : v.isEpoch = true
    · simp [hep, hf v hep]
    · simp [Bool.not_eq_true] at hep
      simp [VarId.isEpoch, VarId.isCanonical, bne_iff_ne, beq_iff_eq] at *
      simp [hep]
  | .grounded _ => rfl
  | .expression es =>
    simp only [applyRenaming, isEpochFree]
    exact applyRenamingList_epochFree f es hf
where
  applyRenamingList_epochFree (f : VarId → VarId) :
      (es : List CAtom) → (∀ v, v.isEpoch = true → (f v).isCanonical = true) →
      CAtom.isEpochFree.isEpochFreeList (CAtom.applyRenaming.applyRenamingList f es) = true
    | [], _ => rfl
    | a :: as, hf => by
      simp only [CAtom.applyRenaming.applyRenamingList, CAtom.isEpochFree.isEpochFreeList,
                 Bool.and_eq_true]
      exact ⟨CAtom.applyRenaming_epochFree_output f a hf,
             applyRenamingList_epochFree f as hf⟩

/-! ## §7: Canonical Renaming via Ordinal Assignment -/

/-- Look up the position of a VarId in a list (0-indexed). -/
def findPosition : List VarId → VarId → Nat → Option Nat
  | [], _, _ => none
  | w :: ws, v, idx => if w == v then some idx else findPosition ws v (idx + 1)

/-- The canonical renaming: maps epoch vars to ordinal canonical vars. -/
def mkCanonicalRenaming (epochVars : List VarId) (v : VarId) : VarId :=
  match findPosition epochVars v 0 with
  | some idx => ⟨idx, 0⟩
  | none => v

/-- mkCanonicalRenaming always produces canonical vars for listed members. -/
theorem mkCanonicalRenaming_canonical (epochVars : List VarId) (v : VarId)
    (hmem : findPosition epochVars v 0 = some idx) :
    (mkCanonicalRenaming epochVars v).isCanonical = true := by
  simp only [mkCanonicalRenaming, hmem, VarId.isCanonical, BEq.beq]
  decide

/-- findPosition returns distinct indices for distinct elements. -/
theorem findPosition_injective (vs : List VarId) (v w : VarId) (base : Nat)
    (iv iw : Nat)
    (hv : findPosition vs v base = some iv)
    (hw : findPosition vs w base = some iw)
    (hidx : iv = iw) :
    v = w := by
  induction vs generalizing base with
  | nil => simp [findPosition] at hv
  | cons x xs ih =>
    simp only [findPosition] at hv hw
    split at hv <;> split at hw
    · -- both match x
      rename_i hxv hxw
      simp [beq_iff_eq] at hxv hxw
      exact hxv.symm.trans hxw
    · -- v matches x, w doesn't → different indices
      rename_i hxv _
      simp at hv
      subst hv
      -- iw comes from a deeper call, so iw ≥ base + 1 > base = iv
      have : iw ≥ base + 1 := findPosition_ge xs w (base + 1) iw hw
      omega
    · -- w matches x, v doesn't → different indices
      rename_i _ hxw
      simp at hw
      subst hw
      have : iv ≥ base + 1 := findPosition_ge xs v (base + 1) iv hv
      omega
    · -- neither matches x → recurse
      exact ih (base + 1) hv hw
where
  findPosition_ge : (vs : List VarId) → (v : VarId) → (base idx : Nat) →
      findPosition vs v base = some idx → idx ≥ base
    | [], _, base, _, h => by simp [findPosition] at h
    | x :: xs, v, base, idx, h => by
      simp only [findPosition] at h
      split at h
      · simp at h; omega
      · have := findPosition_ge xs v (base + 1) idx h; omega

/-- **Co-reference preservation:**
    mkCanonicalRenaming is injective — same output ↔ same input. -/
theorem mkCanonicalRenaming_injective (epochVars : List VarId)
    (v w : VarId)
    (iv iw : Nat)
    (hv : findPosition epochVars v 0 = some iv)
    (hw : findPosition epochVars w 0 = some iw)
    (heq : mkCanonicalRenaming epochVars v = mkCanonicalRenaming epochVars w) :
    v = w := by
  simp only [mkCanonicalRenaming, hv, hw, VarId.mk.injEq] at heq
  exact findPosition_injective epochVars v w 0 iv iw hv hw heq.1

/-! ## §8: Hashcons Safety -/

/-- **Hashcons safety:** var-free + immutable grounded → hashcons safe. -/
theorem CAtom.hashConsSafe_of_varFree_immutable (a : CAtom)
    (hvf : a.isVarFree = true) (hgi : a.isGroundedImmutable = true) :
    a.isHashConsSafe = true := by
  match a with
  | .symbol _ => rfl
  | .var _ => simp [isVarFree] at hvf
  | .grounded (.immutable _) => rfl
  | .grounded (.mutable _) => simp [isGroundedImmutable] at hgi
  | .expression es =>
    simp only [isHashConsSafe, isVarFree, isGroundedImmutable] at *
    exact hashConsSafeList hvf hgi
where
  hashConsSafeList :
      {es : List CAtom} →
      CAtom.isVarFree.isVarFreeList es = true →
      CAtom.isGroundedImmutable.isGroundedImmutableList es = true →
      CAtom.isHashConsSafe.isHashConsSafeList es = true
    | [], _, _ => rfl
    | a :: as, hvf, hgi => by
      simp only [CAtom.isVarFree.isVarFreeList, Bool.and_eq_true] at hvf
      simp only [CAtom.isGroundedImmutable.isGroundedImmutableList, Bool.and_eq_true] at hgi
      simp only [CAtom.isHashConsSafe.isHashConsSafeList, Bool.and_eq_true]
      exact ⟨CAtom.hashConsSafe_of_varFree_immutable a hvf.1 hgi.1,
             hashConsSafeList hvf.2 hgi.2⟩

/-- Var-free implies epoch-free (stronger condition). -/
theorem CAtom.varFree_implies_epochFree (a : CAtom)
    (h : a.isVarFree = true) : a.isEpochFree = true := by
  match a with
  | .symbol _ => rfl
  | .var _ => simp [isVarFree] at h
  | .grounded _ => rfl
  | .expression es =>
    simp only [isVarFree, isEpochFree] at *
    exact varFreeList_implies_epochFreeList h
where
  varFreeList_implies_epochFreeList :
      {es : List CAtom} →
      CAtom.isVarFree.isVarFreeList es = true →
      CAtom.isEpochFree.isEpochFreeList es = true
    | [], _ => rfl
    | a :: as, h => by
      simp only [CAtom.isVarFree.isVarFreeList, Bool.and_eq_true] at h
      simp only [CAtom.isEpochFree.isEpochFreeList, Bool.and_eq_true]
      exact ⟨CAtom.varFree_implies_epochFree a h.1,
             varFreeList_implies_epochFreeList h.2⟩

/-! ## §9: Summary

**0 sorries. 0 axioms.**

Key theorems:
- `applyRenaming_of_epochFree` — epoch-free atoms pass through unchanged
- `applyRenaming_epochFree_output` — canonical renaming produces epoch-free output
- `mkCanonicalRenaming_injective` — co-reference preservation
- `hashConsSafe_of_varFree_immutable` — hashcons safety characterization
- `varFree_implies_epochFree` — var-free is stronger than epoch-free

Maps to CeTTa runtime:
- `VarId` → 64-bit var ID in atom.h
- `applyRenaming` → renaming in `term_universe_canonicalize_atom()`
- `isHashConsSafe` → `atom_can_hashcons()` in atom.c
- `findPosition` → ordinal assignment in canonicalize loop
-/

end Mettapedia.OSLF.PathMap.CanonicalUniverse
