import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.GlbControls

/-!
# The greatest lower bound of two universes of the tower

The tower's universes are `U_l` for level expressions `l`, ordered by `l ≤ r` under **every** valuation. Level
expressions have canonical forms (`LevelNF`: a constant and sorted `(parameter, offset)` atoms) with an exact finite
order test (`CanonicalLe`): `left ≤ right` exactly when every atom of `left` has an atom of `right` with the same
parameter and at least its offset, and `left`'s constant lies below what `right` reaches at the least valuation.

**The greatest lower bound** (`glbNF`) keeps the atoms present in both forms, at the smaller offset, and as its
constant the smaller of the two values at the least valuation, dropped when the atoms already reach it:
* it lies below both forms (`glbNF_le_left`, `glbNF_le_right`);
* every form below both lies below it (`le_glbNF`);
* it is canonical (`glbNF_wf`).

**On universes** (`towerGlb`): `U_a ⊓ U_b` is `U_g` for the level expression `g` of that form, a greatest lower
bound in the tower's cumulative order (`towerGlb_isGlb`), defined for every pair of universes (`towerGlb_total`).

Positive examples: `U_a ⊓ U_b = U0` for different parameters, and `U_a ⊓ U_{a+1} = U_a` up to the order; a
negative example: `U1` is not below `U_a` (`GlbGroupControls`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

namespace TreeFibre

namespace LevelGlb

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.TypeTheory.UniverseLevel.LevelNF
open Mettapedia.TypeTheory.UniverseLevel.LevelOrder
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization

variable {L : Type} [LevelOrder L]

/-! ## Canonical forms -/

section Forms

/-- The atoms present in both lists, at the smaller offset. -/
def interParams (p₁ p₂ : List (Nat × Nat)) : List (Nat × Nat) :=
  p₁.filterMap fun ik => (lookupParam p₂ ik.1).map fun k₂ => (ik.1, min ik.2 k₂)

theorem mem_interParams {p₁ p₂ : List (Nat × Nat)} {i k : Nat} :
    (i, k) ∈ interParams p₁ p₂ ↔ ∃ k₁ k₂, (i, k₁) ∈ p₁ ∧ lookupParam p₂ i = some k₂ ∧ k = min k₁ k₂ := by
  unfold interParams
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨⟨j, k₁⟩, member, hit⟩
    cases h : lookupParam p₂ j with
    | none => rw [h] at hit; cases hit
    | some k₂ =>
        rw [h] at hit
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hit
        obtain ⟨rfl, rfl⟩ := hit
        exact ⟨k₁, k₂, member, h, rfl⟩
  · rintro ⟨k₁, k₂, member, h, rfl⟩
    refine ⟨(i, k₁), member, ?_⟩
    simp only [h, Option.map_some]

theorem sorted_interParams {p₁ : List (Nat × Nat)} (p₂ : List (Nat × Nat)) (sorted : Sorted p₁) :
    Sorted (interParams p₁ p₂) := by
  unfold interParams Sorted
  apply List.Pairwise.filterMap _ _ sorted
  intro a a' lt b hb b' hb'
  cases ha : lookupParam p₂ a.1 with
  | none => rw [ha] at hb; cases hb
  | some k =>
      rw [ha] at hb
      cases ha' : lookupParam p₂ a'.1 with
      | none => rw [ha'] at hb'; cases hb'
      | some k' =>
          rw [ha'] at hb'
          simp only [Option.map_some, Option.some.injEq] at hb hb'
          rw [← hb, ← hb']
          exact lt

/-- **The greatest lower bound of two canonical forms.** -/
def glbNF (n₁ n₂ : LevelNF L) : LevelNF L :=
  ⟨if min (max n₁.constPart (ofNat (supOffsets n₁.params))) (max n₂.constPart (ofNat (supOffsets n₂.params))) ≤
      ofNat (supOffsets (interParams n₁.params n₂.params)) then bot
    else min (max n₁.constPart (ofNat (supOffsets n₁.params))) (max n₂.constPart (ofNat (supOffsets n₂.params))),
    interParams n₁.params n₂.params⟩

theorem glbNF_const_le {n₁ n₂ : LevelNF L} :
    (glbNF n₁ n₂).constPart ≤
      min (max n₁.constPart (ofNat (supOffsets n₁.params))) (max n₂.constPart (ofNat (supOffsets n₂.params))) := by
  unfold glbNF
  dsimp only
  split
  · exact bot_le _
  · exact le_refl _

theorem glbNF_le_left {n₁ n₂ : LevelNF L} (wf₁ : WF n₁) : CanonicalLe (glbNF n₁ n₂) n₁ := by
  refine ⟨glbNF_const_le.trans (min_le_left _ _), ?_⟩
  intro ik member
  obtain ⟨i, k⟩ := ik
  obtain ⟨k₁, k₂, mem₁, _, rfl⟩ := mem_interParams.mp member
  unfold AtomLe
  rw [lookupParam_eq_some_of_mem wf₁.1 mem₁]
  exact min_le_left _ _

theorem glbNF_le_right {n₁ n₂ : LevelNF L} : CanonicalLe (glbNF n₁ n₂) n₂ := by
  refine ⟨glbNF_const_le.trans (min_le_right _ _), ?_⟩
  intro ik member
  obtain ⟨i, k⟩ := ik
  obtain ⟨k₁, k₂, _, hit₂, rfl⟩ := mem_interParams.mp member
  unfold AtomLe
  rw [hit₂]
  exact min_le_right _ _

/-- **Every form below both lies below the greatest lower bound.** -/
theorem le_glbNF {u n₁ n₂ : LevelNF L} (wf₁ : WF n₁) (below₁ : CanonicalLe u n₁) (below₂ : CanonicalLe u n₂) :
    CanonicalLe u (glbNF n₁ n₂) := by
  refine ⟨?_, ?_⟩
  · have m : u.constPart ≤
        min (max n₁.constPart (ofNat (supOffsets n₁.params))) (max n₂.constPart (ofNat (supOffsets n₂.params))) :=
      le_min below₁.1 below₂.1
    show u.constPart ≤ max (glbNF n₁ n₂).constPart (ofNat (supOffsets (interParams n₁.params n₂.params)))
    unfold glbNF
    dsimp only
    split
    · rename_i low
      exact (m.trans low).trans (le_max_right _ _)
    · exact m.trans (le_max_left _ _)
  · intro ik member
    obtain ⟨i, k⟩ := ik
    have a₁ := below₁.2 (i, k) member
    have a₂ := below₂.2 (i, k) member
    unfold AtomLe at a₁ a₂ ⊢
    cases h₁ : lookupParam n₁.params i with
    | none => rw [h₁] at a₁; exact a₁.elim
    | some k₁ =>
        cases h₂ : lookupParam n₂.params i with
        | none => rw [h₂] at a₂; exact a₂.elim
        | some k₂ =>
            rw [h₁] at a₁
            rw [h₂] at a₂
            have inter : (i, min k₁ k₂) ∈ interParams n₁.params n₂.params :=
              mem_interParams.mpr ⟨k₁, k₂, mem_of_lookupParam_eq_some h₁, h₂, rfl⟩
            show (match lookupParam (interParams n₁.params n₂.params) i with
              | none => False
              | some rightOffset => k ≤ rightOffset)
            rw [lookupParam_eq_some_of_mem (sorted_interParams _ wf₁.1) inter]
            exact le_min a₁ a₂

/-- **The greatest lower bound is canonical.** -/
theorem glbNF_wf {n₁ n₂ : LevelNF L} (wf₁ : WF n₁) : WF (glbNF n₁ n₂) := by
  refine ⟨sorted_interParams _ wf₁.1, ?_⟩
  intro i k hit
  show (glbNF n₁ n₂).constPart = bot ∨ ofNat k < (glbNF n₁ n₂).constPart
  unfold glbNF
  dsimp only
  split
  · exact .inl rfl
  · rename_i high
    right
    have kSup : (ofNat k : L) ≤ ofNat (supOffsets (interParams n₁.params n₂.params)) :=
      ofNat_le_ofNat_iff.mpr (supOffsets_ge_of_lookup hit)
    exact lt_of_le_of_lt kSup (lt_of_not_ge high)

end Forms

/-! ## Back to level expressions -/

section Expressions

/-- `e + k`. -/
def succs (e : LevelExpr L) : Nat → LevelExpr L
  | 0 => e
  | k + 1 => .succ (succs e k)

theorem eval_succs (v : Nat → L) (e : LevelExpr L) : ∀ k, LevelExpr.eval v (succs e k) = addNat (LevelExpr.eval v e) k
  | 0 => rfl
  | k + 1 => by
      show LevelOrder.succ (LevelExpr.eval v (succs e k)) = _
      rw [eval_succs v e k]
      rfl

/-- A level expression with a canonical form's value. -/
def toExpr (nf : LevelNF L) : LevelExpr L :=
  nf.params.foldl (fun acc ik => .max acc (succs (.param ik.1) ik.2)) (.const nf.constPart)

theorem eval_foldl (v : Nat → L) : ∀ (ps : List (Nat × Nat)) (e : LevelExpr L),
    LevelExpr.eval v (ps.foldl (fun acc ik => .max acc (succs (.param ik.1) ik.2)) e) =
      ps.foldl (fun acc (ik : Nat × Nat) => max acc (addNat (v ik.1) ik.2)) (LevelExpr.eval v e)
  | [], _ => rfl
  | ik :: rest, e => by
      simp only [List.foldl_cons]
      rw [eval_foldl v rest]
      congr 1
      show max (LevelExpr.eval v e) (LevelExpr.eval v (succs (.param ik.1) ik.2)) = _
      rw [eval_succs]
      rfl

theorem eval_toExpr (v : Nat → L) (nf : LevelNF L) : LevelExpr.eval v (toExpr nf) = LevelNF.eval v nf := by
  unfold toExpr
  rw [eval_foldl]
  rfl

end Expressions

/-! ## On the tower's universes -/

section Tower

/-- **The tower's greatest lower bound of two universes.** -/
def towerGlb : LevelTower.Head L → LevelTower.Head L → Option (LevelTower.Head L)
  | .sort a, .sort b => some (.sort (toExpr (glbNF (normalize a) (normalize b))))
  | _, _ => none

theorem towerGlb_total {a b : LevelTower.Head L} (ha : (LevelTower.rules L).isUniverse a)
    (hb : (LevelTower.rules L).isUniverse b) : ∃ g, towerGlb a b = some g := by
  cases ha with
  | sort l =>
      cases hb with
      | sort r => exact ⟨_, rfl⟩

/-- **It is a greatest lower bound in the cumulative order.** -/
theorem towerGlb_isGlb {a b g : LevelTower.Head L} (found : towerGlb a b = some g) :
    IsGlb (LevelTower.rules L) g a b := by
  cases a with
  | legacyGround => cases found
  | sort l =>
      cases b with
      | legacyGround => cases found
      | sort r =>
          cases found
          refine ⟨.sort _, ?_, ?_, ?_⟩
          · intro v
            rw [eval_toExpr, ← eval_normalize v l]
            exact eval_le_of_canonicalLe (glbNF_le_left (wf_normalize l)) v
          · intro v
            rw [eval_toExpr, ← eval_normalize v r]
            exact eval_le_of_canonicalLe glbNF_le_right v
          · intro u hu below₁ below₂
            cases hu with
            | sort w =>
                intro v
                have c₁ := (normalize_le_iff w l).mpr below₁
                have c₂ := (normalize_le_iff w r).mpr below₂
                rw [eval_toExpr, ← eval_normalize v w]
                exact eval_le_of_canonicalLe (le_glbNF (wf_normalize l) c₁ c₂) v

end Tower

end LevelGlb

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
