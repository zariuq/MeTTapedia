import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic
import Mettapedia.Languages.MeTTa.TensorDSL.Syntax

/-!
# MeTTa Tensor DSL Valence Semantics

Foundational valence algebra and theorem obligations:
- canonicalization idempotence (fixed dummy set)
- dummy-renaming invariance (fresh rename, then canonicalize)
- contraction soundness via arity monotonicity
-/

namespace Mettapedia.Languages.MeTTa.TensorDSL

def dummyMarker : String := "__dummy__"

structure Valence where
  up : List String
  down : List String
deriving DecidableEq, Repr, Inhabited

namespace Valence

def names (v : Valence) : List String :=
  v.up ++ v.down

def arity (v : Valence) : Nat :=
  v.up.length + v.down.length

def append (v₁ v₂ : Valence) : Valence :=
  ⟨v₁.up ++ v₂.up, v₁.down ++ v₂.down⟩

def ofIndices : List Index → Valence
  | [] => ⟨[], []⟩
  | ix :: rest =>
    let v := ofIndices rest
    match ix.variance with
    | .up => ⟨ix.name :: v.up, v.down⟩
    | .down => ⟨v.up, ix.name :: v.down⟩

def dummyNames (v : Valence) : Finset String :=
  v.up.toFinset ∩ v.down.toFinset

def renameInList (dummy : Finset String) (fresh : String) (xs : List String) : List String :=
  xs.map (fun n => if n ∈ dummy then fresh else n)

def canonicalize (dummy : Finset String) (v : Valence) : Valence :=
  ⟨renameInList dummy dummyMarker v.up, renameInList dummy dummyMarker v.down⟩

def canonicalizeAuto (v : Valence) : Valence :=
  canonicalize (dummyNames v) v

def renameDummies (dummy : Finset String) (fresh : String) (v : Valence) : Valence :=
  ⟨renameInList dummy fresh v.up, renameInList dummy fresh v.down⟩

def renameDummiesAuto (fresh : String) (v : Valence) : Valence :=
  renameDummies (dummyNames v) fresh v

def removeOne (target : String) : List String → List String
  | [] => []
  | x :: xs => if x = target then xs else x :: removeOne target xs

def contract (name : String) (v : Valence) : Valence :=
  ⟨removeOne name v.up, removeOne name v.down⟩

theorem renameInList_idempotent (dummy : Finset String) (fresh : String) (xs : List String) :
    renameInList dummy fresh (renameInList dummy fresh xs) = renameInList dummy fresh xs := by
  unfold renameInList
  rw [List.map_map]
  apply List.map_congr_left
  intro a ha
  by_cases h : a ∈ dummy
  · simp [h]
  · simp [h]

theorem canonicalize_idempotent (dummy : Finset String) (v : Valence) :
    canonicalize dummy (canonicalize dummy v) = canonicalize dummy v := by
  cases v
  simp [canonicalize, renameInList_idempotent]

theorem canonicalize_after_dummy_rename_list
    (dummy : Finset String) (fresh : String) (xs : List String)
    (hfresh : fresh ∉ xs) :
    renameInList (insert fresh dummy) dummyMarker (renameInList dummy fresh xs) =
      renameInList dummy dummyMarker xs := by
  unfold renameInList
  rw [List.map_map]
  apply List.map_congr_left
  intro a ha
  have haFresh : a ≠ fresh := by
    intro hEq
    apply hfresh
    simpa [hEq] using ha
  by_cases haDummy : a ∈ dummy
  · simp [haDummy]
  · simp [haDummy, haFresh]

theorem canonicalize_dummy_rename_invariant
    (dummy : Finset String) (fresh : String) (v : Valence)
    (hfresh : fresh ∉ v.names) :
    canonicalize (insert fresh dummy) (renameDummies dummy fresh v) = canonicalize dummy v := by
  rcases v with ⟨up, down⟩
  have hfreshUp : fresh ∉ up := by
    intro h
    apply hfresh
    simp [Valence.names, h]
  have hfreshDown : fresh ∉ down := by
    intro h
    apply hfresh
    simp [Valence.names, h]
  simp [canonicalize, renameDummies, canonicalize_after_dummy_rename_list, hfreshUp, hfreshDown]

theorem removeOne_length_le (target : String) (xs : List String) :
    (removeOne target xs).length ≤ xs.length := by
  induction xs with
  | nil => simp [removeOne]
  | cons x xs ih =>
    by_cases hx : x = target
    · simp [removeOne, hx]
    · simp [removeOne, hx, ih]

theorem removeOne_length_eq_sub_one (target : String) (xs : List String) (hmem : target ∈ xs) :
    (removeOne target xs).length = xs.length - 1 := by
  induction xs with
  | nil =>
    cases hmem
  | cons x xs ih =>
    simp at hmem ⊢
    by_cases hx : x = target
    · simp [removeOne, hx]
    · have hmemTail : target ∈ xs := by
        rcases hmem with hEq | hTail
        · exfalso
          exact hx hEq.symm
        · exact hTail
      have hlenPos : 1 ≤ xs.length := Nat.succ_le_of_lt (List.length_pos_of_mem hmemTail)
      simpa [removeOne, hx, ih hmemTail] using Nat.sub_add_cancel hlenPos

theorem contract_arity_le (name : String) (v : Valence) :
    (contract name v).arity ≤ v.arity := by
  rcases v with ⟨up, down⟩
  simp [Valence.contract, Valence.arity]
  exact Nat.add_le_add (removeOne_length_le name up) (removeOne_length_le name down)

theorem contract_arity_eq_sub_two
    (name : String) (v : Valence)
    (hup : name ∈ v.up) (hdown : name ∈ v.down) :
    (contract name v).arity = v.arity - 2 := by
  rcases v with ⟨up, down⟩
  have hupLen : (removeOne name up).length = up.length - 1 :=
    removeOne_length_eq_sub_one name up hup
  have hdownLen : (removeOne name down).length = down.length - 1 :=
    removeOne_length_eq_sub_one name down hdown
  have hupPos : 1 ≤ up.length := by
    exact Nat.succ_le_of_lt (List.length_pos_of_mem hup)
  have hdownPos : 1 ≤ down.length := by
    exact Nat.succ_le_of_lt (List.length_pos_of_mem hdown)
  have hArith :
      (up.length - 1) + (down.length - 1) = (up.length + down.length) - 2 := by
    omega
  simpa [Valence.contract, Valence.arity, hupLen, hdownLen] using hArith

end Valence

namespace Expr

open Valence

/-- Valence semantics for tensor expressions. -/
def valence : Expr → Valence
  | .tensor _ idxs => Valence.ofIndices idxs
  | .add lhs rhs => (valence lhs).append (valence rhs)
  | .mul lhs rhs => (valence lhs).append (valence rhs)
  | .contract name body => Valence.contract name (valence body)
  | .partialD body ix => (valence body).append (Valence.ofIndices [ix])
  | .covD body ix _ => (valence body).append (Valence.ofIndices [ix])
  | .metric i j => Valence.ofIndices [i, j]
  | .invMetric i j => Valence.ofIndices [i, j]
  | .delta i j => Valence.ofIndices [i, j]

theorem valence_contract_sound (name : String) (body : Expr) :
    valence (.contract name body) = Valence.contract name (valence body) := by
  rfl

end Expr

end Mettapedia.Languages.MeTTa.TensorDSL
