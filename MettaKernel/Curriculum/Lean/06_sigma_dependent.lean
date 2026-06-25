/- ============================================================================
   Lean ladder 06 — Σ-types and dependent / indexed families
   (MeTTaKernel curriculum, DTT ladder, Lean 4 — vanilla)
   Style after "Theorem Proving in Lean 4" (Σ) and "Functional Programming in
   Lean" (length-indexed vectors).
   ========================================================================== -/
namespace ICL06

-- Σ-type: a value paired with *data* depending on it (second component is a Type)
def sigmaPair : Σ _ : Nat, Bool := ⟨3, true⟩
theorem sigmaPair_fst : sigmaPair.fst = 3 := rfl

-- Subtype {x // p x}: a value paired with a *proof* about it (second is a Prop)
def witnessThree : { n : Nat // n = 3 } := ⟨3, rfl⟩
theorem witnessThree_val : witnessThree.val = 3 := rfl

-- length-indexed vectors: an indexed inductive family
inductive Vec (α : Type) : Nat → Type where
  | nil  : Vec α 0
  | cons : {n : Nat} → α → Vec α n → Vec α (n + 1)

-- `head` is total here: the type rules out the empty case (index n+1 ≠ 0)
def Vec.head {α : Type} {n : Nat} : Vec α (n + 1) → α
  | .cons a _ => a

def v123 : Vec Nat 3 := .cons 1 (.cons 2 (.cons 3 .nil))

theorem head_v123 : Vec.head v123 = 1 := rfl

end ICL06
