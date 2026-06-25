/- ============================================================================
   Lean ladder 05 — Inductive Types (own Nat/List, recursion, auto recursors)
   (MeTTaKernel curriculum, DTT ladder, Lean 4 — vanilla)
   Style after "Theorem Proving in Lean 4", ch. Inductive Types.
   ========================================================================== -/
namespace ICL05

inductive MyNat where
  | zero : MyNat
  | succ : MyNat → MyNat

def myAdd : MyNat → MyNat → MyNat
  | n, .zero   => n
  | n, .succ m => .succ (myAdd n m)

theorem myAdd_zero (n : MyNat) : myAdd n .zero = n := rfl

inductive MyList (α : Type) where
  | nil  : MyList α
  | cons : α → MyList α → MyList α

def myLength {α : Type} : MyList α → Nat
  | .nil      => 0
  | .cons _ t => myLength t + 1

theorem myLength_cons {α : Type} (a : α) (l : MyList α) :
    myLength (.cons a l) = myLength l + 1 := rfl

-- every inductive type comes with an automatically-generated recursor
#check @MyNat.rec
#check @MyList.rec

end ICL05
