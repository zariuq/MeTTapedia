-- NEGATIVE: taking the head of the EMPTY vector is a dependent-index type error.
inductive Vec (α : Type) : Nat → Type where
  | nil  : Vec α 0
  | cons : {n : Nat} → α → Vec α n → Vec α (n + 1)
def Vec.head {α : Type} {n : Nat} : Vec α (n + 1) → α
  | .cons a _ => a
def bad : Nat := Vec.head (Vec.nil : Vec Nat 0)
