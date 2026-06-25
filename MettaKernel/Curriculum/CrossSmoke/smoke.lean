-- Cross-system smoke (Lean): the same tiny theorems proved in all three checkers.
theorem imp_id (P : Prop) : P → P := fun p => p
theorem and_elim_l (P Q : Prop) : P ∧ Q → P := fun h => h.1
theorem ex_falso (P : Prop) : False → P := fun h => h.elim
theorem eq_refl_ex {A : Type} (a : A) : a = a := rfl
theorem cong {A B : Type} (f : A → B) (x y : A) : x = y → f x = f y := fun e => by rw [e]
theorem pair_proj {A B : Type} (a : A) (b : B) : (a, b).1 = a := rfl
