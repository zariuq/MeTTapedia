Definition symm_diff : set -> set -> set :=
  fun A B => (A :\: B) :\/: (B :\: A).

Theorem symm_diff_self : forall A:set, symm_diff A A = Empty.
let A.
prove (A :\: A) :\/: (A :\: A) = Empty.
rewrite setminus_selfannih.
prove Empty :\/: Empty = Empty.
apply binunion_idl.
Qed.

Theorem symm_diff_comm : forall A B:set, symm_diff A B = symm_diff B A.
let A. let B.
prove (A :\: B) :\/: (B :\: A) = (B :\: A) :\/: (A :\: B).
apply binunion_com.
Qed.

Theorem symm_diff_empty_l : forall A:set, symm_diff Empty A = A.
let A.
prove (Empty :\: A) :\/: (A :\: Empty) = A.
rewrite setminus_annil.
rewrite setminus_idr.
prove Empty :\/: A = A.
apply binunion_idl.
Qed.

Theorem symm_diff_empty_r : forall A:set, symm_diff A Empty = A.
let A.
prove (A :\: Empty) :\/: (Empty :\: A) = A.
rewrite setminus_idr.
rewrite setminus_annil.
prove A :\/: Empty = A.
apply binunion_idr.
Qed.
