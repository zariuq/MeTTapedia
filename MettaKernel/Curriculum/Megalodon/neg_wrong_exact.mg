(* NEGATIVE: `exact H` offers a proof of A where B is required (type mismatch) *)
Theorem bad : forall A B:prop, A -> B.
let A B.
assume H: A.
exact H.
Qed.
