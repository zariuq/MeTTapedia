(* NEGATIVE: Qed with the goal still open (no proof of A) *)
Theorem bad : forall A:prop, A.
let A.
Qed.
