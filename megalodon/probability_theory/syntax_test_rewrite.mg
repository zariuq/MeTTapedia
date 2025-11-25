Definition A : set := Empty.
Theorem test : A = Empty.
claim H: A = Empty. { reflexivity. }
rewrite H.
reflexivity.
Qed.