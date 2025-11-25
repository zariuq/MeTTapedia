Definition A : set := Empty.
Theorem test_set : A = Empty.
set x := Empty.
claim H: x = Empty.
{ reflexivity. }
rewrite <- H.
reflexivity.
Qed.