Definition A : set := Empty.

Theorem test_claim : A = Empty.
claim H1: A = Empty.
{
  reflexivity.
}
exact H1.
Qed.