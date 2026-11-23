; Recursive constructor matching with two equal physical fork clauses.
(= (strip Z) (Box Z))
(= (strip (S $x)) (strip $x))
(= (fork $x) (strip $x))
(= (fork $x) (strip $x))
!(fork (S (S Z)))
