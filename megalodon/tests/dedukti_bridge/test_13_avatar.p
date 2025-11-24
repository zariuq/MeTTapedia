% AVATAR-ish split: (p | q) & (~p | r) & (~q) & (~r) -> false
fof(c1, axiom, p | q).
fof(c2, axiom, (~p | r)).
fof(c3, axiom, ~q).
fof(c4, axiom, ~r).
fof(goal, conjecture, $false).
