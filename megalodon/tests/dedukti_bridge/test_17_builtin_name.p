% Built-in name hygiene: ensure 'empty' doesn't clash
fof(no_empty, axiom, empty != a).
fof(goal, conjecture, a = empty).
