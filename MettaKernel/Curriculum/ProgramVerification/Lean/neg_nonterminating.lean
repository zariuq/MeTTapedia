-- NEGATIVE: Lean's termination checker rejects this (no decreasing measure)
def loop (n : Nat) : Nat := loop n + 1
