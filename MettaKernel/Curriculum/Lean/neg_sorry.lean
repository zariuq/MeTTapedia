-- NEGATIVE: a `sorry` must be reported; warningAsError makes it a hard error.
set_option warningAsError true
theorem cheat : 2 + 2 = 5 := by sorry
