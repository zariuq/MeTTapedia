import Mettapedia.Logic.LP.VariantMatching

/-! Executable controls for simultaneous, globally consistent renaming. -/

namespace Mettapedia.Logic.LP.VariantMatching.Controls

open UnificationRenaming.Controls

def accepts (left right : List (Term sig)) : Bool := (solve left right).isSome

/-- info: some [(0, 1), (1, 0)] -/
#guard_msgs in
#eval solve [arrow (.var 0) (.var 1)] [arrow (.var 1) (.var 0)]

/-- info: true -/
#guard_msgs in
#eval accepts [arrow (.var 0) (.var 0)] [arrow (.var 2) (.var 2)]

/-- info: false -/
#guard_msgs in
#eval accepts [arrow (.var 0) (.var 0)] [arrow (.var 2) (.var 3)]

/-- info: false -/
#guard_msgs in
#eval accepts [arrow (.var 0) (.var 1)] [arrow (.var 2) (.var 2)]

/-- info: false -/
#guard_msgs in
#eval accepts [.var 0, .var 0] [.var 1, .var 2]

/-- info: false -/
#guard_msgs in
#eval accepts [.var 0, .var 1] [.var 2, .var 2]

-- An identical first constraint still fixes the map used by later ones.
/-- info: false -/
#guard_msgs in
#eval accepts [.var 0, .var 0] [.var 0, .var 1]

/-- info: true -/
#guard_msgs in
#eval accepts [.var 0, .var 1] [.var 1, .var 0]

/-- info: false -/
#guard_msgs in
#eval accepts [.var 0] [arrow (.var 1) (.var 1)]

/-- info: false -/
#guard_msgs in
#eval accepts [arrow (.var 1) (.var 1)] [.var 0]

/-- info: false -/
#guard_msgs in
#eval accepts [.var 0] []

/-- info: some [] -/
#guard_msgs in
#eval solve ([] : List (Term sig)) []

-- Unmentioned variables remain untouched by a saved finite map.
/-- info: (1, 0, 2) -/
#guard_msgs in
#eval (lookup (σ := sig) [(0, 1), (1, 0)] 0,
       lookup (σ := sig) [(0, 1), (1, 0)] 1,
       lookup (σ := sig) [(0, 1), (1, 0)] 2)

#print axioms solve_sound
#print axioms solve_complete
#print axioms solve_none_iff
#print axioms singleton_iff
#print axioms solve_round_trip

end Mettapedia.Logic.LP.VariantMatching.Controls
