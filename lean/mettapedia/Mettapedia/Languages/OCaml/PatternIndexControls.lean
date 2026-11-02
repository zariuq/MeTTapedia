import Mettapedia.Languages.OCaml.PatternEquality

/-! Pattern-pool lookup retains the first exact occurrence and refuses
missing patterns. Duplicate pool entries do not change the selected index.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.OCaml

theorem patternIndex?_first (wanted : MatchPattern) (before after : List MatchPattern)
    (absent : wanted ∉ before) : patternIndex? wanted (before ++ wanted :: after) = some before.length := by
  induction before with
  | nil => simp [patternIndex?, patternEqual_self]
  | cons first rest ih =>
    have different : patternEqual first wanted = false := by
      cases same : patternEqual first wanted with
      | false => rfl
      | true =>
        have equal := (patternEqual_iff first wanted).mp same
        exact (absent (by simp [equal])).elim
    have later : wanted ∉ rest := fun member => absent (List.mem_cons_of_mem first member)
    simp [List.cons_append, patternIndex?, different, ih later]

example : patternIndex? (.tuple [.bind, .wildcard])
    [.bind, .tuple [.bind, .wildcard], .tuple [.bind, .wildcard]] = some 1 := by decide_cbv
example : patternIndex? (.tuple [.wildcard, .bind]) [.tuple [.bind, .wildcard]] = none := by decide_cbv
example : patternIndex? (.variant 0 2 [.bind]) [.variant 0 1 [.bind]] = none := by decide_cbv

#print axioms patternIndex?_first

end Mettapedia.Languages.OCaml
