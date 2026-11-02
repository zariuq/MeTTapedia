import Mettapedia.Languages.OCaml.Syntax

/-! Structural pattern equality with a kernel-checked reflection theorem.
Constructor identities, literal values, nesting and binder positions remain
part of equality; no pattern-equivalence quotient is imposed.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.OCaml

mutual
  def patternEqual : MatchPattern → MatchPattern → Bool
    | .bind, .bind | .wildcard, .wildcard => true
    | .literal first, .literal second => decide (first = second)
    | .tuple first, .tuple second => patternsEqual first second
    | .cons head tail, .cons first rest => patternEqual head first && patternEqual tail rest
    | .variant firstType firstConstructor first, .variant secondType secondConstructor second =>
        decide (firstType = secondType) && decide (firstConstructor = secondConstructor) && patternsEqual first second
    | _, _ => false

  def patternsEqual : List MatchPattern → List MatchPattern → Bool
    | [], [] => true
    | first :: rest, second :: tail => patternEqual first second && patternsEqual rest tail
    | _, _ => false
end

theorem patternEqual_iff (first : MatchPattern) : ∀ second, patternEqual first second = true ↔ first = second := by
  refine MatchPattern.rec
    (motive_1 := fun first => ∀ second, patternEqual first second = true ↔ first = second)
    (motive_2 := fun first => ∀ second, patternsEqual first second = true ↔ first = second)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ first
  · intro second
    cases second <;> simp [patternEqual]
  · intro second
    cases second <;> simp [patternEqual]
  · intro literal second
    cases second <;> simp [patternEqual]
  · intro fields ih second
    cases second <;> simp_all [patternEqual]
  · intro head tail headIH tailIH second
    cases second <;> simp_all [patternEqual]
  · intro typeId constructor fields ih second
    cases second <;> simp_all [patternEqual, and_assoc]
  · intro second
    cases second <;> simp [patternsEqual]
  · intro head rest headIH restIH second
    cases second <;> simp_all [patternsEqual]

theorem patternEqual_self (pattern : MatchPattern) : patternEqual pattern pattern = true :=
  (patternEqual_iff pattern pattern).mpr rfl

def patternIndex? (wanted : MatchPattern) : List MatchPattern → Option Nat
  | [] => none
  | first :: rest => if patternEqual first wanted then some 0 else Nat.succ <$> patternIndex? wanted rest

theorem patternIndex?_sound (wanted : MatchPattern) (pool : List MatchPattern) (index : Nat)
    (found : patternIndex? wanted pool = some index) : pool[index]? = some wanted := by
  induction pool generalizing index with
  | nil => cases found
  | cons first rest ih =>
    simp only [patternIndex?] at found
    split at found
    · rename_i same
      have equal := (patternEqual_iff first wanted).mp same
      cases Option.some.inj found
      simpa only [List.getElem?_cons_zero] using congrArg some equal
    · obtain ⟨tailIndex, tailFound, same⟩ := Option.map_eq_some_iff.mp found
      cases same
      exact ih _ tailFound

theorem patternIndex?_complete (wanted : MatchPattern) (pool : List MatchPattern) (member : wanted ∈ pool) :
    ∃ index, patternIndex? wanted pool = some index := by
  induction pool with
  | nil => cases member
  | cons first rest ih =>
    by_cases same : patternEqual first wanted = true
    · exact ⟨0, by simp [patternIndex?, same]⟩
    · rcases List.mem_cons.mp member with equal | later
      · subst first
        exact (same (patternEqual_self wanted)).elim
      · obtain ⟨index, found⟩ := ih later
        exact ⟨index + 1, by simp [patternIndex?, same, found]⟩

theorem patternIndex?_none_iff (wanted : MatchPattern) (pool : List MatchPattern) :
    patternIndex? wanted pool = none ↔ wanted ∉ pool := by
  constructor
  · intro missing member
    obtain ⟨index, found⟩ := patternIndex?_complete wanted pool member
    rw [missing] at found
    cases found
  · intro absent
    cases found : patternIndex? wanted pool with
    | none => rfl
    | some index =>
      have selected := patternIndex?_sound wanted pool index found
      exact (absent (List.mem_of_getElem? selected)).elim

example : patternEqual (.tuple [.bind, .cons .wildcard (.literal .nil)])
    (.tuple [.bind, .cons .wildcard (.literal .nil)]) = true := by decide_cbv
example : patternEqual (.tuple [.bind, .wildcard]) (.tuple [.wildcard, .bind]) = false := by decide_cbv
example : patternEqual (.variant 0 1 [.bind]) (.variant 0 2 [.bind]) = false := by decide_cbv

#print axioms patternEqual_iff

end Mettapedia.Languages.OCaml
