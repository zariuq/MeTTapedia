import Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeConditionalCompilation
import Mettapedia.Languages.Maude.ConditionalMaxBounds

/-! A comparison reached in a forward normalization path stays inside the
input's successor-count envelope. The finite service covers every true
numeral guard in that envelope, with source equality evidence.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeCompilation.ConditionalCompilation

open Mettapedia.Languages

theorem numeral_guard_bounded (input : Maude.Term) (left right : Nat)
    (inside : Maude.ConditionalMax.successorCount
      (Maude.ConditionalMax.maximum (Maude.ConditionalMax.numeral left) (Maude.ConditionalMax.numeral right)) ≤
      Maude.ConditionalMax.successorCount input) :
    left ≤ Maude.ConditionalMax.successorCount input ∧ right ≤ Maude.ConditionalMax.successorCount input := by
  have first := Maude.ConditionalMax.argument_bounded "max.max"
    [Maude.ConditionalMax.numeral left, Maude.ConditionalMax.numeral right]
    (term := Maude.ConditionalMax.numeral left) (by simp)
  have second := Maude.ConditionalMax.argument_bounded "max.max"
    [Maude.ConditionalMax.numeral left, Maude.ConditionalMax.numeral right]
    (term := Maude.ConditionalMax.numeral right) (by simp)
  rw [Maude.ConditionalMax.count_numeral] at first second
  exact ⟨Nat.le_trans first inside, Nat.le_trans second inside⟩

theorem true_guard_covered (input : Maude.Term) (left right : Nat)
    (inside : Maude.ConditionalMax.successorCount
      (Maude.ConditionalMax.maximum (Maude.ConditionalMax.numeral left) (Maude.ConditionalMax.numeral right)) ≤
      Maude.ConditionalMax.successorCount input) (ordered : left ≤ right) :
    (left, right) ∈ comparisonPairs (Maude.ConditionalMax.successorCount input) := by
  have bounds := numeral_guard_bounded input left right inside
  exact (comparisonPairs_iff _ _ _).mpr ⟨bounds.1, bounds.2, ordered⟩

theorem reached_root_guard_covered {input target : Maude.Term} (left right : Nat)
    (path : Maude.EquationPath Maude.Examples.conditional [] "Nat" input target)
    (shape : target = Maude.ConditionalMax.maximum (Maude.ConditionalMax.numeral left) (Maude.ConditionalMax.numeral right))
    (ordered : left ≤ right) :
    (left, right) ∈ comparisonPairs (Maude.ConditionalMax.successorCount input) := by
  apply true_guard_covered input left right
  · rw [← shape]
    exact Maude.ConditionalMax.equationPath_count path
  · exact ordered

theorem context_contains_hole {context : Maude.VariableContext} {hole result : String}
    (frame : Maude.ArgumentContext Maude.Examples.conditional.signature context hole result) (term : Maude.Term) :
    Maude.ConditionalMax.successorCount term ≤ Maude.ConditionalMax.successorCount (frame.plug term) := by
  rw [Maude.ConditionalMax.context_count]
  omega

theorem reached_context_guard_covered {input state : Maude.Term} {sort : String}
    (path : Maude.EquationPath Maude.Examples.conditional [] sort input state)
    (left right : Nat)
    (inside : Maude.ConditionalMax.successorCount
      (Maude.ConditionalMax.maximum (Maude.ConditionalMax.numeral left) (Maude.ConditionalMax.numeral right)) ≤
      Maude.ConditionalMax.successorCount state)
    (ordered : left ≤ right) :
    (left, right) ∈ comparisonPairs (Maude.ConditionalMax.successorCount input) :=
  true_guard_covered input left right (Nat.le_trans inside (Maude.ConditionalMax.equationPath_count path)) ordered

#print axioms reached_root_guard_covered
#print axioms reached_context_guard_covered

end Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeCompilation.ConditionalCompilation
