import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.Step

/-!
# The ambient program: a larger program admits more, and a union admits what its parts admit

Over any frame action, extensions and code system, at every state. The ambient program enters
admission in one place, the availability of the use (`RState.Available`); the guard predicate and the
result do not mention it. So:

* `RFiring.admits_ambient_mono`, **`succ_ambient_mono`**: a firing admitted beside an ambient program
  is admitted beside every larger one, with the same result. Adding to the ambient program removes
  no transition.
* **`succ_ambient_union`**: the transitions beside a union of two ambient programs are the
  transitions beside one or beside the other. A firing uses one rule.

The transitions beside the empty ambient program are those of the rules the state holds, and they
are among the transitions beside every ambient program (`succ_ambient_mono` at `∅`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences

open Interface (Frames)
open LogicOverTheStep.StepSpan (Succ)

universe uO uT uH uE uOcc uR uC uZ

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {O : Type uOcc} {R : Type uR} {C : Type uC} {Z : Type uZ}

/-- A use available beside an ambient program is available beside every larger one. -/
theorem RState.available_mono {s : RState Tm O R C Z} {A A' : Set C} (larger : A ⊆ A')
    {u : Use C R} (available : s.Available A u) : s.Available A' u := by
  cases u with
  | ambient c => exact larger available
  | held ρ => exact available

/-- A use available beside a union is available beside one of its parts. -/
theorem RState.available_union {s : RState Tm O R C Z} {A B : Set C} {u : Use C R}
    (available : s.Available (A ∪ B) u) : s.Available A u ∨ s.Available B u := by
  cases u with
  | ambient c => exact available
  | held ρ => exact Or.inl available

variable (X : Frames Tm Hom) {E : Extensions.{uO, uH, uE} Hom} {codes : Codes Tm C Z}
  {s : RState Tm O R C Z}

/-- The shapes of the rule occurrences, beside another ambient program beside which the use is
available. -/
theorem RFiring.ruleShapes_of_available (f : RFiring O R E codes s) {A A' : Set C}
    (shapes : f.RuleShapes A) (available : s.Available A' f.use) : f.RuleShapes A' :=
  ⟨available, shapes.arguments, shapes.installed, shapes.madeNodup, shapes.madeLength,
    shapes.madeNew, shapes.removed, shapes.removedNodup, shapes.removedHeld, shapes.published⟩

variable [DecidableEq O]

/-- **A firing admitted beside an ambient program is admitted beside every program beside which its
use is available.** -/
theorem RFiring.admits_of_available (f : RFiring O R E codes s) {A A' : Set C}
    (admitted : f.Admits X A) (available : s.Available A' f.use) : f.Admits X A' := by
  obtain ⟨⟨fresh, rows, shapes⟩, rest⟩ := admitted
  exact ⟨⟨fresh, rows, f.ruleShapes_of_available shapes available⟩, rest⟩

/-- **A firing admitted beside an ambient program is admitted beside every larger one.** -/
theorem RFiring.admits_ambient_mono (f : RFiring O R E codes s) {A A' : Set C} (larger : A ⊆ A')
    (admitted : f.Admits X A) : f.Admits X A' :=
  f.admits_of_available X admitted (RState.available_mono larger admitted.1.2.2.available)

variable [DecidableEq R]

variable (R E codes) in
/-- **Adding to the ambient program removes no transition.** -/
theorem succ_ambient_mono {A A' : Set C} (larger : A ⊆ A') {s t : RState Tm O R C Z}
    (moved : Succ (rstep X O R E codes A).toStep s t) :
    Succ (rstep X O R E codes A').toStep s t := by
  obtain ⟨f, admitted, same⟩ := moved
  exact ⟨f, f.admits_ambient_mono X larger admitted, same⟩

variable (R E codes) in
/-- **The transitions beside a union of ambient programs are those beside one or the other.** -/
theorem succ_ambient_union (A B : Set C) (s t : RState Tm O R C Z) :
    Succ (rstep X O R E codes (A ∪ B)).toStep s t ↔
      Succ (rstep X O R E codes A).toStep s t ∨ Succ (rstep X O R E codes B).toStep s t := by
  constructor
  · rintro ⟨f, admitted, same⟩
    have shapes : f.RuleShapes (A ∪ B) := admitted.1.2.2
    rcases RState.available_union shapes.available with inA | inB
    · exact Or.inl ⟨f, f.admits_of_available X admitted inA, same⟩
    · exact Or.inr ⟨f, f.admits_of_available X admitted inB, same⟩
  · rintro (moved | moved)
    · exact succ_ambient_mono R X E codes Set.subset_union_left moved
    · exact succ_ambient_mono R X E codes Set.subset_union_right moved

#print axioms RFiring.admits_ambient_mono
#print axioms succ_ambient_mono
#print axioms succ_ambient_union

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences
