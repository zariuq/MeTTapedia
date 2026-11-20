import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.Step

/-!
# A firing of a plain code at a closed state is a firing of the present step, with the rule shapes

A spec is **plain** (`Spec.Plain`) when it has no parameters, no rule queries, no installed or
removed rules and no published rows, and the rules it makes have no arguments. A state is **closed** (`RState.Closed`) when no held rule has
arguments. For a firing of a plain spec at a closed state:

* its opening is fresh exactly when it is fresh in the present step (`fresh_iff_base`);
* its information is that of the present step (`information_of_plain`), and so is its guard predicate
  (`holds_iff_base`);
* **`admits_plain`**: it is admitted exactly when its firing of the present step (`RFiring.base`, a
  firing of the one rule the spec contains) is admitted and the shapes of the rule occurrences hold;
* the rows, the knowledge and the frame of its result are those of the present step
  (`toState_result_of_plain`).

So a plain code adds to a rule of the present step exactly this: which occurrence is used, whether it
is kept, and which rule occurrences are made.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire)

universe uO uT uH uE uOcc uR uC uZ

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}

namespace RFiring

variable (X : Frames Tm Hom) {O : Type uOcc} {R : Type uR} {C : Type uC} {Z : Type uZ}
  {E : Extensions.{uO, uH, uE} Hom} {codes : Codes Tm C Z} {s : RState Tm O R C Z}
  (f : RFiring O R E codes s)

/-- **Freshness agrees** at a closed state, for a plain spec. -/
theorem fresh_iff_base (closed : s.Closed) (plain : f.spec.Plain) :
    f.Fresh X ↔ f.base.Fresh X s.toState := by
  have terms : f.spec.terms = f.spec.toRule.terms := Spec.terms_of_plain plain
  constructor
  · intro fresh b g h
    obtain ⟨u, state, rule⟩ := fresh b g h
    refine ⟨u, fun t mentioned => state t ((RState.mentions_of_closed closed t).mpr mentioned),
      fun t inside => rule t ?_⟩
    rw [terms]
    exact inside
  · intro fresh b g h
    obtain ⟨u, state, rule⟩ := fresh b g h
    refine ⟨u, fun t mentioned => state t ((RState.mentions_of_closed closed t).mp mentioned),
      fun t inside => rule t ?_⟩
    rw [terms] at inside
    exact inside

/-- A spec without parameters adds no closure equation. -/
theorem env_of_plain (plain : f.spec.Plain) : f.env X = [] := by
  unfold env
  rw [plain.params]
  rfl

/-- **The information agrees.** -/
theorem information_of_plain (plain : f.spec.Plain) :
    f.information X = f.base.information X s.toState := by
  unfold information
  rw [f.env_of_plain X plain, List.append_nil]

/-- **The guard predicate agrees**: a plain spec has no rule queries, installs nothing and removes
nothing. -/
theorem holds_iff_base (plain : f.spec.Plain) {b : Obj} (σ : Hom (E.target f.ext) b) :
    f.Holds X σ ↔ f.base.Holds X s.toState σ := by
  unfold Holds
  constructor
  · exact fun holds => holds.1
  · intro holds
    refine ⟨holds, ?_, ?_, ?_, ?_⟩
    · intro q inside
      rw [plain.unmatched] at inside
      exact absurd inside List.not_mem_nil
    · intro x inside
      rw [plain.installs, List.zip_nil_left] at inside
      exact absurd inside List.not_mem_nil
    · intro x inside
      rw [plain.removes, List.zip_nil_left] at inside
      exact absurd inside List.not_mem_nil
    · intro x inside
      rw [plain.publishes, List.zip_nil_left] at inside
      exact absurd inside List.not_mem_nil

variable [DecidableEq O]

/-- **Admission of a plain code at a closed state**: its firing of the present step is admitted, and
the shapes of the rule occurrences hold. -/
theorem admits_plain (closed : s.Closed) (plain : f.spec.Plain) (ambient : Set C) :
    f.Admits X ambient ↔ f.base.Admits X s.toState ∧ f.RuleShapes ambient := by
  unfold Admits Shapes Firing.Admits Firing.Shapes
  rw [f.information_of_plain X plain, f.fresh_iff_base X closed plain]
  constructor
  · rintro ⟨⟨fresh, rows, rules⟩, enabled, solvable, asks⟩
    exact ⟨⟨⟨fresh, rows⟩, enabled, solvable,
      fun b σ solved => (f.holds_iff_base X plain σ).mp (asks b σ solved)⟩, rules⟩
  · rintro ⟨⟨⟨fresh, rows⟩, enabled, solvable, asks⟩, rules⟩
    exact ⟨⟨fresh, rows, rules⟩, enabled, solvable,
      fun b σ solved => (f.holds_iff_base X plain σ).mpr (asks b σ solved)⟩

variable [DecidableEq R]

/-- **The rows, the knowledge and the frame of the result** are those of the present step. -/
theorem toState_result_of_plain (plain : f.spec.Plain) :
    (f.result X).toState = f.base.result X s.toState := by
  have info := f.information_of_plain X plain
  unfold result
  rw [info]
  rfl

end RFiring

#print axioms RFiring.fresh_iff_base
#print axioms RFiring.information_of_plain
#print axioms RFiring.holds_iff_base
#print axioms RFiring.admits_plain
#print axioms RFiring.toState_result_of_plain

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences
