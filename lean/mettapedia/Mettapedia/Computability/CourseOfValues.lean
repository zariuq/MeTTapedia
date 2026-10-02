import Mathlib.Computability.Primrec.List

/-!
# Course-of-values recursion from a step

A function on the natural numbers is defined by course-of-values recursion
when its value at `n` is computed from the list of its values below `n`.
Given the step that does the computing, the function is built here by
ordinary recursion on the table of earlier values, and it is primitive
recursive whenever the step is.
-/

set_option autoImplicit false

namespace Mettapedia.Computability

variable {σ : Type*}

/-- The values below a bound, in order. -/
def courseTable (step : List σ → σ) : ℕ → List σ
  | 0 => []
  | bound + 1 => courseTable step bound ++ [step (courseTable step bound)]

/-- The function whose value at `n` is the step applied to the list of its
values below `n`. -/
def courseOfValues (step : List σ → σ) (n : ℕ) : σ :=
  step (courseTable step n)

/-- The table below a bound lists the values of the function below it. -/
theorem courseTable_eq_map (step : List σ → σ) (bound : ℕ) :
    courseTable step bound = (List.range bound).map (courseOfValues step) := by
  induction bound with
  | zero => rfl
  | succ bound recurse =>
      rw [courseTable, List.range_succ, List.map_append, ← recurse]
      rfl

/-- **The recursion equation.**  The value at `n` is the step applied to the
values below `n`. -/
theorem courseOfValues_eq (step : List σ → σ) (n : ℕ) :
    courseOfValues step n = step ((List.range n).map (courseOfValues step)) := by
  rw [← courseTable_eq_map]
  rfl

/-- An earlier value is found in the table at its own position. -/
theorem getD_map_range (function : ℕ → σ) (default : σ) {position bound : ℕ}
    (earlier : position < bound) :
    ((List.range bound).map function).getD position default = function position := by
  simp [List.getD_eq_getElem?_getD, earlier]

/-- **A function defined by course-of-values recursion from a primitive
recursive step is primitive recursive.** -/
theorem courseOfValues_primrec [Primcodable σ] {step : List σ → σ} (primitive : Primrec step) :
    Primrec (courseOfValues step) := by
  have strong : Primrec₂ fun (_ : Unit) n => courseOfValues step n :=
    Primrec.nat_strong_rec (fun (_ : Unit) n => courseOfValues step n)
      (g := fun _ earlier => some (step earlier))
      (Primrec.option_some.comp (primitive.comp Primrec.snd))
      fun _ n => congrArg some (courseOfValues_eq step n).symm
  exact strong.comp (Primrec.const ()) Primrec.id

end Mettapedia.Computability
