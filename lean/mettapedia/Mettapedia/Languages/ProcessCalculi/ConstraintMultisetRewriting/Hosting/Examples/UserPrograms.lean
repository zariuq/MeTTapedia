import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.WellFormedRuns

/-!
# Programs a user writes, elaborated by value, against the run theorems' hypotheses

Surface MeTTa programs, elaborated by value (`Elaboration.elaborate`, every undeclared position by
value), checked against the program-side hypotheses of `WellFormedRuns.arrow_runs_forward`
(`WellFormed` and the fragment with arrows), decided by the kernel:

* `len`, with a base case and a recursive case that uses its own result, `(S (len $t))`
  (`len_hosted`);
* mutual recursion, `even` and `odd` (`evenOdd_hosted`).

A call through a function variable, `($f …)`, has an elaboration clause of its own (a tuple whose head
is not a symbol); programs whose text contains one (such as `map` applying a received function, or
`twice`) are not among these examples.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Examples.UserPrograms

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open SourceLanguage SourceLanguage.Elaboration SourceLanguage.Toolkit
open Hosting

/-! ## A decidable reading of the fragment with arrows -/

/-- The fragment with arrows, as a computation. -/
def arrowB {κ : Keys MSig} {Ty : Type} : Comp κ [] () Ty → Bool
  | .ret _ => true
  | .apply _ => true
  | .let_ _ _ c k => arrowB c && arrowB k
  | .choice c d => arrowB c && arrowB d
  | .fail => true
  | _ => false

theorem arrow_of_arrowB {κ : Keys MSig} {Ty : Type} : ∀ c : Comp κ [] () Ty, arrowB c = true → ArrowComp c
  | .ret _, _ => trivial
  | .apply _, _ => trivial
  | .let_ _ _ c k, h => by
      simp only [arrowB, Bool.and_eq_true] at h
      exact ⟨arrow_of_arrowB c h.1, arrow_of_arrowB k h.2⟩
  | .choice c d, h => by
      simp only [arrowB, Bool.and_eq_true] at h
      exact ⟨arrow_of_arrowB c h.1, arrow_of_arrowB d h.2⟩
  | .fail, _ => trivial
  | .run _, h => by simp [arrowB] at h
  | .query _ _ _, h => by simp [arrowB] at h
  | .add _ _ _, h => by simp [arrowB] at h
  | .remove _ _ _, h => by simp [arrowB] at h
  | .new _ _ _, h => by simp [arrowB] at h
  | .check _ _, h => by simp [arrowB] at h
  | .delay _ _ _ _, h => by simp [arrowB] at h
  | .force _, h => by simp [arrowB] at h

theorem arrowProgram_of {P : SourceLanguage.Program mkeys [] () MTy}
    (all : (P.equations.all fun e => arrowB e.rhs) = true) : ArrowProgram P := by
  intro e member
  exact arrow_of_arrowB e.rhs (List.all_eq_true.mp all e member)

/-- A negative example of the decidable reading: `run` is outside the fragment with arrows. -/
theorem arrowB_run (t : MData) : arrowB (.run t : Comp mkeys [] () MTy) = false := rfl

/-- By value at every undeclared position. -/
def byValue : Params := ⟨fun _ _ => .value, false, false⟩

/-! ## `len` -/

def hL : MData := foD [] [204] 0
def tL : MData := foD [] [204] 1

def lenNilS : SEquation := ⟨[203], "len", [sym "Nil"], .text (sym "Z")⟩
def lenConsS : SEquation :=
  ⟨[204], "len", [tuple [sym "Cons", hL, tL]], .text (tuple [sym "S", tuple [sym "len", tL]])⟩

def lenV : SourceLanguage.Program mkeys [] () MTy := elaborate byValue ⟨[], [lenNilS, lenConsS]⟩

/-- **`len` by value is well formed and in the fragment with arrows.** -/
theorem len_hosted : WellFormed lenV ∧ ArrowProgram lenV :=
  ⟨by decide, arrowProgram_of (by decide)⟩

/-! ## `even` and `odd` -/

def nE : MData := foD [] [221] 0
def nO : MData := foD [] [223] 0

def evenZ : SEquation := ⟨[220], "even", [sym "Z"], .text (sym "True")⟩
def evenS : SEquation := ⟨[221], "even", [tuple [sym "S", nE]], .text (tuple [sym "odd", nE])⟩
def oddZ : SEquation := ⟨[222], "odd", [sym "Z"], .text (sym "False")⟩
def oddS : SEquation := ⟨[223], "odd", [tuple [sym "S", nO]], .text (tuple [sym "even", nO])⟩

def evenOddV : SourceLanguage.Program mkeys [] () MTy := elaborate byValue ⟨[], [evenZ, evenS, oddZ, oddS]⟩

/-- **`even`/`odd` by value are well formed and in the fragment with arrows.** -/
theorem evenOdd_hosted : WellFormed evenOddV ∧ ArrowProgram evenOddV :=
  ⟨by decide, arrowProgram_of (by decide)⟩

#print axioms arrowProgram_of
#print axioms arrowB_run
#print axioms len_hosted
#print axioms evenOdd_hosted

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Examples.UserPrograms
