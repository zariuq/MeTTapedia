import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.FunctionVariables.ExampleTwice

/-!
# A function returned by a function: the head of a tuple is a call

```
(= (get) inc)
(= (inc $n) (S $n))
!((get) Z)
```

The head of the tuple `((get) Z)` is itself a call.

* **By value** (`byValue_answers`): the head is a position that wants a value. It is computed first, at
  its own arrow, and the call is the tuple of its value and the argument's value: the bag is `{(S Z)}`.
* **As it stands** (`asWritten_answers`): the tuple is called as written; no equation's left-hand side
  fits `((get) Z)`, so it is returned as data: the bag is `{((get) Z)}`. The head is never computed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.FunctionVariables.ExampleReturnedFunction

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Elaboration Toolkit
open ExampleTwice (D supply sp byValue incS incE)

def getS : SEquation := ⟨[270], "get", [], .text (sym "inc")⟩

def surface : SProgram := ⟨[], [getS, incS]⟩

/-- `(= (get) inc)`. -/
def getE : Equation mkeys [] () MTy := ⟨[270], tuple [sym "get"], .apply (sym "inc")⟩

/-- The text `((get) Z)`. -/
def text : MData := tuple [tuple [sym "get"], sym "Z"]

macro "unanswered" eq:term : tactic =>
  `(tactic| (rw [$eq:term];
             refine List.forall_mem_cons.mpr ⟨?_, List.forall_mem_cons.mpr ⟨?_, fun _ member => nomatch member⟩⟩
               <;> clash))

macro "other_dead" : tactic =>
  `(tactic| (intro e member;
             simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, false_or] at member;
             subst member; clash))

/-! ## By value -/

namespace ByValue

def program : Program mkeys [] () MTy := elaborateH .byValue byValue surface

theorem program_eq : program.equations = [getE, incE] := rfl

/-- The query: the head `(get)` at its own arrow, then the argument, then the call of the two values. -/
def query : Comp mkeys [] () MTy :=
  .let_ [3, 1] (foD [] [3, 1] 0) (.apply (tuple [sym "get"]))
    (.let_ [3, 0] (foD [] [3, 0] 0) (.apply (sym "Z"))
      (.apply (tuple [foD [] [3, 1] 0, foD [] [3, 0] 0])))

theorem query_eq : elabQueryH .byValue byValue surface (.text text) = query := rfl

def Kf : List (Constraint mkeys [] ()) :=
  [(tuple [sym "get"], tuple [sym "get"]),
   (foD [1] [3, 1] 0, sym "inc"),
   (foD [2] [3, 0] 0, sym "Z"),
   (tuple [sym "inc", foD [3] [240] 0], tuple [foD [1] [3, 1] 0, foD [2] [3, 0] 0]),
   (foD [4, 3] [1, 240, 0] 0, foD [3] [240] 0)]

def vf : MData := tuple [sym "S", foD [4, 3] [1, 240, 0] 0]

def finalB : Branch mkeys [] () MTy := ⟨Kf, .value vf, [], []⟩

theorem along : Along D program supply (Config.initial sp query) ⟨5, 0, sp⟩ finalB := by
  have h := Along.start (D := D) (P := program) (supply := supply) sp query
  -- the head `(get)`, computed: its value is `inc`
  have h := h.letStart
  have h := h.call [] getE [incE] program_eq (by other_dead)
  have h := h.unmatched (by unanswered program_eq)
  have h := h.letBind
  -- the argument
  have h := h.letStart
  have h := h.unmatched (by unanswered program_eq)
  have h := h.letBind
  -- the call of the two values, answered by `inc`
  have h := h.call [getE] incE [] program_eq (by other_dead)
  have h := h.letStart
  have h := h.ret
  have h := h.letBind
  have h := h.unmatched (by unanswered program_eq)
  exact h

def solution : Assignment (fam mkeys) noNames :=
  closeNames [(([1], [3, 1], 0), csym "inc"), (([2], [3, 0], 0), csym "Z"), (([3], [240], 0), csym "Z"),
    (([4, 3], [1, 240, 0], 0), csym "Z")] (csym "a")

theorem live : Solvable Kf := ⟨Empty, noNames, solution, by decide⟩

/-- `(S Z)`. -/
def answer : MClosed := ctuple [csym "S", csym "Z"]

theorem determines : Determines Kf vf answer := by
  refine ⟨live, fun target τ solved => ?_⟩
  simp only [Kf, Models, List.forall_mem_cons] at solved
  obtain ⟨-, -, e3, e4, e5, -⟩ := solved
  have h3 : instantiate τ (foD [2] [3, 0] 0) = symAt "Z" := e3
  have h4 : tupleAt [symAt "inc", instantiate τ (foD [3] [240] 0)] =
      tupleAt [instantiate τ (foD [1] [3, 1] 0), instantiate τ (foD [2] [3, 0] 0)] := e4
  have h5 : instantiate τ (foD [4, 3] [1, 240, 0] 0) = instantiate τ (foD [3] [240] 0) := e5
  show tupleAt [symAt "S", instantiate τ (foD [4, 3] [1, 240, 0] 0)] = _
  rw [h5, (tuple2_inj h4).2, h3]
  rfl

end ByValue

/-- **By value**: the head is computed first; a run ends, quiescent, with the bag `{(S Z)}`. -/
theorem byValue_answers : ∃ C : Config mkeys [] () MTy,
    Runs D ByValue.program supply (Config.initial sp ByValue.query) C ∧
      Config.Quiescent (D := D) ByValue.program supply C ∧
      Config.answers (D := D) C = {{ByValue.answer}} := by
  have finished : Branch.Finished (D := D) ByValue.finalB := ⟨rfl, _, rfl⟩
  obtain ⟨C, runs, quiescent, answers⟩ := Along.answers ByValue.along finished ByValue.live
  have same : Branch.answer (D := D) ByValue.finalB = {ByValue.answer} :=
    Branch.answer_of_determines (D := D) (b := ByValue.finalB) rfl ByValue.determines
  exact ⟨C, runs, quiescent, answers.trans (congrArg (fun s => ({s} : Multiset (Set MClosed))) same)⟩

/-! ## As it stands -/

namespace AsWritten

def program : Program mkeys [] () MTy := elaborateH .asWritten byValue surface

theorem program_eq : program.equations = [getE, incE] := rfl

/-- The query: one call of the tuple as written. -/
def query : Comp mkeys [] () MTy := .apply text

theorem query_eq : elabQueryH .asWritten byValue surface (.text text) = query := rfl

def finalB : Branch mkeys [] () MTy := ⟨[], .value text, [], []⟩

theorem along : Along D program supply (Config.initial sp query) ⟨0, 0, sp⟩ finalB := by
  have h := Along.start (D := D) (P := program) (supply := supply) sp query
  have h := h.unmatched (by unanswered program_eq)
  exact h

/-- `((get) Z)`. -/
def answer : MClosed := ctuple [ctuple [csym "get"], csym "Z"]

theorem determines : Determines ([] : List (Constraint mkeys [] ())) text answer :=
  ⟨live_nil, fun _ _ _ => rfl⟩

end AsWritten

/-- **As it stands**: the tuple is returned as data; a run ends, quiescent, with the bag `{((get) Z)}`. -/
theorem asWritten_answers : ∃ C : Config mkeys [] () MTy,
    Runs D AsWritten.program supply (Config.initial sp AsWritten.query) C ∧
      Config.Quiescent (D := D) AsWritten.program supply C ∧
      Config.answers (D := D) C = {{AsWritten.answer}} := by
  have finished : Branch.Finished (D := D) AsWritten.finalB := ⟨rfl, _, rfl⟩
  obtain ⟨C, runs, quiescent, answers⟩ := Along.answers AsWritten.along finished live_nil
  have same : Branch.answer (D := D) AsWritten.finalB = {AsWritten.answer} :=
    Branch.answer_of_determines (D := D) (b := AsWritten.finalB) rfl AsWritten.determines
  exact ⟨C, runs, quiescent, answers.trans (congrArg (fun s => ({s} : Multiset (Set MClosed))) same)⟩

#print axioms ByValue.query_eq
#print axioms byValue_answers
#print axioms AsWritten.query_eq
#print axioms asWritten_answers

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.FunctionVariables.ExampleReturnedFunction
