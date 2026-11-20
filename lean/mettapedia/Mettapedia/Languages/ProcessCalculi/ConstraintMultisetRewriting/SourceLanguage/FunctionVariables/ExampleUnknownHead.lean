import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.FunctionVariables.ExampleTwice
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.LawExtension

/-!
# A call whose head is unknown when it is reached

```
(= (inc $n) (S $n))
!($h Z)
```

Under the clause by value the query evaluates its argument and calls the tuple of `$h` and the value.
Nothing has bound `$h`. The call of the reference semantics unifies two ways, so the left-hand side
`(inc $n)` fits the call with `$h` bound to `inc`: a run ends, quiescent, with the bag `{(S Z)}`
(`runs_answers`), and the store at the end determines `$h` as `inc` (`head_found`).

Under the clause that runs the tuple when it is reached, the tuple is run with nothing bound; the
program's reading of a tuple whose head is still a name calls it as it stands (`AtRunTime.reading_calls`):
it does not run it again and does not wait. The call finds the head the same way, and a run ends,
quiescent, with the bag `{(S Z)}` (`atRunTime_answers`).

So in the reference semantics a call through an unknown head *finds* the functions that answer it; it
does not wait for the head and does not return the tuple as data. That is a property of
`Semantics.Move.apply`. A system that returns the tuple as data while its head is unknown answers
`($h Z)` for this text.

The condition of the law of extension (`Extension.callsApart`: every datum the program calls is
separated from the added equation) fails at such a call for every equation whose left-hand side has the
shape of the tuple (`not_separated`): a call through a variable can be answered by any of them.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.FunctionVariables.ExampleUnknownHead

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Elaboration Toolkit
open ExampleTwice (D supply sp byValue incS incE)

def surface : SProgram := ⟨[], [incS]⟩

def program : Program mkeys [] () MTy := elaborateH .byValue byValue surface

theorem program_eq : program.equations = [incE] := rfl

/-- `$h`, a name of the query. -/
abbrev hQ : MData := foD [] [3] 0

/-- The query `($h Z)`, elaborated: the argument at its arrow, then the call of the tuple. -/
def query : Comp mkeys [] () MTy :=
  .let_ [3, 0] (foD [] [3, 0] 0) (.apply (sym "Z")) (.apply (tuple [hQ, foD [] [3, 0] 0]))

theorem query_eq : elabQueryH .byValue byValue surface (.text (tuple [hQ, sym "Z"])) = query := rfl

/-- The store at the end. -/
def Kf : List (Constraint mkeys [] ()) :=
  [(foD [0] [3, 0] 0, sym "Z"),
   (tuple [sym "inc", foD [1] [240] 0], tuple [hQ, foD [0] [3, 0] 0]),
   (foD [2, 1] [1, 240, 0] 0, foD [1] [240] 0)]

def vf : MData := tuple [sym "S", foD [2, 1] [1, 240, 0] 0]

def finalB : Branch mkeys [] () MTy := ⟨Kf, .value vf, [], []⟩

macro "unanswered" : tactic =>
  `(tactic| (rw [program_eq];
             refine List.forall_mem_cons.mpr ⟨?_, fun _ member => nomatch member⟩; clash))

theorem along : Along D program supply (Config.initial sp query) ⟨3, 0, sp⟩ finalB := by
  have h := Along.start (D := D) (P := program) (supply := supply) sp query
  have h := h.letStart
  have h := h.unmatched (by unanswered)
  have h := h.letBind
  -- the call `($h v)`: the equation of `inc` fits it, binding `$h`
  have h := h.call [] incE [] program_eq (fun _ member => nomatch member)
  have h := h.letStart
  have h := h.ret
  have h := h.letBind
  have h := h.unmatched (by unanswered)
  exact h

def solution : Assignment (fam mkeys) noNames :=
  closeNames [(([0], [3, 0], 0), csym "Z"), (([], [3], 0), csym "inc"), (([1], [240], 0), csym "Z"),
    (([2, 1], [1, 240, 0], 0), csym "Z")] (csym "a")

theorem live : Solvable Kf := ⟨Empty, noNames, solution, by decide⟩

/-- `(S Z)`. -/
def answer : MClosed := ctuple [csym "S", csym "Z"]

theorem determines : Determines Kf vf answer := by
  refine ⟨live, fun target τ solved => ?_⟩
  simp only [Kf, Models, List.forall_mem_cons] at solved
  obtain ⟨e1, e2, e3, -⟩ := solved
  have h1 : instantiate τ (foD [0] [3, 0] 0) = symAt "Z" := e1
  have h2 : tupleAt [symAt "inc", instantiate τ (foD [1] [240] 0)] =
      tupleAt [instantiate τ hQ, instantiate τ (foD [0] [3, 0] 0)] := e2
  have h3 : instantiate τ (foD [2, 1] [1, 240, 0] 0) = instantiate τ (foD [1] [240] 0) := e3
  show tupleAt [symAt "S", instantiate τ (foD [2, 1] [1, 240, 0] 0)] = _
  rw [h3, (tuple2_inj h2).2, h1]
  rfl

/-- **The run finds the head**: the store at the end determines `$h` as `inc`. -/
theorem head_found : Determines Kf hQ (csym "inc") := by
  refine ⟨live, fun target τ solved => ?_⟩
  simp only [Kf, Models, List.forall_mem_cons] at solved
  obtain ⟨-, e2, -⟩ := solved
  have h2 : tupleAt [symAt "inc", instantiate τ (foD [1] [240] 0)] =
      tupleAt [instantiate τ hQ, instantiate τ (foD [0] [3, 0] 0)] := e2
  exact (tuple2_inj h2).1.symm

/-- **A call through an unknown head is answered by the equation that fits it**: a run ends, quiescent,
with the bag `{(S Z)}`. -/
theorem runs_answers : ∃ C : Config mkeys [] () MTy,
    Runs D program supply (Config.initial sp query) C ∧ Config.Quiescent (D := D) program supply C ∧
      Config.answers (D := D) C = {{answer}} := by
  have finished : Branch.Finished (D := D) finalB := ⟨rfl, _, rfl⟩
  obtain ⟨C, runs, quiescent, answers⟩ := Along.answers along finished live
  have same : Branch.answer (D := D) finalB = {answer} :=
    Branch.answer_of_determines (D := D) (b := finalB) rfl determines
  exact ⟨C, runs, quiescent, answers.trans (congrArg (fun s => ({s} : Multiset (Set MClosed))) same)⟩

/-! ## The law of extension -/

/-- **The call `($h Z)` is not separated from the equation of `inc`**: an instance of the tuple is an
instance of the left-hand side. -/
theorem not_separated : ¬ Extension.Separated (D := D) incE (tuple [hQ, sym "Z"]) := fun apart =>
  apart 0 noNames (closeNames [(([], [3], 0), csym "inc")] (csym "a"))
    (closeNames [(([0], [240], 0), csym "Z")] (csym "a")) rfl

/-! ## At run time -/

namespace AtRunTime

def program : Program mkeys [] () MTy := elaborateH .atRunTime byValue surface

theorem program_eq : program.equations = [incE] := rfl

/-- The query `($h Z)`: the tuple is run as text. -/
def query : Comp mkeys [] () MTy := .run (tuple [hQ, sym "Z"])

theorem query_eq : elabQueryH .atRunTime byValue surface (.text (tuple [hQ, sym "Z"])) = query := rfl

/-- Nothing is bound when the tuple is run. -/
def θ : Assignment (fam mkeys) (fam mkeys) := bindNames []

theorem principal : Principal ([] : List (Constraint mkeys [] ())) θ :=
  principal_bindNames (by decide) (fun _ member => nomatch member)

/-- **The reading of a tuple whose head is still a name calls it as it stands.** -/
theorem reading_calls :
    program.reflect (instantiate θ (tuple [hQ, sym "Z"])) = .apply (tuple [hQ, sym "Z"]) := rfl

def Kf : List (Constraint mkeys [] ()) :=
  [(tuple [sym "inc", foD [0] [240] 0], tuple [hQ, sym "Z"]),
   (foD [1, 0] [1, 240, 0] 0, foD [0] [240] 0)]

def vf : MData := tuple [sym "S", foD [1, 0] [1, 240, 0] 0]

def finalB : Branch mkeys [] () MTy := ⟨Kf, .value vf, [], []⟩

theorem along : Along D program supply (Config.initial sp query) ⟨2, 0, sp⟩ finalB := by
  have h := Along.start (D := D) (P := program) (supply := supply) sp query
  have h := h.run θ principal
  have h := h.call [] incE [] program_eq (fun _ member => nomatch member)
  have h := h.letStart
  have h := h.ret
  have h := h.letBind
  have h := h.unmatched (by
    rw [program_eq]
    refine List.forall_mem_cons.mpr ⟨?_, fun _ member => nomatch member⟩
    clash)
  exact h

def solution : Assignment (fam mkeys) noNames :=
  closeNames [(([], [3], 0), csym "inc"), (([0], [240], 0), csym "Z"), (([1, 0], [1, 240, 0], 0), csym "Z")]
    (csym "a")

theorem live : Solvable Kf := ⟨Empty, noNames, solution, by decide⟩

theorem determines : Determines Kf vf answer := by
  refine ⟨live, fun target τ solved => ?_⟩
  simp only [Kf, Models, List.forall_mem_cons] at solved
  obtain ⟨e1, e2, -⟩ := solved
  have h1 : tupleAt [symAt "inc", instantiate τ (foD [0] [240] 0)] =
      tupleAt [instantiate τ hQ, symAt "Z"] := e1
  have h2 : instantiate τ (foD [1, 0] [1, 240, 0] 0) = instantiate τ (foD [0] [240] 0) := e2
  show tupleAt [symAt "S", instantiate τ (foD [1, 0] [1, 240, 0] 0)] = _
  rw [h2, (tuple2_inj h1).2]
  rfl

end AtRunTime

/-- **At run time, with the head unknown**: the tuple is called as it stands and the call finds the
head; a run ends, quiescent, with the bag `{(S Z)}`. -/
theorem atRunTime_answers : ∃ C : Config mkeys [] () MTy,
    Runs D AtRunTime.program supply (Config.initial sp AtRunTime.query) C ∧
      Config.Quiescent (D := D) AtRunTime.program supply C ∧
      Config.answers (D := D) C = {{answer}} := by
  have finished : Branch.Finished (D := D) AtRunTime.finalB := ⟨rfl, _, rfl⟩
  obtain ⟨C, runs, quiescent, answers⟩ := Along.answers AtRunTime.along finished AtRunTime.live
  have same : Branch.answer (D := D) AtRunTime.finalB = {answer} :=
    Branch.answer_of_determines (D := D) (b := AtRunTime.finalB) rfl AtRunTime.determines
  exact ⟨C, runs, quiescent, answers.trans (congrArg (fun s => ({s} : Multiset (Set MClosed))) same)⟩

#print axioms query_eq
#print axioms along
#print axioms head_found
#print axioms runs_answers
#print axioms not_separated
#print axioms AtRunTime.reading_calls
#print axioms atRunTime_answers

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.FunctionVariables.ExampleUnknownHead
