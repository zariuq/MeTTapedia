import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.WellFormedRuns
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.FunctionVariables.Clauses
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.FunctionVariables.Runs

/-!
# `twice` as written, under the clause by value

```
(= (inc $n) (S $n))
(= (twice $f $x) ($f ($f $x)))
!(twice inc Z)
```

Under `Clause.byValue` the body of `twice` evaluates the inner call `($f $x)` at its own arrow and then
calls the tuple of `$f` and its value (`program_eq`): the code is that of a call of an undeclared
function, with the variable at the head.

* `runs_answers`: a run of the reference semantics from the elaborated query ends, quiescent, with the
  bag `{(S (S Z))}`. Twenty-two steps; at every call the equation that does not fit makes a dead
  alternative.
* `hosted`: the elaborated program and query are in the fragment with arrows and scoped, so the run
  theorem of the translation applies (`Hosting.arrow_answers_of_scoped`): a frontier of states that
  runs of the step reach from the translation's start answers `{(S (S Z))}`.

Under the clause that calls the tuple as it stands, the same text answers `(S (inc Z))`
(`ExampleTwiceAsWritten`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.FunctionVariables.ExampleTwice

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Elaboration Toolkit
open Hosting

abbrev D := untyped.discipline
abbrev N := mettaNodes

def supply : ℕ → MClosed := fun _ => csym "space"
abbrev sp : MClosed → Multiset (Row mkeys [] ()) := fun _ => 0

/-! ## The text and its elaboration -/

/-- By value at every undeclared position. -/
def byValue : Params := ⟨fun _ _ => .value, false, false⟩

abbrev nI : MData := foD [] [240] 0
abbrev fT : MData := foD [] [241] 0
abbrev xT : MData := foD [] [241] 1

def incS : SEquation := ⟨[240], "inc", [nI], .text (tuple [sym "S", nI])⟩
def twiceS : SEquation := ⟨[241], "twice", [fT, xT], .text (tuple [fT, tuple [fT, xT]])⟩
def surface : SProgram := ⟨[], [incS, twiceS]⟩

/-- The program under the clause by value. -/
def program : Program mkeys [] () MTy := elaborateH .byValue byValue surface

/-- `(= (inc $n) (S $n))`: the argument of `S` at its own arrow. -/
def incE : Equation mkeys [] () MTy :=
  ⟨[240], tuple [sym "inc", nI],
    .let_ [1, 240, 0] (foD [] [1, 240, 0] 0) (.ret nI) (.apply (tuple [sym "S", foD [] [1, 240, 0] 0]))⟩

/-- `(= (twice $f $x) ($f ($f $x)))`: the inner call at its own arrow, its own argument at an arrow
inside; each call is the tuple of `$f` and a value. -/
def twiceE : Equation mkeys [] () MTy :=
  ⟨[241], tuple [sym "twice", fT, xT],
    .let_ [1, 241, 0] (foD [] [1, 241, 0] 0)
      (.let_ [1, 241, 0, 0] (foD [] [1, 241, 0, 0] 0) (.ret xT) (.apply (tuple [fT, foD [] [1, 241, 0, 0] 0])))
      (.apply (tuple [fT, foD [] [1, 241, 0] 0]))⟩

theorem program_eq : program.equations = [incE, twiceE] := rfl

/-- The query `(twice inc Z)`, elaborated. -/
def query : Comp mkeys [] () MTy :=
  .let_ [3, 0] (foD [] [3, 0] 0) (.apply (sym "inc"))
    (.let_ [3, 1] (foD [] [3, 1] 0) (.apply (sym "Z"))
      (.apply (tuple [sym "twice", foD [] [3, 0] 0, foD [] [3, 1] 0])))

theorem query_eq :
    elabQueryH .byValue byValue surface (.text (tuple [sym "twice", sym "inc", sym "Z"])) = query := rfl

/-! ## The run -/

/-- The store at the end. -/
def Kf : List (Constraint mkeys [] ()) :=
  [(foD [0] [3, 0] 0, sym "inc"),
   (foD [1] [3, 1] 0, sym "Z"),
   (tuple [sym "twice", foD [2] [241] 0, foD [2] [241] 1], tuple [sym "twice", foD [0] [3, 0] 0, foD [1] [3, 1] 0]),
   (foD [3, 2] [1, 241, 0, 0] 0, foD [2] [241] 1),
   (tuple [sym "inc", foD [4] [240] 0], tuple [foD [2] [241] 0, foD [3, 2] [1, 241, 0, 0] 0]),
   (foD [5, 4] [1, 240, 0] 0, foD [4] [240] 0),
   (foD [6, 2] [1, 241, 0] 0, tuple [sym "S", foD [5, 4] [1, 240, 0] 0]),
   (tuple [sym "inc", foD [7] [240] 0], tuple [foD [2] [241] 0, foD [6, 2] [1, 241, 0] 0]),
   (foD [8, 7] [1, 240, 0] 0, foD [7] [240] 0)]

/-- The value at the end. -/
def vf : MData := tuple [sym "S", foD [8, 7] [1, 240, 0] 0]

/-- The alternative at the end. -/
def finalB : Branch mkeys [] () MTy := ⟨Kf, .value vf, [], []⟩

/-- No equation answers a call whose store ends in a clash with each left-hand side. -/
macro "unanswered" : tactic =>
  `(tactic| (rw [program_eq];
             refine List.forall_mem_cons.mpr ⟨?_, List.forall_mem_cons.mpr ⟨?_, fun _ member => nomatch member⟩⟩
               <;> clash))

/-- The other equation's alternative is dead. -/
macro "other_dead" : tactic =>
  `(tactic| (intro e member;
             simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, false_or] at member;
             subst member; clash))

theorem along : Along D program supply (Config.initial sp query) ⟨9, 0, sp⟩ finalB := by
  have h := Along.start (D := D) (P := program) (supply := supply) sp query
  -- the query's arguments, each at its arrow
  have h := h.letStart
  have h := h.unmatched (by unanswered)
  have h := h.letBind
  have h := h.letStart
  have h := h.unmatched (by unanswered)
  have h := h.letBind
  -- the call of `twice`
  have h := h.call [incE] twiceE [] program_eq (by other_dead)
  -- the inner call `($f $x)`: its argument, then the call, answered by `inc`
  have h := h.letStart
  have h := h.letStart
  have h := h.ret
  have h := h.letBind
  have h := h.call [] incE [twiceE] program_eq (by other_dead)
  have h := h.letStart
  have h := h.ret
  have h := h.letBind
  have h := h.unmatched (by unanswered)
  -- the outer call `($f v)`, answered by `inc`
  have h := h.letBind
  have h := h.call [] incE [twiceE] program_eq (by other_dead)
  have h := h.letStart
  have h := h.ret
  have h := h.letBind
  have h := h.unmatched (by unanswered)
  exact h

/-! ## The answer -/

/-- A solution of the store at the end. -/
def solution : Assignment (fam mkeys) noNames :=
  closeNames [(([0], [3, 0], 0), csym "inc"), (([1], [3, 1], 0), csym "Z"), (([2], [241], 0), csym "inc"),
    (([2], [241], 1), csym "Z"), (([3, 2], [1, 241, 0, 0], 0), csym "Z"), (([4], [240], 0), csym "Z"),
    (([5, 4], [1, 240, 0], 0), csym "Z"), (([6, 2], [1, 241, 0], 0), ctuple [csym "S", csym "Z"]),
    (([7], [240], 0), ctuple [csym "S", csym "Z"]), (([8, 7], [1, 240, 0], 0), ctuple [csym "S", csym "Z"])]
    (csym "a")

theorem live : Solvable Kf := ⟨Empty, noNames, solution, by decide⟩

/-- `(S (S Z))`. -/
def answer : MClosed := ctuple [csym "S", ctuple [csym "S", csym "Z"]]

theorem determines : Determines Kf vf answer := by
  refine ⟨live, fun target τ solved => ?_⟩
  simp only [Kf, Models, List.forall_mem_cons] at solved
  obtain ⟨-, e2, e3, e4, e5, e6, e7, e8, e9, -⟩ := solved
  have h3 : tupleAt [symAt "twice", instantiate τ (foD [2] [241] 0), instantiate τ (foD [2] [241] 1)] =
      tupleAt [symAt "twice", instantiate τ (foD [0] [3, 0] 0), instantiate τ (foD [1] [3, 1] 0)] := e3
  have h5 : tupleAt [symAt "inc", instantiate τ (foD [4] [240] 0)] =
      tupleAt [instantiate τ (foD [2] [241] 0), instantiate τ (foD [3, 2] [1, 241, 0, 0] 0)] := e5
  have h7 : instantiate τ (foD [6, 2] [1, 241, 0] 0) =
      tupleAt [symAt "S", instantiate τ (foD [5, 4] [1, 240, 0] 0)] := e7
  have h8 : tupleAt [symAt "inc", instantiate τ (foD [7] [240] 0)] =
      tupleAt [instantiate τ (foD [2] [241] 0), instantiate τ (foD [6, 2] [1, 241, 0] 0)] := e8
  have z : instantiate τ (foD [1] [3, 1] 0) = symAt "Z" := e2
  have h4 : instantiate τ (foD [3, 2] [1, 241, 0, 0] 0) = instantiate τ (foD [2] [241] 1) := e4
  have h6 : instantiate τ (foD [5, 4] [1, 240, 0] 0) = instantiate τ (foD [4] [240] 0) := e6
  have h9 : instantiate τ (foD [8, 7] [1, 240, 0] 0) = instantiate τ (foD [7] [240] 0) := e9
  show tupleAt [symAt "S", instantiate τ (foD [8, 7] [1, 240, 0] 0)] = _
  rw [h9, (tuple2_inj h8).2, h7, h6, (tuple2_inj h5).2, h4, (tuple3_inj h3).2.2, z]
  rfl

/-- **The run of the text under the clause by value**: it ends, quiescent, with the bag `{(S (S Z))}`. -/
theorem runs_answers : ∃ C : Config mkeys [] () MTy,
    Runs D program supply (Config.initial sp query) C ∧ Config.Quiescent (D := D) program supply C ∧
      Config.answers (D := D) C = {{answer}} := by
  have finished : Branch.Finished (D := D) finalB := ⟨rfl, _, rfl⟩
  obtain ⟨C, runs, quiescent, answers⟩ := Along.answers along finished live
  have same : Branch.answer (D := D) finalB = {answer} :=
    Branch.answer_of_determines (D := D) (b := finalB) rfl determines
  exact ⟨C, runs, quiescent, answers.trans (congrArg (fun s => ({s} : Multiset (Set MClosed))) same)⟩

/-! ## Through the translation -/

theorem program_wellFormed : WellFormed program := by decide

theorem program_arrows : ArrowProgram program := by
  intro e member
  rw [program_eq] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact ⟨trivial, trivial⟩
  · exact ⟨⟨trivial, trivial⟩, trivial⟩

theorem query_scoped : query.Scoped [[3]] := by decide
theorem query_distinct : ([3] :: query.sites).Nodup := by decide
theorem query_arrows : ArrowComp query := ⟨trivial, trivial, trivial⟩

/-- **The call through a function variable, hosted**: a frontier of states that runs of the step of the
translated program reach from the translation's start answers `{(S (S Z))}`. -/
theorem hosted :
    ∃ L : Multiset (Branch mkeys [] () D.Ty × HostState MSig × ℕ),
      frontierAnswers N L = {{answer}} ∧
      ∀ x ∈ L, Relation.ReflTransGen (Fires N program) (Hosting.start N program query) x.2.1 := by
  obtain ⟨C, runs, -, answers⟩ := runs_answers
  obtain ⟨L, same, reached⟩ := arrow_answers_of_scoped N (D := D) (P := program) (supply := supply) sp query
    (equations_of_wellFormed (D := D) program_wellFormed program_arrows) query_scoped query_distinct
    query_arrows runs
  exact ⟨L, same.symm.trans answers, reached⟩

#print axioms program_eq
#print axioms query_eq
#print axioms along
#print axioms determines
#print axioms runs_answers
#print axioms program_wellFormed
#print axioms hosted

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.FunctionVariables.ExampleTwice
