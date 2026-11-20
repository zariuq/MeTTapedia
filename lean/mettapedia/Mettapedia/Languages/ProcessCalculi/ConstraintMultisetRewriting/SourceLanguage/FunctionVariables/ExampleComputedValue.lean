import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.FunctionVariables.ExampleTwice

/-!
# A computed value passed on through a function variable

```
(= (mk) (hold (one)))      ; `mk` computes the datum `(one)`
(= (one) I)
(= (twice $f $x) ($f ($f $x)))
!(twice Box (mk))
```

The argument `(mk)` of `twice` is evaluated: `$x` holds the computed value `(one)`, a datum that has the
shape of a call.

* **By value** (`byValue_answers`): the value is passed on as it is. The bag is `{(Box (Box (one)))}`:
  the computed value never runs (`valuesH_never_run` is the general statement about the code).
* **At run time** (`atRunTime_answers`): the tuple is dereferenced as a whole and read as code, so the
  value `(one)` stands in the text that is read, and is called: the bag is `{(Box (Box I))}`. A computed
  value has run again.

The two bags differ (`bags_differ`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.FunctionVariables.ExampleComputedValue

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Elaboration Toolkit
open ExampleTwice (D supply sp byValue twiceS fT xT)

/-! ## The text -/

def mkS : SEquation := ⟨[260], "mk", [], .text (hold (tuple [sym "one"]))⟩
def oneS : SEquation := ⟨[261], "one", [], .text (sym "I")⟩

def surface : SProgram := ⟨[], [mkS, oneS, twiceS]⟩

/-- `(= (mk) (hold (one)))`: the datum `(one)` is returned. -/
def mkE : Equation mkeys [] () MTy := ⟨[260], tuple [sym "mk"], .ret (tuple [sym "one"])⟩

/-- `(= (one) I)`. -/
def oneE : Equation mkeys [] () MTy := ⟨[261], tuple [sym "one"], .apply (sym "I")⟩

/-- The query `(twice Box (mk))`, elaborated (the same under every clause). -/
def query : Comp mkeys [] () MTy :=
  .let_ [3, 0] (foD [] [3, 0] 0) (.apply (sym "Box"))
    (.let_ [3, 1] (foD [] [3, 1] 0) (.apply (tuple [sym "mk"]))
      (.apply (tuple [sym "twice", foD [] [3, 0] 0, foD [] [3, 1] 0])))

theorem query_eq (cl : Clause) :
    elabQueryH cl byValue surface (.text (tuple [sym "twice", sym "Box", tuple [sym "mk"]])) = query := rfl

/-- No equation of a program of three equations answers the call. -/
macro "unanswered" eq:term : tactic =>
  `(tactic| (rw [$eq:term];
             refine List.forall_mem_cons.mpr ⟨?_, List.forall_mem_cons.mpr ⟨?_,
               List.forall_mem_cons.mpr ⟨?_, fun _ member => nomatch member⟩⟩⟩ <;> clash))

/-- The two other equations' alternatives are dead. -/
macro "others_dead" : tactic =>
  `(tactic| (intro e member;
             simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, false_or] at member;
             rcases member with same | same <;> (subst same; clash)))

/-- The store after the query's arguments and the call of `twice`. -/
def K4 : List (Constraint mkeys [] ()) :=
  [(foD [0] [3, 0] 0, sym "Box"),
   (tuple [sym "mk"], tuple [sym "mk"]),
   (foD [2] [3, 1] 0, tuple [sym "one"]),
   (tuple [sym "twice", foD [3] [241] 0, foD [3] [241] 1], tuple [sym "twice", foD [0] [3, 0] 0, foD [2] [3, 1] 0])]

/-! ## By value -/

namespace ByValue

def program : Program mkeys [] () MTy := elaborateH .byValue byValue surface

theorem program_eq : program.equations = [mkE, oneE, ExampleTwice.twiceE] := rfl

def Kf : List (Constraint mkeys [] ()) :=
  K4 ++
  [(foD [4, 3] [1, 241, 0, 0] 0, foD [3] [241] 1),
   (foD [5, 3] [1, 241, 0] 0, tuple [foD [3] [241] 0, foD [4, 3] [1, 241, 0, 0] 0])]

def vf : MData := tuple [foD [3] [241] 0, foD [5, 3] [1, 241, 0] 0]

def finalB : Branch mkeys [] () MTy := ⟨Kf, .value vf, [], []⟩

theorem along : Along D program supply (Config.initial sp query) ⟨6, 0, sp⟩ finalB := by
  have h := Along.start (D := D) (P := program) (supply := supply) sp query
  have h := h.letStart
  have h := h.unmatched (by unanswered program_eq)
  have h := h.letBind
  -- the argument `(mk)`: its value is the datum `(one)`
  have h := h.letStart
  have h := h.call [] mkE [oneE, ExampleTwice.twiceE] program_eq (by others_dead)
  have h := h.ret
  have h := h.letBind
  have h := h.call [mkE, oneE] ExampleTwice.twiceE [] program_eq (by others_dead)
  -- the inner call `($f $x)`: the value of `$x` is passed on; no equation answers `(Box v)`
  have h := h.letStart
  have h := h.letStart
  have h := h.ret
  have h := h.letBind
  have h := h.unmatched (by unanswered program_eq)
  have h := h.letBind
  have h := h.unmatched (by unanswered program_eq)
  exact h

def solution : Assignment (fam mkeys) noNames :=
  closeNames [(([0], [3, 0], 0), csym "Box"), (([2], [3, 1], 0), ctuple [csym "one"]),
    (([3], [241], 0), csym "Box"), (([3], [241], 1), ctuple [csym "one"]),
    (([4, 3], [1, 241, 0, 0], 0), ctuple [csym "one"]),
    (([5, 3], [1, 241, 0], 0), ctuple [csym "Box", ctuple [csym "one"]])] (csym "a")

theorem live : Solvable Kf := ⟨Empty, noNames, solution, by decide⟩

/-- `(Box (Box (one)))`. -/
def answer : MClosed := ctuple [csym "Box", ctuple [csym "Box", ctuple [csym "one"]]]

theorem determines : Determines Kf vf answer := by
  refine ⟨live, fun target τ solved => ?_⟩
  simp only [Kf, K4, List.cons_append, List.nil_append, Models, List.forall_mem_cons] at solved
  obtain ⟨e1, -, e3, e4, e5, e6, -⟩ := solved
  have h1 : instantiate τ (foD [0] [3, 0] 0) = symAt "Box" := e1
  have h3 : instantiate τ (foD [2] [3, 1] 0) = tupleAt [symAt "one"] := e3
  have h4 : tupleAt [symAt "twice", instantiate τ (foD [3] [241] 0), instantiate τ (foD [3] [241] 1)] =
      tupleAt [symAt "twice", instantiate τ (foD [0] [3, 0] 0), instantiate τ (foD [2] [3, 1] 0)] := e4
  have h5 : instantiate τ (foD [4, 3] [1, 241, 0, 0] 0) = instantiate τ (foD [3] [241] 1) := e5
  have h6 : instantiate τ (foD [5, 3] [1, 241, 0] 0) =
      tupleAt [instantiate τ (foD [3] [241] 0), instantiate τ (foD [4, 3] [1, 241, 0, 0] 0)] := e6
  obtain ⟨-, onF, onX⟩ := tuple3_inj h4
  show tupleAt [instantiate τ (foD [3] [241] 0), instantiate τ (foD [5, 3] [1, 241, 0] 0)] = _
  rw [h6, h5, onF, onX, h1, h3]
  rfl

end ByValue

/-- **By value**: a run ends, quiescent, with the bag `{(Box (Box (one)))}`: the computed value `(one)`
is passed on and never runs. -/
theorem byValue_answers : ∃ C : Config mkeys [] () MTy,
    Runs D ByValue.program supply (Config.initial sp query) C ∧
      Config.Quiescent (D := D) ByValue.program supply C ∧
      Config.answers (D := D) C = {{ByValue.answer}} := by
  have finished : Branch.Finished (D := D) ByValue.finalB := ⟨rfl, _, rfl⟩
  obtain ⟨C, runs, quiescent, answers⟩ := Along.answers ByValue.along finished ByValue.live
  have same : Branch.answer (D := D) ByValue.finalB = {ByValue.answer} :=
    Branch.answer_of_determines (D := D) (b := ByValue.finalB) rfl ByValue.determines
  exact ⟨C, runs, quiescent, answers.trans (congrArg (fun s => ({s} : Multiset (Set MClosed))) same)⟩

/-! ## At run time -/

namespace AtRunTime

def program : Program mkeys [] () MTy := elaborateH .atRunTime byValue surface

/-- `(= (twice $f $x) ($f ($f $x)))`: the tuple is run as text. -/
def twiceE : Equation mkeys [] () MTy :=
  ⟨[241], tuple [sym "twice", fT, xT], .run (tuple [fT, tuple [fT, xT]])⟩

theorem program_eq : program.equations = [mkE, oneE, twiceE] := rfl

/-- What the store has bound when the tuple is run: `$x` is the computed value `(one)`. -/
def θ : Assignment (fam mkeys) (fam mkeys) :=
  bindNames [(([0], [3, 0], 0), sym "Box"), (([2], [3, 1], 0), tuple [sym "one"]),
    (([3], [241], 0), sym "Box"), (([3], [241], 1), tuple [sym "one"])]

theorem principal : Principal K4 θ := by
  refine principal_bindNames (by decide) ?_
  intro entry member X target σ models
  simp only [K4, Models, List.forall_mem_cons] at models
  obtain ⟨e1, -, e3, e4, -⟩ := models
  have h1 : σ (fo [0] [3, 0] 0) = symAt "Box" := (instantiate_foD σ [0] [3, 0] 0).symm.trans e1
  have h3 : σ (fo [2] [3, 1] 0) = tupleAt [symAt "one"] := (instantiate_foD σ [2] [3, 1] 0).symm.trans e3
  have h4 : tupleAt [symAt "twice", instantiate σ (foD [3] [241] 0), instantiate σ (foD [3] [241] 1)] =
      tupleAt [symAt "twice", instantiate σ (foD [0] [3, 0] 0), instantiate σ (foD [2] [3, 1] 0)] := e4
  obtain ⟨-, onF, onX⟩ := tuple3_inj h4
  rw [instantiate_foD, instantiate_foD] at onF onX
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  obtain rfl | rfl | rfl | rfl := member
  · exact h1
  · exact h3
  · exact onF.trans h1
  · exact onX.trans h3

def Kf : List (Constraint mkeys [] ()) :=
  K4 ++
  [(tuple [sym "one"], tuple [sym "one"]),
   (foD [5] [2, 0, 0, 0] 0, sym "I"),
   (foD [6] [2, 0, 0] 0, tuple [sym "Box", foD [5] [2, 0, 0, 0] 0])]

def vf : MData := tuple [sym "Box", foD [6] [2, 0, 0] 0]

def finalB : Branch mkeys [] () MTy := ⟨Kf, .value vf, [], []⟩

theorem along : Along D program supply (Config.initial sp query) ⟨7, 0, sp⟩ finalB := by
  have h := Along.start (D := D) (P := program) (supply := supply) sp query
  have h := h.letStart
  have h := h.unmatched (by unanswered program_eq)
  have h := h.letBind
  have h := h.letStart
  have h := h.call [] mkE [oneE, twiceE] program_eq (by others_dead)
  have h := h.ret
  have h := h.letBind
  have h := h.call [mkE, oneE] twiceE [] program_eq (by others_dead)
  -- the tuple is run: dereferenced, it is the text `(Box (Box (one)))`, and the value `(one)` is called
  have h := h.run θ principal
  have h := h.letStart
  have h := h.letStart
  have h := h.call [mkE] oneE [twiceE] program_eq (by others_dead)
  have h := h.unmatched (by unanswered program_eq)
  have h := h.letBind
  have h := h.unmatched (by unanswered program_eq)
  have h := h.letBind
  have h := h.unmatched (by unanswered program_eq)
  exact h

def solution : Assignment (fam mkeys) noNames :=
  closeNames [(([0], [3, 0], 0), csym "Box"), (([2], [3, 1], 0), ctuple [csym "one"]),
    (([3], [241], 0), csym "Box"), (([3], [241], 1), ctuple [csym "one"]),
    (([5], [2, 0, 0, 0], 0), csym "I"), (([6], [2, 0, 0], 0), ctuple [csym "Box", csym "I"])] (csym "a")

theorem live : Solvable Kf := ⟨Empty, noNames, solution, by decide⟩

/-- `(Box (Box I))`. -/
def answer : MClosed := ctuple [csym "Box", ctuple [csym "Box", csym "I"]]

theorem determines : Determines Kf vf answer := by
  refine ⟨live, fun target τ solved => ?_⟩
  simp only [Kf, K4, List.cons_append, List.nil_append, Models, List.forall_mem_cons] at solved
  obtain ⟨-, -, -, -, -, e6, e7, -⟩ := solved
  have h6 : instantiate τ (foD [5] [2, 0, 0, 0] 0) = symAt "I" := e6
  have h7 : instantiate τ (foD [6] [2, 0, 0] 0) =
      tupleAt [symAt "Box", instantiate τ (foD [5] [2, 0, 0, 0] 0)] := e7
  show tupleAt [symAt "Box", instantiate τ (foD [6] [2, 0, 0] 0)] = _
  rw [h7, h6]
  rfl

end AtRunTime

/-- **At run time**: a run ends, quiescent, with the bag `{(Box (Box I))}`: the computed value `(one)`
was read as code and called. -/
theorem atRunTime_answers : ∃ C : Config mkeys [] () MTy,
    Runs D AtRunTime.program supply (Config.initial sp query) C ∧
      Config.Quiescent (D := D) AtRunTime.program supply C ∧
      Config.answers (D := D) C = {{AtRunTime.answer}} := by
  have finished : Branch.Finished (D := D) AtRunTime.finalB := ⟨rfl, _, rfl⟩
  obtain ⟨C, runs, quiescent, answers⟩ := Along.answers AtRunTime.along finished AtRunTime.live
  have same : Branch.answer (D := D) AtRunTime.finalB = {AtRunTime.answer} :=
    Branch.answer_of_determines (D := D) (b := AtRunTime.finalB) rfl AtRunTime.determines
  exact ⟨C, runs, quiescent, answers.trans (congrArg (fun s => ({s} : Multiset (Set MClosed))) same)⟩

/-- **The two clauses answer the text differently**: `(Box (Box (one)))` is not `(Box (Box I))`. -/
theorem bags_differ : ({{ByValue.answer}} : Multiset (Set MClosed)) ≠ {{AtRunTime.answer}} := by
  intro same
  have inside : ByValue.answer ∈ ({AtRunTime.answer} : Set MClosed) := by
    rw [← Multiset.singleton_inj.mp same]
    exact Set.mem_singleton _
  exact absurd (Set.mem_singleton_iff.mp inside) (by decide)

/-- The code by value runs nothing: the text of `twice` is text whose variables hold values. -/
theorem byValue_runs_nothing :
    Laws.reruns (elabEquationH .byValue byValue [] twiceS).rhs = [] := rfl

/-- The code at run time runs the whole tuple. -/
theorem atRunTime_runs_tuple :
    Laws.reruns (elabEquationH .atRunTime byValue [] twiceS).rhs = [tuple [fT, tuple [fT, xT]]] := rfl

#print axioms query_eq
#print axioms byValue_answers
#print axioms AtRunTime.principal
#print axioms atRunTime_answers
#print axioms bags_differ
#print axioms byValue_runs_nothing
#print axioms atRunTime_runs_tuple

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.FunctionVariables.ExampleComputedValue
