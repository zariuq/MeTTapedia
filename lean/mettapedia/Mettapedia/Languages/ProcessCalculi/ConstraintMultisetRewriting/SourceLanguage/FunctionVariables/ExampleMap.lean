import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.FunctionVariables.Hosted

/-!
# `map` with a function argument, under the clause by value

```
(= (inc $n) (S $n))
(= (map $f Nil) Nil)
(= (map $f (Cons $x $xs)) (Cons ($f $x) (map $f $xs)))
!(map inc (Cons Z Nil))
```

The call `($f $x)` through the function variable is an argument of `Cons`: it is evaluated at its own
arrow, and under the clause by value its own argument too (`program_eq`).

* `runs_answers`: a run ends, quiescent, with the bag `{(Cons (S Z) Nil)}`. Thirty-four steps. At the two
  calls of `map` the equation that does not fit is dead by what the store has bound (`dead_nil_first`,
  `dead_cons_second`), not by the shape of the call: the argument is a name.
* `hosted`: the general theorem (`static_answers`) applies: a frontier of states that runs of the step
  reach from the translation's start answers `{(Cons (S Z) Nil)}`.

Under the clause that calls a tuple as it stands the body differs only in passing `$x` as it is
(`asWritten_body`): the argument of the call through `$f` is a variable that holds a value. No run under
that clause is given here.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.FunctionVariables.ExampleMap

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Elaboration Toolkit
open ExampleTwice (D supply sp byValue incS incE)

/-! ## The text and its elaboration -/

abbrev fN : MData := foD [] [280] 0
abbrev fM : MData := foD [] [281] 0
abbrev xM : MData := foD [] [281] 1
abbrev xsM : MData := foD [] [281] 2

def mapNilS : SEquation := ⟨[280], "map", [fN, sym "Nil"], .text (sym "Nil")⟩
def mapConsS : SEquation :=
  ⟨[281], "map", [fM, tuple [sym "Cons", xM, xsM]],
    .text (tuple [sym "Cons", tuple [fM, xM], tuple [sym "map", fM, xsM]])⟩

def surface : SProgram := ⟨[], [incS, mapNilS, mapConsS]⟩

def program : Program mkeys [] () MTy := elaborateH .byValue byValue surface

/-- `(= (map $f Nil) Nil)`. -/
def mapNilE : Equation mkeys [] () MTy := ⟨[280], tuple [sym "map", fN, sym "Nil"], .apply (sym "Nil")⟩

/-- `(= (map $f (Cons $x $xs)) (Cons ($f $x) (map $f $xs)))`: the call through `$f` at its own arrow,
its argument at an arrow inside; then the recursive call, its arguments at arrows; then `Cons`. -/
def mapConsE : Equation mkeys [] () MTy :=
  ⟨[281], tuple [sym "map", fM, tuple [sym "Cons", xM, xsM]],
    .let_ [1, 281, 0] (foD [] [1, 281, 0] 0)
      (.let_ [1, 281, 0, 0] (foD [] [1, 281, 0, 0] 0) (.ret xM) (.apply (tuple [fM, foD [] [1, 281, 0, 0] 0])))
      (.let_ [1, 281, 1] (foD [] [1, 281, 1] 0)
        (.let_ [1, 281, 1, 0] (foD [] [1, 281, 1, 0] 0) (.ret fM)
          (.let_ [1, 281, 1, 1] (foD [] [1, 281, 1, 1] 0) (.ret xsM)
            (.apply (tuple [sym "map", foD [] [1, 281, 1, 0] 0, foD [] [1, 281, 1, 1] 0]))))
        (.apply (tuple [sym "Cons", foD [] [1, 281, 0] 0, foD [] [1, 281, 1] 0])))⟩

theorem program_eq : program.equations = [incE, mapNilE, mapConsE] := rfl

/-- Under the clause that calls a tuple as it stands, the call through `$f` passes `$x` as it is. -/
theorem asWritten_body :
    (elabEquationH .asWritten byValue [] mapConsS).rhs =
      .let_ [1, 281, 0] (foD [] [1, 281, 0] 0) (.apply (tuple [fM, xM]))
        (.let_ [1, 281, 1] (foD [] [1, 281, 1] 0)
          (.let_ [1, 281, 1, 0] (foD [] [1, 281, 1, 0] 0) (.ret fM)
            (.let_ [1, 281, 1, 1] (foD [] [1, 281, 1, 1] 0) (.ret xsM)
              (.apply (tuple [sym "map", foD [] [1, 281, 1, 0] 0, foD [] [1, 281, 1, 1] 0]))))
          (.apply (tuple [sym "Cons", foD [] [1, 281, 0] 0, foD [] [1, 281, 1] 0]))) := rfl

/-- The text of the query. -/
def queryText : MData := tuple [sym "map", sym "inc", tuple [sym "Cons", sym "Z", sym "Nil"]]

/-- The query `(map inc (Cons Z Nil))`, elaborated. -/
def query : Comp mkeys [] () MTy :=
  .let_ [3, 0] (foD [] [3, 0] 0) (.apply (sym "inc"))
    (.let_ [3, 1] (foD [] [3, 1] 0)
      (.let_ [3, 1, 0] (foD [] [3, 1, 0] 0) (.apply (sym "Z"))
        (.let_ [3, 1, 1] (foD [] [3, 1, 1] 0) (.apply (sym "Nil"))
          (.apply (tuple [sym "Cons", foD [] [3, 1, 0] 0, foD [] [3, 1, 1] 0]))))
      (.apply (tuple [sym "map", foD [] [3, 0] 0, foD [] [3, 1] 0])))

theorem query_eq : elabQueryH .byValue byValue surface (.text queryText) = query := rfl

/-! ## The run -/

/-- The store when `map` is called on the list. -/
def K4 : List (Constraint mkeys [] ()) :=
  [(foD [0] [3, 0] 0, sym "inc"),
   (foD [1] [3, 1, 0] 0, sym "Z"),
   (foD [2] [3, 1, 1] 0, sym "Nil"),
   (foD [3] [3, 1] 0, tuple [sym "Cons", foD [1] [3, 1, 0] 0, foD [2] [3, 1, 1] 0])]

/-- The store when `map` is called on the tail. -/
def K11 : List (Constraint mkeys [] ()) :=
  K4 ++
  [(tuple [sym "map", foD [4] [281] 0, tuple [sym "Cons", foD [4] [281] 1, foD [4] [281] 2]],
      tuple [sym "map", foD [0] [3, 0] 0, foD [3] [3, 1] 0]),
   (foD [5, 4] [1, 281, 0, 0] 0, foD [4] [281] 1),
   (tuple [sym "inc", foD [6] [240] 0], tuple [foD [4] [281] 0, foD [5, 4] [1, 281, 0, 0] 0]),
   (foD [7, 6] [1, 240, 0] 0, foD [6] [240] 0),
   (foD [8, 4] [1, 281, 0] 0, tuple [sym "S", foD [7, 6] [1, 240, 0] 0]),
   (foD [9, 4] [1, 281, 1, 0] 0, foD [4] [281] 0),
   (foD [10, 4] [1, 281, 1, 1] 0, foD [4] [281] 2)]

/-- The store at the end. -/
def Kf : List (Constraint mkeys [] ()) :=
  K11 ++
  [(tuple [sym "map", foD [11] [280] 0, sym "Nil"],
      tuple [sym "map", foD [9, 4] [1, 281, 1, 0] 0, foD [10, 4] [1, 281, 1, 1] 0]),
   (foD [12, 4] [1, 281, 1] 0, sym "Nil")]

def vf : MData := tuple [sym "Cons", foD [8, 4] [1, 281, 0] 0, foD [12, 4] [1, 281, 1] 0]

def finalB : Branch mkeys [] () MTy := ⟨Kf, .value vf, [], []⟩

/-- **The equation for the empty list does not fit the first call**: the store has bound the list to a
`Cons`. -/
theorem dead_nil_first :
    ¬ Solvable (K4 ++ [(instantiate (copyAt mkeys 4) mapNilE.lhs,
      tuple [sym "map", foD [0] [3, 0] 0, foD [3] [3, 1] 0])]) := by
  rintro ⟨X, target, σ, solved⟩
  obtain ⟨inK, last⟩ := (models_append σ _ _).mp solved
  simp only [K4, Models, List.forall_mem_cons] at inK
  obtain ⟨-, -, -, e4, -⟩ := inK
  have new : tupleAt [symAt "map", instantiate σ (foD [4] [280] 0), symAt "Nil"] =
      tupleAt [symAt "map", instantiate σ (foD [0] [3, 0] 0), instantiate σ (foD [3] [3, 1] 0)] :=
    last _ (List.mem_singleton_self _)
  have h4 : instantiate σ (foD [3] [3, 1] 0) =
      tupleAt [symAt "Cons", instantiate σ (foD [1] [3, 1, 0] 0), instantiate σ (foD [2] [3, 1, 1] 0)] := e4
  exact sym_ne_tuple ((tuple3_inj new).2.2.trans h4)

/-- **The equation for a `Cons` does not fit the second call**: the store has bound the tail to `Nil`. -/
theorem dead_cons_second :
    ¬ Solvable (K11 ++ [(instantiate (copyAt mkeys 11) mapConsE.lhs,
      tuple [sym "map", foD [9, 4] [1, 281, 1, 0] 0, foD [10, 4] [1, 281, 1, 1] 0])]) := by
  rintro ⟨X, target, σ, solved⟩
  obtain ⟨inK, last⟩ := (models_append σ _ _).mp solved
  simp only [K11, K4, List.cons_append, List.nil_append, Models, List.forall_mem_cons] at inK
  obtain ⟨-, -, e3, e4, e5, -, -, -, -, -, e11, -⟩ := inK
  have new : tupleAt [symAt "map", instantiate σ (foD [11] [281] 0),
        tupleAt [symAt "Cons", instantiate σ (foD [11] [281] 1), instantiate σ (foD [11] [281] 2)]] =
      tupleAt [symAt "map", instantiate σ (foD [9, 4] [1, 281, 1, 0] 0),
        instantiate σ (foD [10, 4] [1, 281, 1, 1] 0)] :=
    last _ (List.mem_singleton_self _)
  have h3 : instantiate σ (foD [2] [3, 1, 1] 0) = symAt "Nil" := e3
  have h4 : instantiate σ (foD [3] [3, 1] 0) =
      tupleAt [symAt "Cons", instantiate σ (foD [1] [3, 1, 0] 0), instantiate σ (foD [2] [3, 1, 1] 0)] := e4
  have h5 : tupleAt [symAt "map", instantiate σ (foD [4] [281] 0),
        tupleAt [symAt "Cons", instantiate σ (foD [4] [281] 1), instantiate σ (foD [4] [281] 2)]] =
      tupleAt [symAt "map", instantiate σ (foD [0] [3, 0] 0), instantiate σ (foD [3] [3, 1] 0)] := e5
  have h11 : instantiate σ (foD [10, 4] [1, 281, 1, 1] 0) = instantiate σ (foD [4] [281] 2) := e11
  have tail : instantiate σ (foD [4] [281] 2) = symAt "Nil" :=
    ((tuple3_inj ((tuple3_inj h5).2.2.trans h4)).2.2).trans h3
  exact sym_ne_tuple (((tuple3_inj new).2.2.trans h11).trans tail).symm

/-- No equation of the three answers the call. -/
macro "unanswered" : tactic =>
  `(tactic| (rw [program_eq];
             refine List.forall_mem_cons.mpr ⟨?_, List.forall_mem_cons.mpr ⟨?_,
               List.forall_mem_cons.mpr ⟨?_, fun _ member => nomatch member⟩⟩⟩ <;> clash))

/-- The two other equations' alternatives are dead, by the shape of the call. -/
macro "others_dead" : tactic =>
  `(tactic| (intro e member;
             simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, false_or] at member;
             rcases member with same | same <;> (subst same; clash)))

theorem along : Along D program supply (Config.initial sp query) ⟨13, 0, sp⟩ finalB := by
  have h := Along.start (D := D) (P := program) (supply := supply) sp query
  -- the query's arguments: `inc`, and the list `(Cons Z Nil)` built from its evaluated elements
  have h := h.letStart
  have h := h.unmatched (by unanswered)
  have h := h.letBind
  have h := h.letStart
  have h := h.letStart
  have h := h.unmatched (by unanswered)
  have h := h.letBind
  have h := h.letStart
  have h := h.unmatched (by unanswered)
  have h := h.letBind
  have h := h.unmatched (by unanswered)
  have h := h.letBind
  -- the call of `map` on the list: the equation for a `Cons` answers it
  have h := h.withStore K4 rfl
  have h := h.call [incE, mapNilE] mapConsE [] program_eq (by
    intro e member
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with same | same
    · subst same; clash
    · subst same; exact dead_nil_first)
  -- the call through the function variable, `($f $x)`: answered by `inc`
  have h := h.letStart
  have h := h.letStart
  have h := h.ret
  have h := h.letBind
  have h := h.call [] incE [mapNilE, mapConsE] program_eq (by others_dead)
  have h := h.letStart
  have h := h.ret
  have h := h.letBind
  have h := h.unmatched (by unanswered)
  have h := h.letBind
  -- the recursive call `(map $f $xs)` on the tail: the equation for the empty list answers it
  have h := h.letStart
  have h := h.letStart
  have h := h.ret
  have h := h.letBind
  have h := h.letStart
  have h := h.ret
  have h := h.letBind
  have h := h.withStore K11 rfl
  have h := h.call [incE] mapNilE [mapConsE] program_eq (by
    intro e member
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with same | same
    · subst same; clash
    · subst same; exact dead_cons_second)
  have h := h.unmatched (by unanswered)
  have h := h.letBind
  -- `Cons` of the two values
  have h := h.unmatched (by unanswered)
  exact h

/-! ## The answer -/

def solution : Assignment (fam mkeys) noNames :=
  closeNames [(([0], [3, 0], 0), csym "inc"), (([1], [3, 1, 0], 0), csym "Z"), (([2], [3, 1, 1], 0), csym "Nil"),
    (([3], [3, 1], 0), ctuple [csym "Cons", csym "Z", csym "Nil"]),
    (([4], [281], 0), csym "inc"), (([4], [281], 1), csym "Z"), (([4], [281], 2), csym "Nil"),
    (([5, 4], [1, 281, 0, 0], 0), csym "Z"), (([6], [240], 0), csym "Z"), (([7, 6], [1, 240, 0], 0), csym "Z"),
    (([8, 4], [1, 281, 0], 0), ctuple [csym "S", csym "Z"]), (([9, 4], [1, 281, 1, 0], 0), csym "inc"),
    (([10, 4], [1, 281, 1, 1], 0), csym "Nil"), (([11], [280], 0), csym "inc"),
    (([12, 4], [1, 281, 1], 0), csym "Nil")] (csym "a")

theorem live : Solvable Kf := ⟨Empty, noNames, solution, by decide⟩

/-- `(Cons (S Z) Nil)`. -/
def answer : MClosed := ctuple [csym "Cons", ctuple [csym "S", csym "Z"], csym "Nil"]

theorem determines : Determines Kf vf answer := by
  refine ⟨live, fun target τ solved => ?_⟩
  simp only [Kf, K11, K4, List.cons_append, List.nil_append, Models, List.forall_mem_cons] at solved
  obtain ⟨-, e2, -, e4, e5, e6, e7, e8, e9, -, -, -, e13, -⟩ := solved
  have h2 : instantiate τ (foD [1] [3, 1, 0] 0) = symAt "Z" := e2
  have h4 : instantiate τ (foD [3] [3, 1] 0) =
      tupleAt [symAt "Cons", instantiate τ (foD [1] [3, 1, 0] 0), instantiate τ (foD [2] [3, 1, 1] 0)] := e4
  have h5 : tupleAt [symAt "map", instantiate τ (foD [4] [281] 0),
        tupleAt [symAt "Cons", instantiate τ (foD [4] [281] 1), instantiate τ (foD [4] [281] 2)]] =
      tupleAt [symAt "map", instantiate τ (foD [0] [3, 0] 0), instantiate τ (foD [3] [3, 1] 0)] := e5
  have h6 : instantiate τ (foD [5, 4] [1, 281, 0, 0] 0) = instantiate τ (foD [4] [281] 1) := e6
  have h7 : tupleAt [symAt "inc", instantiate τ (foD [6] [240] 0)] =
      tupleAt [instantiate τ (foD [4] [281] 0), instantiate τ (foD [5, 4] [1, 281, 0, 0] 0)] := e7
  have h8 : instantiate τ (foD [7, 6] [1, 240, 0] 0) = instantiate τ (foD [6] [240] 0) := e8
  have h9 : instantiate τ (foD [8, 4] [1, 281, 0] 0) =
      tupleAt [symAt "S", instantiate τ (foD [7, 6] [1, 240, 0] 0)] := e9
  have h13 : instantiate τ (foD [12, 4] [1, 281, 1] 0) = symAt "Nil" := e13
  have first : instantiate τ (foD [4] [281] 1) = instantiate τ (foD [1] [3, 1, 0] 0) :=
    (tuple3_inj ((tuple3_inj h5).2.2.trans h4)).2.1
  show tupleAt [symAt "Cons", instantiate τ (foD [8, 4] [1, 281, 0] 0),
    instantiate τ (foD [12, 4] [1, 281, 1] 0)] = _
  rw [h9, h8, (tuple2_inj h7).2, h6, first, h2, h13]
  rfl

/-- **The run of `map` with a function argument under the clause by value**: it ends, quiescent, with the
bag `{(Cons (S Z) Nil)}`. -/
theorem runs_answers : ∃ C : Config mkeys [] () MTy,
    Runs D program supply (Config.initial sp query) C ∧ Config.Quiescent (D := D) program supply C ∧
      Config.answers (D := D) C = {{answer}} := by
  have finished : Branch.Finished (D := D) finalB := ⟨rfl, _, rfl⟩
  obtain ⟨C, runs, quiescent, answers⟩ := Along.answers along finished live
  have same : Branch.answer (D := D) finalB = {answer} :=
    Branch.answer_of_determines (D := D) (b := finalB) rfl determines
  exact ⟨C, runs, quiescent, answers.trans (congrArg (fun s => ({s} : Multiset (Set MClosed))) same)⟩

/-! ## Through the translation -/

theorem texts : ∀ e ∈ surface.equations,
    ∃ t, e.body = .text t ∧ ValueTextH (paramModes byValue [] e) (hview t) :=
  List.forall_mem_cons.mpr ⟨⟨_, rfl, by decide⟩, List.forall_mem_cons.mpr ⟨⟨_, rfl, by decide⟩,
    List.forall_mem_cons.mpr ⟨⟨_, rfl, by decide⟩, fun _ member => nomatch member⟩⟩⟩

theorem present : ∀ e ∈ surface.equations, (elabEquation byValue [] e).Scoped :=
  List.forall_mem_cons.mpr ⟨by decide, List.forall_mem_cons.mpr ⟨by decide,
    List.forall_mem_cons.mpr ⟨by decide, fun _ member => nomatch member⟩⟩⟩

/-- **`map` with a function argument, hosted**: a frontier of states that runs of the step of the
translated program reach from the translation's start answers `{(Cons (S Z) Nil)}`. -/
theorem hosted :
    ∃ L : Multiset (Branch mkeys [] () untyped.discipline.Ty × Hosting.HostState MSig × ℕ),
      Hosting.frontierAnswers Hosting.mettaNodes L = {{answer}} ∧
      ∀ x ∈ L, Relation.ReflTransGen (Hosting.Fires Hosting.mettaNodes program)
        (Hosting.start Hosting.mettaNodes program query) x.2.1 := by
  obtain ⟨C, runs, -, answers⟩ := runs_answers
  obtain ⟨L, same, reached⟩ := static_answers .byValue byValue Hosting.mettaNodes untyped supply sp
    byValue_faithful byValue_arrows (fun _ _ => rfl) surface rfl texts present queryText (by decide) (by decide)
    runs
  exact ⟨L, same.symm.trans answers, reached⟩

#print axioms program_eq
#print axioms asWritten_body
#print axioms query_eq
#print axioms dead_nil_first
#print axioms dead_cons_second
#print axioms along
#print axioms runs_answers
#print axioms hosted

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.FunctionVariables.ExampleMap
