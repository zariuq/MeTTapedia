import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.FunctionVariables.Hosted

/-!
# `compose`: two function variables, and two functions that fit a call by its shape

```
(= (inc $n) (S $n))
(= (dbl $n) (D $n))
(= (compose $f $g $x) ($f ($g $x)))
!(compose inc dbl Z)
```

Under the clause by value the inner call `($g $x)` is evaluated at its own arrow and the outer call is
the tuple of `$f` and its value (`program_eq`). Both `inc` and `dbl` have left-hand sides of the shape of
each call, a pair; which one answers is decided by what the store has bound the head to
(`dead_inc_inner`, `dead_dbl_outer`): the inner call is answered by `dbl` only, the outer by `inc` only.

* `runs_answers`: a run ends, quiescent, with the bag `{(S (D Z))}`. Twenty-five steps.
* `hosted`: the general theorem (`static_answers`) applies: a frontier of states that runs of the step
  reach from the translation's start answers `{(S (D Z))}`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.FunctionVariables.ExampleCompose

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Elaboration Toolkit
open ExampleTwice (D supply sp byValue incS incE)

/-! ## The text and its elaboration -/

abbrev nD : MData := foD [] [245] 0
abbrev fC : MData := foD [] [246] 0
abbrev gC : MData := foD [] [246] 1
abbrev xC : MData := foD [] [246] 2

def dblS : SEquation := ⟨[245], "dbl", [nD], .text (tuple [sym "D", nD])⟩
def composeS : SEquation := ⟨[246], "compose", [fC, gC, xC], .text (tuple [fC, tuple [gC, xC]])⟩

def surface : SProgram := ⟨[], [incS, dblS, composeS]⟩

def program : Program mkeys [] () MTy := elaborateH .byValue byValue surface

/-- `(= (dbl $n) (D $n))`. -/
def dblE : Equation mkeys [] () MTy :=
  ⟨[245], tuple [sym "dbl", nD],
    .let_ [1, 245, 0] (foD [] [1, 245, 0] 0) (.ret nD) (.apply (tuple [sym "D", foD [] [1, 245, 0] 0]))⟩

/-- `(= (compose $f $g $x) ($f ($g $x)))`: the call through `$g` at its own arrow, its argument at an
arrow inside; then the call of the tuple of `$f` and its value. -/
def composeE : Equation mkeys [] () MTy :=
  ⟨[246], tuple [sym "compose", fC, gC, xC],
    .let_ [1, 246, 0] (foD [] [1, 246, 0] 0)
      (.let_ [1, 246, 0, 0] (foD [] [1, 246, 0, 0] 0) (.ret xC) (.apply (tuple [gC, foD [] [1, 246, 0, 0] 0])))
      (.apply (tuple [fC, foD [] [1, 246, 0] 0]))⟩

theorem program_eq : program.equations = [incE, dblE, composeE] := rfl

/-- The text of the query. -/
def queryText : MData := tuple [sym "compose", sym "inc", sym "dbl", sym "Z"]

/-- The query `(compose inc dbl Z)`, elaborated. -/
def query : Comp mkeys [] () MTy :=
  .let_ [3, 0] (foD [] [3, 0] 0) (.apply (sym "inc"))
    (.let_ [3, 1] (foD [] [3, 1] 0) (.apply (sym "dbl"))
      (.let_ [3, 2] (foD [] [3, 2] 0) (.apply (sym "Z"))
        (.apply (tuple [sym "compose", foD [] [3, 0] 0, foD [] [3, 1] 0, foD [] [3, 2] 0]))))

theorem query_eq : elabQueryH .byValue byValue surface (.text queryText) = query := rfl

/-! ## Tuples of four, and symbols -/

theorem tuple4_inj {X : Type} {target : X → MetaArity MSig} {Δ : Ctx MSig}
    {a b c d a' b' c' d' : Term (signature MSig target) Δ ()}
    (same : tupleAt [a, b, c, d] = tupleAt [a', b', c', d']) : a = a' ∧ b = b' ∧ c = c' ∧ d = d' := by
  obtain ⟨ha, rest1⟩ := Args.cons.inj (op_inj same)
  obtain ⟨hb, rest2⟩ := Args.cons.inj rest1
  obtain ⟨hc, rest3⟩ := Args.cons.inj rest2
  exact ⟨ha, hb, hc, (Args.cons.inj rest3).1⟩

theorem symAt_inj {X : Type} {target : X → MetaArity MSig} {Δ : Ctx MSig} {a b : String}
    (same : (symAt a : Term (signature MSig target) Δ ()) = symAt b) : a = b := by
  have codes := congrArg rootCode same
  simpa [rootCode, symAt, MOp.code] using codes

/-! ## The run -/

/-- The store when the inner call `($g v)` is made. -/
def K5 : List (Constraint mkeys [] ()) :=
  [(foD [0] [3, 0] 0, sym "inc"),
   (foD [1] [3, 1] 0, sym "dbl"),
   (foD [2] [3, 2] 0, sym "Z"),
   (tuple [sym "compose", foD [3] [246] 0, foD [3] [246] 1, foD [3] [246] 2],
      tuple [sym "compose", foD [0] [3, 0] 0, foD [1] [3, 1] 0, foD [2] [3, 2] 0]),
   (foD [4, 3] [1, 246, 0, 0] 0, foD [3] [246] 2)]

/-- The store when the outer call `($f v)` is made. -/
def K8 : List (Constraint mkeys [] ()) :=
  K5 ++
  [(tuple [sym "dbl", foD [5] [245] 0], tuple [foD [3] [246] 1, foD [4, 3] [1, 246, 0, 0] 0]),
   (foD [6, 5] [1, 245, 0] 0, foD [5] [245] 0),
   (foD [7, 3] [1, 246, 0] 0, tuple [sym "D", foD [6, 5] [1, 245, 0] 0])]

/-- The store at the end. -/
def Kf : List (Constraint mkeys [] ()) :=
  K8 ++
  [(tuple [sym "inc", foD [8] [240] 0], tuple [foD [3] [246] 0, foD [7, 3] [1, 246, 0] 0]),
   (foD [9, 8] [1, 240, 0] 0, foD [8] [240] 0)]

def vf : MData := tuple [sym "S", foD [9, 8] [1, 240, 0] 0]

def finalB : Branch mkeys [] () MTy := ⟨Kf, .value vf, [], []⟩

/-- **`inc` does not answer the inner call**: the store has bound its head `$g` to `dbl`. -/
theorem dead_inc_inner :
    ¬ Solvable (K5 ++ [(instantiate (copyAt mkeys 5) incE.lhs,
      tuple [foD [3] [246] 1, foD [4, 3] [1, 246, 0, 0] 0])]) := by
  rintro ⟨X, target, σ, solved⟩
  obtain ⟨inK, last⟩ := (models_append σ _ _).mp solved
  simp only [K5, Models, List.forall_mem_cons] at inK
  obtain ⟨-, e2, -, e4, -⟩ := inK
  have new : tupleAt [symAt "inc", instantiate σ (foD [5] [240] 0)] =
      tupleAt [instantiate σ (foD [3] [246] 1), instantiate σ (foD [4, 3] [1, 246, 0, 0] 0)] :=
    last _ (List.mem_singleton_self _)
  have h2 : instantiate σ (foD [1] [3, 1] 0) = symAt "dbl" := e2
  have h4 : tupleAt [symAt "compose", instantiate σ (foD [3] [246] 0), instantiate σ (foD [3] [246] 1),
        instantiate σ (foD [3] [246] 2)] =
      tupleAt [symAt "compose", instantiate σ (foD [0] [3, 0] 0), instantiate σ (foD [1] [3, 1] 0),
        instantiate σ (foD [2] [3, 2] 0)] := e4
  have heads : (symAt "inc" : Term (signature MSig target) [] ()) = symAt "dbl" :=
    ((tuple2_inj new).1.trans (tuple4_inj h4).2.2.1).trans h2
  exact absurd (symAt_inj heads) (by decide)

/-- **`dbl` does not answer the outer call**: the store has bound its head `$f` to `inc`. -/
theorem dead_dbl_outer :
    ¬ Solvable (K8 ++ [(instantiate (copyAt mkeys 8) dblE.lhs,
      tuple [foD [3] [246] 0, foD [7, 3] [1, 246, 0] 0])]) := by
  rintro ⟨X, target, σ, solved⟩
  obtain ⟨inK, last⟩ := (models_append σ _ _).mp solved
  simp only [K8, K5, List.cons_append, List.nil_append, Models, List.forall_mem_cons] at inK
  obtain ⟨e1, -, -, e4, -⟩ := inK
  have new : tupleAt [symAt "dbl", instantiate σ (foD [8] [245] 0)] =
      tupleAt [instantiate σ (foD [3] [246] 0), instantiate σ (foD [7, 3] [1, 246, 0] 0)] :=
    last _ (List.mem_singleton_self _)
  have h1 : instantiate σ (foD [0] [3, 0] 0) = symAt "inc" := e1
  have h4 : tupleAt [symAt "compose", instantiate σ (foD [3] [246] 0), instantiate σ (foD [3] [246] 1),
        instantiate σ (foD [3] [246] 2)] =
      tupleAt [symAt "compose", instantiate σ (foD [0] [3, 0] 0), instantiate σ (foD [1] [3, 1] 0),
        instantiate σ (foD [2] [3, 2] 0)] := e4
  have heads : (symAt "dbl" : Term (signature MSig target) [] ()) = symAt "inc" :=
    ((tuple2_inj new).1.trans (tuple4_inj h4).2.1).trans h1
  exact absurd (symAt_inj heads) (by decide)

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

theorem along : Along D program supply (Config.initial sp query) ⟨10, 0, sp⟩ finalB := by
  have h := Along.start (D := D) (P := program) (supply := supply) sp query
  -- the query's three arguments
  have h := h.letStart
  have h := h.unmatched (by unanswered)
  have h := h.letBind
  have h := h.letStart
  have h := h.unmatched (by unanswered)
  have h := h.letBind
  have h := h.letStart
  have h := h.unmatched (by unanswered)
  have h := h.letBind
  -- the call of `compose`
  have h := h.call [incE, dblE] composeE [] program_eq (by others_dead)
  -- the inner call `($g $x)`: `dbl` answers it, `inc` does not
  have h := h.letStart
  have h := h.letStart
  have h := h.ret
  have h := h.letBind
  have h := h.withStore K5 rfl
  have h := h.call [incE] dblE [composeE] program_eq (by
    intro e member
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with same | same
    · subst same; exact dead_inc_inner
    · subst same; clash)
  have h := h.letStart
  have h := h.ret
  have h := h.letBind
  have h := h.unmatched (by unanswered)
  -- the outer call `($f v)`: `inc` answers it, `dbl` does not
  have h := h.letBind
  have h := h.withStore K8 rfl
  have h := h.call [] incE [dblE, composeE] program_eq (by
    intro e member
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, false_or] at member
    rcases member with same | same
    · subst same; exact dead_dbl_outer
    · subst same; clash)
  have h := h.letStart
  have h := h.ret
  have h := h.letBind
  have h := h.unmatched (by unanswered)
  exact h

/-! ## The answer -/

def solution : Assignment (fam mkeys) noNames :=
  closeNames [(([0], [3, 0], 0), csym "inc"), (([1], [3, 1], 0), csym "dbl"), (([2], [3, 2], 0), csym "Z"),
    (([3], [246], 0), csym "inc"), (([3], [246], 1), csym "dbl"), (([3], [246], 2), csym "Z"),
    (([4, 3], [1, 246, 0, 0], 0), csym "Z"), (([5], [245], 0), csym "Z"), (([6, 5], [1, 245, 0], 0), csym "Z"),
    (([7, 3], [1, 246, 0], 0), ctuple [csym "D", csym "Z"]), (([8], [240], 0), ctuple [csym "D", csym "Z"]),
    (([9, 8], [1, 240, 0], 0), ctuple [csym "D", csym "Z"])] (csym "a")

theorem live : Solvable Kf := ⟨Empty, noNames, solution, by decide⟩

/-- `(S (D Z))`. -/
def answer : MClosed := ctuple [csym "S", ctuple [csym "D", csym "Z"]]

theorem determines : Determines Kf vf answer := by
  refine ⟨live, fun target τ solved => ?_⟩
  simp only [Kf, K8, K5, List.cons_append, List.nil_append, Models, List.forall_mem_cons] at solved
  obtain ⟨-, -, e3, e4, e5, e6, e7, e8, e9, e10, -⟩ := solved
  have h3 : instantiate τ (foD [2] [3, 2] 0) = symAt "Z" := e3
  have h4 : tupleAt [symAt "compose", instantiate τ (foD [3] [246] 0), instantiate τ (foD [3] [246] 1),
        instantiate τ (foD [3] [246] 2)] =
      tupleAt [symAt "compose", instantiate τ (foD [0] [3, 0] 0), instantiate τ (foD [1] [3, 1] 0),
        instantiate τ (foD [2] [3, 2] 0)] := e4
  have h5 : instantiate τ (foD [4, 3] [1, 246, 0, 0] 0) = instantiate τ (foD [3] [246] 2) := e5
  have h6 : tupleAt [symAt "dbl", instantiate τ (foD [5] [245] 0)] =
      tupleAt [instantiate τ (foD [3] [246] 1), instantiate τ (foD [4, 3] [1, 246, 0, 0] 0)] := e6
  have h7 : instantiate τ (foD [6, 5] [1, 245, 0] 0) = instantiate τ (foD [5] [245] 0) := e7
  have h8 : instantiate τ (foD [7, 3] [1, 246, 0] 0) =
      tupleAt [symAt "D", instantiate τ (foD [6, 5] [1, 245, 0] 0)] := e8
  have h9 : tupleAt [symAt "inc", instantiate τ (foD [8] [240] 0)] =
      tupleAt [instantiate τ (foD [3] [246] 0), instantiate τ (foD [7, 3] [1, 246, 0] 0)] := e9
  have h10 : instantiate τ (foD [9, 8] [1, 240, 0] 0) = instantiate τ (foD [8] [240] 0) := e10
  show tupleAt [symAt "S", instantiate τ (foD [9, 8] [1, 240, 0] 0)] = _
  rw [h10, (tuple2_inj h9).2, h8, h7, (tuple2_inj h6).2, h5, (tuple4_inj h4).2.2.2, h3]
  rfl

/-- **The run of `compose` under the clause by value**: it ends, quiescent, with the bag `{(S (D Z))}`. -/
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

/-- **`compose`, hosted**: a frontier of states that runs of the step of the translated program reach
from the translation's start answers `{(S (D Z))}`. -/
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
#print axioms query_eq
#print axioms dead_inc_inner
#print axioms dead_dbl_outer
#print axioms along
#print axioms runs_answers
#print axioms hosted

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.FunctionVariables.ExampleCompose
