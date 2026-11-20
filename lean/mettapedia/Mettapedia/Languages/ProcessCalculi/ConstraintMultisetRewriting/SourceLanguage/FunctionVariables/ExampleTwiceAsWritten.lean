import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.FunctionVariables.ExampleTwice

/-!
# `twice` as written, under the clause that calls the tuple as it stands

The text of `ExampleTwice`, under `Clause.asWritten`. The elaborated program is the one
`Elaboration.elaborate` makes (`program_is_elaborate`): the body of `twice` is one call of the whole
tuple `($f ($f $x))`, whose inner call is passed as text (`program_eq`). A run ends, quiescent, with the
bag `{(S (inc Z))}` (`runs_answers`): the inner call is never made.

This is the control for `ExampleTwice.runs_answers`: the same text, the same reference semantics, the
other clause, and another bag (`bags_differ`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.FunctionVariables.ExampleTwiceAsWritten

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Elaboration Toolkit
open ExampleTwice (D supply sp byValue surface incE nI fT xT query)

/-- The program under the clause that calls the tuple as it stands. -/
def program : Program mkeys [] () MTy := elaborateH .asWritten byValue surface

/-- **It is the elaboration's program.** -/
theorem program_is_elaborate : program = elaborate byValue surface := elaborateH_asWritten byValue surface

/-- The body of `inc` has no tuple with a head that is not a symbol: every clause elaborates it as
`Elaboration.elabText` does. -/
theorem inc_alike (cl : Clause) (modes : Name mkeys → VarMode) (path : List ℕ) :
    elabH cl byValue [] modes path (hview (tuple [sym "S", nI])) =
      elabText byValue [] modes path (view (tuple [sym "S", nI])) := by
  rw [← forget_hview]
  exact elabH_eq cl byValue [] modes path _ (.inr ⟨trivial, trivial⟩)

/-- `(= (twice $f $x) ($f ($f $x)))`: one call of the whole tuple. -/
def twiceE : Equation mkeys [] () MTy :=
  ⟨[241], tuple [sym "twice", fT, xT], .apply (tuple [fT, tuple [fT, xT]])⟩

theorem program_eq : program.equations = [incE, twiceE] := rfl

theorem query_eq :
    elabQueryH .asWritten byValue surface (.text (tuple [sym "twice", sym "inc", sym "Z"])) = query := rfl

/-- The store at the end. -/
def Kf : List (Constraint mkeys [] ()) :=
  [(foD [0] [3, 0] 0, sym "inc"),
   (foD [1] [3, 1] 0, sym "Z"),
   (tuple [sym "twice", foD [2] [241] 0, foD [2] [241] 1], tuple [sym "twice", foD [0] [3, 0] 0, foD [1] [3, 1] 0]),
   (tuple [sym "inc", foD [3] [240] 0], tuple [foD [2] [241] 0, tuple [foD [2] [241] 0, foD [2] [241] 1]]),
   (foD [4, 3] [1, 240, 0] 0, foD [3] [240] 0)]

def vf : MData := tuple [sym "S", foD [4, 3] [1, 240, 0] 0]

def finalB : Branch mkeys [] () MTy := ⟨Kf, .value vf, [], []⟩

macro "unanswered" : tactic =>
  `(tactic| (rw [program_eq];
             refine List.forall_mem_cons.mpr ⟨?_, List.forall_mem_cons.mpr ⟨?_, fun _ member => nomatch member⟩⟩
               <;> clash))

macro "other_dead" : tactic =>
  `(tactic| (intro e member;
             simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, false_or] at member;
             subst member; clash))

theorem along : Along D program supply (Config.initial sp query) ⟨5, 0, sp⟩ finalB := by
  have h := Along.start (D := D) (P := program) (supply := supply) sp query
  have h := h.letStart
  have h := h.unmatched (by unanswered)
  have h := h.letBind
  have h := h.letStart
  have h := h.unmatched (by unanswered)
  have h := h.letBind
  have h := h.call [incE] twiceE [] program_eq (by other_dead)
  -- the whole tuple `($f ($f $x))` is called: `inc` answers it, with the inner call as its argument
  have h := h.call [] incE [twiceE] program_eq (by other_dead)
  have h := h.letStart
  have h := h.ret
  have h := h.letBind
  have h := h.unmatched (by unanswered)
  exact h

def solution : Assignment (fam mkeys) noNames :=
  closeNames [(([0], [3, 0], 0), csym "inc"), (([1], [3, 1], 0), csym "Z"), (([2], [241], 0), csym "inc"),
    (([2], [241], 1), csym "Z"), (([3], [240], 0), ctuple [csym "inc", csym "Z"]),
    (([4, 3], [1, 240, 0], 0), ctuple [csym "inc", csym "Z"])] (csym "a")

theorem live : Solvable Kf := ⟨Empty, noNames, solution, by decide⟩

/-- `(S (inc Z))`. -/
def answer : MClosed := ctuple [csym "S", ctuple [csym "inc", csym "Z"]]

theorem determines : Determines Kf vf answer := by
  refine ⟨live, fun target τ solved => ?_⟩
  simp only [Kf, Models, List.forall_mem_cons] at solved
  obtain ⟨e1, e2, e3, e4, e5, -⟩ := solved
  have h1 : instantiate τ (foD [0] [3, 0] 0) = symAt "inc" := e1
  have h2 : instantiate τ (foD [1] [3, 1] 0) = symAt "Z" := e2
  have h3 : tupleAt [symAt "twice", instantiate τ (foD [2] [241] 0), instantiate τ (foD [2] [241] 1)] =
      tupleAt [symAt "twice", instantiate τ (foD [0] [3, 0] 0), instantiate τ (foD [1] [3, 1] 0)] := e3
  have h4 : tupleAt [symAt "inc", instantiate τ (foD [3] [240] 0)] =
      tupleAt [instantiate τ (foD [2] [241] 0),
        tupleAt [instantiate τ (foD [2] [241] 0), instantiate τ (foD [2] [241] 1)]] := e4
  have h5 : instantiate τ (foD [4, 3] [1, 240, 0] 0) = instantiate τ (foD [3] [240] 0) := e5
  obtain ⟨-, onF, onX⟩ := tuple3_inj h3
  show tupleAt [symAt "S", instantiate τ (foD [4, 3] [1, 240, 0] 0)] = _
  rw [h5, (tuple2_inj h4).2, onF, onX, h1, h2]
  rfl

/-- **The run of the text under the clause that calls the tuple as it stands**: it ends, quiescent, with
the bag `{(S (inc Z))}`. -/
theorem runs_answers : ∃ C : Config mkeys [] () MTy,
    Runs D program supply (Config.initial sp query) C ∧ Config.Quiescent (D := D) program supply C ∧
      Config.answers (D := D) C = {{answer}} := by
  have finished : Branch.Finished (D := D) finalB := ⟨rfl, _, rfl⟩
  obtain ⟨C, runs, quiescent, answers⟩ := Along.answers along finished live
  have same : Branch.answer (D := D) finalB = {answer} :=
    Branch.answer_of_determines (D := D) (b := finalB) rfl determines
  exact ⟨C, runs, quiescent, answers.trans (congrArg (fun s => ({s} : Multiset (Set MClosed))) same)⟩

/-- **The two clauses answer the text differently**: `(S (inc Z))` is not `(S (S Z))`. -/
theorem bags_differ : ({{answer}} : Multiset (Set MClosed)) ≠ {{ExampleTwice.answer}} := by
  intro same
  have inside : answer ∈ ({ExampleTwice.answer} : Set MClosed) := by
    rw [← Multiset.singleton_inj.mp same]
    exact Set.mem_singleton _
  exact absurd (Set.mem_singleton_iff.mp inside) (by decide)

#print axioms program_is_elaborate
#print axioms inc_alike
#print axioms program_eq
#print axioms along
#print axioms runs_answers
#print axioms bags_differ

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.FunctionVariables.ExampleTwiceAsWritten
