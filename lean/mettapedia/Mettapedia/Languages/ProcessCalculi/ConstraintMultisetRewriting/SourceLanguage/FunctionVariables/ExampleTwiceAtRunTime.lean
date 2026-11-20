import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.FunctionVariables.ExampleTwice

/-!
# `twice` as written, under the clause that runs the tuple when it is reached

The text of `ExampleTwice`, under `Clause.atRunTime`: the body of `twice` is `run` of the whole tuple
`($f ($f $x))` (`program_eq`). When the alternative reaches it, the store has bound `$f` to `inc` and
`$x` to `Z` (`principal`); the tuple dereferenced is the text `(inc (inc Z))`, and the program's reading
of it as code evaluates the inner call at its own arrow. A run ends, quiescent, with the bag
`{(S (S Z))}` (`runs_answers`), in twenty-three steps.

The right-hand side of `twice` is a `run`: the program is outside the fragment with arrows
(`not_arrows`), so the run theorems of the translation do not apply to it.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.FunctionVariables.ExampleTwiceAtRunTime

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Elaboration Toolkit
open ExampleTwice (D supply sp byValue surface incE nI fT xT query)

/-- The program under the clause that runs the tuple when it is reached. -/
def program : Program mkeys [] () MTy := elaborateH .atRunTime byValue surface

/-- `(= (twice $f $x) ($f ($f $x)))`: the tuple is run as text. -/
def twiceE : Equation mkeys [] () MTy :=
  ⟨[241], tuple [sym "twice", fT, xT], .run (tuple [fT, tuple [fT, xT]])⟩

theorem program_eq : program.equations = [incE, twiceE] := rfl

theorem query_eq :
    elabQueryH .atRunTime byValue surface (.text (tuple [sym "twice", sym "inc", sym "Z"])) = query := rfl

/-- The right-hand side of `twice` is not of the fragment with arrows. -/
theorem not_arrows : ¬ Hosting.ArrowProgram program := fun arrows =>
  arrows twiceE (by rw [program_eq]; exact List.mem_cons_of_mem _ List.mem_cons_self)

/-- The store when the tuple is run. -/
def K3 : List (Constraint mkeys [] ()) :=
  [(foD [0] [3, 0] 0, sym "inc"),
   (foD [1] [3, 1] 0, sym "Z"),
   (tuple [sym "twice", foD [2] [241] 0, foD [2] [241] 1], tuple [sym "twice", foD [0] [3, 0] 0, foD [1] [3, 1] 0])]

/-- What the store has bound when the tuple is run. -/
def θ : Assignment (fam mkeys) (fam mkeys) :=
  bindNames [(([0], [3, 0], 0), sym "inc"), (([1], [3, 1], 0), sym "Z"), (([2], [241], 0), sym "inc"),
    (([2], [241], 1), sym "Z")]

theorem principal : Principal K3 θ := by
  refine principal_bindNames (by decide) ?_
  intro entry member X target σ models
  simp only [K3, Models, List.forall_mem_cons] at models
  obtain ⟨e1, e2, e3, -⟩ := models
  have h1 : σ (fo [0] [3, 0] 0) = symAt "inc" := (instantiate_foD σ [0] [3, 0] 0).symm.trans e1
  have h2 : σ (fo [1] [3, 1] 0) = symAt "Z" := (instantiate_foD σ [1] [3, 1] 0).symm.trans e2
  have h3 : tupleAt [symAt "twice", instantiate σ (foD [2] [241] 0), instantiate σ (foD [2] [241] 1)] =
      tupleAt [symAt "twice", instantiate σ (foD [0] [3, 0] 0), instantiate σ (foD [1] [3, 1] 0)] := e3
  obtain ⟨-, onF, onX⟩ := tuple3_inj h3
  rw [instantiate_foD, instantiate_foD] at onF onX
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  obtain rfl | rfl | rfl | rfl := member
  · exact h1
  · exact h2
  · exact onF.trans h1
  · exact onX.trans h2

/-- The store at the end. -/
def Kf : List (Constraint mkeys [] ()) :=
  K3 ++
  [(foD [3] [2, 0, 0, 0] 0, sym "Z"),
   (tuple [sym "inc", foD [4] [240] 0], tuple [sym "inc", foD [3] [2, 0, 0, 0] 0]),
   (foD [5, 4] [1, 240, 0] 0, foD [4] [240] 0),
   (foD [6] [2, 0, 0] 0, tuple [sym "S", foD [5, 4] [1, 240, 0] 0]),
   (tuple [sym "inc", foD [7] [240] 0], tuple [sym "inc", foD [6] [2, 0, 0] 0]),
   (foD [8, 7] [1, 240, 0] 0, foD [7] [240] 0)]

def vf : MData := tuple [sym "S", foD [8, 7] [1, 240, 0] 0]

def finalB : Branch mkeys [] () MTy := ⟨Kf, .value vf, [], []⟩

macro "unanswered" : tactic =>
  `(tactic| (rw [program_eq];
             refine List.forall_mem_cons.mpr ⟨?_, List.forall_mem_cons.mpr ⟨?_, fun _ member => nomatch member⟩⟩
               <;> clash))

macro "other_dead" : tactic =>
  `(tactic| (intro e member;
             simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, false_or] at member;
             subst member; clash))

theorem along : Along D program supply (Config.initial sp query) ⟨9, 0, sp⟩ finalB := by
  have h := Along.start (D := D) (P := program) (supply := supply) sp query
  have h := h.letStart
  have h := h.unmatched (by unanswered)
  have h := h.letBind
  have h := h.letStart
  have h := h.unmatched (by unanswered)
  have h := h.letBind
  have h := h.call [incE] twiceE [] program_eq (by other_dead)
  -- the tuple is run: dereferenced, it is the text `(inc (inc Z))`, read as code by value
  have h := h.run θ principal
  have h := h.letStart
  have h := h.letStart
  have h := h.unmatched (by unanswered)
  have h := h.letBind
  have h := h.call [] incE [twiceE] program_eq (by other_dead)
  have h := h.letStart
  have h := h.ret
  have h := h.letBind
  have h := h.unmatched (by unanswered)
  have h := h.letBind
  have h := h.call [] incE [twiceE] program_eq (by other_dead)
  have h := h.letStart
  have h := h.ret
  have h := h.letBind
  have h := h.unmatched (by unanswered)
  exact h

def solution : Assignment (fam mkeys) noNames :=
  closeNames [(([0], [3, 0], 0), csym "inc"), (([1], [3, 1], 0), csym "Z"), (([2], [241], 0), csym "inc"),
    (([2], [241], 1), csym "Z"), (([3], [2, 0, 0, 0], 0), csym "Z"), (([4], [240], 0), csym "Z"),
    (([5, 4], [1, 240, 0], 0), csym "Z"), (([6], [2, 0, 0], 0), ctuple [csym "S", csym "Z"]),
    (([7], [240], 0), ctuple [csym "S", csym "Z"]), (([8, 7], [1, 240, 0], 0), ctuple [csym "S", csym "Z"])]
    (csym "a")

theorem live : Solvable Kf := ⟨Empty, noNames, solution, by decide⟩

theorem determines : Determines Kf vf ExampleTwice.answer := by
  refine ⟨live, fun target τ solved => ?_⟩
  simp only [Kf, K3, List.cons_append, List.nil_append, Models, List.forall_mem_cons] at solved
  obtain ⟨-, -, -, e4, e5, e6, e7, e8, e9, -⟩ := solved
  have h4 : instantiate τ (foD [3] [2, 0, 0, 0] 0) = symAt "Z" := e4
  have h5 : tupleAt [symAt "inc", instantiate τ (foD [4] [240] 0)] =
      tupleAt [symAt "inc", instantiate τ (foD [3] [2, 0, 0, 0] 0)] := e5
  have h6 : instantiate τ (foD [5, 4] [1, 240, 0] 0) = instantiate τ (foD [4] [240] 0) := e6
  have h7 : instantiate τ (foD [6] [2, 0, 0] 0) =
      tupleAt [symAt "S", instantiate τ (foD [5, 4] [1, 240, 0] 0)] := e7
  have h8 : tupleAt [symAt "inc", instantiate τ (foD [7] [240] 0)] =
      tupleAt [symAt "inc", instantiate τ (foD [6] [2, 0, 0] 0)] := e8
  have h9 : instantiate τ (foD [8, 7] [1, 240, 0] 0) = instantiate τ (foD [7] [240] 0) := e9
  show tupleAt [symAt "S", instantiate τ (foD [8, 7] [1, 240, 0] 0)] = _
  rw [h9, (tuple2_inj h8).2, h7, h6, (tuple2_inj h5).2, h4]
  rfl

/-- **The run of the text under the clause that runs the tuple when it is reached**: it ends, quiescent,
with the bag `{(S (S Z))}`. -/
theorem runs_answers : ∃ C : Config mkeys [] () MTy,
    Runs D program supply (Config.initial sp query) C ∧ Config.Quiescent (D := D) program supply C ∧
      Config.answers (D := D) C = {{ExampleTwice.answer}} := by
  have finished : Branch.Finished (D := D) finalB := ⟨rfl, _, rfl⟩
  obtain ⟨C, runs, quiescent, answers⟩ := Along.answers along finished live
  have same : Branch.answer (D := D) finalB = {ExampleTwice.answer} :=
    Branch.answer_of_determines (D := D) (b := finalB) rfl determines
  exact ⟨C, runs, quiescent, answers.trans (congrArg (fun s => ({s} : Multiset (Set MClosed))) same)⟩

#print axioms program_eq
#print axioms not_arrows
#print axioms principal
#print axioms along
#print axioms runs_answers

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.FunctionVariables.ExampleTwiceAtRunTime
