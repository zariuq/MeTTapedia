import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.FunctionVariables.ExampleTwiceAsWritten

/-!
# A function variable bound to a function that holds its parameter

```
(: keep (-> Atom Atom))
(= (keep $x) (Kept $x))
(= (twice $f $x) ($f ($f $x)))
!(twice keep Z)
```

`keep` holds its parameter: called directly, `(keep (keep Z))` answers `(Kept (keep Z))`
(`direct_answers`). Called through `$f`, the clauses part:

* **by value** (`byValue_answers`): the inner `($f $x)` is evaluated before the outer call, so `keep`
  receives the value `(Kept Z)`: the bag is `{(Kept (Kept Z))}`. The function's declaration is not
  consulted, because where the tuple is written the function is not known.
* **as it stands** (`asWritten_answers`): the bag is `{(Kept (keep Z))}`: every argument of a tuple whose
  head is not a symbol is held, whatever function the head turns out to be.
* **at run time** (`atRunTime_answers`): the tuple is run when the alternative reaches it; the store has
  bound `$f` to `keep`, the reading of the dereferenced text consults `keep`'s declaration and holds the
  argument: the bag is `{(Kept (keep Z))}`. This clause leaves the fragment with arrows (it is a `run`).

So naming a function that holds a parameter changes its call under the clause by value
(`byValue_differs`), and does not under the other two. The clause `Clause.declared` gives the code of
the first when the variable's declared type holds nothing, and the code of the second when it holds
the parameter (`declared_none`, `declared_holding`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.FunctionVariables.ExampleHolding

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Elaboration Toolkit
open ExampleTwice (D supply sp byValue twiceS fT xT)

/-! ## The text -/

abbrev xK : MData := foD [] [250] 0

def keepS : SEquation := ⟨[250], "keep", [xK], .text (tuple [sym "Kept", xK])⟩

/-- `keep` holds its parameter and its result. -/
def surface : SProgram := ⟨[⟨"keep", [.atom], .atom⟩], [keepS, twiceS]⟩

/-- `(= (keep $x) (Kept $x))`: the result is returned as written. -/
def keepE : Equation mkeys [] () MTy := ⟨[250], tuple [sym "keep", xK], .ret (tuple [sym "Kept", xK])⟩

/-- The query `(twice keep Z)`, elaborated (the same under every clause). -/
def query : Comp mkeys [] () MTy :=
  .let_ [3, 0] (foD [] [3, 0] 0) (.apply (sym "keep"))
    (.let_ [3, 1] (foD [] [3, 1] 0) (.apply (sym "Z"))
      (.apply (tuple [sym "twice", foD [] [3, 0] 0, foD [] [3, 1] 0])))

theorem query_eq (cl : Clause) :
    elabQueryH cl byValue surface (.text (tuple [sym "twice", sym "keep", sym "Z"])) = query := rfl

/-- No equation of a program of two equations answers the call. -/
macro "unanswered" eq:term : tactic =>
  `(tactic| (rw [$eq:term];
             refine List.forall_mem_cons.mpr ⟨?_, List.forall_mem_cons.mpr ⟨?_, fun _ member => nomatch member⟩⟩
               <;> clash))

/-- The other equation's alternative is dead. -/
macro "other_dead" : tactic =>
  `(tactic| (intro e member;
             simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, false_or] at member;
             subst member; clash))

/-- The store after the query's arguments and the call of `twice`. -/
def K3 : List (Constraint mkeys [] ()) :=
  [(foD [0] [3, 0] 0, sym "keep"),
   (foD [1] [3, 1] 0, sym "Z"),
   (tuple [sym "twice", foD [2] [241] 0, foD [2] [241] 1], tuple [sym "twice", foD [0] [3, 0] 0, foD [1] [3, 1] 0])]

/-! ## By value -/

namespace ByValue

def program : Program mkeys [] () MTy := elaborateH .byValue byValue surface

theorem program_eq : program.equations = [keepE, ExampleTwice.twiceE] := rfl

def Kf : List (Constraint mkeys [] ()) :=
  K3 ++
  [(foD [3, 2] [1, 241, 0, 0] 0, foD [2] [241] 1),
   (tuple [sym "keep", foD [4] [250] 0], tuple [foD [2] [241] 0, foD [3, 2] [1, 241, 0, 0] 0]),
   (foD [5, 2] [1, 241, 0] 0, tuple [sym "Kept", foD [4] [250] 0]),
   (tuple [sym "keep", foD [6] [250] 0], tuple [foD [2] [241] 0, foD [5, 2] [1, 241, 0] 0])]

def vf : MData := tuple [sym "Kept", foD [6] [250] 0]

def finalB : Branch mkeys [] () MTy := ⟨Kf, .value vf, [], []⟩

theorem along : Along D program supply (Config.initial sp query) ⟨7, 0, sp⟩ finalB := by
  have h := Along.start (D := D) (P := program) (supply := supply) sp query
  have h := h.letStart
  have h := h.unmatched (by unanswered program_eq)
  have h := h.letBind
  have h := h.letStart
  have h := h.unmatched (by unanswered program_eq)
  have h := h.letBind
  have h := h.call [keepE] ExampleTwice.twiceE [] program_eq (by other_dead)
  -- the inner call `($f $x)`, answered by `keep` on the value of `$x`
  have h := h.letStart
  have h := h.letStart
  have h := h.ret
  have h := h.letBind
  have h := h.call [] keepE [ExampleTwice.twiceE] program_eq (by other_dead)
  have h := h.ret
  -- the outer call `($f v)`, answered by `keep` on the value `(Kept Z)`
  have h := h.letBind
  have h := h.call [] keepE [ExampleTwice.twiceE] program_eq (by other_dead)
  have h := h.ret
  exact h

def solution : Assignment (fam mkeys) noNames :=
  closeNames [(([0], [3, 0], 0), csym "keep"), (([1], [3, 1], 0), csym "Z"), (([2], [241], 0), csym "keep"),
    (([2], [241], 1), csym "Z"), (([3, 2], [1, 241, 0, 0], 0), csym "Z"), (([4], [250], 0), csym "Z"),
    (([5, 2], [1, 241, 0], 0), ctuple [csym "Kept", csym "Z"]),
    (([6], [250], 0), ctuple [csym "Kept", csym "Z"])] (csym "a")

theorem live : Solvable Kf := ⟨Empty, noNames, solution, by decide⟩

/-- `(Kept (Kept Z))`. -/
def answer : MClosed := ctuple [csym "Kept", ctuple [csym "Kept", csym "Z"]]

theorem determines : Determines Kf vf answer := by
  refine ⟨live, fun target τ solved => ?_⟩
  simp only [Kf, K3, List.cons_append, List.nil_append, Models, List.forall_mem_cons] at solved
  obtain ⟨-, e2, e3, e4, e5, e6, e7, -⟩ := solved
  have h2 : instantiate τ (foD [1] [3, 1] 0) = symAt "Z" := e2
  have h3 : tupleAt [symAt "twice", instantiate τ (foD [2] [241] 0), instantiate τ (foD [2] [241] 1)] =
      tupleAt [symAt "twice", instantiate τ (foD [0] [3, 0] 0), instantiate τ (foD [1] [3, 1] 0)] := e3
  have h4 : instantiate τ (foD [3, 2] [1, 241, 0, 0] 0) = instantiate τ (foD [2] [241] 1) := e4
  have h5 : tupleAt [symAt "keep", instantiate τ (foD [4] [250] 0)] =
      tupleAt [instantiate τ (foD [2] [241] 0), instantiate τ (foD [3, 2] [1, 241, 0, 0] 0)] := e5
  have h6 : instantiate τ (foD [5, 2] [1, 241, 0] 0) =
      tupleAt [symAt "Kept", instantiate τ (foD [4] [250] 0)] := e6
  have h7 : tupleAt [symAt "keep", instantiate τ (foD [6] [250] 0)] =
      tupleAt [instantiate τ (foD [2] [241] 0), instantiate τ (foD [5, 2] [1, 241, 0] 0)] := e7
  show tupleAt [symAt "Kept", instantiate τ (foD [6] [250] 0)] = _
  rw [(tuple2_inj h7).2, h6, (tuple2_inj h5).2, h4, (tuple3_inj h3).2.2, h2]
  rfl

end ByValue

/-- **By value**: a run ends, quiescent, with the bag `{(Kept (Kept Z))}`. -/
theorem byValue_answers : ∃ C : Config mkeys [] () MTy,
    Runs D ByValue.program supply (Config.initial sp query) C ∧
      Config.Quiescent (D := D) ByValue.program supply C ∧
      Config.answers (D := D) C = {{ByValue.answer}} := by
  have finished : Branch.Finished (D := D) ByValue.finalB := ⟨rfl, _, rfl⟩
  obtain ⟨C, runs, quiescent, answers⟩ := Along.answers ByValue.along finished ByValue.live
  have same : Branch.answer (D := D) ByValue.finalB = {ByValue.answer} :=
    Branch.answer_of_determines (D := D) (b := ByValue.finalB) rfl ByValue.determines
  exact ⟨C, runs, quiescent, answers.trans (congrArg (fun s => ({s} : Multiset (Set MClosed))) same)⟩

/-! ## As it stands -/

/-- `(Kept (keep Z))`: the answer of the direct call `(keep (keep Z))`. -/
def heldAnswer : MClosed := ctuple [csym "Kept", ctuple [csym "keep", csym "Z"]]

namespace AsWritten

def program : Program mkeys [] () MTy := elaborateH .asWritten byValue surface

theorem program_eq : program.equations = [keepE, ExampleTwiceAsWritten.twiceE] := rfl

def Kf : List (Constraint mkeys [] ()) :=
  K3 ++
  [(tuple [sym "keep", foD [3] [250] 0], tuple [foD [2] [241] 0, tuple [foD [2] [241] 0, foD [2] [241] 1]])]

def vf : MData := tuple [sym "Kept", foD [3] [250] 0]

def finalB : Branch mkeys [] () MTy := ⟨Kf, .value vf, [], []⟩

theorem along : Along D program supply (Config.initial sp query) ⟨4, 0, sp⟩ finalB := by
  have h := Along.start (D := D) (P := program) (supply := supply) sp query
  have h := h.letStart
  have h := h.unmatched (by unanswered program_eq)
  have h := h.letBind
  have h := h.letStart
  have h := h.unmatched (by unanswered program_eq)
  have h := h.letBind
  have h := h.call [keepE] ExampleTwiceAsWritten.twiceE [] program_eq (by other_dead)
  -- the whole tuple is called: `keep` answers it, holding the inner call
  have h := h.call [] keepE [ExampleTwiceAsWritten.twiceE] program_eq (by other_dead)
  have h := h.ret
  exact h

def solution : Assignment (fam mkeys) noNames :=
  closeNames [(([0], [3, 0], 0), csym "keep"), (([1], [3, 1], 0), csym "Z"), (([2], [241], 0), csym "keep"),
    (([2], [241], 1), csym "Z"), (([3], [250], 0), ctuple [csym "keep", csym "Z"])] (csym "a")

theorem live : Solvable Kf := ⟨Empty, noNames, solution, by decide⟩

theorem determines : Determines Kf vf heldAnswer := by
  refine ⟨live, fun target τ solved => ?_⟩
  simp only [Kf, K3, List.cons_append, List.nil_append, Models, List.forall_mem_cons] at solved
  obtain ⟨e1, e2, e3, e4, -⟩ := solved
  have h1 : instantiate τ (foD [0] [3, 0] 0) = symAt "keep" := e1
  have h2 : instantiate τ (foD [1] [3, 1] 0) = symAt "Z" := e2
  have h3 : tupleAt [symAt "twice", instantiate τ (foD [2] [241] 0), instantiate τ (foD [2] [241] 1)] =
      tupleAt [symAt "twice", instantiate τ (foD [0] [3, 0] 0), instantiate τ (foD [1] [3, 1] 0)] := e3
  have h4 : tupleAt [symAt "keep", instantiate τ (foD [3] [250] 0)] =
      tupleAt [instantiate τ (foD [2] [241] 0),
        tupleAt [instantiate τ (foD [2] [241] 0), instantiate τ (foD [2] [241] 1)]] := e4
  obtain ⟨-, onF, onX⟩ := tuple3_inj h3
  show tupleAt [symAt "Kept", instantiate τ (foD [3] [250] 0)] = _
  rw [(tuple2_inj h4).2, onF, onX, h1, h2]
  rfl

end AsWritten

/-- **As it stands**: a run ends, quiescent, with the bag `{(Kept (keep Z))}`. -/
theorem asWritten_answers : ∃ C : Config mkeys [] () MTy,
    Runs D AsWritten.program supply (Config.initial sp query) C ∧
      Config.Quiescent (D := D) AsWritten.program supply C ∧
      Config.answers (D := D) C = {{heldAnswer}} := by
  have finished : Branch.Finished (D := D) AsWritten.finalB := ⟨rfl, _, rfl⟩
  obtain ⟨C, runs, quiescent, answers⟩ := Along.answers AsWritten.along finished AsWritten.live
  have same : Branch.answer (D := D) AsWritten.finalB = {heldAnswer} :=
    Branch.answer_of_determines (D := D) (b := AsWritten.finalB) rfl AsWritten.determines
  exact ⟨C, runs, quiescent, answers.trans (congrArg (fun s => ({s} : Multiset (Set MClosed))) same)⟩

/-! ## At run time -/

namespace AtRunTime

def program : Program mkeys [] () MTy := elaborateH .atRunTime byValue surface

/-- `(= (twice $f $x) ($f ($f $x)))`: the tuple is run as text. -/
def twiceE : Equation mkeys [] () MTy :=
  ⟨[241], tuple [sym "twice", fT, xT], .run (tuple [fT, tuple [fT, xT]])⟩

theorem program_eq : program.equations = [keepE, twiceE] := rfl

/-- What the store has bound when the tuple is run. -/
def θ : Assignment (fam mkeys) (fam mkeys) :=
  bindNames [(([0], [3, 0], 0), sym "keep"), (([1], [3, 1], 0), sym "Z"), (([2], [241], 0), sym "keep"),
    (([2], [241], 1), sym "Z")]

theorem principal : Principal K3 θ := by
  refine principal_bindNames (by decide) ?_
  intro entry member X target σ models
  simp only [K3, Models, List.forall_mem_cons] at models
  obtain ⟨e1, e2, e3, -⟩ := models
  have h1 : σ (fo [0] [3, 0] 0) = symAt "keep" := (instantiate_foD σ [0] [3, 0] 0).symm.trans e1
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

def Kf : List (Constraint mkeys [] ()) :=
  K3 ++ [(tuple [sym "keep", foD [3] [250] 0], tuple [sym "keep", tuple [sym "keep", sym "Z"]])]

def vf : MData := tuple [sym "Kept", foD [3] [250] 0]

def finalB : Branch mkeys [] () MTy := ⟨Kf, .value vf, [], []⟩

theorem along : Along D program supply (Config.initial sp query) ⟨4, 0, sp⟩ finalB := by
  have h := Along.start (D := D) (P := program) (supply := supply) sp query
  have h := h.letStart
  have h := h.unmatched (by unanswered program_eq)
  have h := h.letBind
  have h := h.letStart
  have h := h.unmatched (by unanswered program_eq)
  have h := h.letBind
  have h := h.call [keepE] twiceE [] program_eq (by other_dead)
  -- the tuple is run: dereferenced, it is `(keep (keep Z))`, read with `keep`'s declaration
  have h := h.run θ principal
  have h := h.call [] keepE [twiceE] program_eq (by other_dead)
  have h := h.ret
  exact h

def solution : Assignment (fam mkeys) noNames :=
  closeNames [(([0], [3, 0], 0), csym "keep"), (([1], [3, 1], 0), csym "Z"), (([2], [241], 0), csym "keep"),
    (([2], [241], 1), csym "Z"), (([3], [250], 0), ctuple [csym "keep", csym "Z"])] (csym "a")

theorem live : Solvable Kf := ⟨Empty, noNames, solution, by decide⟩

theorem determines : Determines Kf vf heldAnswer := by
  refine ⟨live, fun target τ solved => ?_⟩
  simp only [Kf, K3, List.cons_append, List.nil_append, Models, List.forall_mem_cons] at solved
  obtain ⟨-, -, -, e4, -⟩ := solved
  have h4 : tupleAt [symAt "keep", instantiate τ (foD [3] [250] 0)] =
      tupleAt [symAt "keep", tupleAt [symAt "keep", symAt "Z"]] := e4
  show tupleAt [symAt "Kept", instantiate τ (foD [3] [250] 0)] = _
  rw [(tuple2_inj h4).2]
  rfl

end AtRunTime

/-- **At run time**: a run ends, quiescent, with the bag `{(Kept (keep Z))}`. -/
theorem atRunTime_answers : ∃ C : Config mkeys [] () MTy,
    Runs D AtRunTime.program supply (Config.initial sp query) C ∧
      Config.Quiescent (D := D) AtRunTime.program supply C ∧
      Config.answers (D := D) C = {{heldAnswer}} := by
  have finished : Branch.Finished (D := D) AtRunTime.finalB := ⟨rfl, _, rfl⟩
  obtain ⟨C, runs, quiescent, answers⟩ := Along.answers AtRunTime.along finished AtRunTime.live
  have same : Branch.answer (D := D) AtRunTime.finalB = {heldAnswer} :=
    Branch.answer_of_determines (D := D) (b := AtRunTime.finalB) rfl AtRunTime.determines
  exact ⟨C, runs, quiescent, answers.trans (congrArg (fun s => ({s} : Multiset (Set MClosed))) same)⟩

/-! ## The clauses compared -/

/-- **By value, naming a function that holds its parameter changes its call**: `(Kept (Kept Z))` is not
`(Kept (keep Z))`. -/
theorem byValue_differs : ({{ByValue.answer}} : Multiset (Set MClosed)) ≠ {{heldAnswer}} := by
  intro same
  have inside : ByValue.answer ∈ ({heldAnswer} : Set MClosed) := by
    rw [← Multiset.singleton_inj.mp same]
    exact Set.mem_singleton _
  exact absurd (Set.mem_singleton_iff.mp inside) (by decide)

/-- **A declared type that holds nothing gives the program by value.** -/
theorem declared_none :
    elaborateH (.declared fun _ _ => false) byValue surface = ByValue.program := rfl

/-- **A declared type that holds the parameter gives the program that calls the tuple as it stands**
(for this text, whose tuples have one argument each). -/
theorem declared_holding :
    (elaborateH (.declared fun _ _ => true) byValue surface).equations = AsWritten.program.equations := rfl

/-! ## The direct call -/

namespace Direct

/-- The query `(keep (keep Z))`, elaborated: the argument is held, by `keep`'s declaration. -/
def query : Comp mkeys [] () MTy := .apply (tuple [sym "keep", tuple [sym "keep", sym "Z"]])

theorem query_eq (cl : Clause) :
    elabQueryH cl byValue surface (.text (tuple [sym "keep", tuple [sym "keep", sym "Z"]])) = query := rfl

def Kf : List (Constraint mkeys [] ()) :=
  [(tuple [sym "keep", foD [0] [250] 0], tuple [sym "keep", tuple [sym "keep", sym "Z"]])]

def vf : MData := tuple [sym "Kept", foD [0] [250] 0]

def finalB : Branch mkeys [] () MTy := ⟨Kf, .value vf, [], []⟩

theorem along : Along D ByValue.program supply (Config.initial sp query) ⟨1, 0, sp⟩ finalB := by
  have h := Along.start (D := D) (P := ByValue.program) (supply := supply) sp query
  have h := h.call [] keepE [ExampleTwice.twiceE] ByValue.program_eq (by other_dead)
  have h := h.ret
  exact h

def solution : Assignment (fam mkeys) noNames :=
  closeNames [(([0], [250], 0), ctuple [csym "keep", csym "Z"])] (csym "a")

theorem live : Solvable Kf := ⟨Empty, noNames, solution, by decide⟩

theorem determines : Determines Kf vf heldAnswer := by
  refine ⟨live, fun target τ solved => ?_⟩
  simp only [Kf, Models, List.forall_mem_cons] at solved
  obtain ⟨e1, -⟩ := solved
  have h1 : tupleAt [symAt "keep", instantiate τ (foD [0] [250] 0)] =
      tupleAt [symAt "keep", tupleAt [symAt "keep", symAt "Z"]] := e1
  show tupleAt [symAt "Kept", instantiate τ (foD [0] [250] 0)] = _
  rw [(tuple2_inj h1).2]
  rfl

end Direct

/-- **The direct call `(keep (keep Z))`**: a run ends, quiescent, with the bag `{(Kept (keep Z))}`. -/
theorem direct_answers : ∃ C : Config mkeys [] () MTy,
    Runs D ByValue.program supply (Config.initial sp Direct.query) C ∧
      Config.Quiescent (D := D) ByValue.program supply C ∧
      Config.answers (D := D) C = {{heldAnswer}} := by
  have finished : Branch.Finished (D := D) Direct.finalB := ⟨rfl, _, rfl⟩
  obtain ⟨C, runs, quiescent, answers⟩ := Along.answers Direct.along finished Direct.live
  have same : Branch.answer (D := D) Direct.finalB = {heldAnswer} :=
    Branch.answer_of_determines (D := D) (b := Direct.finalB) rfl Direct.determines
  exact ⟨C, runs, quiescent, answers.trans (congrArg (fun s => ({s} : Multiset (Set MClosed))) same)⟩

/-! ## The text decides: a `hold` mark at the call -/

/-- `(= (twice $f $x) ($f (hold ($f $x))))`: the inner call is passed as text, by a mark. -/
def twiceMarkedS : SEquation := ⟨[241], "twice", [fT, xT], .text (tuple [fT, hold (tuple [fT, xT])])⟩

def surfaceMarked : SProgram := ⟨[⟨"keep", [.atom], .atom⟩], [keepS, twiceMarkedS]⟩

/-- **By value, a `hold` mark passes text**: the marked text under the clause by value is the program
that calls the unmarked tuple as it stands. -/
theorem marked_program : elaborateH .byValue byValue surfaceMarked = AsWritten.program := rfl

/-- **By value with the mark**: a run ends, quiescent, with the bag `{(Kept (keep Z))}`, the answer of
the direct call. -/
theorem marked_answers : ∃ C : Config mkeys [] () MTy,
    Runs D (elaborateH .byValue byValue surfaceMarked) supply (Config.initial sp query) C ∧
      Config.Quiescent (D := D) (elaborateH .byValue byValue surfaceMarked) supply C ∧
      Config.answers (D := D) C = {{heldAnswer}} := by
  rw [marked_program]
  exact asWritten_answers

/-! ## Through the translation -/

open Hosting in
theorem query_scoped : query.Scoped [[3]] := by decide

open Hosting in
theorem query_distinct : ([3] :: query.sites).Nodup := by decide

open Hosting in
theorem query_arrows : ArrowComp query := ⟨trivial, trivial, trivial⟩

open Hosting in
/-- **By value, hosted**: a frontier of states that runs of the step reach from the translation's start
answers `{(Kept (Kept Z))}`. -/
theorem byValue_hosted :
    ∃ L : Multiset (Branch mkeys [] () D.Ty × HostState MSig × ℕ),
      frontierAnswers mettaNodes L = {{ByValue.answer}} ∧
      ∀ x ∈ L, Relation.ReflTransGen (Fires mettaNodes ByValue.program)
        (Hosting.start mettaNodes ByValue.program query) x.2.1 := by
  have wellFormed : WellFormed ByValue.program := by decide
  have arrows : ArrowProgram ByValue.program := by
    intro e member
    rw [ByValue.program_eq] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with same | same
    · subst same; trivial
    · subst same; exact ⟨⟨trivial, trivial⟩, trivial⟩
  obtain ⟨C, runs, -, answers⟩ := byValue_answers
  obtain ⟨L, same, reached⟩ := arrow_answers_of_scoped mettaNodes (D := D) (P := ByValue.program)
    (supply := supply) sp query (equations_of_wellFormed (D := D) wellFormed arrows) query_scoped
    query_distinct query_arrows runs
  exact ⟨L, same.symm.trans answers, reached⟩

open Hosting in
/-- **By value with the mark, hosted**: a frontier of states that runs of the step reach from the
translation's start answers `{(Kept (keep Z))}`. -/
theorem marked_hosted :
    ∃ L : Multiset (Branch mkeys [] () D.Ty × HostState MSig × ℕ),
      frontierAnswers mettaNodes L = {{heldAnswer}} ∧
      ∀ x ∈ L, Relation.ReflTransGen (Fires mettaNodes (elaborateH .byValue byValue surfaceMarked))
        (Hosting.start mettaNodes (elaborateH .byValue byValue surfaceMarked) query) x.2.1 := by
  rw [marked_program]
  have wellFormed : WellFormed AsWritten.program := by decide
  have arrows : ArrowProgram AsWritten.program := by
    intro e member
    rw [AsWritten.program_eq] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with same | same
    · subst same; trivial
    · subst same; trivial
  obtain ⟨C, runs, -, answers⟩ := asWritten_answers
  obtain ⟨L, same, reached⟩ := arrow_answers_of_scoped mettaNodes (D := D) (P := AsWritten.program)
    (supply := supply) sp query (equations_of_wellFormed (D := D) wellFormed arrows) query_scoped
    query_distinct query_arrows runs
  exact ⟨L, same.symm.trans answers, reached⟩

#print axioms query_eq
#print axioms byValue_answers
#print axioms asWritten_answers
#print axioms AtRunTime.principal
#print axioms atRunTime_answers
#print axioms byValue_differs
#print axioms declared_none
#print axioms declared_holding
#print axioms direct_answers
#print axioms marked_program
#print axioms marked_answers
#print axioms byValue_hosted
#print axioms marked_hosted

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.FunctionVariables.ExampleHolding
