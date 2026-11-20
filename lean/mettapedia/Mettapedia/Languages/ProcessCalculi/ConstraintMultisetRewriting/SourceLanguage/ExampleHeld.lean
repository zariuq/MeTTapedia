import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Toolkit

/-!
# A held argument used twice, with a choice inside, under two readings

The surface program:

```
(: dup (-> Atom %Undefined%))
(= (two) (superpose 1 2))
(= (dup $x) (pair $x $x))
!(dup (two))
```

`dup` holds its argument, so `(two)` reaches the body as text, and the body uses it twice at positions
that want a value. What happens is exactly the open bit of the evaluation question.

* `heldRuns = false` (held text stays data): one answer, `(pair (two) (two))` (`stays_example`).
* `heldRuns = true` (held text runs where a value is wanted): each use runs `(two)` on its own, with
  its own choice, so four answers: `(pair 1 1)`, `(pair 1 2)`, `(pair 2 1)`, `(pair 2 2)`
  (`runs_example`).

The elaborations are the two readings of one surface program (`elaborate_stays`, `elaborate_runs`):
they differ only in the explicit forms the elaboration inserts at the two uses (`ret $x` against
`run $x`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.ExampleHeld

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Elaboration Toolkit

/-- The trivial discipline with its type language on the nose. -/
abbrev D : Discipline MSig [] () := ⟨MTy, fun _ _ => True⟩

/-! ## The surface program and its two elaborations -/

def decls : List Decl := [⟨"dup", [.atom], .undefined⟩]

def x : MData := foD [] [101] 0

def twoS : SEquation := ⟨[100], "two", [], .choice (.text (num 1)) (.text (num 2))⟩
def dupS : SEquation := ⟨[101], "dup", [x], .text (tuple [sym "pair", x, x])⟩
def surface : SProgram := ⟨decls, [twoS, dupS]⟩

def call : MData := tuple [sym "dup", tuple [sym "two"]]
def querySurface : SComp := .text call

/-- The two readings (by value at undeclared positions, results of held type returned as written). -/
def reading (heldRuns : Bool) : Params := ⟨fun _ _ => .value, heldRuns, false⟩

/-- The explicit form each reading puts at a use of the held parameter. -/
def use (heldRuns : Bool) (d : MData) : Comp mkeys [] () MTy := if heldRuns then .run d else .ret d

def twoE : Equation mkeys [] () MTy := ⟨[100], tuple [sym "two"], .choice (.ret (num 1)) (.ret (num 2))⟩

def dupBody (heldRuns : Bool) : Comp mkeys [] () MTy :=
  .let_ [1, 101, 0] (foD [] [1, 101, 0] 0) (use heldRuns x)
    (.let_ [1, 101, 1] (foD [] [1, 101, 1] 0) (use heldRuns x)
      (.apply (tuple [sym "pair", foD [] [1, 101, 0] 0, foD [] [1, 101, 1] 0])))

def dupE (heldRuns : Bool) : Equation mkeys [] () MTy := ⟨[101], tuple [sym "dup", x], dupBody heldRuns⟩

def core (heldRuns : Bool) : Program mkeys [] () MTy :=
  ⟨[twoE, dupE heldRuns], (elaborate (reading heldRuns) surface).reflect⟩

/-- **The elaboration under "held text stays data"**, computed by the kernel. -/
theorem elaborate_stays : elaborate (reading false) surface = core false := rfl

/-- **The elaboration under "held text runs"**, computed by the kernel. -/
theorem elaborate_runs : elaborate (reading true) surface = core true := rfl

/-- The query holds its argument under both readings. -/
theorem query_elaborated (heldRuns : Bool) :
    elabQuery (reading heldRuns) surface querySurface = .apply call := rfl

/-- Text read at run time: `(two)` is a call. -/
theorem reflect_two (heldRuns : Bool) :
    (core heldRuns).reflect (tuple [sym "two"]) = .apply (tuple [sym "two"]) := rfl

def supply : ℕ → MClosed := fun _ => csym "space"

def start : Config mkeys [] () MTy := Config.initial (fun _ => 0) (.apply call)

/-! ## Names of the run -/

def X0 : MData := foD [0] [101] 0
def S0 : MData := foD [0] [1, 101, 0] 0
def S1 : MData := foD [0] [1, 101, 1] 0
def K1 : List (Constraint mkeys [] ()) := [(tuple [sym "dup", X0], call)]

/-- The alternative of the first call that the equation of `two` makes: dead. -/
def deadTwo (heldRuns : Bool) : Branch mkeys [] () MTy :=
  callBranch D 0 [] call [] [] twoE |> fun b => (b : Branch mkeys [] () MTy) |> fun b =>
    if heldRuns then b else b

theorem deadTwo_dead (heldRuns : Bool) : ¬ Solvable (deadTwo heldRuns).store := by
  cases heldRuns <;>
  exact dead_of_length (ts := [sym "two"]) (ts' := [sym "dup", tuple [sym "two"]]) (List.mem_singleton_self _)
    (by decide)

theorem K1_entails {X : Type} {target : X → MetaArity MSig} (σ : Assignment (fam mkeys) target)
    (solved : Models σ K1) : σ (fo [0] [101] 0) = instantiate σ (tuple [sym "two"]) := by
  have first := solved _ (List.mem_singleton_self _)
  have pair : tupleAt [symAt "dup", σ (fo [0] [101] 0)] = tupleAt [symAt "dup", instantiate σ (tuple [sym "two"])] := by
    rw [← instantiate_foD σ [0] [101] 0]
    exact first
  exact (tuple2_inj pair).2

/-! ## Held text stays data: one answer -/

def Y0 : MData := foD [1, 0] [1, 101, 0] 0
def Y1 : MData := foD [2, 0] [1, 101, 1] 0
def stayStore : List (Constraint mkeys [] ()) := K1 ++ [(Y0, X0)] ++ [(Y1, X0)]

def stayClose : Assignment (fam mkeys) noNames :=
  closeNames [(([0], [101], 0), ctuple [csym "two"]), (([1, 0], [1, 101, 0], 0), ctuple [csym "two"]),
    (([2, 0], [1, 101, 1], 0), ctuple [csym "two"])] (csym "a")

theorem stayStore_live : Solvable stayStore :=
  ⟨Empty, noNames, stayClose, fun e member => by
    simp only [stayStore, K1, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at member
    rcases member with rfl | rfl | rfl <;> rfl⟩

def stayFinal : Branch mkeys [] () MTy := ⟨stayStore, .value (tuple [sym "pair", Y0, Y1]), [], []⟩

theorem stays_runs :
    Runs D (core false) supply start ⟨⟨3, 0, fun _ => 0⟩, stayFinal ::ₘ deadTwo false ::ₘ 0⟩ := by
  have live1 : Solvable K1 := solvable_of_append (two := [(Y0, X0)]) (solvable_of_append stayStore_live)
  have live2 : Solvable (K1 ++ [(Y0, X0)]) := solvable_of_append stayStore_live
  have unmatched : ∀ e ∈ (core false).equations,
      ¬ Solvable (stayStore ++ [(instantiate (copyAt mkeys 3) e.lhs, tuple [sym "pair", Y0, Y1])]) := by
    intro e member
    simp only [core, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact dead_of_length (ts := [sym "two"]) (ts' := [sym "pair", Y0, Y1])
        (List.mem_append_right _ (List.mem_singleton_self _)) (by decide)
    · exact dead_of_length (ts := [sym "dup", foD [3] [101] 0]) (ts' := [sym "pair", Y0, Y1])
        (List.mem_append_right _ (List.mem_singleton_self _)) (by decide)
  have matched : ∃ e ∈ (core false).equations,
      Solvable ([] ++ [(instantiate (copyAt mkeys 0) e.lhs, call)]) :=
    ⟨dupE false, List.mem_cons.mpr (Or.inr (List.mem_singleton_self _)), live1⟩
  -- the call of `pair` is unmatched: its text is the answer
  refine Relation.ReflTransGen.tail (b := ⟨⟨3, 0, fun _ => 0⟩,
    ⟨stayStore, .eval (.apply (tuple [sym "pair", Y0, Y1])), [], []⟩ ::ₘ deadTwo false ::ₘ 0⟩) ?_
    (Step.of_eq (D := D) (P := core false) (supply := supply) rfl rfl stayStore_live
      (.unmatched _ _ _ _ _ unmatched))
  -- the second use
  refine Relation.ReflTransGen.tail (b := ⟨⟨2, 0, fun _ => 0⟩,
    ⟨K1 ++ [(Y0, X0)], .value X0, [.bindTo [1, 101, 1] S1 (.apply (tuple [sym "pair", Y0, S1]))], []⟩ ::ₘ
      deadTwo false ::ₘ 0⟩) ?_
    (Step.of_eq (D := D) (P := core false) (supply := supply) rfl rfl live2 (.letBind _ _ _ _ _ _ _ _))
  refine Relation.ReflTransGen.tail (b := ⟨⟨2, 0, fun _ => 0⟩,
    ⟨K1 ++ [(Y0, X0)], .eval (.ret X0), [.bindTo [1, 101, 1] S1 (.apply (tuple [sym "pair", Y0, S1]))], []⟩ ::ₘ
      deadTwo false ::ₘ 0⟩) ?_
    (Step.of_eq (D := D) (P := core false) (supply := supply) rfl rfl live2 (.ret _ _ _ _ _))
  refine Relation.ReflTransGen.tail (b := ⟨⟨2, 0, fun _ => 0⟩,
    ⟨K1 ++ [(Y0, X0)], .eval (.let_ [1, 101, 1] S1 (.ret X0) (.apply (tuple [sym "pair", Y0, S1]))), [], []⟩ ::ₘ
      deadTwo false ::ₘ 0⟩) ?_
    (Step.of_eq (D := D) (P := core false) (supply := supply) rfl rfl live2 (.letStart _ _ _ _ _ _ _ _))
  -- the first use
  refine Relation.ReflTransGen.tail (b := ⟨⟨1, 0, fun _ => 0⟩,
    ⟨K1, .value X0, [.bindTo [1, 101, 0] S0 (.let_ [1, 101, 1] S1 (.ret X0)
      (.apply (tuple [sym "pair", S0, S1])))], []⟩ ::ₘ deadTwo false ::ₘ 0⟩) ?_
    (Step.of_eq (D := D) (P := core false) (supply := supply) rfl rfl live1 (.letBind _ _ _ _ _ _ _ _))
  refine Relation.ReflTransGen.tail (b := ⟨⟨1, 0, fun _ => 0⟩,
    ⟨K1, .eval (.ret X0), [.bindTo [1, 101, 0] S0 (.let_ [1, 101, 1] S1 (.ret X0)
      (.apply (tuple [sym "pair", S0, S1])))], []⟩ ::ₘ deadTwo false ::ₘ 0⟩) ?_
    (Step.of_eq (D := D) (P := core false) (supply := supply) rfl rfl live1 (.ret _ _ _ _ _))
  refine Relation.ReflTransGen.tail (b := ⟨⟨1, 0, fun _ => 0⟩,
    ⟨K1, .eval ((dupE false).rhs.inst (copyAt mkeys 0)), [], []⟩ ::ₘ deadTwo false ::ₘ 0⟩) ?_
    (Step.of_eq (D := D) (P := core false) (supply := supply) rfl rfl live1 (.letStart _ _ _ _ _ _ _ _))
  -- the call of `dup`: one alternative per equation
  exact Relation.ReflTransGen.single
    (Step.of_eq (D := D) (P := core false) (supply := supply) (rest := 0) rfl
      (by rw [add_zero, Multiset.cons_swap]; rfl) live_nil (.apply _ _ _ _ _ matched))

theorem stay_determines :
    Determines stayStore (tuple [sym "pair", Y0, Y1]) (ctuple [csym "pair", ctuple [csym "two"], ctuple [csym "two"]]) := by
  refine ⟨stayStore_live, fun target σ solved => ?_⟩
  have xTwo := K1_entails σ (fun e member => solved e (List.mem_append_left _ (List.mem_append_left _ member)))
  have y0 := solved (Y0, X0) (by simp [stayStore])
  have y1 := solved (Y1, X0) (by simp [stayStore])
  show tupleAt [symAt "pair", instantiate σ Y0, instantiate σ Y1] = _
  rw [y0, y1]
  show tupleAt [symAt "pair", instantiate σ (foD [0] [101] 0), instantiate σ (foD [0] [101] 0)] = _
  rw [instantiate_foD, xTwo]
  rfl

theorem stays_example :
    ∃ C, Runs D (elaborate (reading false) surface) supply
        (Config.initial (fun _ => 0) (elabQuery (reading false) surface querySurface)) C ∧
      Config.Quiescent (D := D) (elaborate (reading false) surface) supply C ∧
      Config.answers (D := D) C = {{ctuple [csym "pair", ctuple [csym "two"], ctuple [csym "two"]]}} := by
  rw [elaborate_stays, query_elaborated]
  refine ⟨_, stays_runs, ?_, ?_⟩
  · intro b member live w' bs moved
    have member' : b ∈ stayFinal ::ₘ deadTwo false ::ₘ 0 := member
    rcases Multiset.mem_cons.mp member' with same | rest
    · have shape : b = ⟨stayStore, .value (tuple [sym "pair", Y0, Y1]), [], []⟩ := same
      subst shape
      cases moved
    · rcases Multiset.mem_cons.mp rest with same | none
      · subst same
        exact absurd live (deadTwo_dead false)
      · cases none
  · rw [answers_cons_finished (D := D) (b := stayFinal) ⟨rfl, _, rfl⟩ stayStore_live,
      answers_cons_dead (D := D) (deadTwo_dead false), answers_zero,
      answer_of_determines rfl stay_determines]
    rfl

#print axioms elaborate_stays
#print axioms elaborate_runs
#print axioms stays_example

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.ExampleHeld
