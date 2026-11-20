import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.ExampleHeldRuns

/-!
# Every position annotated: the same bag under every reading

The program of `ExampleHeld` with every position annotated:

```
(= (two) (superpose 1 2))
(= (dup $x) (pair (run $x) (hold $x)))
!(dup (hold (two)))
```

The marks decide every position, so no parameter of the elaboration is consulted: for **every**
reading (every strategy at every position, both bits) the elaborated program is the same core
program (`elaborate_annotated`), and its run reaches the same bag
`{(pair 1 (two)), (pair 2 (two))}` (`annotated_example`, stated for an arbitrary reading).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.ExampleAnnotated

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Elaboration Toolkit ExampleHeld ExampleHeldRuns

def dupA : SEquation := ⟨[101], "dup", [x], .text (tuple [sym "pair", run x, hold x])⟩
def surfaceA : SProgram := ⟨[], [twoS, dupA]⟩
def queryA : SComp := .text (tuple [sym "dup", hold (tuple [sym "two"])])

def dupBodyA : Comp mkeys [] () MTy :=
  .let_ [1, 101, 0] (foD [] [1, 101, 0] 0) (.run x) (.apply (tuple [sym "pair", foD [] [1, 101, 0] 0, x]))

def dupEA : Equation mkeys [] () MTy := ⟨[101], tuple [sym "dup", x], dupBodyA⟩

/-- **The elaboration does not depend on the reading.** -/
theorem elaborate_annotated (π : Params) : (elaborate π surfaceA).equations = [twoE, dupEA] := rfl

theorem query_annotated (π : Params) : elabQuery π surfaceA queryA = .apply call := rfl

theorem reflect_two_annotated (π : Params) :
    (elaborate π surfaceA).reflect (tuple [sym "two"]) = .apply (tuple [sym "two"]) := rfl

/-! ## The run, for an arbitrary reading -/

variable (π : Params)

abbrev PA := elaborate π surfaceA

def kA : Comp mkeys [] () MTy := .apply (tuple [sym "pair", S0, X0])
def fA : Frame mkeys [] () MTy := .bindTo [1, 101, 0] S0 kA

def deadTwoA : Branch mkeys [] () MTy := callBranch D 0 [] call [] [] twoE
def deadDA : Branch mkeys [] () MTy :=
  ⟨K1 ++ [(tuple [sym "dup", foD [1] [101] 0], two)], .eval (dupEA.rhs.inst (copyAt mkeys 1)), [fA], []⟩

def KA (v : Int) (n : ℕ) : List (Constraint mkeys [] ()) := K2 ++ [(Y0 n, num v)]
def finA (v : Int) (n : ℕ) : Branch mkeys [] () MTy := ⟨KA v n, .value (tuple [sym "pair", Y0 n, X0]), [], []⟩

def closeA (v : Int) (n : ℕ) : Assignment (fam mkeys) noNames :=
  closeNames [(([0], [101], 0), ctuple [csym "two"]), (([n, 0], [1, 101, 0], 0), cnum v)] (csym "a")

theorem liveA1 : Solvable (KA 1 2) := ⟨Empty, noNames, closeA 1 2, by decide⟩
theorem liveA2 : Solvable (KA 2 3) := ⟨Empty, noNames, closeA 2 3, by decide⟩

theorem unmatchedA (v : Int) (n m : ℕ) :
    ∀ e ∈ (PA π).equations,
      ¬ Solvable (KA v n ++ [(instantiate (copyAt mkeys m) e.lhs, tuple [sym "pair", Y0 n, X0])]) := by
  intro e member
  rw [elaborate_annotated] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact dead_of_length (ts := [sym "two"]) (ts' := [sym "pair", Y0 n, X0])
      (List.mem_append_right _ (List.mem_singleton_self _)) (by simp)
  · exact dead_of_length (ts := [sym "dup", foD [m] [101] 0]) (ts' := [sym "pair", Y0 n, X0])
      (List.mem_append_right _ (List.mem_singleton_self _)) (by simp)

theorem annotated_runs :
    Runs D (PA π) supply (Config.initial (fun _ => 0) (.apply call))
      ⟨⟨4, 0, sp⟩, finA 2 3 ::ₘ finA 1 2 ::ₘ deadDA ::ₘ deadTwoA ::ₘ 0⟩ := by
  have liveK2 : Solvable K2 := solvable_of_append liveA1
  have liveK1 : Solvable K1 := solvable_of_append liveK2
  have principal1 : Principal K1 (bindNames [(([0], [101], 0), two)]) := by
    refine principal_bindNames (by decide) ?_
    intro entry member X target σ models
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    subst member
    exact K1_entails σ models
  have matched1 : ∃ e ∈ (PA π).equations, Solvable ([] ++ [(instantiate (copyAt mkeys 0) e.lhs, call)]) :=
    ⟨dupEA, by rw [elaborate_annotated]; exact List.mem_cons.mpr (Or.inr (List.mem_singleton_self _)), liveK1⟩
  have matched2 : ∃ e ∈ (PA π).equations, Solvable (K1 ++ [(instantiate (copyAt mkeys 1) e.lhs, two)]) :=
    ⟨twoE, by rw [elaborate_annotated]; exact List.mem_cons.mpr (Or.inl rfl), liveK2⟩
  -- the second alternative of the choice
  refine Relation.ReflTransGen.tail (b := ⟨⟨4, 0, sp⟩,
      ⟨KA 2 3, .eval (.apply (tuple [sym "pair", Y0 3, X0])), [], []⟩ ::ₘ finA 1 2 ::ₘ deadDA ::ₘ deadTwoA ::ₘ 0⟩) ?_
    (Step.of_eq (D := D) (P := PA π) (supply := supply) rfl rfl liveA2
      (.unmatched ⟨4, 0, sp⟩ (KA 2 3) (tuple [sym "pair", Y0 3, X0]) [] [] (unmatchedA π 2 3 4)))
  refine Relation.ReflTransGen.tail (b := ⟨⟨3, 0, sp⟩,
      ⟨K2, .value (num 2), [fA], []⟩ ::ₘ finA 1 2 ::ₘ deadDA ::ₘ deadTwoA ::ₘ 0⟩) ?_
    (Step.of_eq (D := D) (P := PA π) (supply := supply) rfl rfl liveK2 (.letBind _ _ _ _ _ _ _ _))
  refine Relation.ReflTransGen.tail (b := ⟨⟨3, 0, sp⟩,
      ⟨K2, .eval (.ret (num 2)), [fA], []⟩ ::ₘ finA 1 2 ::ₘ deadDA ::ₘ deadTwoA ::ₘ 0⟩) ?_
    (Step.of_eq (D := D) (P := PA π) (supply := supply) rfl rfl liveK2 (.ret _ _ _ _ _))
  -- the first alternative of the choice
  refine Relation.ReflTransGen.tail (b := ⟨⟨3, 0, sp⟩,
      ⟨K2, .eval (.ret (num 2)), [fA], []⟩ ::ₘ
      ⟨KA 1 2, .eval (.apply (tuple [sym "pair", Y0 2, X0])), [], []⟩ ::ₘ deadDA ::ₘ deadTwoA ::ₘ 0⟩) ?_
    (Step.of_eq (D := D) (P := PA π) (supply := supply) (Multiset.cons_swap _ _ _)
      (by rw [Multiset.singleton_add, Multiset.cons_swap]; rfl) liveA1
      (.unmatched ⟨3, 0, sp⟩ (KA 1 2) (tuple [sym "pair", Y0 2, X0]) [] [] (unmatchedA π 1 2 3)))
  refine Relation.ReflTransGen.tail (b := ⟨⟨2, 0, sp⟩,
      ⟨K2, .eval (.ret (num 2)), [fA], []⟩ ::ₘ
      ⟨K2, .value (num 1), [fA], []⟩ ::ₘ deadDA ::ₘ deadTwoA ::ₘ 0⟩) ?_
    (Step.of_eq (D := D) (P := PA π) (supply := supply) (Multiset.cons_swap _ _ _)
      (by rw [Multiset.singleton_add, Multiset.cons_swap]; rfl) liveK2 (.letBind _ _ _ _ _ _ _ _))
  refine Relation.ReflTransGen.tail (b := ⟨⟨2, 0, sp⟩,
      ⟨K2, .eval (.ret (num 1)), [fA], []⟩ ::ₘ
      ⟨K2, .eval (.ret (num 2)), [fA], []⟩ ::ₘ deadDA ::ₘ deadTwoA ::ₘ 0⟩) ?_
    (Step.of_eq (D := D) (P := PA π) (supply := supply) rfl
      (by rw [Multiset.singleton_add, Multiset.cons_swap]; rfl) liveK2 (.ret _ _ _ _ _))
  -- the choice of `two`
  refine Relation.ReflTransGen.tail (b := ⟨⟨2, 0, sp⟩,
      ⟨K2, .eval (.choice (.ret (num 1)) (.ret (num 2))), [fA], []⟩ ::ₘ deadDA ::ₘ deadTwoA ::ₘ 0⟩) ?_
    (Step.of_eq (D := D) (P := PA π) (supply := supply) rfl rfl liveK2 (.choice _ _ _ _ _ _))
  -- the explicit run of the held text `(two)`
  refine Relation.ReflTransGen.tail (b := ⟨⟨1, 0, sp⟩, ⟨K1, .eval (.apply two), [fA], []⟩ ::ₘ deadTwoA ::ₘ 0⟩) ?_
    (Step.of_eq (D := D) (P := PA π) (supply := supply) rfl
      (by rw [elaborate_annotated]; rfl) liveK1 (.apply _ _ _ _ _ matched2))
  refine Relation.ReflTransGen.tail (b := ⟨⟨1, 0, sp⟩, ⟨K1, .eval (.run X0), [fA], []⟩ ::ₘ deadTwoA ::ₘ 0⟩) ?_
    (Step.of_eq (D := D) (P := PA π) (supply := supply) rfl rfl liveK1
      (.run _ _ _ _ _ (bindNames [(([0], [101], 0), two)]) principal1))
  refine Relation.ReflTransGen.tail (b := ⟨⟨1, 0, sp⟩,
      ⟨K1, .eval (dupEA.rhs.inst (copyAt mkeys 0)), [], []⟩ ::ₘ deadTwoA ::ₘ 0⟩) ?_
    (Step.of_eq (D := D) (P := PA π) (supply := supply) rfl rfl liveK1 (.letStart _ _ _ _ _ _ _ _))
  -- the call of `dup`
  exact Relation.ReflTransGen.single
    (Step.of_eq (D := D) (P := PA π) (supply := supply) (rest := 0) rfl
      (by rw [elaborate_annotated, add_zero, Multiset.cons_swap]; rfl) live_nil (.apply _ _ _ _ _ matched1))

theorem finA_determines (v : Int) (n : ℕ) (live : Solvable (KA v n)) :
    Determines (KA v n) (tuple [sym "pair", Y0 n, X0]) (ctuple [csym "pair", cnum v, ctuple [csym "two"]]) := by
  refine ⟨live, fun target σ solved => ?_⟩
  have xTwo := K1_entails σ (fun e member => solved e (by simp [KA, K2, List.mem_append, member]))
  have y0 := solved (Y0 n, num v) (by simp [KA])
  show tupleAt [symAt "pair", instantiate σ (Y0 n), instantiate σ (foD [0] [101] 0)] = _
  rw [y0, instantiate_foD, xTwo]
  rfl

theorem deadDA_dead : ¬ Solvable deadDA.store :=
  dead_of_length (ts := [sym "dup", foD [1] [101] 0]) (ts' := [sym "two"])
    (List.mem_append_right _ (List.mem_singleton_self _)) (by simp)

theorem deadTwoA_dead : ¬ Solvable deadTwoA.store :=
  dead_of_length (ts := [sym "two"]) (ts' := [sym "dup", tuple [sym "two"]]) (List.mem_singleton_self _)
    (by simp)

/-- The run has ended: every live alternative is finished. -/
theorem annotated_quiescent : Config.Quiescent (D := D) (PA π) supply
    (⟨⟨4, 0, sp⟩, finA 2 3 ::ₘ finA 1 2 ::ₘ deadDA ::ₘ deadTwoA ::ₘ 0⟩ : Config mkeys [] () MTy) :=
  Config.quiescent_of_finished fun b member live => by
    simp only [Multiset.mem_cons, Multiset.notMem_zero, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact ⟨rfl, _, rfl⟩
    · exact ⟨rfl, _, rfl⟩
    · exact absurd live deadDA_dead
    · exact absurd live deadTwoA_dead

/-- **The example**: for every reading, a run of the annotated program ends with the bag
`{(pair 2 (two)), (pair 1 (two))}`. -/
theorem annotated_example (π : Params) :
    ∃ C, Runs D (elaborate π surfaceA) supply (Config.initial (fun _ => 0) (elabQuery π surfaceA queryA)) C ∧
      Config.Quiescent (D := D) (elaborate π surfaceA) supply C ∧
      Config.answers (D := D) C =
        {{ctuple [csym "pair", cnum 2, ctuple [csym "two"]]}, {ctuple [csym "pair", cnum 1, ctuple [csym "two"]]}} := by
  rw [query_annotated]
  refine ⟨_, annotated_runs π, annotated_quiescent π, ?_⟩
  rw [answers_cons_finished (D := D) (b := finA 2 3) ⟨rfl, _, rfl⟩ liveA2,
    answers_cons_finished (D := D) (b := finA 1 2) ⟨rfl, _, rfl⟩ liveA1,
    answers_cons_dead (D := D) deadDA_dead, answers_cons_dead (D := D) deadTwoA_dead, answers_zero,
    answer_of_determines rfl (finA_determines 2 3 liveA2), answer_of_determines rfl (finA_determines 1 2 liveA1)]
  rfl

#print axioms elaborate_annotated
#print axioms annotated_example

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.ExampleAnnotated
