import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.ExampleHeld
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.ExampleLet

/-!
# The held program without its declaration: by value, two answers

The surface program of `ExampleHeld` without the declaration of `dup`:

```
(= (two) (superpose 1 2))
(= (dup $x) (pair $x $x))
!(dup (two))
```

By value, `(two)` is computed once, before `dup` is called, and each of its values is used twice:
the run ends with the bag `{(pair 1 1), (pair 2 2)}` (`byValue_example`). With `dup` holding its
argument the bag is `{(pair (two) (two))}` when held text stays (`ExampleHeld.stays_example`) and has
four answers when held text runs (`ExampleHeldRuns.runs_example`): the three readings of the same text
give three different bags.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.ExampleByValue

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Elaboration Toolkit ExampleHeld

/-- The surface program without the declaration of `dup`. -/
def surfaceV : SProgram := ⟨[], [twoS, dupS]⟩

def coreV : Program mkeys [] () MTy := ⟨[twoE, dupE false], (elaborate (reading false) surfaceV).reflect⟩

/-- **The elaboration by value**, computed by the kernel: the body of `dup` returns its variable. -/
theorem elaborate_byValue : elaborate (reading false) surfaceV = coreV := rfl

def two : MData := tuple [sym "two"]
def Q0 : MData := foD [] [3, 0] 0

/-- **The query by value**: `(two)` is computed first, and `dup` is called on its value. -/
def queryV : Comp mkeys [] () MTy := .let_ [3, 0] Q0 (.apply two) (.apply (tuple [sym "dup", Q0]))

theorem query_byValue : elabQuery (reading false) surfaceV querySurface = queryV := rfl

abbrev sp : MClosed → Multiset (Row mkeys [] ()) := fun _ => 0

/-! ## One value of `(two)`, from scope `n` -/

def Qn (n : ℕ) : MData := foD [n] [3, 0] 0
def Xn (n : ℕ) : MData := foD [n] [101] 0
def S0n (n : ℕ) : MData := foD [n] [1, 101, 0] 0
def S1n (n : ℕ) : MData := foD [n] [1, 101, 1] 0
def Y0n (n : ℕ) : MData := foD [n + 2, n + 1] [1, 101, 0] 0
def Y1n (n : ℕ) : MData := foD [n + 3, n + 1] [1, 101, 1] 0

def frame0 : Frame mkeys [] () MTy := .bindTo [3, 0] Q0 (.apply (tuple [sym "dup", Q0]))
def K1 : List (Constraint mkeys [] ()) := [(two, two)]
def start (v : Int) : Branch mkeys [] () MTy := ⟨K1, .eval (.ret (num v)), [frame0], []⟩
def K2 (v : Int) (n : ℕ) : List (Constraint mkeys [] ()) := K1 ++ [(Qn n, num v)]
def K3 (v : Int) (n : ℕ) : List (Constraint mkeys [] ()) :=
  K2 v n ++ [(tuple [sym "dup", Xn (n + 1)], tuple [sym "dup", Qn n])]
def K4 (v : Int) (n : ℕ) : List (Constraint mkeys [] ()) := K3 v n ++ [(Y0n n, Xn (n + 1))]
def K5 (v : Int) (n : ℕ) : List (Constraint mkeys [] ()) := K4 v n ++ [(Y1n n, Xn (n + 1))]
def k1 (n : ℕ) : Comp mkeys [] () MTy := .apply (tuple [sym "pair", Y0n n, S1n (n + 1)])
def f1 (n : ℕ) : Frame mkeys [] () MTy := .bindTo [1, 101, 1] (S1n (n + 1)) (k1 n)
def k0 (n : ℕ) : Comp mkeys [] () MTy :=
  .let_ [1, 101, 1] (S1n (n + 1)) (.ret (Xn (n + 1))) (.apply (tuple [sym "pair", S0n (n + 1), S1n (n + 1)]))
def f0 (n : ℕ) : Frame mkeys [] () MTy := .bindTo [1, 101, 0] (S0n (n + 1)) (k0 n)
def fin (v : Int) (n : ℕ) : Branch mkeys [] () MTy := ⟨K5 v n, .value (tuple [sym "pair", Y0n n, Y1n n]), [], []⟩
def deadT (v : Int) (n : ℕ) : Branch mkeys [] () MTy :=
  callBranch D (n + 1) (K2 v n) (tuple [sym "dup", Qn n]) [] [] twoE

/-- Every store of the alternative is solved by sending every name to `v`. -/
theorem live5 (v : Int) (n : ℕ) : Solvable (K5 v n) :=
  ⟨Empty, noNames, ExampleLet.constant (cnum v), fun e member => by
    simp only [K5, K4, K3, K2, K1, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;> rfl⟩

theorem deadT_dead (v : Int) (n : ℕ) : ¬ Solvable (deadT v n).store :=
  dead_of_length (ts := [sym "two"]) (ts' := [sym "dup", Qn n])
    (List.mem_append_right _ (List.mem_singleton_self _)) (by simp)

theorem fin_determines (v : Int) (n : ℕ) :
    Determines (K5 v n) (tuple [sym "pair", Y0n n, Y1n n]) (ctuple [csym "pair", cnum v, cnum v]) := by
  refine ⟨live5 v n, fun target σ solved => ?_⟩
  have q := solved (Qn n, num v) (by simp [K5, K4, K3, K2])
  have dup := solved (tuple [sym "dup", Xn (n + 1)], tuple [sym "dup", Qn n]) (by simp [K5, K4, K3])
  have y0 := solved (Y0n n, Xn (n + 1)) (by simp [K5, K4])
  have y1 := solved (Y1n n, Xn (n + 1)) (by simp [K5])
  have pair : tupleAt [symAt "dup", instantiate σ (Xn (n + 1))] = tupleAt [symAt "dup", instantiate σ (Qn n)] := dup
  have xq := (tuple2_inj pair).2
  show tupleAt [symAt "pair", instantiate σ (Y0n n), instantiate σ (Y1n n)] = _
  rw [y0, y1, xq, q]
  rfl

/-- **One value `v` of `(two)`**, from scope `n`: `dup` is called on it and its body uses it twice. -/
theorem subtree (v : Int) (n : ℕ) :
    Runs D coreV supply ⟨⟨n, 0, sp⟩, {start v}⟩ ⟨⟨n + 4, 0, sp⟩, fin v n ::ₘ deadT v n ::ₘ 0⟩ := by
  have live4 : Solvable (K4 v n) := solvable_of_append (live5 v n)
  have live3 : Solvable (K3 v n) := solvable_of_append live4
  have live2 : Solvable (K2 v n) := solvable_of_append live3
  have unmatched : ∀ e ∈ coreV.equations,
      ¬ Solvable (K5 v n ++ [(instantiate (copyAt mkeys (n + 4)) e.lhs, tuple [sym "pair", Y0n n, Y1n n])]) := by
    intro e member
    simp only [coreV, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact dead_of_length (ts := [sym "two"]) (ts' := [sym "pair", Y0n n, Y1n n])
        (List.mem_append_right _ (List.mem_singleton_self _)) (by simp)
    · exact dead_of_length (ts := [sym "dup", foD [n + 4] [101] 0]) (ts' := [sym "pair", Y0n n, Y1n n])
        (List.mem_append_right _ (List.mem_singleton_self _)) (by simp)
  have matched : ∃ e ∈ coreV.equations,
      Solvable (K2 v n ++ [(instantiate (copyAt mkeys (n + 1)) e.lhs, tuple [sym "dup", Qn n])]) :=
    ⟨dupE false, List.mem_cons.mpr (Or.inr (List.mem_singleton_self _)), live3⟩
  -- the call of `pair` is unmatched: its text is the answer
  refine Relation.ReflTransGen.tail (b := ⟨⟨n + 4, 0, sp⟩,
      ⟨K5 v n, .eval (.apply (tuple [sym "pair", Y0n n, Y1n n])), [], []⟩ ::ₘ deadT v n ::ₘ 0⟩) ?_
    (Step.of_eq (D := D) (P := coreV) (supply := supply) rfl rfl (live5 v n) (.unmatched _ _ _ _ _ unmatched))
  -- the second use of the value
  refine Relation.ReflTransGen.tail (b := ⟨⟨n + 3, 0, sp⟩,
      ⟨K4 v n, .value (Xn (n + 1)), [f1 n], []⟩ ::ₘ deadT v n ::ₘ 0⟩) ?_
    (Step.of_eq (D := D) (P := coreV) (supply := supply) rfl rfl live4 (.letBind _ _ _ _ _ _ _ _))
  refine Relation.ReflTransGen.tail (b := ⟨⟨n + 3, 0, sp⟩,
      ⟨K4 v n, .eval (.ret (Xn (n + 1))), [f1 n], []⟩ ::ₘ deadT v n ::ₘ 0⟩) ?_
    (Step.of_eq (D := D) (P := coreV) (supply := supply) rfl rfl live4 (.ret _ _ _ _ _))
  refine Relation.ReflTransGen.tail (b := ⟨⟨n + 3, 0, sp⟩,
      ⟨K4 v n, .eval (.let_ [1, 101, 1] (S1n (n + 1)) (.ret (Xn (n + 1))) (k1 n)), [], []⟩ ::ₘ
        deadT v n ::ₘ 0⟩) ?_
    (Step.of_eq (D := D) (P := coreV) (supply := supply) rfl rfl live4 (.letStart _ _ _ _ _ _ _ _))
  -- the first use of the value
  refine Relation.ReflTransGen.tail (b := ⟨⟨n + 2, 0, sp⟩,
      ⟨K3 v n, .value (Xn (n + 1)), [f0 n], []⟩ ::ₘ deadT v n ::ₘ 0⟩) ?_
    (Step.of_eq (D := D) (P := coreV) (supply := supply) rfl rfl live3 (.letBind _ _ _ _ _ _ _ _))
  refine Relation.ReflTransGen.tail (b := ⟨⟨n + 2, 0, sp⟩,
      ⟨K3 v n, .eval (.ret (Xn (n + 1))), [f0 n], []⟩ ::ₘ deadT v n ::ₘ 0⟩) ?_
    (Step.of_eq (D := D) (P := coreV) (supply := supply) rfl rfl live3 (.ret _ _ _ _ _))
  refine Relation.ReflTransGen.tail (b := ⟨⟨n + 2, 0, sp⟩,
      ⟨K3 v n, .eval ((dupE false).rhs.inst (copyAt mkeys (n + 1))), [], []⟩ ::ₘ deadT v n ::ₘ 0⟩) ?_
    (Step.of_eq (D := D) (P := coreV) (supply := supply) rfl rfl live3 (.letStart _ _ _ _ _ _ _ _))
  -- the call of `dup`: one alternative per equation
  refine Relation.ReflTransGen.tail (b := ⟨⟨n + 1, 0, sp⟩,
      {⟨K2 v n, .eval (.apply (tuple [sym "dup", Qn n])), [], []⟩}⟩) ?_
    (Step.of_eq (D := D) (P := coreV) (supply := supply) (rest := 0) rfl
      (by rw [add_zero, Multiset.cons_swap]; rfl) live2 (.apply _ _ _ _ _ matched))
  -- the value of `(two)` is bound
  refine Relation.ReflTransGen.tail (b := ⟨⟨n, 0, sp⟩, {⟨K1, .value (num v), [frame0], []⟩}⟩) ?_
    (step_one (solvable_of_append live2) (.letBind _ _ _ _ _ _ _ _))
  exact Relation.ReflTransGen.single (step_one (solvable_of_append live2) (.ret _ _ _ _ _))

/-! ## The whole run -/

def bT : Branch mkeys [] () MTy := callBranch D 0 [] two [frame0] [] twoE
def bD : Branch mkeys [] () MTy := callBranch D 0 [] two [frame0] [] (dupE false)

theorem bD_dead : ¬ Solvable bD.store :=
  dead_of_length (ts := [sym "dup", foD [0] [101] 0]) (ts' := [sym "two"]) (List.mem_singleton_self _) (by decide)

def finalBag : Multiset (Branch mkeys [] () MTy) :=
  fin 2 5 ::ₘ deadT 2 5 ::ₘ fin 1 1 ::ₘ deadT 1 1 ::ₘ bD ::ₘ 0

def R1 : Multiset (Branch mkeys [] () MTy) := start 2 ::ₘ bD ::ₘ 0
def R2 : Multiset (Branch mkeys [] () MTy) := fin 1 1 ::ₘ deadT 1 1 ::ₘ bD ::ₘ 0

theorem runs_all : Runs D coreV supply (Config.initial (fun _ => 0) queryV) ⟨⟨9, 0, sp⟩, finalBag⟩ := by
  have liveK1 : Solvable K1 :=
    solvable_of_append (solvable_of_append (solvable_of_append (solvable_of_append (live5 1 0))))
  have matched : ∃ e ∈ coreV.equations, Solvable ([] ++ [(instantiate (copyAt mkeys 0) e.lhs, two)]) :=
    ⟨twoE, List.mem_cons.mpr (Or.inl rfl), liveK1⟩
  have first : Runs D coreV supply ⟨⟨1, 0, sp⟩, {start 1} + R1⟩ ⟨⟨5, 0, sp⟩, (fin 1 1 ::ₘ deadT 1 1 ::ₘ 0) + R1⟩ :=
    (subtree 1 1).frame R1
  have second : Runs D coreV supply ⟨⟨5, 0, sp⟩, {start 2} + R2⟩ ⟨⟨9, 0, sp⟩, (fin 2 5 ::ₘ deadT 2 5 ::ₘ 0) + R2⟩ :=
    (subtree 2 5).frame R2
  have bridge : (fin 1 1 ::ₘ deadT 1 1 ::ₘ 0) + R1 = {start 2} + R2 := by
    simp only [R1, R2, Multiset.cons_add, zero_add, Multiset.singleton_add]
    rw [Multiset.cons_swap (deadT 1 1) (start 2), Multiset.cons_swap (fin 1 1) (start 2)]
  have exit : (fin 2 5 ::ₘ deadT 2 5 ::ₘ 0) + R2 = finalBag := by
    simp only [R2, finalBag, Multiset.cons_add, zero_add]
  have entry : ({start 1} + R1 : Multiset (Branch mkeys [] () MTy)) = start 1 ::ₘ start 2 ::ₘ bD ::ₘ 0 := by
    simp only [R1, Multiset.singleton_add]
  rw [bridge] at first
  rw [exit] at second
  rw [entry] at first
  refine (Relation.ReflTransGen.trans ?_ first).trans second
  -- the choice of `(two)`
  refine Relation.ReflTransGen.tail (b := ⟨⟨1, 0, sp⟩, bT ::ₘ bD ::ₘ 0⟩) ?_
    (Step.of_eq (D := D) (P := coreV) (supply := supply) (b := bT) (rest := bD ::ₘ 0) rfl rfl liveK1
      (.choice _ _ _ _ _ _))
  -- the call of `(two)`: one alternative per equation
  refine Relation.ReflTransGen.tail (b := ⟨⟨0, 0, sp⟩, {⟨[], .eval (.apply two), [frame0], []⟩}⟩) ?_
    (Step.of_eq (D := D) (P := coreV) (supply := supply) (rest := 0) rfl (by rw [add_zero]; rfl) live_nil
      (.apply _ _ _ _ _ matched))
  exact Relation.ReflTransGen.single (step_one live_nil (.letStart _ _ _ _ _ _ _ _))

theorem final_quiescent : Config.Quiescent (D := D) coreV supply (⟨⟨9, 0, sp⟩, finalBag⟩ : Config mkeys [] () MTy) :=
  Config.quiescent_of_finished fun b member live => by
    simp only [finalBag, Multiset.mem_cons, Multiset.notMem_zero, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    · exact ⟨rfl, _, rfl⟩
    · exact absurd live (deadT_dead 2 5)
    · exact ⟨rfl, _, rfl⟩
    · exact absurd live (deadT_dead 1 1)
    · exact absurd live bD_dead

theorem final_answers : Config.answers (D := D) (⟨⟨9, 0, sp⟩, finalBag⟩ : Config mkeys [] () MTy) =
    {{ctuple [csym "pair", cnum 2, cnum 2]}, {ctuple [csym "pair", cnum 1, cnum 1]}} := by
  rw [finalBag, answers_cons_finished (D := D) (b := fin 2 5) ⟨rfl, _, rfl⟩ (live5 2 5),
    answers_cons_dead (D := D) (deadT_dead 2 5),
    answers_cons_finished (D := D) (b := fin 1 1) ⟨rfl, _, rfl⟩ (live5 1 1),
    answers_cons_dead (D := D) (deadT_dead 1 1), answers_cons_dead (D := D) bD_dead, answers_zero,
    answer_of_determines rfl (fin_determines 2 5), answer_of_determines rfl (fin_determines 1 1)]
  rfl

/-- **The example**: by value, the run ends with the bag `{(pair 2 2), (pair 1 1)}`. -/
theorem byValue_example :
    ∃ C, Runs D (elaborate (reading false) surfaceV) supply
        (Config.initial (fun _ => 0) (elabQuery (reading false) surfaceV querySurface)) C ∧
      Config.Quiescent (D := D) (elaborate (reading false) surfaceV) supply C ∧
      Config.answers (D := D) C =
        {{ctuple [csym "pair", cnum 2, cnum 2]}, {ctuple [csym "pair", cnum 1, cnum 1]}} := by
  rw [elaborate_byValue, query_byValue]
  exact ⟨_, runs_all, final_quiescent, final_answers⟩

#print axioms elaborate_byValue
#print axioms query_byValue
#print axioms byValue_example

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.ExampleByValue
