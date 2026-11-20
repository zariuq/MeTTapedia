import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.ExampleHeldRuns
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.ExampleByValue

/-!
# The strategy alone changes the bag: the undeclared `dup` passed by name has four answers

The surface program of `ExampleByValue` declares nothing:

```
(= (two) (superpose 1 2))
(= (dup $x) (pair $x $x))
!(dup (two))
```

Passed by value at every position it has two answers (`ExampleByValue.byValue_example`). Passed by
name at `dup` (by value elsewhere, `dupByName`), it elaborates to the same equations and query as the
declared program of `ExampleHeld` under "held text runs" (`byName_equations`, `byName_query`): each
use of `$x` runs `(two)` on its own. The by-name program reads `(two)`, the one text the run reflects,
as the same call (`byName_reads_two`), so the four-answer run carries over (`byName_example`). The
strategy is thus a parameter that changes the bag by itself, and by name at a position and "held text
runs" at a held position insert the same explicit form.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.ExampleByName

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Elaboration Toolkit ExampleHeld ExampleHeldRuns
open ExampleByValue (surfaceV)

/-- Pass the argument of `dup` by name, every other undeclared position by value. -/
def dupByName : Params := ⟨fun f _ => if f = "dup" then .name else .value, false, false⟩

/-- The by-name program. -/
abbrev PN : Program mkeys [] () MTy := elaborate dupByName surfaceV

theorem byName_equations : PN.equations = (core true).equations := rfl

theorem byName_query : elabQuery dupByName surfaceV querySurface = .apply call := rfl

theorem byName_reads_two : PN.reflect two = .apply two := rfl

theorem unmatchedN (v : Int) (n : ℕ) (w : Int) (s : ℕ) (m : ℕ) :
    ∀ e ∈ PN.equations,
      ¬ Solvable (K5 v n w s ++ [(instantiate (copyAt mkeys m) e.lhs, tuple [sym "pair", Y0 n, Y1 s])]) :=
  unmatched_at v n w s m

/-- **The subtree of one answer of the first use**, under the by-name program. -/
theorem subtreeN (v : Int) (n : ℕ) (live1 : Solvable (K5 v n 1 (n + 2))) (live2 : Solvable (K5 v n 2 (n + 3)))
    (principal : Principal (K3 v n) (θ v n)) :
    Runs D PN supply ⟨⟨n, 0, sp⟩, {b2 v}⟩
      ⟨⟨n + 4, 0, sp⟩, fin v n 1 (n + 2) ::ₘ fin v n 2 (n + 3) ::ₘ deadE v n ::ₘ 0⟩ := by
  have live4 : Solvable (K4 v n) := solvable_of_append live1
  have live3 : Solvable (K3 v n) := solvable_of_append live4
  have live2' : Solvable K2 := solvable_of_append live3
  have matched : ∃ e ∈ PN.equations, Solvable (K3 v n ++ [(instantiate (copyAt mkeys (n + 1)) e.lhs, two)]) :=
    ⟨twoE, List.mem_cons.mpr (Or.inl rfl), live4⟩
  refine Relation.ReflTransGen.tail (b := ⟨⟨n + 4, 0, sp⟩, fin v n 1 (n + 2) ::ₘ
      ⟨K5 v n 2 (n + 3), .eval (.apply (tuple [sym "pair", Y0 n, Y1 (n + 3)])), [], []⟩ ::ₘ deadE v n ::ₘ 0⟩) ?_
    (Step.of_eq (D := D) (P := PN) (supply := supply) (Multiset.cons_swap _ _ _)
      (by rw [Multiset.singleton_add, Multiset.cons_swap]; rfl) live2
      (.unmatched ⟨n + 4, 0, sp⟩ (K5 v n 2 (n + 3)) (tuple [sym "pair", Y0 n, Y1 (n + 3)]) [] []
        (unmatchedN v n 2 (n + 3) (n + 4))))
  refine Relation.ReflTransGen.tail (b := ⟨⟨n + 3, 0, sp⟩, fin v n 1 (n + 2) ::ₘ
      ⟨K4 v n, .value (num 2), [f1 n], []⟩ ::ₘ deadE v n ::ₘ 0⟩) ?_
    (Step.of_eq (D := D) (P := PN) (supply := supply) (Multiset.cons_swap _ _ _)
      (by rw [Multiset.singleton_add, Multiset.cons_swap]; rfl) live4 (.letBind _ _ _ _ _ _ _ _))
  refine Relation.ReflTransGen.tail (b := ⟨⟨n + 3, 0, sp⟩, fin v n 1 (n + 2) ::ₘ
      ⟨K4 v n, .eval (.ret (num 2)), [f1 n], []⟩ ::ₘ deadE v n ::ₘ 0⟩) ?_
    (Step.of_eq (D := D) (P := PN) (supply := supply) (Multiset.cons_swap _ _ _)
      (by rw [Multiset.singleton_add, Multiset.cons_swap]; rfl) live4 (.ret _ _ _ _ _))
  refine Relation.ReflTransGen.tail (b := ⟨⟨n + 3, 0, sp⟩,
      ⟨K5 v n 1 (n + 2), .eval (.apply (tuple [sym "pair", Y0 n, Y1 (n + 2)])), [], []⟩ ::ₘ
      ⟨K4 v n, .eval (.ret (num 2)), [f1 n], []⟩ ::ₘ deadE v n ::ₘ 0⟩) ?_
    (Step.of_eq (D := D) (P := PN) (supply := supply) rfl rfl live1
      (.unmatched ⟨n + 3, 0, sp⟩ (K5 v n 1 (n + 2)) (tuple [sym "pair", Y0 n, Y1 (n + 2)]) [] []
        (unmatchedN v n 1 (n + 2) (n + 3))))
  refine Relation.ReflTransGen.tail (b := ⟨⟨n + 2, 0, sp⟩,
      ⟨K4 v n, .value (num 1), [f1 n], []⟩ ::ₘ
      ⟨K4 v n, .eval (.ret (num 2)), [f1 n], []⟩ ::ₘ deadE v n ::ₘ 0⟩) ?_
    (Step.of_eq (D := D) (P := PN) (supply := supply) rfl rfl live4 (.letBind _ _ _ _ _ _ _ _))
  refine Relation.ReflTransGen.tail (b := ⟨⟨n + 2, 0, sp⟩,
      ⟨K4 v n, .eval (.ret (num 1)), [f1 n], []⟩ ::ₘ
      ⟨K4 v n, .eval (.ret (num 2)), [f1 n], []⟩ ::ₘ deadE v n ::ₘ 0⟩) ?_
    (Step.of_eq (D := D) (P := PN) (supply := supply) rfl rfl live4 (.ret _ _ _ _ _))
  refine Relation.ReflTransGen.tail (b := ⟨⟨n + 2, 0, sp⟩,
      ⟨K4 v n, .eval (.choice (.ret (num 1)) (.ret (num 2))), [f1 n], []⟩ ::ₘ deadE v n ::ₘ 0⟩) ?_
    (Step.of_eq (D := D) (P := PN) (supply := supply) rfl rfl live4 (.choice _ _ _ _ _ _))
  refine Relation.ReflTransGen.tail (b := ⟨⟨n + 1, 0, sp⟩, {⟨K3 v n, .eval (.apply two), [f1 n], []⟩}⟩) ?_
    (Step.of_eq (D := D) (P := PN) (supply := supply) (rest := 0) rfl rfl live3 (.apply _ _ _ _ _ matched))
  -- the second use runs `(two)`, which the by-name program reads as the same call
  refine Relation.ReflTransGen.tail (b := ⟨⟨n + 1, 0, sp⟩, {⟨K3 v n, .eval (.run X0), [f1 n], []⟩}⟩) ?_
    (step_one live3 (.run _ _ _ _ _ (θ v n) principal))
  refine Relation.ReflTransGen.tail (b := ⟨⟨n + 1, 0, sp⟩,
      {⟨K3 v n, .eval (.let_ [1, 101, 1] S1 (.run X0) (.apply (tuple [sym "pair", Y0 n, S1]))), [], []⟩}⟩) ?_
    (step_one live3 (.letStart _ _ _ _ _ _ _ _))
  refine Relation.ReflTransGen.tail (b := ⟨⟨n, 0, sp⟩, {⟨K2, .value (num v), [f0], []⟩}⟩) ?_
    (step_one live2' (.letBind _ _ _ _ _ _ _ _))
  exact Relation.ReflTransGen.single (step_one live2' (.ret _ _ _ _ _))

/-- The first call and the first use, up to the first choice. -/
theorem prefixN :
    Runs D PN supply start ⟨⟨2, 0, sp⟩, b2 1 ::ₘ b2 2 ::ₘ
      ⟨K1 ++ [(tuple [sym "dup", foD [1] [101] 0], two)], .eval ((dupE true).rhs.inst (copyAt mkeys 1)), [f0], []⟩ ::ₘ
      deadTwo true ::ₘ 0⟩ := by
  have liveK2 : Solvable K2 := solvable_of_append (solvable_of_append (solvable_of_append live_1_2_1))
  have liveK1 : Solvable K1 := solvable_of_append liveK2
  have principal1 : Principal K1 (bindNames [(([0], [101], 0), two)]) := by
    refine principal_bindNames (by decide) ?_
    intro entry member X target σ models
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    subst member
    exact K1_entails σ models
  have matched1 : ∃ e ∈ PN.equations, Solvable ([] ++ [(instantiate (copyAt mkeys 0) e.lhs, call)]) :=
    ⟨dupE true, List.mem_cons.mpr (Or.inr (List.mem_singleton_self _)), liveK1⟩
  have matched2 : ∃ e ∈ PN.equations, Solvable (K1 ++ [(instantiate (copyAt mkeys 1) e.lhs, two)]) :=
    ⟨twoE, List.mem_cons.mpr (Or.inl rfl), liveK2⟩
  refine Relation.ReflTransGen.tail (b := ⟨⟨2, 0, sp⟩,
      ⟨K2, .eval (.choice (.ret (num 1)) (.ret (num 2))), [f0], []⟩ ::ₘ
      ⟨K1 ++ [(tuple [sym "dup", foD [1] [101] 0], two)], .eval ((dupE true).rhs.inst (copyAt mkeys 1)), [f0], []⟩ ::ₘ
      deadTwo true ::ₘ 0⟩) ?_
    (Step.of_eq (D := D) (P := PN) (supply := supply) rfl rfl liveK2 (.choice _ _ _ _ _ _))
  refine Relation.ReflTransGen.tail (b := ⟨⟨1, 0, sp⟩, ⟨K1, .eval (.apply two), [f0], []⟩ ::ₘ deadTwo true ::ₘ 0⟩) ?_
    (Step.of_eq (D := D) (P := PN) (supply := supply) rfl rfl liveK1 (.apply _ _ _ _ _ matched2))
  refine Relation.ReflTransGen.tail (b := ⟨⟨1, 0, sp⟩, ⟨K1, .eval (.run X0), [f0], []⟩ ::ₘ deadTwo true ::ₘ 0⟩) ?_
    (Step.of_eq (D := D) (P := PN) (supply := supply) rfl rfl liveK1
      (.run _ _ _ _ _ (bindNames [(([0], [101], 0), two)]) principal1))
  refine Relation.ReflTransGen.tail (b := ⟨⟨1, 0, sp⟩,
      ⟨K1, .eval ((dupE true).rhs.inst (copyAt mkeys 0)), [], []⟩ ::ₘ deadTwo true ::ₘ 0⟩) ?_
    (Step.of_eq (D := D) (P := PN) (supply := supply) rfl rfl liveK1 (.letStart _ _ _ _ _ _ _ _))
  exact Relation.ReflTransGen.single
    (Step.of_eq (D := D) (P := PN) (supply := supply) (rest := 0) rfl
      (by rw [add_zero, Multiset.cons_swap]; rfl) live_nil (.apply _ _ _ _ _ matched1))

theorem runs_allN : Runs D PN supply start ⟨⟨10, 0, sp⟩, finalBag⟩ := by
  have first : Runs D PN supply ⟨⟨2, 0, sp⟩, {b2 1} + R1⟩ ⟨⟨6, 0, sp⟩, A + R1⟩ :=
    (subtreeN 1 2 live_1_2_1 live_1_2_2 principal_1_2).frame R1
  have second : Runs D PN supply ⟨⟨6, 0, sp⟩, {b2 2} + R2⟩ ⟨⟨10, 0, sp⟩, B + R2⟩ :=
    (subtreeN 2 6 live_2_6_1 live_2_6_2 principal_2_6).frame R2
  have bridge : A + R1 = {b2 2} + R2 := by
    simp only [A, R1, R2, Multiset.cons_add, zero_add, Multiset.singleton_add]
    rw [Multiset.cons_swap (deadE 1 2) (b2 2), Multiset.cons_swap (fin 1 2 2 5) (b2 2),
      Multiset.cons_swap (fin 1 2 1 4) (b2 2)]
  have entry : ({b2 1} + R1 : Multiset (Branch mkeys [] () MTy)) = b2 1 ::ₘ R1 := Multiset.singleton_add _ _
  have exit : B + R2 = finalBag := by
    simp only [B, R2, finalBag, Multiset.cons_add, zero_add]
  rw [← bridge] at second
  rw [entry] at first
  rw [exit] at second
  exact (prefixN.trans first).trans second

theorem final_quiescentN :
    Config.Quiescent (D := D) PN supply (⟨⟨10, 0, sp⟩, finalBag⟩ : Config mkeys [] () MTy) :=
  Config.quiescent_of_finished fun b member live => by
    simp only [finalBag, Multiset.mem_cons, Multiset.notMem_zero, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact fin_finished 2 6 1 8
    · exact fin_finished 2 6 2 9
    · exact absurd live (deadE_dead 2 6)
    · exact fin_finished 1 2 1 4
    · exact fin_finished 1 2 2 5
    · exact absurd live (deadE_dead 1 2)
    · exact absurd live deadD_dead
    · exact absurd live (deadTwo_dead true)

/-- **The by-name reading of the undeclared `dup` has a run that ends with four answers.** -/
theorem byName_example :
    ∃ C, Runs D (elaborate dupByName surfaceV) supply
        (Config.initial (fun _ => 0) (elabQuery dupByName surfaceV querySurface)) C ∧
      Config.Quiescent (D := D) (elaborate dupByName surfaceV) supply C ∧
      Config.answers (D := D) C =
        {{ctuple [csym "pair", cnum 2, cnum 1]}, {ctuple [csym "pair", cnum 2, cnum 2]},
          {ctuple [csym "pair", cnum 1, cnum 1]}, {ctuple [csym "pair", cnum 1, cnum 2]}} := by
  rw [byName_query]
  exact ⟨_, runs_allN, final_quiescentN, runs_answers⟩

#print axioms byName_example

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.ExampleByName
