import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.ExampleAnnotated
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Laws

/-!
# The transfer law applied to the annotated program

The annotated program of `ExampleAnnotated` runs one text, `run X0`, where the store of the alternative
binds `X0` to `(two)`. Every most general solution of that store dereferences `X0` to `(two)`
(`principal_X0`), and every reading reads `(two)` as the same call. So every configuration of the run
reflects only the text `(two)` (`annotated_runs_along`), and the law carries the run under one reading
to the run under every other (`annotated_runs_transferred`).

**The control** (`every_instance_fails`): asking the readings to agree on every instance of `X0`, not on
its dereferencing by the store, fails at the same configuration, because `(f a)` is an instance of
`X0` and the readings by value and by name read it differently.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.ExampleTransfer

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Elaboration Toolkit Laws ExampleHeld ExampleHeldRuns ExampleAnnotated

/-- The text the run reflects. -/
abbrev OnlyTwo : MData → Prop := fun u => u = two

/-- **Every most general solution of the store dereferences `X0` to `(two)`.** -/
theorem principal_X0 {θ : Assignment (fam mkeys) (fam mkeys)} (principal : Principal K1 θ) :
    instantiate θ X0 = two := by
  rw [show X0 = foD [0] [101] 0 from rfl, instantiate_foD, K1_entails θ principal.1]
  rfl

/-- Every reading reads `(two)` the same way. -/
theorem readings_agree (π π' : Params) : ∀ t, OnlyTwo t → (PA π).reflect t = (PA π').reflect t := by
  intro t only
  subst only
  exact (reflect_two_annotated π).trans (reflect_two_annotated π').symm

/-- The configuration about to run `X0`. -/
def atRun : Config mkeys [] () MTy := ⟨⟨1, 0, sp⟩, ⟨K1, .eval (.run X0), [fA], []⟩ ::ₘ deadTwoA ::ₘ 0⟩

theorem atRun_only : RunsOnly atRun OnlyTwo := by
  intro b member t focus θ principal
  simp only [atRun, Multiset.mem_cons, Multiset.notMem_zero, or_false] at member
  rcases member with rfl | rfl
  · simp only [Focus.eval.injEq, Comp.run.injEq] at focus
    subst focus
    exact principal_X0 principal
  · exact absurd ⟨_, _, θ, principal.1⟩ deadTwoA_dead

/-- **The annotated run, with every configuration reflecting only `(two)`.** -/
theorem annotated_runs_along (π : Params) :
    Relation.ReflTransGen (fun C₁ C₂ => Step D (PA π) supply C₁ C₂ ∧ RunsOnly C₁ OnlyTwo)
      (Config.initial (fun _ => 0) (.apply call))
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
  -- no alternative of these configurations is about to run
  have noRun : ∀ (C : Config mkeys [] () MTy),
      (∀ b ∈ C.branches, ∀ t, b.focus ≠ .eval (.run t)) → RunsOnly C OnlyTwo :=
    fun C none => runsOnly_of_none none
  refine Relation.ReflTransGen.tail (b := ⟨⟨4, 0, sp⟩,
      ⟨KA 2 3, .eval (.apply (tuple [sym "pair", Y0 3, X0])), [], []⟩ ::ₘ finA 1 2 ::ₘ deadDA ::ₘ deadTwoA ::ₘ 0⟩)
    ?_ ⟨Step.of_eq (D := D) (P := PA π) (supply := supply) rfl rfl liveA2
      (.unmatched ⟨4, 0, sp⟩ (KA 2 3) (tuple [sym "pair", Y0 3, X0]) [] [] (unmatchedA π 2 3 4)),
      noRun _ (by
        intro b member t focus
        simp only [Multiset.mem_cons, Multiset.notMem_zero, or_false] at member
        rcases member with rfl | rfl | rfl | rfl <;> cases focus)⟩
  refine Relation.ReflTransGen.tail (b := ⟨⟨3, 0, sp⟩,
      ⟨K2, .value (num 2), [fA], []⟩ ::ₘ finA 1 2 ::ₘ deadDA ::ₘ deadTwoA ::ₘ 0⟩) ?_
    ⟨Step.of_eq (D := D) (P := PA π) (supply := supply) rfl rfl liveK2 (.letBind _ _ _ _ _ _ _ _),
      noRun _ (by
        intro b member t focus
        simp only [Multiset.mem_cons, Multiset.notMem_zero, or_false] at member
        rcases member with rfl | rfl | rfl | rfl <;> cases focus)⟩
  refine Relation.ReflTransGen.tail (b := ⟨⟨3, 0, sp⟩,
      ⟨K2, .eval (.ret (num 2)), [fA], []⟩ ::ₘ finA 1 2 ::ₘ deadDA ::ₘ deadTwoA ::ₘ 0⟩) ?_
    ⟨Step.of_eq (D := D) (P := PA π) (supply := supply) rfl rfl liveK2 (.ret _ _ _ _ _),
      noRun _ (by
        intro b member t focus
        simp only [Multiset.mem_cons, Multiset.notMem_zero, or_false] at member
        rcases member with rfl | rfl | rfl | rfl <;> cases focus)⟩
  refine Relation.ReflTransGen.tail (b := ⟨⟨3, 0, sp⟩,
      ⟨K2, .eval (.ret (num 2)), [fA], []⟩ ::ₘ
      ⟨KA 1 2, .eval (.apply (tuple [sym "pair", Y0 2, X0])), [], []⟩ ::ₘ deadDA ::ₘ deadTwoA ::ₘ 0⟩) ?_
    ⟨Step.of_eq (D := D) (P := PA π) (supply := supply) (Multiset.cons_swap _ _ _)
      (by rw [Multiset.singleton_add, Multiset.cons_swap]; rfl) liveA1
      (.unmatched ⟨3, 0, sp⟩ (KA 1 2) (tuple [sym "pair", Y0 2, X0]) [] [] (unmatchedA π 1 2 3)),
      noRun _ (by
        intro b member t focus
        simp only [Multiset.mem_cons, Multiset.notMem_zero, or_false] at member
        rcases member with rfl | rfl | rfl | rfl <;> cases focus)⟩
  refine Relation.ReflTransGen.tail (b := ⟨⟨2, 0, sp⟩,
      ⟨K2, .eval (.ret (num 2)), [fA], []⟩ ::ₘ
      ⟨K2, .value (num 1), [fA], []⟩ ::ₘ deadDA ::ₘ deadTwoA ::ₘ 0⟩) ?_
    ⟨Step.of_eq (D := D) (P := PA π) (supply := supply) (Multiset.cons_swap _ _ _)
      (by rw [Multiset.singleton_add, Multiset.cons_swap]; rfl) liveK2 (.letBind _ _ _ _ _ _ _ _),
      noRun _ (by
        intro b member t focus
        simp only [Multiset.mem_cons, Multiset.notMem_zero, or_false] at member
        rcases member with rfl | rfl | rfl | rfl <;> cases focus)⟩
  refine Relation.ReflTransGen.tail (b := ⟨⟨2, 0, sp⟩,
      ⟨K2, .eval (.ret (num 1)), [fA], []⟩ ::ₘ
      ⟨K2, .eval (.ret (num 2)), [fA], []⟩ ::ₘ deadDA ::ₘ deadTwoA ::ₘ 0⟩) ?_
    ⟨Step.of_eq (D := D) (P := PA π) (supply := supply) rfl
      (by rw [Multiset.singleton_add, Multiset.cons_swap]; rfl) liveK2 (.ret _ _ _ _ _),
      noRun _ (by
        intro b member t focus
        simp only [Multiset.mem_cons, Multiset.notMem_zero, or_false] at member
        rcases member with rfl | rfl | rfl | rfl <;> cases focus)⟩
  refine Relation.ReflTransGen.tail (b := ⟨⟨2, 0, sp⟩,
      ⟨K2, .eval (.choice (.ret (num 1)) (.ret (num 2))), [fA], []⟩ ::ₘ deadDA ::ₘ deadTwoA ::ₘ 0⟩) ?_
    ⟨Step.of_eq (D := D) (P := PA π) (supply := supply) rfl rfl liveK2 (.choice _ _ _ _ _ _),
      noRun _ (by
        intro b member t focus
        simp only [Multiset.mem_cons, Multiset.notMem_zero, or_false] at member
        rcases member with rfl | rfl | rfl <;> cases focus)⟩
  refine Relation.ReflTransGen.tail (b := ⟨⟨1, 0, sp⟩, ⟨K1, .eval (.apply two), [fA], []⟩ ::ₘ deadTwoA ::ₘ 0⟩) ?_
    ⟨Step.of_eq (D := D) (P := PA π) (supply := supply) rfl
      (by rw [elaborate_annotated]; rfl) liveK1 (.apply _ _ _ _ _ matched2),
      noRun _ (by
        intro b member t focus
        simp only [Multiset.mem_cons, Multiset.notMem_zero, or_false] at member
        rcases member with rfl | rfl <;> cases focus)⟩
  refine Relation.ReflTransGen.tail (b := atRun) ?_
    ⟨Step.of_eq (D := D) (P := PA π) (supply := supply) rfl rfl liveK1
      (.run _ _ _ _ _ (bindNames [(([0], [101], 0), two)]) principal1), atRun_only⟩
  refine Relation.ReflTransGen.tail (b := ⟨⟨1, 0, sp⟩,
      ⟨K1, .eval (dupEA.rhs.inst (copyAt mkeys 0)), [], []⟩ ::ₘ deadTwoA ::ₘ 0⟩) ?_
    ⟨Step.of_eq (D := D) (P := PA π) (supply := supply) rfl rfl liveK1 (.letStart _ _ _ _ _ _ _ _),
      noRun _ (by
        intro b member t focus
        simp only [Multiset.mem_cons, Multiset.notMem_zero, or_false] at member
        rcases member with rfl | rfl <;> cases focus)⟩
  exact Relation.ReflTransGen.single
    ⟨Step.of_eq (D := D) (P := PA π) (supply := supply) (rest := 0) rfl
      (by rw [elaborate_annotated, add_zero, Multiset.cons_swap]; rfl) live_nil (.apply _ _ _ _ _ matched1),
      noRun _ (by
        intro b member t focus
        rw [Multiset.mem_singleton.mp member] at focus
        cases focus)⟩

/-- **The law applied to its example**: the annotated run under any reading `π` is, by the transfer
law, a run under every reading `π'`. -/
theorem annotated_runs_transferred (π π' : Params) :
    Runs D (PA π') supply (Config.initial (fun _ => 0) (.apply call))
      ⟨⟨4, 0, sp⟩, finA 2 3 ::ₘ finA 1 2 ::ₘ deadDA ::ₘ deadTwoA ::ₘ 0⟩ :=
  runs_transfer_along (by rw [elaborate_annotated, elaborate_annotated]) (readings_agree π π')
    (annotated_runs_along π)

/-! ## The control: agreement on every instance -/

/-- The stronger form of the hypothesis: agreement on every instance of the text about to run. -/
def RunsOnlyEvery (C : Config mkeys [] () MTy) (A : MData → Prop) : Prop :=
  ∀ b ∈ C.branches, ∀ t, b.focus = .eval (.run t) → ∀ θ, A (instantiate θ t)

def valueReading : Params := ⟨fun _ _ => .value, false, false⟩
def nameReading : Params := ⟨fun _ _ => .name, false, false⟩

/-- Whether a computation is a call. -/
def isApply : Comp mkeys [] () MTy → Bool
  | .apply _ => true
  | _ => false

/-- The readings by value and by name read `(f a)` differently. -/
theorem readings_differ :
    (PA valueReading).reflect (tuple [sym "f", sym "a"]) ≠ (PA nameReading).reflect (tuple [sym "f", sym "a"]) := by
  intro same
  have byValue : isApply ((PA valueReading).reflect (tuple [sym "f", sym "a"])) = false := rfl
  have byName : isApply ((PA nameReading).reflect (tuple [sym "f", sym "a"])) = true := rfl
  rw [same, byName] at byValue
  cases byValue

/-- **The control**: at the configuration about to run `X0`, agreement on every instance of `X0`
fails between the readings by value and by name, while agreement on the dereferenced text holds
(`atRun_only`). -/
theorem every_instance_fails :
    ¬ RunsOnlyEvery atRun (fun u => (PA valueReading).reflect u = (PA nameReading).reflect u) := by
  intro every
  have at_fa := every ⟨K1, .eval (.run X0), [fA], []⟩
    (show _ ∈ (⟨K1, .eval (.run X0), [fA], []⟩ : Branch mkeys [] () MTy) ::ₘ deadTwoA ::ₘ 0 from
      Multiset.mem_cons_self _ _) X0 rfl
    (bindNames [(([0], [101], 0), tuple [sym "f", sym "a"])])
  exact readings_differ at_fa

#print axioms principal_X0
#print axioms annotated_runs_along
#print axioms annotated_runs_transferred
#print axioms every_instance_fails

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.ExampleTransfer
