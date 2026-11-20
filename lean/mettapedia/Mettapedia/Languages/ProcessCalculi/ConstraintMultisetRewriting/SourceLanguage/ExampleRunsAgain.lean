import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Toolkit

/-!
# A computed value inside text that is run is read as code again

`Laws.values_never_run` is a statement about the elaboration: text without explicit `run` marks, whose
variables hold computed values, elaborates to code that runs nothing. A `run` at run time dereferences
its text through the store, so a computed value that the text holds is read as code again. This is the
control: it fails exactly the hypothesis "no explicit `run` mark".

```
(= (f) (hold (g 1)))      ; `f` computes the datum `(g 1)`
(= (g 1) done)
!(let $v (f) (run $v))    ; the computed value is run
```

The call `(f)` computes the value `(g 1)`; the `run` dereferences `$v` to it and reads it as the call
`(g 1)` (`called_again`), which answers `done`: the bag is `{done}`, not `{(g 1)}` (`runs_again`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.ExampleRunsAgain

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Elaboration Toolkit

abbrev D : Discipline MSig [] () := ⟨MTy, fun _ _ => True⟩

def gOne : MData := tuple [sym "g", num 1]

def Ef : Equation mkeys [] () MTy := ⟨[100], tuple [sym "f"], .ret gOne⟩
def Eg : Equation mkeys [] () MTy := ⟨[101], gOne, .ret (sym "done")⟩

/-- The program: text is read as a call. -/
def program : Program mkeys [] () MTy := ⟨[Ef, Eg], fun t => .apply t⟩

def supply : ℕ → MClosed := fun _ => csym "fresh"

def v : MData := mvar [3, 1] 0

def query : Comp mkeys [] () MTy := .let_ [3, 1] v (.apply (tuple [sym "f"])) (.run v)

def start : Config mkeys [] () MTy := Config.initial (fun _ => 0) query

theorem program_wellFormed : WellFormed program := by decide

theorem query_wellFormed : QueryWellFormed program [3] query := by decide

def fr : Frame mkeys [] () MTy := .bindTo [3, 1] v (.run v)

def K1 : List (Constraint mkeys [] ()) := [] ++ [(instantiate (copyAt mkeys 0) Ef.lhs, tuple [sym "f"])]
def deadG : Branch mkeys [] () MTy := callBranch D 0 [] (tuple [sym "f"]) [fr] [] Eg
def v1 : MData := foD [1] [3, 1] 0
def K2 : List (Constraint mkeys [] ()) := K1 ++ [(v1, gOne)]
def K3 : List (Constraint mkeys [] ()) := K2 ++ [(instantiate (copyAt mkeys 2) Eg.lhs, gOne)]
def deadF : Branch mkeys [] () MTy := callBranch D 2 K2 gOne [] [] Ef

def finalB : Branch mkeys [] () MTy := ⟨K3, .value (sym "done"), [], []⟩
def final : Config mkeys [] () MTy := ⟨⟨3, 0, fun _ => 0⟩, finalB ::ₘ deadF ::ₘ deadG ::ₘ 0⟩

def closeK3 : Assignment (fam mkeys) noNames :=
  closeNames [(([1], [3, 1], 0), ctuple [csym "g", cnum 1])] (csym "a")

theorem K3_live : Solvable K3 := ⟨Empty, noNames, closeK3, by decide⟩
theorem K2_live : Solvable K2 := solvable_of_append K3_live
theorem K1_live : Solvable K1 := solvable_of_append K2_live

theorem deadG_dead : ¬ Solvable deadG.store :=
  dead_of_length (ts := [sym "g", num 1]) (ts' := [sym "f"]) (List.mem_singleton_self _) (by decide)

theorem deadF_dead : ¬ Solvable deadF.store :=
  dead_of_length (ts := [sym "f"]) (ts' := [sym "g", num 1])
    (List.mem_append_right _ (List.mem_singleton_self _)) (by decide)

/-- Every solution of `K2` reads `$v` as the computed value `(g 1)`. -/
theorem principal_v : Principal K2 (bindNames [(([1], [3, 1], 0), gOne)]) := by
  refine principal_bindNames (by decide) ?_
  intro entry member X target σ models
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  subst member
  have e : instantiate σ (foD [1] [3, 1] 0) = instantiate σ gOne := models (v1, gOne) (by simp [K2])
  rw [instantiate_foD] at e
  exact e

/-- The configuration where the computed value is called again. -/
def again : Config mkeys [] () MTy := ⟨⟨2, 0, fun _ => 0⟩, ⟨K2, .eval (.apply gOne), [], []⟩ ::ₘ deadG ::ₘ 0⟩

theorem runs_to_again : Runs D program supply start again := by
  have matched1 : ∃ e ∈ program.equations, Solvable ([] ++ [(instantiate (copyAt mkeys 0) e.lhs, tuple [sym "f"])]) :=
    ⟨Ef, List.mem_cons_self, K1_live⟩
  -- the run of `$v`, dereferenced to `(g 1)`, read as the call `(g 1)`
  refine Relation.ReflTransGen.tail (b := ⟨⟨2, 0, fun _ => 0⟩, ⟨K2, .eval (.run v1), [], []⟩ ::ₘ deadG ::ₘ 0⟩) ?_
    (Step.of_eq (D := D) (P := program) (supply := supply) rfl rfl K2_live
      (.run _ _ _ _ _ (bindNames [(([1], [3, 1], 0), gOne)]) principal_v))
  -- the bind of the computed value
  refine Relation.ReflTransGen.tail (b := ⟨⟨1, 0, fun _ => 0⟩, ⟨K1, .value gOne, [fr], []⟩ ::ₘ deadG ::ₘ 0⟩) ?_
    (Step.of_eq (D := D) (P := program) (supply := supply) rfl rfl K1_live (.letBind _ _ _ _ _ _ _ _))
  refine Relation.ReflTransGen.tail (b := ⟨⟨1, 0, fun _ => 0⟩, ⟨K1, .eval (.ret gOne), [fr], []⟩ ::ₘ deadG ::ₘ 0⟩) ?_
    (Step.of_eq (D := D) (P := program) (supply := supply) rfl rfl K1_live (.ret _ _ _ _ _))
  -- the call `(f)`: one alternative per equation
  refine Relation.ReflTransGen.tail (b := ⟨⟨0, 0, fun _ => 0⟩, {⟨[], .eval (.apply (tuple [sym "f"])), [fr], []⟩}⟩) ?_
    (Step.of_eq (D := D) (P := program) (supply := supply) (rest := 0) rfl (by rw [add_zero]; rfl) live_nil
      (.apply _ _ _ _ _ matched1))
  exact Relation.ReflTransGen.single
    (Step.of_eq (D := D) (P := program) (supply := supply) (rest := 0) rfl (by rw [add_zero]; rfl) live_nil
      (.letStart _ _ _ _ _ _ _ _))

/-- **The computed value `(g 1)` is called again**: a run reaches an alternative whose focus is the
call `(g 1)`, the value that `(f)` computed. -/
theorem called_again : Runs D program supply start again ∧
    ∃ b ∈ again.branches, b.focus = .eval (.apply gOne) ∧ Solvable b.store :=
  ⟨runs_to_again, ⟨K2, .eval (.apply gOne), [], []⟩,
    (show _ ∈ (⟨K2, .eval (.apply gOne), [], []⟩ : Branch mkeys [] () MTy) ::ₘ deadG ::ₘ 0 from
      Multiset.mem_cons_self _ _), rfl, K2_live⟩

theorem runs_final : Runs D program supply start final := by
  have matched2 : ∃ e ∈ program.equations, Solvable (K2 ++ [(instantiate (copyAt mkeys 2) e.lhs, gOne)]) :=
    ⟨Eg, List.mem_cons_of_mem _ List.mem_cons_self, K3_live⟩
  refine runs_to_again.trans ?_
  refine Relation.ReflTransGen.tail (b := ⟨⟨3, 0, fun _ => 0⟩,
      ⟨K3, .eval (.ret (sym "done")), [], []⟩ ::ₘ deadF ::ₘ deadG ::ₘ 0⟩) ?_
    (Step.of_eq (D := D) (P := program) (supply := supply) rfl rfl K3_live (.ret _ _ _ _ _))
  exact Relation.ReflTransGen.single
    (Step.of_eq (D := D) (P := program) (supply := supply) rfl
      (by
        show (_ : Multiset (Branch mkeys [] () MTy)) =
          (deadF ::ₘ ⟨K3, .eval (.ret (sym "done")), [], []⟩ ::ₘ 0) + (deadG ::ₘ 0)
        rw [Multiset.cons_add, Multiset.cons_add, zero_add, Multiset.cons_swap]) K2_live
      (.apply _ _ _ _ _ matched2))

theorem final_quiescent : Config.Quiescent (D := D) program supply final :=
  Config.quiescent_of_finished fun b member live => by
    simp only [final, Multiset.mem_cons, Multiset.notMem_zero, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact ⟨rfl, _, rfl⟩
    · exact absurd live deadF_dead
    · exact absurd live deadG_dead

/-- **The bag is `{done}`**: the computed value was run again. -/
theorem runs_again :
    WellFormed program ∧ QueryWellFormed program [3] query ∧ Runs D program supply start final ∧
      Config.Quiescent (D := D) program supply final ∧ Config.answers (D := D) final = {{csym "done"}} := by
  refine ⟨program_wellFormed, query_wellFormed, runs_final, final_quiescent, ?_⟩
  show Config.answers (D := D) (⟨⟨3, 0, fun _ => 0⟩, finalB ::ₘ deadF ::ₘ deadG ::ₘ 0⟩ : Config mkeys [] () MTy) = _
  rw [answers_cons_finished (D := D) (b := finalB) ⟨rfl, _, rfl⟩ K3_live, answers_cons_dead (D := D) deadF_dead,
    answers_cons_dead (D := D) deadG_dead, answers_zero,
    answer_of_determines (g := csym "done") rfl ⟨K3_live, fun _ _ _ => rfl⟩]
  rfl

#print axioms called_again
#print axioms runs_again

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.ExampleRunsAgain
