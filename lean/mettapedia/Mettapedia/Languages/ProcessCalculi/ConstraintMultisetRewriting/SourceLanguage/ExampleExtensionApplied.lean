import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.ExampleExtension

/-!
# The extension law applied to a non-empty program, and its condition not necessary

The new equation is `e = (= (h $x) done)` of `ExampleExtension`.

* **The law applied** (`law_applied`): the program `(= (g $y) $y)` calls `(g (h 1))`, which holds
  `e`'s head as data. The program and the query satisfy the law's condition (`condition`). The run
  without `e` ends with `{(h 1)}` (`without_e`); the law then gives a run with `e` that ends, quiescent,
  with the same bag, without computing that run.
* **The condition is sufficient, not necessary** (`condition_not_necessary`): the query `run (k 1)` is
  outside the condition (it runs text), and its bag is `{(k 1)}` with and without `e`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.ExampleExtensionApplied

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Elaboration Toolkit Extension ExampleExtension

/-- `(= (g $y) $y)`. -/
def Eg : Equation mkeys [] () MTy := ⟨[101], tuple [sym "g", foD [] [101] 0], .ret (foD [] [101] 0)⟩

/-- **A non-empty program.** -/
def P2 : Program mkeys [] () MTy := ⟨[Eg], fun t => .apply t⟩

def start : Config mkeys [] () MTy := Config.initial (fun _ => 0) callQuery

/-- **The condition holds**: the program's right-hand side calls nothing, and the query's call has head
`g`, not `h`. -/
theorem condition : ProgramApart (D := D) P2 e ∧ Related (D := D) e start start := by
  refine ⟨fun e' member => ?_, rfl, ⟨0, (add_zero _).symm, by simp⟩, ?_⟩
  · simp only [P2, List.mem_singleton] at member
    subst member
    trivial
  · intro b member
    rw [Multiset.mem_singleton.mp member]
    exact call_condition.2

def y0 : MData := foD [0] [101] 0
def Ky : List (Constraint mkeys [] ()) := [] ++ [(instantiate (copyAt mkeys 0) Eg.lhs, gText)]

theorem Ky_live : Solvable Ky :=
  ⟨Empty, noNames, closeNames [(([0], [101], 0), hOne)] (csym "a"), by decide⟩

theorem y0_determined : Determines Ky y0 hOne := by
  refine ⟨Ky_live, fun target σ solved => ?_⟩
  have e1 := solved _ (List.mem_singleton_self _)
  have pair : tupleAt [symAt "g", instantiate σ (foD [0] [101] 0)] = tupleAt [symAt "g", instantiate σ text] := e1
  have inner := (tuple2_inj pair).2
  show instantiate σ (foD [0] [101] 0) = _
  rw [inner]
  rfl

def final : Config mkeys [] () MTy := ⟨⟨1, 0, fun _ => 0⟩, {⟨Ky, .value y0, [], []⟩}⟩

theorem without_e : Runs D P2 supply start final ∧ Config.Quiescent (D := D) P2 supply final ∧
    Config.answers (D := D) final = {{hOne}} := by
  refine ⟨?_, Config.quiescent_single, ?_⟩
  · refine Relation.ReflTransGen.tail (b := ⟨⟨1, 0, fun _ => 0⟩, {⟨Ky, .eval (.ret y0), [], []⟩}⟩) ?_
      (step_one Ky_live (.ret _ _ _ _ _))
    exact Relation.ReflTransGen.single
      (Step.of_eq (D := D) (P := P2) (supply := supply) (rest := 0) rfl rfl live_nil
        (.apply ⟨0, 0, fun _ => 0⟩ [] gText [] [] ⟨Eg, List.mem_singleton_self _, Ky_live⟩))
  · show Config.answers (D := D) (⟨⟨1, 0, fun _ => 0⟩, {⟨Ky, .value y0, [], []⟩}⟩ : Config mkeys [] () MTy) = _
    rw [answers_singleton (D := D) (b := ⟨Ky, .value y0, [], []⟩) ⟨rfl, _, rfl⟩ Ky_live,
      answer_of_determines rfl y0_determined]

/-- **The law applied to a non-empty program**: from the run without `e`, the law gives a run with `e`
that ends, quiescent, with the same bag. -/
theorem law_applied :
    ∃ C, Runs D (extend P2 e) supply start C ∧ Config.Quiescent (D := D) (extend P2 e) supply C ∧
      Config.answers (D := D) C = {{hOne}} := by
  obtain ⟨C, runs, related⟩ := extension_backward supply condition.1 without_e.1 condition.2
  refine ⟨C, runs, Config.quiescent_of_finished fun b member live => ?_, ?_⟩
  · obtain ⟨_, ⟨dead, split, deadDead⟩, _⟩ := related
    rw [split] at member
    rcases Multiset.mem_add.mp member with old | gone
    · rw [Multiset.mem_singleton.mp old]
      exact ⟨rfl, _, rfl⟩
    · exact absurd live (deadDead b gone)
  · rw [answers_related related, without_e.2.2]

/-! ## The condition is not necessary -/

/-- `(k 1)`, a text that does not hold `e`'s head. -/
def kText : MData := tuple [sym "k", num 1]
def kClosed : MClosed := ctuple [csym "k", cnum 1]

def runQuery : Comp mkeys [] () MTy := .run kText

def runFinal : Config mkeys [] () MTy := ⟨⟨0, 0, fun _ => 0⟩, {⟨[], .value kText, [], []⟩}⟩

theorem runFinal_answers : Config.answers (D := D) runFinal = {{kClosed}} := by
  rw [show runFinal = ⟨⟨0, 0, fun _ => 0⟩, {⟨[], .value kText, [], []⟩}⟩ from rfl,
    answers_singleton (D := D) ⟨rfl, _, rfl⟩ live_nil,
    answer_of_determines (g := kClosed) rfl ⟨live_nil, fun _ _ _ => rfl⟩]

/-- **Outside the condition, the same bag**: the query runs text, so the condition fails; with and
without `e`, the bag is `{(k 1)}`. -/
theorem condition_not_necessary :
    ¬ BranchApart (D := D) e (⟨[], .eval runQuery, [], []⟩ : Branch mkeys [] () MTy) ∧
      Runs D P supply (Config.initial (fun _ => 0) runQuery) runFinal ∧
      Config.Quiescent (D := D) P supply runFinal ∧
      Runs D (extend P e) supply (Config.initial (fun _ => 0) runQuery) runFinal ∧
      Config.Quiescent (D := D) (extend P e) supply runFinal ∧
      Config.answers (D := D) runFinal = {{kClosed}} := by
  refine ⟨fun apart => apart.1 runQuery rfl, ?_, Config.quiescent_single, ?_, Config.quiescent_single,
    runFinal_answers⟩
  · refine Relation.ReflTransGen.tail (b := ⟨⟨0, 0, fun _ => 0⟩, {⟨[], .eval (.apply kText), [], []⟩}⟩) ?_
      (step_one live_nil (.unmatched _ _ _ _ _ (fun e' member => by cases member)))
    exact Relation.ReflTransGen.single (step_one live_nil (.run _ _ _ _ _ (generator (fam mkeys)) principal_nil))
  · refine Relation.ReflTransGen.tail (b := ⟨⟨0, 0, fun _ => 0⟩, {⟨[], .eval (.apply kText), [], []⟩}⟩) ?_
      (step_one live_nil (.unmatched _ _ _ _ _ fun e' member => ?_))
    · exact Relation.ReflTransGen.single (step_one live_nil (.run _ _ _ _ _ (generator (fam mkeys)) principal_nil))
    · simp only [Extension.extend, P, List.nil_append, List.mem_singleton] at member
      subst member
      exact dead_new (separated_of_heads (D' := D) e (f := "k") (g := "h") (args := [num 1])
        (args' := [foD [] [100] 0]) rfl (by decide)) 0 []

#print axioms condition
#print axioms law_applied
#print axioms condition_not_necessary

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.ExampleExtensionApplied
