import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Toolkit
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.LawRenaming

/-!
# Renaming bound names: an instance, and the control

* `(= (f $x $y) $y)` answers `(f 1 2)` with the bag `{2}` (`original_example`).
* Swapping `$x` and `$y` is a renaming of bound names (`swap`); the renamed program is
  `(= (f $y $x) $x)` (`swapped_program`), and the law gives it a run from the same query with the same
  bag (`swapped_example`).
* **The control**: sending `$y` to `$x` is a map of names with no inverse. It gives
  `(= (f $x $x) $x)`, under which `(f 1 2)` is unmatched: the bag is `{(f 1 2)}` (`merged_example`).
  The law needs the inverse.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.ExampleRenaming

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Elaboration Toolkit Renaming

abbrev D : Discipline MSig [] () := ⟨MTy, fun _ _ => True⟩

def supply : ℕ → MClosed := fun _ => csym "space"

def x : MData := foD [] [100] 0
def y : MData := foD [] [100] 1

def original : Program mkeys [] () MTy := ⟨[⟨[100], tuple [sym "f", x, y], .ret y⟩], fun t => .apply t⟩
def merged : Program mkeys [] () MTy := ⟨[⟨[100], tuple [sym "f", x, x], .ret x⟩], fun t => .apply t⟩

def call : MData := tuple [sym "f", num 1, num 2]
def query : Comp mkeys [] () MTy := .apply call

/-! ## The original program -/

def x0 : MData := foD [0] [100] 0
def y0 : MData := foD [0] [100] 1
def store : List (Constraint mkeys [] ()) := [(tuple [sym "f", x0, y0], call)]

theorem store_live : Solvable store :=
  ⟨Empty, noNames, closeNames [(([0], [100], 0), cnum 1), (([0], [100], 1), cnum 2)] (csym "a"), by decide⟩

theorem y0_determined : Determines store y0 (cnum 2) := by
  refine ⟨store_live, fun target σ solved => ?_⟩
  have equal := solved _ (List.mem_singleton_self _)
  have parts : tupleAt [symAt "f", σ (fo [0] [100] 0), σ (fo [0] [100] 1)] =
      tupleAt [symAt "f", instantiate σ (num 1), instantiate σ (num 2)] := by
    rw [← instantiate_foD σ [0] [100] 0, ← instantiate_foD σ [0] [100] 1]
    exact equal
  rw [y0, instantiate_foD]
  exact (tuple3_inj parts).2.2

def final : Config mkeys [] () MTy := ⟨⟨1, 0, fun _ => 0⟩, {⟨store, .value y0, [], []⟩}⟩

theorem original_runs : Runs D original supply (Config.initial (fun _ => 0) query) final := by
  refine Relation.ReflTransGen.tail (b := ⟨⟨1, 0, fun _ => 0⟩, {⟨store, .eval (.ret y0), [], []⟩}⟩) ?_
    (step_one store_live (.ret _ _ _ _ _))
  exact Relation.ReflTransGen.single
    (Step.of_eq (D := D) (P := original) (supply := supply) (rest := 0) rfl rfl live_nil
      (.apply ⟨0, 0, fun _ => 0⟩ [] call [] [] ⟨_, List.mem_singleton_self _, store_live⟩))

theorem original_answers : Config.answers (D := D) final = {{cnum 2}} := by
  have bag := answers_singleton (D := D) (w := ⟨1, 0, fun _ => 0⟩) (b := ⟨store, .value y0, [], []⟩)
    ⟨rfl, _, rfl⟩ store_live
  rw [answer_of_determines rfl y0_determined] at bag
  exact bag

/-- **The original program**: `(f 1 2)` has the bag `{2}`, and the run has ended. -/
theorem original_example :
    ∃ C, Runs D original supply (Config.initial (fun _ => 0) query) C ∧
      Config.Quiescent (D := D) original supply C ∧ Config.answers (D := D) C = {{cnum 2}} :=
  ⟨final, original_runs, Config.quiescent_single, original_answers⟩

/-! ## The swap: a renaming of bound names -/

/-- Exchange the indices `0` and `1` at every site. -/
def swapIndex (i : ℕ) : ℕ := if i = 0 then 1 else if i = 1 then 0 else i

theorem swapIndex_swapIndex (i : ℕ) : swapIndex (swapIndex i) = i := by
  unfold swapIndex
  by_cases zero : i = 0
  · subst zero
    rfl
  · by_cases one : i = 1
    · subst one
      rfl
    · simp [zero, one]

def swap : KeyRenaming :=
  ⟨fun _ => swapIndex, fun _ => swapIndex, fun _ => swapIndex_swapIndex, fun _ => swapIndex_swapIndex⟩

/-- The renamed program is `(= (f $y $x) $x)`. -/
theorem swapped_program :
    (swap.rProg original).equations = [⟨[100], tuple [sym "f", y, x], .ret x⟩] := rfl

/-- **The law at work**: the renamed program has a run from the same query with the same bag. -/
theorem swapped_example :
    ∃ C, Runs D (swap.rProg original) supply (Config.initial (fun _ => 0) query) C ∧
      Config.answers (D := D) C = {{cnum 2}} := by
  obtain ⟨C, runs, same⟩ := swap.runs_rename_answers (D := D) original_runs
  exact ⟨C, runs, same.trans original_answers⟩

/-! ## The control: merging two names -/

def mergedStore : List (Constraint mkeys [] ()) := [(tuple [sym "f", x0, x0], call)]

theorem mergedStore_dead : ¬ Solvable ([] ++ mergedStore) := by
  rintro ⟨X, target, σ, solved⟩
  have equal := solved _ (List.mem_singleton_self _)
  have parts : tupleAt [symAt "f", σ (fo [0] [100] 0), σ (fo [0] [100] 0)] =
      tupleAt [symAt "f", instantiate σ (num 1), instantiate σ (num 2)] := by
    rw [← instantiate_foD σ [0] [100] 0]
    exact equal
  have one := (tuple3_inj parts).2.1
  have two := (tuple3_inj parts).2.2
  have numbers : instantiate σ (num 1) = instantiate σ (num 2) := one.symm.trans two
  change (Term.op (Sum.inl (MOp.num 1)) .nil : Term (signature MSig target) [] ()) =
    Term.op (Sum.inl (MOp.num 2)) .nil at numbers
  injection numbers with _ _ hop _
  simp at hop

def mergedFinal : Config mkeys [] () MTy := ⟨⟨0, 0, fun _ => 0⟩, {⟨[], .value call, [], []⟩}⟩

/-- **The control**: under `(= (f $x $x) $x)`, `(f 1 2)` is unmatched; the bag is `{(f 1 2)}`. -/
theorem merged_example :
    ∃ C, Runs D merged supply (Config.initial (fun _ => 0) query) C ∧
      Config.Quiescent (D := D) merged supply C ∧
      Config.answers (D := D) C = {{ctuple [csym "f", cnum 1, cnum 2]}} := by
  refine ⟨mergedFinal, Relation.ReflTransGen.single (step_one live_nil (.unmatched _ _ _ _ _ fun e member => ?_)),
    Config.quiescent_single, ?_⟩
  · rw [List.mem_singleton.mp member]
    exact mergedStore_dead
  · have bag := answers_singleton (D := D) (w := ⟨0, 0, fun _ => 0⟩) (b := ⟨[], .value call, [], []⟩)
      ⟨rfl, _, rfl⟩ live_nil
    rw [answer_of_determines (g := ctuple [csym "f", cnum 1, cnum 2]) rfl ⟨live_nil, fun _ _ _ => rfl⟩] at bag
    exact bag

#print axioms original_example
#print axioms swapped_program
#print axioms swapped_example
#print axioms merged_example

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.ExampleRenaming
