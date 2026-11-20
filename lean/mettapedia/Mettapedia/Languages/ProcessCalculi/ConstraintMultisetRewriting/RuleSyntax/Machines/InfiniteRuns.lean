import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Machines.PartialRecursive

/-!
# Divergence of the nineteen-rule program as an infinite run, and the knowledge along a run

`PartialRecursive.diverges_iff` says that `c.eval v = Part.none` exactly when no halted state is reachable
from the start state. This module states divergence as an infinite run of the step (`RuleSyntax.step` at the
one first-order frame over rows with unknowns, one match per firing):

* `infiniteRun_of_diverges`: when `c.eval v` has no value, the step has an infinite run from the start state;
* `diverges_of_infiniteRun`: an infinite run from the start state forces `c.eval v = Part.none`;
* `diverges_iff_infiniteRun`: the two together;
* `halts_xor_infiniteRun`: from the start state the program halts with some output or has an infinite run,
  and not both;
* `infiniteRun_iff_not_acc`: an infinite run is the failure of accessibility of the step, the form in which
  the tree's general results on divergence are stated (`OperationalCorrespondence.normalization_reflected`,
  `Representation.Hosting.WeakCorrespondence.acc_of_acc`).
* Controls: `loop_diverges`, `loop_infiniteRun` (`fix succ` on `[0]`, a code with no value and an infinite
  run), `succ_no_infiniteRun` (successor on `[2]`, a code with a value and no infinite run).

## The knowledge along a run

The result of a firing keeps the firing's information as its knowledge. A rule of the nineteen-rule program
takes one row and has no read and no tell, so every firing adds one equation (`knowledge_length_after`), and
the `n`-th state of every run from the start has `n` equations (`knowledge_length_along`), though it reads as
one row. Instance: the infinite run of `fix succ` on `[0]`, whose knowledge grows without bound
(`loop_knowledge_unbounded`). The size of a state is not the size of the row it reads as.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Machines.InfiniteRuns

open LogicOverTheStep.StepSpan (Succ)
open PartialRecursive
open Presentation.Schematic
open Mettapedia.Languages.PartrecMachine
open Turing.ToPartrec

/-- **An infinite run of the step of the nineteen-rule program from a state.** -/
def InfiniteRun (s : SState ℕ) : Prop :=
  ∃ run : ℕ → SState ℕ, run 0 = s ∧ ∀ n, Succ (schematicStep ℕ program).toStep (run n) (run (n + 1))

/-- **An infinite run is the failure of accessibility** of the step of the program as a system. -/
theorem infiniteRun_iff_not_acc (s : SState ℕ) :
    InfiniteRun s ↔ ¬ Acc (fun next state => (stepSystem ℕ program).Step state next) s := by
  constructor
  · rintro ⟨run, starts, steps⟩
    exact not_acc_iff_exists_descending_chain.mpr ⟨run, starts, steps⟩
  · intro notAccessible
    obtain ⟨run, starts, steps⟩ := not_acc_iff_exists_descending_chain.mp notAccessible
    exact ⟨run, starts, steps⟩

/-- A state reads as the row of a point that the authored machine reaches from the pending evaluation. -/
def Reached (c : Code) (v : List ℕ) (s : SState ℕ) : Prop :=
  ∃ p : Point, ReadsBag s {p.row} ∧ Relation.ReflTransGen Reduces (normalTerm c .halt v) p.pattern

theorem reached_start (c : Code) (v : List ℕ) : Reached c v (start c v) :=
  ⟨.normal c .halt v, rowState_reads (eNormal c .halt v), .refl⟩

/-- When the evaluation has no value, every point the machine reaches has a successor. -/
theorem successor_of_diverges {c : Code} {v : List ℕ} (diverges : c.eval v = Part.none) {p : Point}
    (reach : Relation.ReflTransGen Reduces (normalTerm c .halt v) p.pattern) : ∃ p', successor p = some p' := by
  cases p with
  | normal c' k v' => exact ⟨_, rfl⟩
  | config cfg =>
      cases cfg with
      | ret k v' => exact ⟨_, rfl⟩
      | halt w =>
          have member : w ∈ c.eval v := (adequacy c v w).mp reach
          rw [diverges] at member
          exact absurd member (Part.notMem_none w)

theorem reached_step {c : Code} {v : List ℕ} (diverges : c.eval v = Part.none) {s : SState ℕ}
    (reached : Reached c v s) : ∃ s', Succ (schematicStep ℕ program).toStep s s' ∧ Reached c v s' := by
  obtain ⟨p, reads, reach⟩ := reached
  obtain ⟨p', stepped⟩ := successor_of_diverges diverges reach
  have reduces : Reduces p.pattern p'.pattern := (reduces_iff_successor p _).mpr ⟨p', stepped, rfl⟩
  obtain ⟨g, admitted, p'', same, reads'⟩ := firing_of_reduction reads reduces
  have reduces' : Reduces p.pattern p''.pattern := by
    rw [← same]
    exact reduces
  exact ⟨_, ⟨g, admitted, rfl⟩, p'', reads', reach.tail reduces'⟩

/-- **A code whose evaluation has no value has an infinite run from its start state.** -/
theorem infiniteRun_of_diverges (c : Code) (v : List ℕ) (diverges : c.eval v = Part.none) :
    InfiniteRun (start c v) := by
  let next : {s // Reached c v s} → {s // Reached c v s} := fun s =>
    ⟨Classical.choose (reached_step diverges s.2), (Classical.choose_spec (reached_step diverges s.2)).2⟩
  let run : ℕ → {s // Reached c v s} := fun n => next^[n] ⟨start c v, reached_start c v⟩
  refine ⟨fun n => (run n).1, rfl, fun n => ?_⟩
  have later : run (n + 1) = next (run n) := Function.iterate_succ_apply' next n _
  show Succ _ (run n).1 (run (n + 1)).1
  rw [later]
  exact (Classical.choose_spec (reached_step diverges (run n).2)).1

/-- **An infinite run from the start state forces the evaluation to have no value.** -/
theorem diverges_of_infiniteRun (c : Code) (v : List ℕ) (infinite : InfiniteRun (start c v)) :
    c.eval v = Part.none := by
  obtain ⟨run, atStart, steps⟩ := infinite
  have advance : ∀ n (p : Point), ReadsBag (run n) {p.row} →
      ∃ p', successor p = some p' ∧ ReadsBag (run (n + 1)) {p'.row} := by
    intro n p reads
    obtain ⟨g, admitted, isNext⟩ := steps n
    obtain ⟨p', stepped, -, reads'⟩ := reduction_of_firing reads g admitted
    exact ⟨p', stepped, isNext ▸ reads'⟩
  have never : ∀ (w : List ℕ) (t : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern),
      Relation.ReflTransGen Reduces t (encCfg (.halt w)) →
      ∀ (n : ℕ) (p : Point), t = p.pattern → ReadsBag (run n) {p.row} → False := by
    intro w t reach
    induction reach using Relation.ReflTransGen.head_induction_on with
    | refl =>
        intro n p same reads
        obtain ⟨p', stepped, -⟩ := advance n p reads
        rw [pattern_halt same.symm] at stepped
        simp [successor] at stepped
    | head first _ ih =>
        intro n p same reads
        obtain ⟨p', stepped, reads'⟩ := advance n p reads
        rw [same] at first
        obtain ⟨p'', stepped'', isNext⟩ := (reduces_iff_successor p _).mp first
        have samePoint : p' = p'' := Option.some.inj (stepped.symm.trans stepped'')
        rw [← samePoint] at isNext
        exact ih (n + 1) p' isNext reads'
  refine Part.eq_none_iff.mpr fun w member => ?_
  have reads0 : ReadsBag (run 0) {(Point.normal c .halt v).row} := by
    rw [atStart]
    exact rowState_reads (eNormal c .halt v)
  exact never w _ ((adequacy c v w).mpr member) 0 (.normal c .halt v) rfl reads0

/-- **Divergence is an infinite run**: the evaluation has no value exactly when the step has an infinite run
from the start state. -/
theorem diverges_iff_infiniteRun (c : Code) (v : List ℕ) : c.eval v = Part.none ↔ InfiniteRun (start c v) :=
  ⟨infiniteRun_of_diverges c v, diverges_of_infiniteRun c v⟩

/-- **From the start state the program halts with an output or runs for ever, and not both.** -/
theorem halts_xor_infiniteRun (c : Code) (v : List ℕ) :
    ((∃ w, Halts c v w) ∧ ¬ InfiniteRun (start c v)) ∨ (InfiniteRun (start c v) ∧ ¬ ∃ w, Halts c v w) := by
  by_cases halts : ∃ w, Halts c v w
  · refine Or.inl ⟨halts, fun infinite => ?_⟩
    obtain ⟨w, halted⟩ := halts
    have member := (halts_iff c v w).mp halted
    rw [diverges_of_infiniteRun c v infinite] at member
    exact Part.notMem_none w member
  · refine Or.inr ⟨infiniteRun_of_diverges c v ((diverges_iff c v).mp fun w h => halts ⟨w, h⟩), halts⟩

/-! ## A diverging code: the fixed point of the successor on `[0]` -/

/-- The four points the machine passes through from the pending evaluation of `fix succ` on `[0]`. -/
def loopPoints : List Point :=
  [.normal (.fix .succ) .halt [0], .normal .succ (.fix .succ .halt) [0],
    .config (.ret (.fix .succ .halt) [1]), .normal .succ (.fix .succ .halt) []]

theorem loop_closed {t : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern}
    (reach : Relation.ReflTransGen Reduces (normalTerm (.fix .succ) .halt [0]) t) :
    ∃ p ∈ loopPoints, t = p.pattern := by
  induction reach with
  | refl => exact ⟨_, List.mem_cons_self, rfl⟩
  | tail _ last earlier =>
      obtain ⟨p, inside, rfl⟩ := earlier
      obtain ⟨p', stepped, rfl⟩ := (reduces_iff_successor p _).mp last
      simp only [loopPoints, List.mem_cons, List.not_mem_nil, or_false] at inside
      rcases inside with rfl | rfl | rfl | rfl
      · cases stepped
        exact ⟨.normal .succ (.fix .succ .halt) [0], List.mem_cons_of_mem _ List.mem_cons_self, rfl⟩
      · cases stepped
        exact ⟨.config (.ret (.fix .succ .halt) [1]),
          List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), rfl⟩
      · cases stepped
        exact ⟨.normal .succ (.fix .succ .halt) [],
          List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)), rfl⟩
      · cases stepped
        exact ⟨.config (.ret (.fix .succ .halt) [1]),
          List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), rfl⟩

/-- **The fixed point of the successor on `[0]` has no value.** -/
theorem loop_diverges : (Code.fix .succ).eval [0] = Part.none := by
  refine Part.eq_none_iff.mpr fun w member => ?_
  obtain ⟨p, inside, same⟩ := loop_closed ((adequacy _ _ w).mpr member)
  have isHalt := pattern_halt same.symm
  subst isHalt
  simp [loopPoints] at inside

/-- **Control: a code with an infinite run.** -/
theorem loop_infiniteRun : InfiniteRun (start (.fix .succ) [0]) :=
  infiniteRun_of_diverges _ _ loop_diverges

/-- **Control: a code with no infinite run.** -/
theorem succ_no_infiniteRun : ¬ InfiniteRun (start .succ [2]) := fun infinite => by
  have member := (halts_iff .succ [2] [3]).mp succ_two_halts
  rw [diverges_of_infiniteRun _ _ infinite] at member
  exact Part.notMem_none _ member

/-! ## The knowledge along a run -/

section Knowledge

open Interface (Frames)
open OneFrame (ext)

/-- **Every admitted firing of the nineteen-rule program adds one equation to the knowledge.** -/
theorem knowledge_length_after {s : SState ℕ} (g : Firing ℕ E {r | r ∈ program} s.frame)
    (admitted : (schematicStep ℕ program).Admits (s := s) g) :
    ((schematicStep ℕ program).result g admitted).knowledge.length = s.knowledge.length + 1 := by
  obtain ⟨-, ⟨-, -, takeLength, -, -, -⟩, -⟩ := (admits_iff g).mp admitted
  obtain ⟨n, -, isRule⟩ := List.mem_map.mp g.member
  have takeOne : g.rule.body.take.length = 1 := by rw [← isRule]; rfl
  have readZero : g.rule.body.read.length = 0 := by rw [← isRule]; rfl
  have tellZero : g.rule.body.tell.length = 0 := by rw [← isRule]; rfl
  have known : X.applyStore ((ext A).weaken g.ext) s.knowledge = s.knowledge :=
    Frames.applyStore_id (X := X) s.knowledge
  show (X.applyStore ((ext A).weaken g.ext) s.knowledge ++ g.matching X s (g.opened X).take g.selection.taken ++
    g.matching X s (g.opened X).read g.selection.read ++ (g.opened X).tell).length = _
  rw [known]
  unfold Firing.matching
  simp only [List.length_append, List.length_zipWith]
  have openedTake : (g.opened X).take.length = 1 := by
    show (g.rule.body.take.map _).length = 1
    rw [List.length_map, takeOne]
  have openedRead : (g.opened X).read.length = 0 := by
    show (g.rule.body.read.map _).length = 0
    rw [List.length_map, readZero]
  have openedTell : (g.opened X).tell.length = 0 := by
    show (g.rule.body.tell.map _).length = 0
    rw [List.length_map, tellZero]
  rw [openedTake, openedRead, openedTell, ← takeLength, takeOne]
  simp

/-- **Along every run from the start state, the `n`-th state has `n` equations of knowledge.** -/
theorem knowledge_length_along (c : Code) (v : List ℕ) (run : ℕ → SState ℕ) (atStart : run 0 = start c v)
    (steps : ∀ n, Succ (schematicStep ℕ program).toStep (run n) (run (n + 1))) :
    ∀ n, (run n).knowledge.length = n
  | 0 => by rw [atStart]; rfl
  | n + 1 => by
      obtain ⟨g, admitted, isNext⟩ := steps n
      rw [← isNext, knowledge_length_after g admitted, knowledge_length_along c v run atStart steps n]

/-- **Instance: the infinite run of `fix succ` on `[0]` reads as one row at every state and its knowledge
grows without bound.** -/
theorem loop_knowledge_unbounded :
    ∃ run : ℕ → SState ℕ, run 0 = start (.fix .succ) [0] ∧
      (∀ n, Succ (schematicStep ℕ program).toStep (run n) (run (n + 1))) ∧
      ∀ n, (run n).knowledge.length = n := by
  obtain ⟨run, atStart, steps⟩ := loop_infiniteRun
  exact ⟨run, atStart, steps, knowledge_length_along _ _ run atStart steps⟩

end Knowledge

#print axioms infiniteRun_iff_not_acc
#print axioms knowledge_length_after
#print axioms knowledge_length_along
#print axioms loop_knowledge_unbounded
#print axioms loop_diverges
#print axioms loop_infiniteRun
#print axioms succ_no_infiniteRun
#print axioms infiniteRun_of_diverges
#print axioms diverges_of_infiniteRun
#print axioms diverges_iff_infiniteRun
#print axioms halts_xor_infiniteRun

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Machines.InfiniteRuns
