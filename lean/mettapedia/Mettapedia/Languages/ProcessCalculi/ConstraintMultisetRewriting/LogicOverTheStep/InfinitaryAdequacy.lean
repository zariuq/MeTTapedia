import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.ProgramAdequacy
import Mettapedia.GSLT.Logic.ImageFinitenessNecessary

/-!
# Adequacy without covers: infinitary conjunctions, and one greatest fixed point

Finitary Hennessy–Milner adequacy needs finite covers of successor sets
(`ProgramAdequacy`), and the unrestricted first-order step has none
(`ProgramAdequacy.base_not_imageFiniteBisimilar`). Two other mechanisms are compared here, over
the tree's Hennessy–Milner systems (`Mettapedia.GSLT.HennessyMilner.System`), with their own
diamond, which over the step is OSLF's possibility over firings (`isat_dia_iff`).

## Infinitary conjunctions

`IFormula` allows conjunctions indexed by any type of the terms' universe. Then:

* `isat_iff_of_isBisimulation`: bisimulations preserve every infinitary formula;
* **`iequivalent_iff_bisimilar`**: infinitary logical equivalence is bisimilarity on **every**
  system, with no branching hypothesis: the conjunction ranges over the actual successors;
* `isat_ofFinitary`: the finitary formulas embed with their satisfaction, so infinitary
  equivalence implies finitary equivalence (`logicallyEquivalent_of_iequivalent`);
* on the step: `step_iequivalent_iff_bisimilar` for every step and observation set, and
  `base_iequivalent_iff_bisimilar` on the unrestricted ground first-order step.
* **Control** (`infinitary_separates_tree_counterexample`): on the tree's counterexample
  (`ImageFinitenessNecessary`) two states satisfy the same finitary formulas, are not bisimilar,
  and an infinitary formula separates them.

## One greatest fixed point

`Endless`, an infinite run, is `νX.◇X`: the greatest post-fixed point of possibility
(`endless_le_diamond`, `le_endless`). It is invariant under bisimulations
(`endless_of_isBisimulation`), and it separates the same two states of the tree's counterexample
(`endless_separates`), which no finitary formula does. A modal μ-calculus therefore sees past the
depth bound of finitary formulas; adequacy of the full μ-calculus on the unrestricted step is not
claimed here.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.InfinitaryAdequacy

open Mettapedia.GSLT Mettapedia.GSLT.HennessyMilner
open Mettapedia.OSLF.Framework.DerivedModalities
open FragmentsOfTheStep.TransitionMaps
open StepSpan

universe u uAtom uLabel uO uT uH uOcc uS uF

/-- **Infinitary formulas**: atoms, negation, the labelled diamond, and conjunctions indexed by any
type of universe `v`. -/
inductive IFormula.{v, w, x} (Atom : Type w) (Label : Type x) : Type (max w x (v + 1)) where
  | atom (atom : Atom)
  | conj {Index : Type v} (parts : Index → IFormula Atom Label)
  | neg (inner : IFormula Atom Label)
  | dia (label : Label) (inner : IFormula Atom Label)

section Systems

variable {S : GSLT.{u}} (M : System.{uAtom, uLabel} S)

/-- Satisfaction. -/
def isat : IFormula.{u, uAtom, uLabel} M.Atom M.Label → S.Term → Prop
  | .atom a, t => M.observes a t
  | .conj parts, t => ∀ i, isat (parts i) t
  | .neg inner, t => ¬ isat inner t
  | .dia l inner, t => ∃ t', M.act l t t' ∧ isat inner t'

/-- **Bisimulations preserve every infinitary formula.** -/
theorem isat_iff_of_isBisimulation {R : S.Term → S.Term → Prop} (bisimulation : M.IsBisimulation R) :
    ∀ (φ : IFormula.{u, uAtom, uLabel} M.Atom M.Label) {x y : S.Term}, R x y →
      (isat M φ x ↔ isat M φ y)
  | .atom a, _, _, related => bisimulation.2.2 related a
  | .conj parts, _, _, related =>
      forall_congr' fun i => isat_iff_of_isBisimulation bisimulation (parts i) related
  | .neg inner, _, _, related => not_congr (isat_iff_of_isBisimulation bisimulation inner related)
  | .dia l inner, _, _, related => by
      constructor
      · rintro ⟨x', step, holds⟩
        obtain ⟨y', step', related'⟩ := bisimulation.1 related l step
        exact ⟨y', step', (isat_iff_of_isBisimulation bisimulation inner related').mp holds⟩
      · rintro ⟨y', step, holds⟩
        obtain ⟨x', step', related'⟩ := bisimulation.2.1 related l step
        exact ⟨x', step', (isat_iff_of_isBisimulation bisimulation inner related').mpr holds⟩

/-- Infinitary logical equivalence. -/
def IEquivalent (x y : S.Term) : Prop :=
  ∀ φ : IFormula.{u, uAtom, uLabel} M.Atom M.Label, isat M φ x ↔ isat M φ y

theorem exists_separating {x y : S.Term} (inequivalent : ¬ IEquivalent M x y) :
    ∃ φ : IFormula.{u, uAtom, uLabel} M.Atom M.Label, isat M φ x ∧ ¬ isat M φ y := by
  obtain ⟨φ, disagree⟩ := not_forall.mp inequivalent
  by_cases holds : isat M φ x
  · exact ⟨φ, holds, fun other => disagree ⟨fun _ => other, fun _ => holds⟩⟩
  · exact ⟨.neg φ, holds, fun notThere =>
      disagree ⟨fun here => absurd here holds, fun there => absurd there notThere⟩⟩

/-- **A matching step**: the conjunction over the actual successors of one side separates. -/
theorem matching_step {x y : S.Term} (equivalent : IEquivalent M x y) (l : M.Label) {x' : S.Term}
    (step : M.act l x x') : ∃ y', M.act l y y' ∧ IEquivalent M x' y' := by
  by_contra none
  have separate : ∀ i : {y' // M.act l y y'},
      ∃ φ : IFormula.{u, uAtom, uLabel} M.Atom M.Label, isat M φ x' ∧ ¬ isat M φ i.1 :=
    fun i => exists_separating M fun same => none ⟨i.1, i.2, same⟩
  choose δ holds fails using separate
  have here : isat M (.dia l (.conj δ)) x := ⟨x', step, holds⟩
  obtain ⟨y', step', all⟩ := (equivalent (.dia l (.conj δ))).mp here
  exact fails ⟨y', step'⟩ (all ⟨y', step'⟩)

theorem iequivalent_isBisimulation : M.IsBisimulation (IEquivalent M) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x y equivalent l x' step
    exact matching_step M equivalent l step
  · intro x y equivalent l y' step
    obtain ⟨x', step', equivalent'⟩ := matching_step M (fun φ => (equivalent φ).symm) l step
    exact ⟨x', step', fun φ => (equivalent' φ).symm⟩
  · intro x y equivalent a
    exact equivalent (.atom a)

/-- **Infinitary adequacy, on every system**: no branching hypothesis. -/
theorem iequivalent_iff_bisimilar (x y : S.Term) : IEquivalent M x y ↔ M.Bisimilar x y := by
  constructor
  · intro equivalent
    exact ⟨IEquivalent M, iequivalent_isBisimulation M, equivalent⟩
  · rintro ⟨R, bisimulation, related⟩ φ
    exact isat_iff_of_isBisimulation M bisimulation φ related

/-- The finitary formulas, as infinitary ones. -/
def ofFinitary {Atom : Type uAtom} {Label : Type uLabel} :
    Formula Atom Label → IFormula.{u, uAtom, uLabel} Atom Label
  | .top => .conj (Index := PEmpty.{u + 1}) fun i => i.elim
  | .atom a => .atom a
  | .conj l r => .conj (Index := ULift.{u} Bool) fun i => bif i.down then ofFinitary l else ofFinitary r
  | .neg inner => .neg (ofFinitary inner)
  | .dia l inner => .dia l (ofFinitary inner)

/-- **The finitary formulas embed with their satisfaction.** -/
theorem isat_ofFinitary : ∀ (φ : Formula M.Atom M.Label) (t : S.Term),
    isat M (ofFinitary.{u} φ) t ↔ M.sat φ t
  | .top, _ => ⟨fun _ => trivial, fun _ i => i.elim⟩
  | .atom _, _ => Iff.rfl
  | .conj l r, t => by
      constructor
      · intro all
        exact ⟨(isat_ofFinitary l t).mp (all ⟨true⟩), (isat_ofFinitary r t).mp (all ⟨false⟩)⟩
      · rintro ⟨first, second⟩ ⟨b⟩
        cases b
        · exact (isat_ofFinitary r t).mpr second
        · exact (isat_ofFinitary l t).mpr first
  | .neg inner, t => not_congr (isat_ofFinitary inner t)
  | .dia l inner, t => exists_congr fun t' => and_congr_right fun _ => isat_ofFinitary inner t'

/-- Infinitary equivalence implies finitary equivalence. -/
theorem logicallyEquivalent_of_iequivalent {x y : S.Term} (equivalent : IEquivalent M x y) :
    M.LogicallyEquivalent x y :=
  fun φ => (isat_ofFinitary M φ x).symm.trans ((equivalent (ofFinitary φ)).trans (isat_ofFinitary M φ y))

/-! ## One greatest fixed point -/

/-- **An infinite run**: `νX.◇X`. -/
def Endless (l : M.Label) (x : S.Term) : Prop :=
  ∃ run : ℕ → S.Term, run 0 = x ∧ ∀ n, M.act l (run n) (run (n + 1))

/-- It is a post-fixed point of possibility. -/
theorem endless_le_diamond (l : M.Label) {x : S.Term} (endless : Endless M l x) :
    ∃ x', M.act l x x' ∧ Endless M l x' := by
  obtain ⟨run, start, steps⟩ := endless
  exact ⟨run 1, start ▸ steps 0, fun n => run (n + 1), rfl, fun n => steps (n + 1)⟩

/-- **It is the greatest one**: every post-fixed point of possibility has infinite runs. -/
theorem le_endless (l : M.Label) (X : S.Term → Prop) (post : ∀ x, X x → ∃ x', M.act l x x' ∧ X x')
    {x : S.Term} (holds : X x) : Endless M l x := by
  choose next step stays using post
  let run : ℕ → {y // X y} := fun n => Nat.rec ⟨x, holds⟩ (fun _ y => ⟨next y.1 y.2, stays y.1 y.2⟩) n
  exact ⟨fun n => (run n).1, rfl, fun n => step (run n).1 (run n).2⟩

/-- **It is invariant under bisimulations.** -/
theorem endless_of_isBisimulation {R : S.Term → S.Term → Prop} (bisimulation : M.IsBisimulation R)
    (l : M.Label) {x y : S.Term} (related : R x y) (endless : Endless M l x) : Endless M l y := by
  refine le_endless M l (fun y => ∃ x, R x y ∧ Endless M l x) ?_ ⟨x, related, endless⟩
  rintro y ⟨x, related, endless⟩
  obtain ⟨x', step, endless'⟩ := endless_le_diamond M l endless
  obtain ⟨y', step', related'⟩ := bisimulation.1 related l step
  exact ⟨y', step', x', related', endless'⟩

end Systems

/-! ## Over the step -/

section Step

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH} {X : Interface.Frames Tm Hom}
  {O : Type uOcc} [DecidableEq O] {State : Type uS} {Firing : State → Type uF}
  (P : Interface.Step X O State Firing) {Atom : Type} (observes : Atom → State → Prop)

/-- **The infinitary diamond over the step is OSLF's possibility over its firings.** -/
theorem isat_dia_iff (φ : IFormula.{uS, 0, 0} (stepSystem P observes).Atom (stepSystem P observes).Label)
    (s : State) :
    isat (stepSystem P observes) (.dia () φ) s ↔
      derivedDiamond (firingSpan P) (isat (stepSystem P observes) φ) s := by
  constructor
  · rintro ⟨t, step, holds⟩
    exact (congrFun (firing_diamond_eq P _) s).mpr ((diamond_iff _ _ _).mpr ⟨t, step, holds⟩)
  · intro holds
    obtain ⟨t, step, there⟩ := (diamond_iff _ _ _).mp ((congrFun (firing_diamond_eq P _) s).mp holds)
    exact ⟨t, step, there⟩

/-- **Infinitary adequacy for every step**, with every observation set. -/
theorem step_iequivalent_iff_bisimilar (left right : State) :
    IEquivalent (stepSystem P observes) left right ↔ (stepSystem P observes).Bisimilar left right :=
  iequivalent_iff_bisimilar (stepSystem P observes) left right

end Step

/-- **On the unrestricted ground first-order step**, where finite covers fail, infinitary
equivalence is bisimilarity. -/
theorem base_iequivalent_iff_bisimilar (left right : NamesOnTheStep.IssuingControls.Conf) :
    IEquivalent (stepSystem NamesOnTheStep.IssuingControls.base ProgramAdequacy.storeView) left right ↔
      (stepSystem NamesOnTheStep.IssuingControls.base ProgramAdequacy.storeView).Bisimilar left right :=
  iequivalent_iff_bisimilar (stepSystem NamesOnTheStep.IssuingControls.base ProgramAdequacy.storeView)
    left right

/-! ## Controls on the tree's counterexample -/

section Controls

open ImageFinitenessNecessary

/-- **Control: the infinitary logic separates what the finitary logic cannot.** -/
theorem infinitary_separates_tree_counterexample :
    hm.LogicallyEquivalent St.left St.right ∧ ¬ hm.Bisimilar St.left St.right ∧
      ∃ φ : IFormula.{0, 0, 0} hm.Atom hm.Label, isat hm φ St.left ∧ ¬ isat hm φ St.right := by
  refine ⟨logically_equivalent, not_bisimilar, ?_⟩
  apply exists_separating
  intro equivalent
  exact not_bisimilar ((iequivalent_iff_bisimilar hm St.left St.right).mp equivalent)

/-- The endless chain runs forever. -/
theorem endless_right : Endless hm () St.right :=
  le_endless hm () (fun s => s = St.right ∨ s = St.endless)
    (by
      rintro s (rfl | rfl)
      · exact ⟨St.endless, ImageFinitenessNecessary.Step.rightEndless, Or.inr rfl⟩
      · exact ⟨St.endless, ImageFinitenessNecessary.Step.endlessLoop, Or.inr rfl⟩)
    (Or.inl rfl)

theorem step_from_chain {j : ℕ} {t : St} (step : ImageFinitenessNecessary.Step (St.chain (j + 1)) t) :
    t = St.chain j := by
  cases step
  rfl

theorem no_step_from_zero (t : St) : ¬ ImageFinitenessNecessary.Step (St.chain 0) t := by
  intro step
  cases step

/-- From a chain, every run descends. -/
theorem chain_descends (run : ℕ → St) (steps : ∀ n, hm.act () (run n) (run (n + 1))) (m : ℕ) :
    ∀ k, k ≤ m → run 0 = St.chain m → run k = St.chain (m - k) := by
  intro k
  induction k with
  | zero => intro _ start; simpa using start
  | succ k ih =>
      intro bound start
      have here := ih (Nat.le_of_succ_le bound) start
      have step : ImageFinitenessNecessary.Step (run k) (run (k + 1)) := steps k
      rw [here] at step
      obtain ⟨j, hj⟩ : ∃ j, m - k = j + 1 := ⟨m - k - 1, by omega⟩
      rw [hj] at step
      rw [step_from_chain step, show m - (k + 1) = j by omega]

/-- **No run from `left` is endless**: it enters a finite chain and stops. -/
theorem not_endless_left : ¬ Endless hm () St.left := by
  rintro ⟨run, start, steps⟩
  have first : ImageFinitenessNecessary.Step St.left (run 1) := start ▸ steps 0
  cases hfirst : run 1 with
  | chain n =>
      have descends := chain_descends (fun k => run (k + 1)) (fun k => steps (k + 1)) n n le_rfl hfirst
      have stuck : ImageFinitenessNecessary.Step (run (n + 1)) (run (n + 1 + 1)) := steps (n + 1)
      simp only [Nat.sub_self] at descends
      rw [descends] at stuck
      exact no_step_from_zero _ stuck
  | left => rw [hfirst] at first; cases first
  | right => rw [hfirst] at first; cases first
  | endless => rw [hfirst] at first; cases first

/-- **Control: one greatest fixed point separates the counterexample** that finitary formulas do
not. -/
theorem endless_separates :
    hm.LogicallyEquivalent St.left St.right ∧ Endless hm () St.right ∧ ¬ Endless hm () St.left :=
  ⟨logically_equivalent, endless_right, not_endless_left⟩

end Controls

#print axioms isat_iff_of_isBisimulation
#print axioms matching_step
#print axioms iequivalent_isBisimulation
#print axioms iequivalent_iff_bisimilar
#print axioms isat_ofFinitary
#print axioms logicallyEquivalent_of_iequivalent
#print axioms endless_le_diamond
#print axioms le_endless
#print axioms endless_of_isBisimulation
#print axioms isat_dia_iff
#print axioms step_iequivalent_iff_bisimilar
#print axioms base_iequivalent_iff_bisimilar
#print axioms infinitary_separates_tree_counterexample
#print axioms endless_right
#print axioms not_endless_left
#print axioms endless_separates

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.InfinitaryAdequacy
