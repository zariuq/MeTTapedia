import Mettapedia.GSLT.Logic.HennessyMilnerAdequacy

/-!
# A counterexample to unconditional finitary HML adequacy

Every direction of the Hennessy-Milner correspondence that goes from logic back
to behaviour is proved here under the hypothesis that each state has finitely
many successor classes under each label.  The hypothesis appears in ten
statements and nothing shows it is doing work, which leaves open the reading that
it is a convenience of the proof rather than a fact about the theorem.

It is not.  This module exhibits a system in which two states satisfy exactly
the same formulas of the full fragment and are not bisimilar, so the
correspondence fails outright once the hypothesis is dropped.

The obstruction is the one the modal language cannot see past: every formula has
a finite modal depth, so no formula can distinguish a state that steps forever
from one that steps exactly as many times as that formula can look.  A state
whose successors include arbitrarily long finite chains therefore satisfies the
same formulas as one whose successors include the infinite chain as well, while
the infinite chain has no bisimilar partner among the finite ones.

This disproves the unrestricted uniform converse for generic transition
systems. Image-finiteness is a sufficient hypothesis, not a necessary condition
for every individual adequate system. No theorem here realizes this example
with the source's full minimal-context and higher-order-label hypotheses, so it
does not refute that stronger source-specific statement.
-/

namespace Mettapedia.GSLT.HennessyMilner

set_option autoImplicit false

namespace ImageFinitenessNecessary

/-- Four kinds of state: the two candidates, the chains of each finite length,
and the chain that never stops. -/
inductive St where
  | left
  | right
  | chain (n : Nat)
  | endless
  deriving DecidableEq

/-- `left` branches to every finite chain; `right` branches to those and to the
endless one; a chain of length `n+1` steps to one of length `n`; the endless
chain steps to itself. -/
inductive Step : St → St → Prop where
  | leftChain (n : Nat) : Step .left (.chain n)
  | rightChain (n : Nat) : Step .right (.chain n)
  | rightEndless : Step .right .endless
  | chainDown (n : Nat) : Step (.chain (n + 1)) (.chain n)
  | endlessLoop : Step .endless .endless

/-- The theory: states up to equality, with that step relation. -/
def sys : GSLT where
  Term := St
  equations := ⟨Eq, ⟨fun _ => rfl, Eq.symm, Eq.trans⟩⟩
  rewrites := Step
  rewrites_resp_left := by
    intro t t' u he h
    exact ⟨u, he ▸ h, rfl⟩
  rewrites_resp_right := by
    intro t u u' h he
    exact he ▸ h

/-- One label, no atomic observations: the separation is to be the modality's
work alone, so nothing else is given to it. -/
def hm : System.{0, 0} sys where
  Atom := Empty
  observes := fun a _ => a.elim
  observes_resp := by intro a; exact a.elim
  Label := Unit
  act := fun _ => Step
  act_resp_left := by
    intro _ t t' u he h
    exact ⟨u, he ▸ h, rfl⟩
  act_resp_right := by
    intro _ t u u' h he
    exact he ▸ h

/-! ## The modal depth of a formula -/

/-- How far a formula can look. -/
def depth : Formula hm.Atom hm.Label → Nat
  | .top => 0
  | .atom _ => 0
  | .conj l r => max (depth l) (depth r)
  | .neg i => depth i
  | .dia _ i => depth i + 1

/-- **No formula can see past its own depth.**  A chain at least as long as the
formula can look satisfies exactly what the endless chain satisfies. -/
theorem agree : ∀ (f : Formula hm.Atom hm.Label) (n : Nat), depth f ≤ n →
    (hm.sat f St.endless ↔ hm.sat f (St.chain n))
  | .top, _, _ => Iff.rfl
  | .atom a, _, _ => a.elim
  | .conj l r, n, hle => by
      have hl : depth l ≤ n := le_trans (le_max_left _ _) hle
      have hr : depth r ≤ n := le_trans (le_max_right _ _) hle
      exact and_congr (agree l n hl) (agree r n hr)
  | .neg i, n, hle => not_congr (agree i n hle)
  | .dia _ i, n, hle => by
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := by
        cases n with
        | zero => exact absurd hle (by simp [depth])
        | succ m => exact ⟨m, rfl⟩
      have hi : depth i ≤ m := Nat.le_of_succ_le_succ hle
      constructor
      · rintro ⟨target, hstep, hsat⟩
        cases hstep
        exact ⟨St.chain m, Step.chainDown m, (agree i m hi).mp hsat⟩
      · rintro ⟨target, hstep, hsat⟩
        cases hstep
        exact ⟨St.endless, Step.endlessLoop, (agree i m hi).mpr hsat⟩

/-! ## The two candidates satisfy the same formulas -/

theorem logically_equivalent : hm.LogicallyEquivalent St.left St.right := by
  intro f
  induction f with
  | top => exact Iff.rfl
  | atom a => exact a.elim
  | conj _ _ ihl ihr => exact and_congr ihl ihr
  | neg _ ih => exact not_congr ih
  | dia _ i _ =>
      constructor
      · rintro ⟨target, hstep, hsat⟩
        cases hstep with
        | leftChain n => exact ⟨St.chain n, Step.rightChain n, hsat⟩
      · rintro ⟨target, hstep, hsat⟩
        cases hstep with
        | rightChain n => exact ⟨St.chain n, Step.leftChain n, hsat⟩
        | rightEndless =>
            exact ⟨St.chain (depth i), Step.leftChain (depth i),
              (agree i (depth i) (Nat.le_refl _)).mp hsat⟩

/-! ## They are not bisimilar -/

/-- How many steps a state is guaranteed to be able to take. -/
def Runs : Nat → St → Prop
  | 0, _ => True
  | k + 1, s => ∃ t, Step s t ∧ Runs k t

theorem runs_endless : ∀ k, Runs k St.endless
  | 0 => trivial
  | k + 1 => ⟨St.endless, Step.endlessLoop, runs_endless k⟩

theorem not_runs_chain : ∀ (n : Nat), ¬ Runs (n + 1) (St.chain n)
  | 0 => by
      rintro ⟨t, hstep, -⟩
      cases hstep
  | n + 1 => by
      rintro ⟨t, hstep, hruns⟩
      cases hstep
      exact not_runs_chain n hruns

/-- A bisimulation preserves how long a state can run, read from the right. -/
theorem runs_of_bisim {R : St → St → Prop} (hR : hm.IsBisimulation R) :
    ∀ (k : Nat) {s t : St}, R s t → Runs k t → Runs k s
  | 0, _, _, _, _ => trivial
  | k + 1, _, _, hst, ⟨t', hstep, hruns⟩ => by
      obtain ⟨s', hstep', hrel⟩ := hR.2.1 hst () hstep
      exact ⟨s', hstep', runs_of_bisim hR k hrel hruns⟩

/-- **The two candidates are not bisimilar.**  The step to the endless chain has
no match: every successor of `left` is a chain of some finite length, and no
finite chain runs as long as the endless one. -/
theorem not_bisimilar : ¬ hm.Bisimilar St.left St.right := by
  rintro ⟨R, hR, hLR⟩
  obtain ⟨t, hstep, hrel⟩ := hR.2.1 hLR () Step.rightEndless
  cases hstep with
  | leftChain n =>
      exact not_runs_chain n (runs_of_bisim hR (n + 1) hrel (runs_endless (n + 1)))

/-! ## And the system is not image-finite -/

theorem chain_injective {m n : Nat} (h : St.chain m = St.chain n) : m = n := by
  injection h

/-- **The hypothesis fails here**, which is what makes the counterexample a
counterexample to dropping it rather than to the theorem. -/
theorem not_imageFinite : ¬ hm.ImageFiniteModulo := by
  intro hfin
  obtain ⟨reps, hrepsFin, hrep⟩ := hfin () St.left
  have hsub : Set.range (fun n : Nat => St.chain n) ⊆ reps := by
    rintro _ ⟨n, rfl⟩
    obtain ⟨r, hmem, heq⟩ := hrep (Step.leftChain n)
    have heq' : St.chain n = r := heq
    show St.chain n ∈ reps
    exact heq' ▸ hmem
  have hinj : Function.Injective (fun n : Nat => St.chain n) := fun _ _ h =>
    chain_injective h
  exact (Set.infinite_range_of_injective hinj) (hrepsFin.subset hsub)

/-- **Adequacy fails without image-finiteness.**  Two states of one system that
satisfy exactly the same formulas of the full fragment and are not bisimilar,
in a system where the hypothesis does not hold.  So the hypothesis is not a
convenience of the proof. -/
theorem adequacy_needs_image_finiteness :
    hm.LogicallyEquivalent St.left St.right
      ∧ ¬ hm.Bisimilar St.left St.right
      ∧ ¬ hm.ImageFiniteModulo :=
  ⟨logically_equivalent, not_bisimilar, not_imageFinite⟩

/-! ### Positive control

The theorem itself is not vacuous where the hypothesis holds: a state is
bisimilar to itself, and logically equivalent to itself, with no finiteness
needed for that direction. -/

theorem bisimilar_refl_here (s : St) : hm.Bisimilar s s := by
  refine ⟨Eq, ⟨?_, ?_, ?_⟩, rfl⟩
  · intro a b hab _ a' hs
    subst hab
    exact ⟨a', hs, rfl⟩
  · intro a b hab _ b' hs
    subst hab
    exact ⟨b', hs, rfl⟩
  · intro _ _ _ atom
    exact atom.elim

end ImageFinitenessNecessary

end Mettapedia.GSLT.HennessyMilner
