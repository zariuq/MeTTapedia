/-
# The congruence is a declared observer

Correctness for a translation into these combinators is stated relative to a
restricted class of observers — the contexts in the image of the translation.
The question this file answers is whether that restriction is a new notion or an
instance of the observation-indexed admission discipline already in use.

It is an instance, and the identification is exact rather than analogical.
`LawfulAt` asks that a declared observer see no difference between a
transformation's source and target. The structural congruence of this calculus
is precisely lawfulness at the observer that reports a soup's component bag:

```
    Cong p q  ↔  LawfulAt soupObserver (rearrangement p q)
```

Two consequences follow without further work. The reactive-system reading
factors through the observer — `agent` is constant on congruence classes, so its
transitions are transitions of observations rather than of terms. And coarsening
the observer can only enlarge the set of lawful transformations, by
postcomposition; so a correctness notion restricted to encoded contexts inherits
everything proved for full component observation.

The scope boundary of the mechanized congruence becomes a canary rather than a
caveat: an atom's arguments are *visible* to this observer, which is why the
relation is closed under parallel composition and not under atom constructors.
That is a fact about what the observer resolves, and it is recorded here as a
negative control beside the positive one.

What is **owed**: the interesting half of the restriction is that it should buy
something — that there are transformations lawful for encoded contexts and not
for arbitrary ones. Exhibiting one needs the translation, and the general
direction proved below is the cheap half.
-/
import Mettapedia.Languages.ProcessCalculi.RhoCombinators.ReactiveSystem
import Mettapedia.Languages.ProcessCalculi.RhoCombinators.CongruenceScope
import Mettapedia.GSLT.Core.ObservationIndexedPruning

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCombinators

open Mettapedia.Cybernetics
open Mettapedia.GSLT.Core.ObservationIndexedPruning
open Mettapedia.GSLT.BagRelativePushout (bag)
open Comb

/-! ## The observer -/

/-- What a parallel context can observe of a soup: its component bag.  Order is
not observable, multiplicity is. -/
def soupObserver : Observer (List Comb) (Multiset Comb) where
  observe atoms := (atoms : Multiset Comb)

/-- A rearrangement of one soup into another, presented to the discipline as a
change over the atoms each one is made of. -/
def rearrangement (p q : Comb) : Change Comb Unit where
  source := componentList p
  target := componentList q
  receipt := ()

/-! ## The identification -/

/-- **Structural congruence is lawfulness at the component observer.**  The
congruence of this calculus is not an extra equivalence imposed on top of the
syntax; it is exactly the kernel of a declared observation. -/
theorem cong_iff_lawful (p q : Comb) :
    Cong p q ↔ LawfulAt soupObserver (rearrangement p q) := by
  simp only [LawfulAt, soupObserver, rearrangement]
  constructor
  · intro h
    rw [← components_eq_coe, ← components_eq_coe]
    exact cong_components h
  · intro h
    refine cong_of_components ?_
    rw [components_eq_coe, components_eq_coe]
    exact h

/-- **The reactive-system reading factors through the observer.**  Agents are
component bags, so congruent soups are the same agent and the labelled
transitions are transitions of observations. -/
theorem agent_eq_of_cong {p q : Comb} (h : Cong p q) : agent p = agent q :=
  congrArg bag (cong_components h)

/-- Reduction only ever relates observations: congruent sources have the same
transitions. -/
theorem step_iff_of_cong {p q p' q' : Comb} (hp : Cong p q) (hp' : Cong p' q') :
    Step Cong p p' ↔ Step Cong q q' :=
  ⟨fun h => Step.congruent (Cong.symm hp) h hp',
    fun h => Step.congruent hp h (Cong.symm hp')⟩

/-! ## Controls -/

/-- Positive control: commuting two parallel components is invisible. -/
theorem parComm_lawful (p q : Comb) :
    LawfulAt soupObserver (rearrangement (par p q) (par q p)) :=
  (cong_iff_lawful _ _).mp (Cong.parComm p q)

/-- Positive control: discarding a unit is invisible. -/
theorem parNil_lawful (p : Comb) :
    LawfulAt soupObserver (rearrangement (par p nil) p) :=
  (cong_iff_lawful _ _).mp (Cong.parNil p)

/-- **Negative control: an atom's arguments are visible.**  Rewriting inside a
name position changes what this observer reports, so the congruence is closed
under parallel composition and not under atom constructors.  That is a
statement about the observer's resolution, and it is why results proved with
this relation do not silently assume a coarser one. -/
theorem atom_argument_not_lawful :
    ¬ LawfulAt soupObserver (rearrangement (kk (par nil nil)) (kk nil)) := fun lawful =>
  components_not_invariant_under_atom_closure
    (cong_components ((cong_iff_lawful _ _).mpr lawful))

/-! ## Restricting the observer -/

/-- A guard that accepts exactly the rearrangements its observer cannot see.
Soundness is immediate, which is the point: the certificate a guard needs is
component equality, and nothing weaker is being smuggled in as one. -/
def componentGuard : Guard soupObserver Unit where
  accepts change := LawfulAt soupObserver change
  sound _ accepted := accepted

/-- The guard declines a change that alters an atom's argument. -/
theorem componentGuard_rejects_atom_argument :
    ¬ componentGuard.accepts (rearrangement (kk (par nil nil)) (kk nil)) :=
  Guard.rejects_of_not_lawful componentGuard _ atom_argument_not_lawful

/-- **Restricting the observer class is a postcomposition.**  Any coarser
observation of a soup — in particular, whatever a restricted class of contexts
can report — is the component observer followed by a summary, so every
transformation lawful for full component observation remains lawful under the
restriction.  This is the sense in which correctness relative to encoded
contexts is an instance of the admission discipline and not a parallel notion. -/
theorem lawful_under_restricted_observation {Coarse : Type}
    (summarize : Multiset Comb → Coarse) {change : Change Comb Unit}
    (lawful : LawfulAt soupObserver change) :
    LawfulAt (soupObserver.postcompose summarize) change :=
  lawfulAt_postcompose soupObserver summarize lawful

/-- The same, for the congruence directly: congruent soups are indistinguishable
to every coarsening of the component observer. -/
theorem restricted_observation_of_cong {Coarse : Type}
    (summarize : Multiset Comb → Coarse) {p q : Comb} (h : Cong p q) :
    LawfulAt (soupObserver.postcompose summarize) (rearrangement p q) :=
  lawful_under_restricted_observation summarize ((cong_iff_lawful p q).mp h)

end Mettapedia.Languages.ProcessCalculi.RhoCombinators
