import Mettapedia.OSLF.Framework.FormulaFixpoint
import Mettapedia.OSLF.Formula

/-!
# Reachability as a least fixpoint, and the tube shape as a formula

A shape is not a designation to be attached to a term from outside; it should
be a formula of the generated logic, satisfied or not by the term itself.  This
module does that for one shape, and the shape is chosen because stating it is
impossible without a fixpoint: it asks about *pathways*, not steps.

What is formalised is the *pathway condition* alone, over a pipe network: a
directed pathway from intake to expulsion, and no pathway back.  The first
conjunct is a least fixed point, and the second is proved by the induction
principle of that same fixed point.  Both halves are witnessed: one network is a
tube and one, differing by a single return pipe, is not.

**This is not the source material's tube shape**, and the distance should be
stated plainly.  That shape asks for a boundary namespace factoring as intake
and expulsion sub-namespaces of a reflective calculus, with a directed *redex*
pathway between them.  Here the stations are opaque names, the pipes are a list
given as a parameter rather than read off a term, and the step relation is
membership in that list rather than the calculus's own.  So the shape is
attached from outside, which is what a shape-as-formula is meant to avoid.

Two further cautions.  The source's criterion has three clauses — the agent
admits bulk material with a non-absorbable fraction, an occupancy ratio at or
above one, and a separability near zero — of which only the pathway condition
appears here.  And the source explicitly declines to state the no-return
condition absolutely, since observed return paths exist and a proposition that
forbids observed behaviour is worse than one that predicts it.  `IsTube` below
makes it a defining conjunct, which is the stronger reading.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.TubeShape

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.FormulaFixpoint

/-! ## Reachability -/

/-- The transformer whose least fixed point is "can reach the goal".

It is not a new transformer: it is the disjunction connective composed with the
step modality, both of which the fixpoint layer already supplies, so its
monotonicity is theirs and is not proved again here. -/
def reachStep (step : Pattern → Pattern → Prop) (goal : Pred) : Pred →o Pred :=
  comp (orWith goal) (diaOf step)

theorem reachStep_apply (step : Pattern → Pattern → Prop) (goal reached : Pred)
    (term : Pattern) :
    reachStep step goal reached term ↔
      goal term ∨ ∃ next, step term next ∧ reached next :=
  Iff.rfl

/-- "Some directed pathway leads from here to the goal." -/
def Reaches (step : Pattern → Pattern → Prop) (goal : Pred) : Pred :=
  lfp (reachStep step goal)

/-- Arriving is reaching. -/
theorem reaches_of_goal {step : Pattern → Pattern → Prop} {goal : Pred}
    {term : Pattern} (hgoal : goal term) : Reaches step goal term :=
  mem_lfp_of_mem_apply (Or.inl hgoal)

/-- One step towards something that reaches is reaching. -/
theorem reaches_of_step {step : Pattern → Pattern → Prop} {goal : Pred}
    {term next : Pattern} (hstep : step term next)
    (hreaches : Reaches step goal next) : Reaches step goal term :=
  mem_lfp_of_mem_apply (Or.inr ⟨next, hstep, hreaches⟩)

/-- **The induction principle for reachability.**  An invariant that holds of
the goal and is preserved backwards along steps holds of everything that
reaches the goal.  This is Knaster–Tarski's `lfp_le`, and it is how a *negative*
pathway claim is proved: exhibit an invariant the goal violates. -/
theorem reaches_induction {step : Pattern → Pattern → Prop} {goal invariant : Pred}
    (base : ∀ term, goal term → invariant term)
    (inductive_step : ∀ term next, step term next → invariant next → invariant term) :
    ∀ term, Reaches step goal term → invariant term := by
  have pre : (reachStep step goal) invariant ≤ invariant := by
    intro term
    rintro (hgoal | ⟨next, hstep, hinv⟩)
    · exact base term hgoal
    · exact inductive_step term next hstep hinv
  exact fun term member => lfp_le pre term member

/-! ## A pipe network -/

/-- A station of the network. -/
def stationAt (name : String) : Pattern := .apply "At" [.apply name []]

/-- Material moves along a declared pipe. -/
def pipeStep (network : List (String × String)) (source target : Pattern) : Prop :=
  ∃ from_ to_, (from_, to_) ∈ network ∧ source = stationAt from_ ∧ target = stationAt to_

theorem pipeStep_of_mem {network : List (String × String)} {from_ to_ : String}
    (member : (from_, to_) ∈ network) : pipeStep network (stationAt from_) (stationAt to_) :=
  ⟨from_, to_, member, rfl, rfl⟩

/-- Stations are distinguishable. -/
theorem stationAt_injective {first second : String} (equal : stationAt first = stationAt second) :
    first = second := by
  simpa [stationAt] using equal

/-! ## The shape -/

/-- The predicate naming one station. -/
def isAt (name : String) : Pred := fun term => term = stationAt name

/-- **The tube shape.**  A network is a tube between two stations when material
placed at the intake reaches the expulsion, and material at the expulsion
reaches the intake by no pathway at all. -/
def IsTube (network : List (String × String)) (intake expulsion : String) : Prop :=
  Reaches (pipeStep network) (isAt expulsion) (stationAt intake) ∧
    ¬ Reaches (pipeStep network) (isAt intake) (stationAt expulsion)

/-! ## The shape as a formula of the generated logic

The module's opening claim is that a shape should be a formula the term itself
satisfies, not a designation attached from outside.  Here is that formula.  It
is a generator, because the condition is about pathways rather than steps, and
it is the reason the formula language carries a binder at all.

What the formula does **not** do is fold the two halves of the tube condition
into one satisfaction: the pathway clause is about the intake and the no-return
clause is about the expulsion, so the shape is a pair of satisfactions at two
named stations.  That is a property of the condition, not of the formula
language.
-/

open Mettapedia.OSLF.Formula

/-- **The pathway formula**: a station reaches the goal when it is the goal, or
some pipe leads from it to a station that does.  Five nodes, and it does not
grow with the network. -/
def reachFormula (goal : String) : OSLFFormula :=
  .mu (.or (.atom goal) (.dia (.var 0)))

theorem reachFormula_size (goal : String) : (reachFormula goal).size = 5 := rfl

/-- The atoms are the stations. -/
def stationSem : AtomSem := fun name => isAt name

/-- **The formula's extension is reachability.**  Each direction is one of the
fixed point's two halves: the generator is below every pre-fixed point, and it
is itself one. -/
theorem sem_reachFormula_iff (network : List (String × String)) (goal : String)
    (term : Pattern) :
    sem (pipeStep network) stationSem (reachFormula goal) term ↔
      Reaches (pipeStep network) (isAt goal) term := by
  constructor
  · intro holds
    exact holds (Reaches (pipeStep network) (isAt goal)) trivial
      (fun _ step => mem_lfp_of_mem_apply step)
  · intro reaches candidate _ closed
    exact lfp_le (p := candidate) (fun t step => closed t step) term reaches

/-- **So the tube shape is stated in the logic.**  The pathway clause is the
formula satisfied at the intake, and the no-return clause is the same formula
for the other station, refuted at the expulsion. -/
theorem isTube_iff_sem (network : List (String × String)) (intake expulsion : String) :
    IsTube network intake expulsion ↔
      sem (pipeStep network) stationSem (reachFormula expulsion) (stationAt intake) ∧
        ¬ sem (pipeStep network) stationSem (reachFormula intake) (stationAt expulsion) := by
  rw [IsTube, sem_reachFormula_iff, sem_reachFormula_iff]

/-! ## A positive instance

Intake, a middle stage, expulsion. -/

namespace Positive

/-- Two pipes in series. -/
def network : List (String × String) := [("intake", "middle"), ("middle", "expulsion")]

theorem reaches_expulsion :
    Reaches (pipeStep network) (isAt "expulsion") (stationAt "intake") := by
  refine reaches_of_step
    (pipeStep_of_mem (from_ := "intake") (to_ := "middle") (by decide)) ?_
  refine reaches_of_step
    (pipeStep_of_mem (from_ := "middle") (to_ := "expulsion") (by decide)) ?_
  exact reaches_of_goal rfl

/-- Nothing leaves the expulsion, so the intake is unreachable from it.  The
invariant is "is the expulsion station", preserved backwards because no pipe
ends at the expulsion's predecessor set beyond the expulsion itself. -/
theorem no_return :
    ¬ Reaches (pipeStep network) (isAt "intake") (stationAt "expulsion") := by
  intro reaches
  have invariant : ∀ term, Reaches (pipeStep network) (isAt "intake") term →
      term ≠ stationAt "expulsion" := by
    refine reaches_induction (invariant := fun term => term ≠ stationAt "expulsion") ?_ ?_
    · intro term hgoal
      rw [show term = stationAt "intake" from hgoal]
      intro equal
      exact absurd (stationAt_injective equal) (by decide)
    · intro term next hstep _
      obtain ⟨from_, to_, member, hsource, _⟩ := hstep
      subst hsource
      intro equal
      have : from_ = "expulsion" := stationAt_injective equal
      subst this
      simp [network] at member
  exact invariant (stationAt "expulsion") reaches rfl

theorem isTube : IsTube network "intake" "expulsion" :=
  ⟨reaches_expulsion, no_return⟩

end Positive

/-! ## A negative instance

The same network with one return pipe added.  Every other feature is
unchanged, so the failure is attributable to the return path alone. -/

namespace Negative

/-- The series, plus a pipe from the expulsion back to the intake. -/
def network : List (String × String) :=
  [("intake", "middle"), ("middle", "expulsion"), ("expulsion", "intake")]

theorem reaches_expulsion :
    Reaches (pipeStep network) (isAt "expulsion") (stationAt "intake") := by
  refine reaches_of_step
    (pipeStep_of_mem (from_ := "intake") (to_ := "middle") (by decide)) ?_
  refine reaches_of_step
    (pipeStep_of_mem (from_ := "middle") (to_ := "expulsion") (by decide)) ?_
  exact reaches_of_goal rfl

/-- The return pipe is a pathway back, so the second conjunct fails. -/
theorem returns :
    Reaches (pipeStep network) (isAt "intake") (stationAt "expulsion") := by
  refine reaches_of_step
    (pipeStep_of_mem (from_ := "expulsion") (to_ := "intake") (by decide)) ?_
  exact reaches_of_goal rfl

/-- Hence this network is not a tube, though it still delivers. -/
theorem not_isTube : ¬ IsTube network "intake" "expulsion" := by
  rintro ⟨_, noReturn⟩
  exact noReturn returns

end Negative

/-- **The positive network satisfies the formula at its intake**, and the
negative one satisfies the return formula at its expulsion.  Both read through
`sem`, so the separation is a separation *in the logic*. -/
theorem formula_separates :
    sem (pipeStep Positive.network) stationSem (reachFormula "expulsion")
        (stationAt "intake") ∧
      ¬ sem (pipeStep Positive.network) stationSem (reachFormula "intake")
        (stationAt "expulsion") ∧
      sem (pipeStep Negative.network) stationSem (reachFormula "intake")
        (stationAt "expulsion") :=
  ⟨(sem_reachFormula_iff _ _ _).mpr Positive.reaches_expulsion,
    fun holds => Positive.no_return ((sem_reachFormula_iff _ _ _).mp holds),
    (sem_reachFormula_iff _ _ _).mpr Negative.returns⟩

/-- The two instances differ by one pipe, and the shape separates them. -/
theorem tube_separates :
    IsTube Positive.network "intake" "expulsion" ∧
      ¬ IsTube Negative.network "intake" "expulsion" :=
  ⟨Positive.isTube, Negative.not_isTube⟩

end Mettapedia.OSLF.Framework.TubeShape
