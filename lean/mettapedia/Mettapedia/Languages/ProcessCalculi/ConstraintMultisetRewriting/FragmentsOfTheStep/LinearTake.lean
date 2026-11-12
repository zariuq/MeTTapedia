import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.GroundFirings

/-!
# Linear take: monotone under union, and independent firings interchange

A rule is in the **linear-take fragment** (`NoAbsenceOrCount`) when every check it asks is an
equality: no absence and no count. It may take, read, make and tell.

* `union_monotone`: over ground terms, a firing of the fragment admitted at a store stays admitted
  beside any other store whose occurrences its made identities avoid (from
  `Composition.valid_union`; with no checks at all this is `Composition.positive_monotone`).
* `linearTake_interchange`: two firings without checks whose footprints do not interfere (neither
  makes what the other takes or reads, neither reads what the other takes, and the later one makes no
  identity the earlier took) run in either order to the same configuration up to solutions, for every
  substitution action (`GuardFreeProcessOrders.swap_valid`).

## Controls

* Positive: `Controls.takes_interchange`: a taker of `A` and a taker of `B`, in both orders.
* Negative, just outside: `Controls.absence_breaks_interchange`: `spawn` (make `T` where `U` is
  absent) and a maker of `U` have non-interfering footprints, run in one order, and not in the other.
  With `Composition.absence_not_monotone`, absence also breaks monotonicity under union.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep

open NamesOnTheStep NamesOnTheStep.IssuingControls GroundFirings
open GuardFreeProcessOrders (SameUpTo NoCause NoAsym NoReuse)

namespace LinearTake

/-- **The linear-take fragment**: every check is an equality. -/
def NoAbsenceOrCount {T : Type*} (rule : RuleInstance T) : Prop :=
  ∀ c ∈ rule.checks, ∃ l r, c = Check.equal l r

/-- **Monotone under union**: a firing of the fragment stays admitted beside another store. -/
theorem union_monotone {C D : Conf} {f : Fir} (fragment : NoAbsenceOrCount f.rule)
    (noQueries : f.queries = []) (admitted : base.Admits (s := C) f)
    (fresh : ∀ o ∈ f.selection.made, o ∉ D.present) (knowledge : ∀ e ∈ D.equations, e.1 = e.2) :
    base.Admits (s := NullsOnTheStep.Composition.union C D) f := by
  refine NullsOnTheStep.Composition.valid_union admitted fresh knowledge (fun c member => ?_) noQueries
  obtain ⟨l, r, rfl⟩ := fragment c member
  have firing := (show f.Valid ground Prod.fst C from admitted).firing
  obtain ⟨u, solved⟩ := firing.consistent
  cases u
  exact firing.checks _ member () solved

/-- **Independent firings interchange**, for every substitution action. -/
theorem linearTake_interchange {T S O : Type*} [DecidableEq O] (A : SubstitutionAction T S)
    (label : O → T) {f g : ConditionalSchedule.Firing T O} {C : Configuration T O}
    (fFree : f.1.checks = []) (gFree : g.1.checks = []) (noCause : NoCause f g) (noAsym : NoAsym f g)
    (noReuse : NoReuse f g) (first : f.2.Valid A label f.1 C)
    (second : g.2.Valid A label g.1 (f.2.result label f.1 C)) :
    g.2.Valid A label g.1 C ∧ f.2.Valid A label f.1 (g.2.result label g.1 C) ∧
      SameUpTo A (g.2.result label g.1 (f.2.result label f.1 C))
        (f.2.result label f.1 (g.2.result label g.1 C)) :=
  GuardFreeProcessOrders.swap_valid A label fFree gFree noCause noAsym noReuse first second

end LinearTake

namespace LinearTake.Controls

def factA : Expr := .sym 60
def factB : Expr := .sym 61
def factV : Expr := .sym 62
def factW : Expr := .sym 63

def both : Conf := ⟨[], {(factA, 0), (factB, 0)}⟩

def takeA : ConditionalSchedule.Firing Expr Occ := (rule [factA] [] [factW], ⟨[(factA, 0)], [], [(factW, 0)]⟩)
def takeB : ConditionalSchedule.Firing Expr Occ := (rule [factB] [] [factV], ⟨[(factB, 0)], [], [(factV, 0)]⟩)

theorem takeA_valid : takeA.2.Valid ground Prod.fst takeA.1 both :=
  ground_valid (by decide) (by decide) rfl rfl rfl (by decide) (by decide) rfl (no_checks rfl)

theorem takeB_after : takeB.2.Valid ground Prod.fst takeB.1 (takeA.2.result Prod.fst takeA.1 both) :=
  ground_valid (by decide) (by decide) rfl rfl rfl (by decide) (result_knowledge takeA_valid) rfl
    (no_checks rfl)

/-- **Positive control.** A taker of `A` and a taker of `B` run in both orders. -/
theorem takes_interchange :
    takeB.2.Valid ground Prod.fst takeB.1 both ∧
      takeA.2.Valid ground Prod.fst takeA.1 (takeB.2.result Prod.fst takeB.1 both) ∧
      SameUpTo ground (takeB.2.result Prod.fst takeB.1 (takeA.2.result Prod.fst takeA.1 both))
        (takeA.2.result Prod.fst takeA.1 (takeB.2.result Prod.fst takeB.1 both)) :=
  linearTake_interchange ground Prod.fst rfl rfl (by unfold NoCause; decide) (by unfold NoAsym; decide)
    (by unfold NoReuse; decide) takeA_valid takeB_after

/-- `spawn`: make `T` where `U` is absent. -/
def spawnFiring : ConditionalSchedule.Firing Expr Occ :=
  (NullsOnTheStep.Separations.spawn, NullsOnTheStep.Separations.spawnAt.1.selection)

/-- A maker of `U`. -/
def makeU : ConditionalSchedule.Firing Expr Occ := (rule [] [] [factU], ⟨[], [], [(factU, 0)]⟩)

theorem spawn_valid : spawnFiring.2.Valid ground Prod.fst spawnFiring.1 NullsOnTheStep.Separations.emptyS.1 :=
  (PredicateQueryAdmission.valid_empty_iff ground Prod.fst _ _ _).mp NullsOnTheStep.Separations.spawn_admitted.1

theorem makeU_after :
    makeU.2.Valid ground Prod.fst makeU.1 (spawnFiring.2.result Prod.fst spawnFiring.1 NullsOnTheStep.Separations.emptyS.1) :=
  ground_valid (by decide) (by decide) rfl rfl rfl (by decide) (result_knowledge spawn_valid) rfl
    (no_checks rfl)

/-- **Negative control.** `spawn` asks absence, so it is outside the fragment; its footprint does
not interfere with the maker of `U`, it runs before it, and it is refused after it. -/
theorem absence_breaks_interchange :
    ¬ NoAbsenceOrCount spawnFiring.1 ∧ NoCause spawnFiring makeU ∧ NoAsym spawnFiring makeU ∧
      NoReuse spawnFiring makeU ∧
      spawnFiring.2.Valid ground Prod.fst spawnFiring.1 NullsOnTheStep.Separations.emptyS.1 ∧
      makeU.2.Valid ground Prod.fst makeU.1
        (spawnFiring.2.result Prod.fst spawnFiring.1 NullsOnTheStep.Separations.emptyS.1) ∧
      ¬ spawnFiring.2.Valid ground Prod.fst spawnFiring.1
        (makeU.2.result Prod.fst makeU.1 NullsOnTheStep.Separations.emptyS.1) := by
  refine ⟨fun fragment => ?_, by unfold NoCause; decide, by unfold NoAsym; decide,
    by unfold NoReuse; decide, spawn_valid, makeU_after, fun refused => ?_⟩
  · obtain ⟨l, r, same⟩ := fragment _ (List.mem_singleton.mpr rfl)
    cases same
  · exact absent_refuted refused (p := factU) (List.mem_singleton.mpr rfl) (o := (factU, 0))
      (by decide) rfl

end LinearTake.Controls

open LinearTake in
#print axioms union_monotone
open LinearTake in
#print axioms linearTake_interchange
#print axioms LinearTake.Controls.takes_interchange
#print axioms LinearTake.Controls.absence_breaks_interchange

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep
