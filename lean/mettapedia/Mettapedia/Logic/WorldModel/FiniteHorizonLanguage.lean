import Mettapedia.Logic.FinitaryRuleSystem.DirectedUnion
import Mettapedia.Logic.WorldModel.OpenEnded

/-!
# Finite-horizon languages over open-ended worlds

A finite-horizon formula consists of a stage and a predicate on the snapshot
visible at that stage.  Its meaning is the corresponding cylinder property of
the primary world.  Such formulas lift coherently to every later stage: the
later evaluator first restricts its snapshot, so extending the observation
horizon does not change the formula's meaning.

This gives two complementary finite-support principles.

* A derivation in a directed union of monotone finitary rule systems already
  belongs to one finite stage.
* A finite-horizon formula has a stage-local evaluator, and its meaning is
  unchanged when the horizon grows.

Neither principle says that every property of an open-ended world is visible
at a finite horizon.  The Cantor-space control proves that `someBitTrue` has no
finite-horizon representation, although the first-bit property does.  Thus
finite certified work can remain stable under extension without identifying
the open-ended semantic whole with any fixed finite view.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.WorldModel.FiniteHorizonLanguage

open Mettapedia.Logic
open Mettapedia.Logic.FinitaryRuleSystem
open Mettapedia.Logic.WorldModel.OpenEnded

universe uWorld uSnapshot uJudgment uStage

/-! ## Stage-local formulas and their meanings -/

/-- A predicate whose entire observation demand is exposed as one finite
horizon. -/
structure Formula {World : Type uWorld}
    (observation : PrefixObservation.{uWorld, uSnapshot} World) where
  stage : Nat
  predicate : observation.Snapshot stage → Prop

namespace Formula

variable {World : Type uWorld}
variable {observation : PrefixObservation.{uWorld, uSnapshot} World}

/-- Interpret a finite-horizon formula as a property of primary worlds. -/
def meaning (formula : Formula observation) : World -> Prop :=
  CylinderProperty observation formula.stage formula.predicate

/-- Every formula in the finite-horizon language is finitely determined. -/
theorem meaning_finitelyDetermined (formula : Formula observation) :
    FinitelyDetermined observation formula.meaning :=
  cylinderProperty_finitelyDetermined observation formula.stage
    formula.predicate

/-- Reindex a formula to a later observation horizon by restricting the later
snapshot back to the horizon the formula actually uses. -/
def lift (formula : Formula observation) {later : Nat}
    (horizon : formula.stage <= later) : Formula observation where
  stage := later
  predicate := fun snapshot =>
    formula.predicate (observation.restrict horizon snapshot)

/-- Horizon extension preserves meaning pointwise. -/
theorem lift_meaning_iff (formula : Formula observation) {later : Nat}
    (horizon : formula.stage <= later) (world : World) :
    (formula.lift horizon).meaning world <-> formula.meaning world := by
  simp only [meaning, lift, CylinderProperty]
  rw [observation.observe_restrict horizon world]

/-- Successive horizon extensions agree semantically with direct extension.
No equality of formula records is required: the invariant is their meaning. -/
theorem lift_lift_meaning_iff (formula : Formula observation)
    {middle later : Nat} (first : formula.stage <= middle)
    (second : middle <= later) (world : World) :
    ((formula.lift first).lift second).meaning world <->
      (formula.lift (first.trans second)).meaning world := by
  exact (((formula.lift first).lift_meaning_iff second world).trans
    (formula.lift_meaning_iff first world)).trans
      (formula.lift_meaning_iff (first.trans second) world).symm

/-- A decidable local predicate supplies a Boolean finite-horizon evaluator. -/
def evaluate (formula : Formula observation)
    [DecidablePred formula.predicate] (world : World) : Bool :=
  decide (formula.predicate (observation.observe formula.stage world))

/-- The Boolean evaluator is exact for the formula's open-world meaning. -/
theorem evaluate_eq_true_iff (formula : Formula observation)
    [DecidablePred formula.predicate] (world : World) :
    formula.evaluate world = true <-> formula.meaning world := by
  simp [evaluate, meaning, CylinderProperty]

end Formula

/-! ## Finitary proof search has the same finite-support shape -/

/-- An explicit finite-stage certificate for a judgment in a growing rule
system. -/
structure StagedDerivation {Judgment : Type uJudgment}
    {Stage : Type uStage} (rules : Stage -> List Judgment -> Judgment -> Prop)
    (judgment : Judgment) where
  stage : Stage
  derivation : Derives (rules stage) judgment

/-- A staged proof is always a proof in the pointwise union. -/
def StagedDerivation.toUnion {Judgment : Type uJudgment}
    {Stage : Type uStage} {rules : Stage -> List Judgment -> Judgment -> Prop}
    {judgment : Judgment} (certificate : StagedDerivation rules judgment) :
    Derives (UnionRules rules) judgment :=
  certificate.derivation.mono (fun _premises _conclusion rule =>
    Exists.intro certificate.stage rule)

/-- For a directed monotone family, union derivability is equivalent to
possessing one explicit finite-stage certificate. -/
theorem derives_union_iff_nonempty_staged
    {Judgment : Type uJudgment} {Stage : Type uStage}
    [SemilatticeSup Stage]
    {rules : Stage -> List Judgment -> Judgment -> Prop}
    (monotone : MonotoneRules rules) (judgment : Judgment) :
    Derives (UnionRules rules) judgment <->
      Nonempty (StagedDerivation rules judgment) := by
  constructor
  · intro derivation
    obtain ⟨stage, staged⟩ := derives_union_exists_stage monotone derivation
    exact ⟨⟨stage, staged⟩⟩
  · rintro ⟨certificate⟩
    exact certificate.toUnion

/-! ## Cantor-space controls -/

open Mettapedia.Computability

/-- The first-bit question as an explicit stage-one formula. -/
def firstBitFormula : Formula cantorPrefixObservation where
  stage := 1
  predicate := fun snapshot => snapshot ⟨0, by omega⟩ = true

theorem firstBitFormula_meaning_iff (world : CantorSpace) :
    firstBitFormula.meaning world <-> firstBitTrue world :=
  Iff.rfl

/-- The first-bit formula remains exact at every later nonzero horizon. -/
theorem firstBitFormula_lift_meaning_iff {later : Nat}
    (horizon : 1 <= later) (world : CantorSpace) :
    (firstBitFormula.lift horizon).meaning world <-> firstBitTrue world :=
  (firstBitFormula.lift_meaning_iff horizon world).trans
    (firstBitFormula_meaning_iff world)

/-- The open-tail property is outside the finite-horizon language: no single
formula record can represent it at all primary worlds. -/
theorem someBitTrue_not_representable :
    ¬ ∃ formula : Formula cantorPrefixObservation,
      ∀ world, formula.meaning world <-> someBitTrue world := by
  rintro ⟨formula, represents⟩
  apply someBitTrue_not_finitelyDetermined
  refine ⟨formula.stage, formula.predicate, ?_⟩
  intro world
  exact (represents world).symm

/-! ## Axiom audit -/

#print axioms Formula.lift_meaning_iff
#print axioms Formula.lift_lift_meaning_iff
#print axioms Formula.evaluate_eq_true_iff
#print axioms derives_union_iff_nonempty_staged
#print axioms firstBitFormula_lift_meaning_iff
#print axioms someBitTrue_not_representable

end Mettapedia.Logic.WorldModel.FiniteHorizonLanguage
