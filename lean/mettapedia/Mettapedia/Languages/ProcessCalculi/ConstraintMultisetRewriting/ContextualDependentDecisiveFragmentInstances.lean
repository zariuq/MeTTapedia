import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentDecisiveFragmentRules
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentDecisiveLocals

/-!
# The settling criterion in the cumulative tower

In the tower, with the actual normalizer, whose successful runs are kept, the rigid round is
eventually constant in its locals and pattern rules on every store. The settling criterion
therefore applies there. Its first instance is the class of stores containing an equation between
distinct rigid locals, defined from the store: the distinct-locals rule eventually fires, and the
criterion gives decisiveness at one joint budget with a certified refutation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentDecisiveFragment

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentWorklist ContextualDependentDecisiveDriver
open ContextualDependentExecutableConversion ContextualDependentExecutableChecking

variable {L : Type} [UniverseLevel.LevelOrder L]
variable [DecidableEq (LevelTower.Head L)] [DecidableRel (LevelTower.rules L).headEq]
  [∀ head, Decidable ((LevelTower.rules L).isUniverse head)] [DecidableRel (LevelTower.rules L).cumulative]

local instance settingHeadEq (valuation : Nat → L) : DecidableRel (TowerModel.setting valuation).R.headEq :=
  inferInstanceAs (DecidableRel (LevelTower.rules L).headEq)

local instance settingUniverse (valuation : Nat → L) (head : LevelTower.Head L) :
    Decidable ((TowerModel.setting valuation).R.isUniverse head) :=
  inferInstanceAs (Decidable ((LevelTower.rules L).isUniverse head))

local instance settingCumulative (valuation : Nat → L) : DecidableRel (TowerModel.setting valuation).R.cumulative :=
  inferInstanceAs (DecidableRel (LevelTower.rules L).cumulative)

variable (valuation : Nat → L)
  (rigid : ∀ name, (TowerModel.setting valuation).roles name = .rigid)
  (normalizes : ∀ {Θ : Context (TowerModel.setting valuation).R} {type : TypeOver Θ} (term : Term Θ type),
    ∃ code : Tm (LevelTower.Head L) Θ.arity,
      ContextualDependentNormalChecking.Normal (S := TowerModel.setting valuation) code ∧
      Equal (TowerModel.setting valuation).R Θ.raw term.code code type.code)
  (certifyNormal : ∀ {n : Nat} (term : Tm (LevelTower.Head L) n),
    Option (PLift (ContextualDependentNormalChecking.Normal (S := TowerModel.setting valuation) term)))

/-- The rigid round of the tower, as a fuel-indexed family. -/
abbrev towerFamily :=
  rigidFamily (S := TowerModel.setting valuation) rigid TowerModel.facts TowerModel.complete TowerModel.roots
    TowerModel.heads TowerModel.algebra declared tc red (fun _ => none) normalizes certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique

/-- **The criterion's first instance**: the stores with an equation between distinct rigid locals. -/
def distinctSettled : Settled (towerFamily valuation rigid normalizes certifyNormal) :=
  settledWhereFiring (S := TowerModel.setting valuation) rigid TowerModel.facts TowerModel.complete TowerModel.roots
    TowerModel.heads TowerModel.algebra declared tc red (fun _ => none) normalizes certifyNormal
    (fun fuel term => ContextualDependentExecutableDiscovery.red_stable fuel term)
    ContextualDependentNormalCheckingTower.head_typing_unique
    (fun problem => ∃ equation ∈ problem, ContextualDependentDecisiveLocals.DistinctLocals equation)
    (fun inside _ => by
      obtain ⟨fuel, fires⟩ := ContextualDependentDecisiveLocals.localsRule_eventually valuation rigid _ inside
      exact ⟨fuel, fun larger enough => .inl (fires larger enough)⟩)

/-- **Decisiveness on stores with distinct rigid locals, through the criterion**: one joint budget
decides the store, with the same outcome at every larger joint budget. -/
theorem distinct_decided {Θ : Context (LevelTower.rules L)} {problem : EquationStore (TotalTerm Θ)}
    (inside : ∃ equation ∈ problem, ContextualDependentDecisiveLocals.DistinctLocals equation) :
    ∃ budget, ∀ larger, budget ≤ larger →
      run ((towerFamily valuation rigid normalizes certifyNormal).solver larger) problem larger =
        run ((towerFamily valuation rigid normalizes certifyNormal).solver budget) problem budget ∧
      ((∃ state finished, run ((towerFamily valuation rigid normalizes certifyNormal).solver larger) problem larger =
          .solved state finished ∧ (frames (TowerModel.setting valuation).levels).Principal problem state.answer) ∨
        (∃ absent, run ((towerFamily valuation rigid normalizes certifyNormal).solver larger) problem larger =
          .refuted absent)) :=
  (distinctSettled valuation rigid normalizes certifyNormal).decided inside

end ContextualDependentDecisiveFragment
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
