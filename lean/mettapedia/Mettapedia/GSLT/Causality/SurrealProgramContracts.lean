import Mettapedia.GSLT.Causality.SurrealCostValuation
import Mettapedia.SetTheory.Surreal.OrdinalEmbedding
import Mathlib.Order.WellFounded

/-!
# Numeric program contracts with distinct rank and budget obligations

A ranking certificate decreases on every admitted source step. Reading an
ordinal rank as a surreal preserves and reflects this condition and proves
the absence of infinite source reductions. Decreasing arbitrary nonnegative
surreals would not suffice.

A budget contract quantifies over the declared class of occurrence paths.
Reading its dyadic costs as surreals preserves the exact contract, including
any policy, context or provenance restriction selecting those paths. Neither
contract identifies distinct retained paths.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.SurrealProgramContracts

open Mettapedia.GSLT
open Mettapedia.GSLT.Core.InteractionEvent
open Mettapedia.GSLT.Causality.OccurrenceHistory
open Mettapedia.GSLT.Causality.SurrealCostValuation
open Mettapedia.SetTheory.SignExpansion.Surreal

universe uSite uEvent

def Ranks (theory : GSLT) (rank : theory.Term → Ordinal) : Prop :=
  ∀ source target, theory.Step source target → rank target < rank source

theorem ranks_iff_surreal (theory : GSLT) (rank : theory.Term → Ordinal) :
    Ranks theory rank ↔
      ∀ source target, theory.Step source target →
        ofOrdinal (rank target) < ofOrdinal (rank source) := by
  simp only [Ranks, ofOrdinal_lt_iff]

theorem ranks_wellFounded (theory : GSLT) (rank : theory.Term → Ordinal)
    (decreases : Ranks theory rank) :
    WellFounded (fun target source => theory.Step source target) :=
  Subrelation.wf (fun {_ _} step => decreases _ _ step) (InvImage.wf rank Ordinal.lt_wf)

theorem no_infinite_of_wellFounded (theory : GSLT)
    (wellFounded : WellFounded (fun target source => theory.Step source target)) :
    ¬ ∃ run : Nat → theory.Term, ∀ n, theory.Step (run n) (run (n + 1)) := by
  have cannotContinue : ∀ source,
      Acc (fun target source => theory.Step source target) source →
        ∀ run : Nat → theory.Term, run 0 = source →
          (∀ n, theory.Step (run n) (run (n + 1))) → False := by
    intro source accessible
    induction accessible with
    | intro source _ ih =>
        intro run initial steps
        apply ih (run 1) (initial ▸ steps 0) (fun n => run (n + 1)) rfl
        intro n
        exact steps (n + 1)
  rintro ⟨run, steps⟩
  exact cannotContinue (run 0) (wellFounded.apply (run 0)) run rfl steps

theorem no_infinite_reduction (theory : GSLT) (rank : theory.Term → Ordinal)
    (decreases : Ranks theory rank) :
    ¬ ∃ run : Nat → theory.Term, ∀ n, theory.Step (run n) (run (n + 1)) :=
  no_infinite_of_wellFounded theory (ranks_wellFounded theory rank decreases)

theorem no_surreal_ordinal_rank_on_loop (theory : GSLT) (source : theory.Term)
    (loop : theory.Step source source) : ¬ ∃ rank, Ranks theory rank := by
  rintro ⟨rank, decreases⟩
  exact (lt_irrefl (rank source)) (decreases source source loop)

variable {theory : GSLT} {P : InteractionPresentation.{uSite, uEvent} theory}

/-- An event balance extends to every retained path. The potential can live
in any additive monoid; subtraction and a group completion are unnecessary. -/
theorem event_potential_onPath {Cost : Type*} [AddMonoid Cost]
    (valuation : OccurrenceValuation P Cost) (potential : theory.Term → Cost)
    (balanced : ∀ {source target}, (event : Occurrence P source target) →
      valuation.grade event + potential target = potential source)
    {source target : theory.Term} (path : OccurrencePath P source target) :
    valuation.onPath path + potential target = potential source := by
  induction path with
  | refl => simp [OccurrenceValuation.onPath]
  | cons event rest ih =>
      rw [OccurrenceValuation.onPath, add_assoc, ih]
      exact balanced event

/-- The selected executions remain an explicit index of the budget claim. -/
def WithinBudget (valuation : OccurrenceValuation P SurrealCostValuation.Dyadic)
    {source target : theory.Term} (admitted : OccurrencePath P source target → Prop)
    (budget : SurrealCostValuation.Dyadic) : Prop :=
  ∀ path, admitted path → valuation.onPath path ≤ budget

theorem budget_contract_iff (valuation : OccurrenceValuation P SurrealCostValuation.Dyadic)
    {source target : theory.Term} (admitted : OccurrencePath P source target → Prop)
    (budget : SurrealCostValuation.Dyadic) :
    WithinBudget valuation admitted budget ↔
      ∀ path, admitted path → (read valuation).onPath path ≤ toSurreal budget := by
  simp only [WithinBudget, budget_iff]

/-- A dependent evidence consumer can change the numeric representation
while receiving the identical qualified occurrence path. -/
noncomputable def qualifiedBudgetEquiv (valuation : OccurrenceValuation P SurrealCostValuation.Dyadic)
    {source target : theory.Term} (admitted : OccurrencePath P source target → Prop)
    (budget : SurrealCostValuation.Dyadic) :
    {path : OccurrencePath P source target //
      admitted path ∧ valuation.onPath path ≤ budget} ≃
    {path : OccurrencePath P source target //
      admitted path ∧ (read valuation).onPath path ≤ toSurreal budget} where
  toFun path := ⟨path.1, path.2.1, (budget_iff valuation path.1 budget).mpr path.2.2⟩
  invFun path := ⟨path.1, path.2.1, (budget_iff valuation path.1 budget).mp path.2.2⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

@[simp] theorem qualifiedBudgetEquiv_path (valuation : OccurrenceValuation P SurrealCostValuation.Dyadic)
    {source target : theory.Term} (admitted : OccurrencePath P source target → Prop)
    (budget : SurrealCostValuation.Dyadic) (path : {path : OccurrencePath P source target //
      admitted path ∧ valuation.onPath path ≤ budget}) :
    (qualifiedBudgetEquiv valuation admitted budget path).1 = path.1 := rfl

end Mettapedia.GSLT.Causality.SurrealProgramContracts
