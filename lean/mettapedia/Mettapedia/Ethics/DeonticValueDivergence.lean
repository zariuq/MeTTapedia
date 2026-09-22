import Mettapedia.Ethics.Core

/-!
# Where deontic verdicts and value verdicts come apart

The ethics ontology maps imperative sentences to value judgments by a simple
correspondence: obligatory as good, prohibited as bad, permitted as permissible.
It also notes that the correspondence loses granularity — adherence to a rule can
be good yet optional, and non-obligatory good is simply permissible.  This module
makes that loss exact.

Both kinds of semantics yield one verdict for a formula at a world: a deontic
semantics rules prohibition first, then obligation, else permission
(`DeonticSemantics.verdict`); a value semantics rules good first, then bad, else
permissible (`ValueSemantics.verdict`).

When the two semantics agree on what is ruled out — bad is prohibited, and
permitted means not prohibited (`AgreeOnProhibition`) — the translated deontic
verdict equals the value verdict exactly when none of three divergences occurs
(`verdicts_agree_iff`):

* **supererogatory** — good and permitted, yet not obligatory;
* **obligatory but not good** — required, yet not good;
* **prohibited good** — good, yet prohibited.

No other combination separates the verdicts.
-/

set_option autoImplicit false

namespace Mettapedia.Ethics

universe u

open Classical

variable {World : Type u}

/-- The deontic verdict on a formula at a world: prohibition first, then
obligation, otherwise permission. -/
noncomputable def DeonticSemantics.verdict (deontic : DeonticSemantics World) (formula : Formula World)
    (world : World) : DeonticAttribute :=
  if deontic.deontic .Prohibition formula world then .Prohibition
  else if deontic.deontic .Obligation formula world then .Obligation
  else .Permission

/-- The value verdict on a formula at a world: good first, then bad, otherwise
permissible. -/
noncomputable def ValueSemantics.verdict (value : ValueSemantics World) (formula : Formula World)
    (world : World) : MoralValueAttribute :=
  if value.morally .MorallyGood formula world then .MorallyGood
  else if value.morally .MorallyBad formula world then .MorallyBad
  else .MorallyPermissible

theorem DeonticSemantics.verdict_eq_prohibition_iff (deontic : DeonticSemantics World)
    (formula : Formula World) (world : World) :
    deontic.verdict formula world = .Prohibition ↔ deontic.deontic .Prohibition formula world := by
  unfold DeonticSemantics.verdict
  split_ifs <;> simp_all

theorem DeonticSemantics.verdict_eq_obligation_iff (deontic : DeonticSemantics World)
    (formula : Formula World) (world : World) :
    deontic.verdict formula world = .Obligation ↔
      ¬ deontic.deontic .Prohibition formula world ∧ deontic.deontic .Obligation formula world := by
  unfold DeonticSemantics.verdict
  split_ifs <;> simp_all

theorem DeonticSemantics.verdict_eq_permission_iff (deontic : DeonticSemantics World)
    (formula : Formula World) (world : World) :
    deontic.verdict formula world = .Permission ↔
      ¬ deontic.deontic .Prohibition formula world ∧ ¬ deontic.deontic .Obligation formula world := by
  unfold DeonticSemantics.verdict
  split_ifs <;> simp_all

theorem ValueSemantics.verdict_eq_good_iff (value : ValueSemantics World) (formula : Formula World)
    (world : World) :
    value.verdict formula world = .MorallyGood ↔ value.morally .MorallyGood formula world := by
  unfold ValueSemantics.verdict
  split_ifs <;> simp_all

theorem ValueSemantics.verdict_eq_bad_iff (value : ValueSemantics World) (formula : Formula World)
    (world : World) :
    value.verdict formula world = .MorallyBad ↔
      ¬ value.morally .MorallyGood formula world ∧ value.morally .MorallyBad formula world := by
  unfold ValueSemantics.verdict
  split_ifs <;> simp_all

theorem ValueSemantics.verdict_eq_permissible_iff (value : ValueSemantics World) (formula : Formula World)
    (world : World) :
    value.verdict formula world = .MorallyPermissible ↔
      ¬ value.morally .MorallyGood formula world ∧ ¬ value.morally .MorallyBad formula world := by
  unfold ValueSemantics.verdict
  split_ifs <;> simp_all

theorem deonticToMoralValue_eq_iff (deontic : DeonticAttribute) (value : MoralValueAttribute) :
    deonticToMoralValue deontic = value ↔ deontic = moralValueToDeontic value := by
  cases deontic <;> cases value <;> decide

/-- The two semantics agree on what is ruled out. -/
structure AgreeOnProhibition (deontic : DeonticSemantics World) (value : ValueSemantics World) :
    Prop where
  bad_iff_prohibition : ∀ formula world,
    value.morally .MorallyBad formula world ↔ deontic.deontic .Prohibition formula world
  permission_iff_not_prohibition : ∀ formula world,
    deontic.deontic .Permission formula world ↔ ¬ deontic.deontic .Prohibition formula world

section Divergences

variable (deontic : DeonticSemantics World) (value : ValueSemantics World)

/-- Good and permitted, yet not obligatory. -/
def Supererogatory (formula : Formula World) (world : World) : Prop :=
  value.morally .MorallyGood formula world ∧ deontic.deontic .Permission formula world ∧
    ¬ deontic.deontic .Obligation formula world

/-- Obligatory and permitted, yet not good. -/
def ObligatoryNotGood (formula : Formula World) (world : World) : Prop :=
  deontic.deontic .Obligation formula world ∧ deontic.deontic .Permission formula world ∧
    ¬ value.morally .MorallyGood formula world

/-- Good, yet prohibited. -/
def ProhibitedGood (formula : Formula World) (world : World) : Prop :=
  value.morally .MorallyGood formula world ∧ deontic.deontic .Prohibition formula world

/-- **The verdicts agree exactly when no divergence occurs.** -/
theorem verdicts_agree_iff (agree : AgreeOnProhibition deontic value) (formula : Formula World)
    (world : World) :
    deonticToMoralValue (deontic.verdict formula world) = value.verdict formula world ↔
      ¬ Supererogatory deontic value formula world ∧ ¬ ObligatoryNotGood deontic value formula world ∧
        ¬ ProhibitedGood deontic value formula world := by
  simp only [DeonticSemantics.verdict, ValueSemantics.verdict, Supererogatory, ObligatoryNotGood,
    ProhibitedGood, agree.bad_iff_prohibition, agree.permission_iff_not_prohibition]
  by_cases good : value.morally .MorallyGood formula world <;>
    by_cases prohibited : deontic.deontic .Prohibition formula world <;>
    by_cases obligatory : deontic.deontic .Obligation formula world <;>
    simp [good, prohibited, obligatory, deonticToMoralValue]

end Divergences

#print axioms verdicts_agree_iff

end Mettapedia.Ethics
