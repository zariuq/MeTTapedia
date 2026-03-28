import Mettapedia.Logic.DDLPlus.Core
import Mettapedia.Logic.WorldModelAdditive
import Mettapedia.Ethics.Core
import Mettapedia.Ethics.GewirthBridge

set_option autoImplicit false

/-!
# DDLPlus → WM Bridge

Connects Carmo-Jones Dyadic Deontic Logic satisfaction to WM positive
evidence, closing the chain: Ethics → DDLPlus → WM.

**Key principle**: deontic satisfaction at a world-pair = WM positive evidence
at the singleton state containing that world-pair.

## The full PGC → WM chain (composed here)

```
PGC_strong (Ethics/GewirthPGC.lean, 0 sorry, 0 axioms)
    ▼
PGC_strong_implies_obligation_nonInterference (Ethics/GewirthBridge.lean)
    ▼  PGC → DeonticSemantics.sat
pgc_nonInterference_wmPositiveEvidence  ← THIS MODULE
    ▼  DeonticSemantics.sat → WM positive evidence
WM meta-stability stack (MarkovLogic*, MetaGoalShellPreservation*)
```
-/

namespace Mettapedia.Logic.DDLPlus.WMBridge

open Mettapedia.Logic.DDLPlus.Core
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.PLNWorldModelAdditive
open Mettapedia.Ethics
open Mettapedia.Ethics.Gewirth
open Mettapedia.Ethics.GewirthBridge
open scoped ENNReal Classical

universe u

/-- A pointed deontic state: a specific (context, world) pair in Kaplanian
two-dimensional semantics, packaged for WM consumption. -/
structure PointedDeontic (Ctx World : Type u) where
  context : Ctx
  world : World

/-- A deontic WM query: a decidable world-proposition. -/
structure DeonticWMQuery (Ctx World : Type u) where
  formula : Ctx × World → Prop
  [decFormula : DecidablePred formula]

attribute [instance] DeonticWMQuery.decFormula

/-- Evidence type for multisets of pointed deontic states. -/
noncomputable instance deonticEvidenceType (Ctx World : Type u) :
    EvidenceType (Multiset (PointedDeontic Ctx World)) :=
  multisetEvidenceType (PointedDeontic Ctx World)

/-- Atomic evidence: positive if the formula holds, zero otherwise. -/
noncomputable def deonticAtomicEvidence
    {Ctx World : Type u}
    (pd : PointedDeontic Ctx World)
    (q : DeonticWMQuery Ctx World) : BinaryEvidence where
  pos := if q.formula (pd.context, pd.world) then 1 else 0
  neg := if q.formula (pd.context, pd.world) then 0 else 1

/-- BinaryWorldModel instance for deontic states. -/
noncomputable instance deonticBWM (Ctx World : Type u) :
    BinaryWorldModel
      (Multiset (PointedDeontic Ctx World))
      (DeonticWMQuery Ctx World) :=
  worldModelOfAtomicEvidence deonticAtomicEvidence

/-- If a formula holds at `(c, w)`, the atomic evidence has positive pos. -/
theorem deonticAtomicEvidence_pos_of_sat
    {Ctx World : Type u}
    (pd : PointedDeontic Ctx World)
    (q : DeonticWMQuery Ctx World)
    (hsat : q.formula (pd.context, pd.world)) :
    (deonticAtomicEvidence pd q).pos = 1 := by
  simp [deonticAtomicEvidence, hsat]

/-- If a formula does NOT hold at `(c, w)`, the atomic evidence has zero pos. -/
theorem deonticAtomicEvidence_pos_of_not_sat
    {Ctx World : Type u}
    (pd : PointedDeontic Ctx World)
    (q : DeonticWMQuery Ctx World)
    (hnotsat : ¬ q.formula (pd.context, pd.world)) :
    (deonticAtomicEvidence pd q).pos = 0 := by
  simp [deonticAtomicEvidence, hnotsat]

/-- **The DDLPlus → WM bridge theorem (atomic level).**

If a deontic formula holds at `(c, w)`, the atomic WM evidence is positive.
This is the fundamental semantic bridge: deontic truth → WM support. -/
theorem wmPositiveEvidence_of_deonticSat
    {Ctx World : Type u}
    (c : Ctx) (w : World)
    (q : DeonticWMQuery Ctx World)
    (hsat : q.formula (c, w)) :
    (deonticAtomicEvidence ⟨c, w⟩ q).pos ≠ 0 := by
  rw [deonticAtomicEvidence_pos_of_sat ⟨c, w⟩ q hsat]
  exact one_ne_zero

/-- **The full PGC → WM chain.**

If PGC assumptions hold and agent `x` acts on purpose at context `C`, then
the non-interference obligation has positive WM evidence.

This composes:
1. `PGC_strong_implies_obligation_nonInterference` (PGC → deontic satisfaction)
2. `wmPositiveEvidence_of_deonticSat` (deontic satisfaction → WM evidence)

**0 axioms, 0 sorry.** -/
theorem pgc_nonInterference_wmPositiveEvidence
    (I : PGCInterpretation) (h : PGCAssumptions I)
    (C : I.Ctx) (x : I.Entity)
    (hPPA : PPA I.ActsOnPurpose x C (I.worldOf C)) :
    let sem := deonticSemanticsOfGewirthOi (Ctx := I.Ctx) I.ob I.pv
    let obligationFormula : I.Ctx × I.World → Prop :=
      sem.deontic .Obligation
        (WorldEmbedding.ofMeaning (NonInterference I.InterferesWith x I.FWB))
    (deonticAtomicEvidence
      (⟨C, I.worldOf C⟩ : PointedDeontic I.Ctx I.World)
      ⟨obligationFormula⟩).pos ≠ 0 := by
  intro sem obligationFormula
  apply wmPositiveEvidence_of_deonticSat
  exact PGC_strong_implies_obligation_nonInterference I h C x hPPA

end Mettapedia.Logic.DDLPlus.WMBridge
