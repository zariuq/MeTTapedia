import Mettapedia.Ethics.GewirthPGC
import Mettapedia.Logic.DDLPlus.Core
import Mettapedia.Logic.DDLPlus.Theorems
import Mettapedia.OSLF.Framework.GovernanceInstance

set_option autoImplicit false

/-!
# Gewirth Bridge: PGC ↔ DDLPlus + Governance Ethics

Connects the Gewirth PGC proof to the Mettapedia DDLPlus framework and to the
governance OSLF layer.

## Architecture

```
PGCInterpretation (3 sem conditions)
        │
        │  + sem_3a, sem_4a, sem_4b, sem_5c, sem_5d
        ▼
PGCFullFrame
        │
        ├──→ toDDLPlusFrame     (DDLPlusFrame I.World)
        │         gives access to ALL CJ theorems (CJ_3 through CJ_15)
        │
        ├──→ toGovFrame         (GovFrame I.World)
        │         connects PGC's ob to governance deontic norms
        │
        └──→ pgc_is_governance_norm
                  PGC conclusion = ideal_obl in DDLPlus
```

## Key Result

`pgc_is_governance_norm`: every purposeful agent's right to non-interference
with their FWB is an instance of `ideal_obl` in the DDLPlus framework.
-/

namespace Mettapedia.Ethics.GewirthBridge

open Mettapedia.Ethics (Formula DeonticAttribute DeonticSemantics)
open Mettapedia.Ethics.Gewirth
open Mettapedia.Logic.DDLPlus.Core (WProp DDLPlusFrame ideal_obl)
open Mettapedia.OSLF.Framework.GovernanceInstance (GovFrame)

universe u

/-! ## §1 WorldEmbedding

Canonical isomorphism between `Meaning Ctx World` and `Formula (Ctx × World)`.
-/

namespace WorldEmbedding

abbrev PairWorld (Ctx World : Type u) : Type u := Ctx × World

/-- Embed a `Formula` over pairs as a curried `Gewirth.Meaning`. -/
def toMeaning {Ctx World : Type u}
    (φ : Formula (PairWorld Ctx World)) : Gewirth.Meaning Ctx World :=
  fun c w => φ (c, w)

/-- Flatten a curried `Gewirth.Meaning` into a `Formula` over pairs. -/
def ofMeaning {Ctx World : Type u}
    (m : Gewirth.Meaning Ctx World) : Formula (PairWorld Ctx World) :=
  fun cw => m cw.1 cw.2

theorem ofMeaning_toMeaning {Ctx World : Type u}
    (φ : Formula (PairWorld Ctx World)) :
    ofMeaning (toMeaning φ) = φ := by
  funext ⟨c, w⟩; rfl

theorem toMeaning_ofMeaning {Ctx World : Type u}
    (m : Gewirth.Meaning Ctx World) :
    toMeaning (ofMeaning m) = m := by
  funext c w; rfl

end WorldEmbedding

open WorldEmbedding

/-! ## §2 Deontic Semantics from Gewirth's Oi -/

/-- The `DeonticSemantics` induced by Gewirth's ideal obligation `Oi`.
    Obligation  ↔ Oi(φ)
    Prohibition ↔ Oi(¬φ)
    Permission  ↔ ¬Oi(¬φ) -/
noncomputable def deonticSemanticsOfGewirthOi {Ctx World : Type u}
    (ob : Formula World → Formula World → Prop)
    (pv : World → Formula World) :
    DeonticSemantics (PairWorld Ctx World) :=
  ⟨fun tag φ =>
    match tag with
    | .Obligation =>
        ofMeaning (Oi ob pv (toMeaning φ))
    | .Prohibition =>
        ofMeaning (Oi ob pv (fun c w => ¬ toMeaning φ c w))
    | .Permission =>
        fun cw => ¬ (ofMeaning (Oi ob pv (fun c w => ¬ toMeaning φ c w))) cw⟩

theorem deonticSemanticsOfGewirthOi_obligation {Ctx World : Type u}
    (ob : Formula World → Formula World → Prop)
    (pv : World → Formula World)
    (φ : Formula (PairWorld Ctx World)) :
    (deonticSemanticsOfGewirthOi (Ctx := Ctx) ob pv).deontic .Obligation φ =
      ofMeaning (Oi ob pv (toMeaning φ)) := rfl

/-! ## §3 PGC → Deontic Obligation

The PGC conclusion expressed as a deontic obligation sentence. -/

theorem PGC_strong_implies_obligation_nonInterference
    (I : PGCInterpretation) (h : PGCAssumptions I) :
    ∀ C x, PPA I.ActsOnPurpose x C (I.worldOf C) →
      (deonticSemanticsOfGewirthOi (Ctx := I.Ctx) I.ob I.pv).deontic .Obligation
        (ofMeaning (NonInterference I.InterferesWith x I.FWB))
        (C, I.worldOf C) := by
  intro C x hPPA
  have hAtC := PGC_strong_ofAssumptions I h C x hPPA
  simp only [deonticSemanticsOfGewirthOi, ofMeaning, toMeaning, Oi]
  exact hAtC

/-! ## §4 PGCFullFrame

A `PGCFullFrame` extends `PGCInterpretation` with all conditions needed to
build a `DDLPlusFrame` (the 3 PGC conditions plus sem_3a, sem_4a, sem_4b,
sem_5c, sem_5d). -/

/-- A full PGC frame: PGCInterpretation + the four additional conditions needed
    for a complete DDLPlusFrame (seriality, av ⊆ pv, pv reflexive,
    obligation conjunction, obligation transfer). -/
structure PGCFullFrame : Type (u + 1) where
  Ctx    : Type u
  World  : Type u
  Entity : Type u
  worldOf : Ctx → World
  av     : World → Formula World
  pv     : World → Formula World
  ob     : Formula World → Formula World → Prop
  ActsOnPurpose   : Entity → Gewirth.Meaning Ctx World → Gewirth.Meaning Ctx World
  NeedsForPurpose : Entity → (Entity → Gewirth.Meaning Ctx World) →
      Gewirth.Meaning Ctx World → Gewirth.Meaning Ctx World
  Good            : Entity → Gewirth.Meaning Ctx World → Gewirth.Meaning Ctx World
  FWB             : Entity → Gewirth.Meaning Ctx World
  InterferesWith  : Entity → Gewirth.Meaning Ctx World → Gewirth.Meaning Ctx World
  -- Conditions shared with PGCInterpretation
  sem_5a : ∀ X : Formula World, ¬ ob X (fun _ => False)
  sem_5b : ∀ X Y Z : Formula World,
      SetEq (Inter X Y) (Inter X Z) → (ob X Y ↔ ob X Z)
  sem_5e : ∀ X Y Z : Formula World,
      Subset Y X → ob X Z → Instantiated (Inter Y Z) → ob Y Z
  -- Additional DDLPlusFrame conditions
  sem_3a : ∀ v : World, ∃ v', av v v'
  sem_4a : ∀ v v' : World, av v v' → pv v v'
  sem_4b : ∀ v : World, pv v v
  sem_5c : ∀ X Y Z : Formula World,
      (∃ v, X v ∧ Y v ∧ Z v) → ob X Y → ob X Z → ob X (fun v => Y v ∧ Z v)
  sem_5d : ∀ X Y Z : Formula World,
      (∀ v, Y v → X v) → ob X Y → (∀ v, X v → Z v) →
      ob Z (fun v => (Z v ∧ ¬ X v) ∨ Y v)

/-- Project a `PGCFullFrame` to a `PGCInterpretation` (forgetting the extra conditions). -/
@[reducible]
def PGCFullFrame.toPGCInterpretation (F : PGCFullFrame) : PGCInterpretation where
  Ctx             := F.Ctx
  World           := F.World
  Entity          := F.Entity
  worldOf         := F.worldOf
  av              := F.av
  pv              := F.pv
  ob              := F.ob
  ActsOnPurpose   := F.ActsOnPurpose
  NeedsForPurpose := F.NeedsForPurpose
  Good            := F.Good
  FWB             := F.FWB
  InterferesWith  := F.InterferesWith

/-! ## §5 PGCFullFrame → DDLPlusFrame -/

/-- A `PGCFullFrame` induces a full `DDLPlusFrame` over its world type.
    `F.ob`, `F.pv`, `F.av` are used directly; all 7 semantic conditions are met.

    Note: `SetEq (Inter X Y) (Inter X Z)` is definitionally `∀ v, (X v ∧ Y v) ↔ (X v ∧ Z v)`,
    so `F.sem_5b` directly satisfies DDLPlusFrame's `sem_5b`.  Similarly for `F.sem_5e`. -/
@[reducible]
def PGCFullFrame.toDDLPlusFrame (F : PGCFullFrame) : DDLPlusFrame F.World where
  av      := F.av
  pv      := F.pv
  ob      := F.ob
  sem_3a  := F.sem_3a
  sem_4a  := F.sem_4a
  sem_4b  := F.sem_4b
  sem_5a  := F.sem_5a
  sem_5b  := fun X Y Z h => F.sem_5b X Y Z (fun v => h v)
  sem_5c  := F.sem_5c
  sem_5d  := F.sem_5d
  sem_5e  := fun X Y Z h1 h2 h3 => F.sem_5e X Y Z h1 h2 h3

/-! ## §6 PGCFullFrame → GovFrame -/

/-- A `PGCFullFrame` induces a `GovFrame` over its world type.
    The 5 `GovFrame` conditions are exactly the 5 DDLPlus `ob`-conditions. -/
def PGCFullFrame.toGovFrame (F : PGCFullFrame) : GovFrame F.World where
  ob          := F.ob
  ob_not_bot  := F.sem_5a
  ob_cong     := fun X Y Z h => F.sem_5b X Y Z (fun v => h v)
  ob_conj     := F.sem_5c
  ob_transfer := F.sem_5d
  ob_restrict := fun X Y Z h1 h2 h3 => F.sem_5e X Y Z h1 h2 h3

/-! ## §7 PGC Conclusion as Ideal Obligation in DDLPlus -/

/-- The PGC conclusion is a theorem about `ideal_obl` in DDLPlus.

    For any purposeful agent `x`, the right to non-interference with their FWB
    is exactly `ideal_obl F.toDDLPlusFrame` applied to the non-interference
    predicate.

    This is the key integration result: PGC is not merely *analogous* to
    DDLPlus ideal obligation — it *is* DDLPlus ideal obligation, provably.

    **0 axioms, 0 sorries.** -/
theorem pgc_is_governance_norm
    (F : PGCFullFrame) (h : PGCAssumptions F.toPGCInterpretation)
    (c : F.Ctx) (x : F.Entity)
    (hppa : PPA F.ActsOnPurpose x c (F.worldOf c)) :
    ideal_obl F.toDDLPlusFrame
      (NonInterference F.InterferesWith x F.FWB)
      c (F.worldOf c) := by
  -- PGC_strong gives RightTo = Oi ob pv (NonInterference ...)
  -- ideal_obl F.toDDLPlusFrame φ c w = F.ob (F.pv w) (φ c) ∧ ∃ v', F.pv w v' ∧ ¬ φ c v'
  -- Oi F.ob F.pv φ c w = F.ob (F.pv w) (φ c) ∧ ∃ v, F.pv w v ∧ ¬ φ c v
  -- These are definitionally equal since F.toDDLPlusFrame.{ob,pv} = F.{ob,pv}.
  have hpgc : RightTo F.ob F.pv F.InterferesWith x F.FWB c (F.worldOf c) :=
    PGC_strong
      (worldOf         := F.worldOf)
      (av              := F.av) (pv := F.pv) (ob := F.ob)
      (ActsOnPurpose   := F.ActsOnPurpose)
      (NeedsForPurpose := F.NeedsForPurpose)
      (Good            := F.Good) (FWB := F.FWB)
      (InterferesWith  := F.InterferesWith)
      (sem_5a          := h.sem_5a)
      (sem_5b          := h.sem_5b)
      (sem_5e          := h.sem_5e)
      (explicationGoodness1 := h.explicationGoodness1)
      (explicationGoodness2 := h.explicationGoodness2)
      (explicationGoodness3 := h.explicationGoodness3)
      (explicationFWB1 := h.explicationFWB1)
      (explicationFWB2 := h.explicationFWB2)
      (explicationFWB3 := h.explicationFWB3)
      (OIOAC           := h.OIOAC)
      (explicationInterference := h.explicationInterference)
      c x hppa
  -- hpgc : Oi F.ob F.pv (NonInterference ...) c (F.worldOf c)
  -- goal : ideal_obl F.toDDLPlusFrame (NonInterference ...) c (F.worldOf c)
  -- Unfold both to F.ob (F.pv (F.worldOf c)) (NonInterference ... c) ∧ ∃ v, ...
  -- toDDLPlusFrame is @[reducible], so ideal_obl F.toDDLPlusFrame unfolds to Oi F.ob F.pv
  exact hpgc

#check @PGCFullFrame.toDDLPlusFrame
#check @PGCFullFrame.toGovFrame
#check @pgc_is_governance_norm
#check @PGC_strong_implies_obligation_nonInterference

end Mettapedia.Ethics.GewirthBridge
