import Mettapedia.Ethics.Core

set_option autoImplicit false

/-!
# Gewirth's Principle of Generic Consistency (PGC)

Semantic embedding of Gewirth's PGC proof (0 axioms, 0 sorries).

Ported from `foet/Foet/GewirthPGC.lean` with Mettapedia namespace and
integrated with `Mettapedia.Ethics.Core`.

## PGC Statement

Every agent who acts on purpose has a right that other agents not interfere
with their freedom and well-being (FWB).

## Architecture

- §1 Local abbreviations (Meaning, set-theoretic helpers, validity)
- §2 Modal operators (boxD, boxA, diaA, boxP, diaP)
- §3 Deontic operators (Ocond, Oi, RightTo)
- §4 Purposive agency operators (PPA, NonInterference)
- §5 Interpretation packaging (PGCInterpretation, PGCAssumptions)
- §6 Helper lemmas (sem_5ab, CJ_14p)
- §7 Main theorem (PGC_strong, PGC_strong_ofAssumptions)

## Notes

- `ldValid worldOf φ` corresponds to `KaplanianContext.ld_valid` in DDLPlus.Core.
- `Oi ob pv φ` is definitionally `ideal_obl` when `ob`, `pv` come from a DDLPlusFrame.
  The bridge is made explicit in `Mettapedia/Ethics/GewirthBridge.lean`.
- The local `CJ_14p` helper (§6) has a standalone interface (sem_5e as a parameter);
  the DDLPlus.Theorems version uses a full DDLPlusFrame.  Both are 0-axiom proofs.
-/

namespace Mettapedia.Ethics.Gewirth

open Mettapedia.Ethics

universe u

/-! ## §1 Types and Set-Theoretic Helpers -/

abbrev Meaning (Ctx : Type u) (World : Type u) : Type u :=
  Ctx → Formula World

abbrev Property (Entity : Type u) (Ctx : Type u) (World : Type u) : Type u :=
  Entity → Meaning Ctx World

abbrev Subset {World : Type u} (X Y : Formula World) : Prop :=
  ∀ w, X w → Y w

abbrev Inter {World : Type u} (X Y : Formula World) : Formula World :=
  fun w => X w ∧ Y w

abbrev SetEq {World : Type u} (X Y : Formula World) : Prop :=
  ∀ w, X w ↔ Y w

abbrev Instantiated {World : Type u} (X : Formula World) : Prop :=
  ∃ w, X w

/-! ## §2 Validity and Modal Operators -/

/-- LD truth: φ evaluated at context `c` and its designated world `worldOf c`. -/
def ldTrueCtx {Ctx World : Type u} (worldOf : Ctx → World)
    (φ : Meaning Ctx World) (c : Ctx) : Prop :=
  φ c (worldOf c)

/-- LD validity: true in every context at its own world.
    Corresponds to `KaplanianContext.ld_valid` in DDLPlus.Core. -/
def ldValid {Ctx World : Type u} (worldOf : Ctx → World)
    (φ : Meaning Ctx World) : Prop :=
  ∀ c, ldTrueCtx worldOf φ c

/-- Classical modal validity: true at all contexts and worlds. -/
def modValid {Ctx World : Type u} (φ : Meaning Ctx World) : Prop :=
  ∀ c w, φ c w

/-- Diagonal necessity operator: □ᴰφ is true iff φ is LD-valid.
    Corresponds to `KaplanianContext.box_D` in DDLPlus.Core. -/
def boxD {Ctx World : Type u} (worldOf : Ctx → World)
    (φ : Meaning Ctx World) : Meaning Ctx World :=
  fun _ _ => ldValid worldOf φ

/-- Actual necessity: □ₐφ = "φ holds in all actual alternatives av". -/
def boxA {Ctx World : Type u} (av : World → Formula World)
    (φ : Meaning Ctx World) : Meaning Ctx World :=
  fun c w => ∀ v, av w v → φ c v

/-- Actual possibility: ◇ₐφ = "φ holds in some actual alternative". -/
def diaA {Ctx World : Type u} (av : World → Formula World)
    (φ : Meaning Ctx World) : Meaning Ctx World :=
  fun c w => ∃ v, av w v ∧ φ c v

/-- Possible necessity: □ₚφ = "φ holds in all possible alternatives pv". -/
def boxP {Ctx World : Type u} (pv : World → Formula World)
    (φ : Meaning Ctx World) : Meaning Ctx World :=
  fun c w => ∀ v, pv w v → φ c v

/-- Possible possibility: ◇ₚφ = "φ holds in some possible alternative". -/
def diaP {Ctx World : Type u} (pv : World → Formula World)
    (φ : Meaning Ctx World) : Meaning Ctx World :=
  fun c w => ∃ v, pv w v ∧ φ c v

/-! ## §3 Deontic Operators -/

/-- Conditional obligation: O⟨φ|σ⟩ = ob(σ c)(φ c) lifted to a Meaning. -/
def Ocond {Ctx World : Type u} (ob : Formula World → Formula World → Prop)
    (φ σ : Meaning Ctx World) : Meaning Ctx World :=
  fun c _ => ob (σ c) (φ c)

/-- Ideal obligation: Oᵢφ at (c, w) = ob(pv w)(φ c) + violability witness.
    Definitionally equal to `ideal_obl` (DDLPlus.Core) when ob, pv come from a frame. -/
def Oi {Ctx World : Type u} (ob : Formula World → Formula World → Prop)
    (pv : World → Formula World) (φ : Meaning Ctx World) : Meaning Ctx World :=
  fun c w => ob (pv w) (φ c) ∧ ∃ v, pv w v ∧ ¬ φ c v

/-! ## §4 Purposive Agency Operators -/

/-- Purposeful purposive action: PPA(a) holds iff `a` acts on some purpose `E`. -/
def PPA {Ctx World Entity : Type u}
    (ActsOnPurpose : Entity → Meaning Ctx World → Meaning Ctx World) (a : Entity) :
    Meaning Ctx World :=
  fun c w => ∃ E : Meaning Ctx World, ActsOnPurpose a E c w

/-- Non-interference: no agent `b` interferes with `P a` in the current context. -/
def NonInterference {Ctx World Entity : Type u}
    (InterferesWith : Entity → Meaning Ctx World → Meaning Ctx World)
    (a : Entity) (P : Entity → Meaning Ctx World) : Meaning Ctx World :=
  fun c w => ∀ b : Entity, ¬ InterferesWith b (P a) c w

/-- The right to X: ideal obligation of non-interference with X. -/
def RightTo {Ctx World Entity : Type u} (ob : Formula World → Formula World → Prop)
    (pv : World → Formula World)
    (InterferesWith : Entity → Meaning Ctx World → Meaning Ctx World)
    (a : Entity) (P : Entity → Meaning Ctx World) : Meaning Ctx World :=
  Oi ob pv (NonInterference InterferesWith a P)

/-! ## §5 Interpretation Packaging -/

/-- Bundles all non-logical symbols of the Gewirth embedding. -/
structure PGCInterpretation : Type (u + 1) where
  Ctx    : Type u
  World  : Type u
  Entity : Type u
  worldOf : Ctx → World
  av    : World → Formula World
  pv    : World → Formula World
  ob    : Formula World → Formula World → Prop
  ActsOnPurpose   : Entity → Meaning Ctx World → Meaning Ctx World
  NeedsForPurpose :
    Entity → (Entity → Meaning Ctx World) → Meaning Ctx World → Meaning Ctx World
  Good          : Entity → Meaning Ctx World → Meaning Ctx World
  FWB           : Entity → Meaning Ctx World
  InterferesWith : Entity → Meaning Ctx World → Meaning Ctx World

/-- Names for all PGC assumptions and the conclusion. -/
inductive PGCStatementName : Type
  | sem_5a
  | sem_5b
  | sem_5e
  | explicationGoodness1
  | explicationGoodness2
  | explicationGoodness3
  | explicationFWB1
  | explicationFWB2
  | explicationFWB3
  | OIOAC
  | explicationInterference
  | PGC_strong
  deriving DecidableEq, Repr

/-- The proposition associated with each named PGC assumption or conclusion. -/
def PGCStatement (I : PGCInterpretation) : PGCStatementName → Prop
  | .sem_5a =>
      ∀ X : Formula I.World, ¬ I.ob X (fun _ => False)
  | .sem_5b =>
      ∀ X Y Z : Formula I.World,
        SetEq (Inter X Y) (Inter X Z) → (I.ob X Y ↔ I.ob X Z)
  | .sem_5e =>
      ∀ X Y Z : Formula I.World,
        Subset Y X → I.ob X Z → Instantiated (Inter Y Z) → I.ob Y Z
  | .explicationGoodness1 =>
      ldValid I.worldOf
        (fun c w => ∀ a P, I.ActsOnPurpose a P c w → I.Good a P c w)
  | .explicationGoodness2 =>
      ldValid I.worldOf
        (fun c w => ∀ (P : Meaning I.Ctx I.World) (M : I.Entity → Meaning I.Ctx I.World)
            (a : I.Entity),
          (I.Good a P c w ∧ I.NeedsForPurpose a M P c w) → I.Good a (M a) c w)
  | .explicationGoodness3 =>
      ldValid I.worldOf
        (fun c w => ∀ (φ : Meaning I.Ctx I.World) (a : I.Entity),
          diaP I.pv φ c w →
            Ocond I.ob φ (boxD I.worldOf (I.Good a φ)) c w)
  | .explicationFWB1 =>
      ldValid I.worldOf
        (fun c w => ∀ (P : Meaning I.Ctx I.World) (a : I.Entity),
          I.NeedsForPurpose a I.FWB P c w)
  | .explicationFWB2 =>
      ldValid I.worldOf
        (fun c w => ∀ a : I.Entity, diaP I.pv (I.FWB a) c w)
  | .explicationFWB3 =>
      ldValid I.worldOf
        (fun c w => ∀ a : I.Entity,
          diaP I.pv (fun c' w' => ¬ I.FWB a c' w') c w)
  | .OIOAC =>
      ldValid I.worldOf
        (fun c w => ∀ (φ : Meaning I.Ctx I.World),
          Oi I.ob I.pv φ c w →
            Oi I.ob I.pv (diaA I.av φ) c w)
  | .explicationInterference =>
      modValid
        (fun c w => ∀ (φ : Meaning I.Ctx I.World),
          (∃ b : I.Entity, I.InterferesWith b φ c w) ↔
            ¬ diaA I.av φ c w)
  | .PGC_strong =>
      ldValid I.worldOf
        (fun c w => ∀ x : I.Entity,
          PPA I.ActsOnPurpose x c w →
            RightTo I.ob I.pv I.InterferesWith x I.FWB c w)

/-- All PGC assumptions bundled as a single proposition. -/
structure PGCAssumptions (I : PGCInterpretation) : Prop where
  sem_5a               : PGCStatement I .sem_5a
  sem_5b               : PGCStatement I .sem_5b
  sem_5e               : PGCStatement I .sem_5e
  explicationGoodness1 : PGCStatement I .explicationGoodness1
  explicationGoodness2 : PGCStatement I .explicationGoodness2
  explicationGoodness3 : PGCStatement I .explicationGoodness3
  explicationFWB1      : PGCStatement I .explicationFWB1
  explicationFWB2      : PGCStatement I .explicationFWB2
  explicationFWB3      : PGCStatement I .explicationFWB3
  OIOAC                : PGCStatement I .OIOAC
  explicationInterference : PGCStatement I .explicationInterference

/-! ## §6 Helper Lemmas -/

/-- `ob X Y` implies instantiation of `X ∩ Y`.
    Uses only sem_5a and sem_5b; standalone to avoid requiring a full DDLPlusFrame. -/
theorem sem_5ab {World : Type u} {ob : Formula World → Formula World → Prop}
    (sem_5a : ∀ X, ¬ ob X (fun _ => False))
    (sem_5b : ∀ X Y Z, SetEq (Inter X Y) (Inter X Z) → (ob X Y ↔ ob X Z))
    {X Y : Formula World} :
    ob X Y → Instantiated (Inter X Y) := by
  classical
  intro hOb
  by_cases hInst : Instantiated (Inter X Y)
  · exact hInst
  · have hEmpty : SetEq (Inter X Y) (Inter X (fun _ => False)) := by
      intro w
      constructor
      · intro hXY
        exfalso
        apply hInst
        exact ⟨w, hXY⟩
      · intro hXF
        cases hXF.2
    have hObFalse : ob X (fun _ => False) := by
      have hEq := (sem_5b X Y (fun _ => False) hEmpty).1 hOb
      simpa using hEq
    exact absurd hObFalse (sem_5a X)

/-- CJ_14p (standalone): conditional obligation + box_p B + dia_p A + dia_p ¬A → Oi A.
    Local version with sem_5e as an explicit parameter, matching the calling convention
    in PGC_strong.  The frame-based version is in `Mettapedia.Logic.DDLPlus.Theorems`. -/
theorem CJ_14p {Ctx World : Type u} {ob : Formula World → Formula World → Prop}
    {pv : World → Formula World}
    (sem_5e : ∀ X Y Z, Subset Y X → ob X Z → Instantiated (Inter Y Z) → ob Y Z)
    (A B : Meaning Ctx World) :
    modValid (fun c w =>
      Ocond ob B A c w ∧
        boxP pv A c w ∧
          diaP pv B c w ∧
            diaP pv (fun c' w' => ¬ B c' w') c w →
              Oi ob pv B c w) := by
  intro c w
  intro h
  rcases h with ⟨hO, hBoxA, hDiaB, hDiaNotB⟩
  have hSubset : Subset (pv w) (A c) := fun v hv => hBoxA v hv
  have hInst : Instantiated (Inter (pv w) (B c)) := by
    rcases hDiaB with ⟨v, hv, hBv⟩
    exact ⟨v, hv, hBv⟩
  have hOb : ob (pv w) (B c) :=
    sem_5e (A c) (pv w) (B c) hSubset hO hInst
  rcases hDiaNotB with ⟨v, hv, hNotBv⟩
  exact ⟨hOb, v, hv, hNotBv⟩

/-! ## §7 Main Theorem: PGC_strong -/

/-- Gewirth's Principle of Generic Consistency (strong form).

Every purposeful agent `x` has an ideal right that no other agent interfere
with their freedom and well-being (FWB).

**0 axioms, 0 sorries.**
-/
theorem PGC_strong {Ctx World Entity : Type u}
    (worldOf : Ctx → World)
    (av pv : World → Formula World)
    (ob : Formula World → Formula World → Prop)
    (ActsOnPurpose   : Entity → Meaning Ctx World → Meaning Ctx World)
    (NeedsForPurpose : Entity → (Entity → Meaning Ctx World) →
        Meaning Ctx World → Meaning Ctx World)
    (Good          : Entity → Meaning Ctx World → Meaning Ctx World)
    (FWB           : Entity → Meaning Ctx World)
    (InterferesWith : Entity → Meaning Ctx World → Meaning Ctx World)
    (sem_5a : ∀ X, ¬ ob X (fun _ => False))
    (sem_5b : ∀ X Y Z, SetEq (Inter X Y) (Inter X Z) → (ob X Y ↔ ob X Z))
    (sem_5e : ∀ X Y Z, Subset Y X → ob X Z → Instantiated (Inter Y Z) → ob Y Z)
    (explicationGoodness1 :
      ldValid worldOf
        (fun c w => ∀ a P, ActsOnPurpose a P c w → Good a P c w))
    (explicationGoodness2 :
      ldValid worldOf
        (fun c w => ∀ (P : Meaning Ctx World) (M : Entity → Meaning Ctx World)
            (a : Entity),
          (Good a P c w ∧ NeedsForPurpose a M P c w) → Good a (M a) c w))
    (explicationGoodness3 :
      ldValid worldOf
        (fun c w => ∀ (φ : Meaning Ctx World) (a : Entity),
          diaP pv φ c w →
            Ocond ob φ (boxD worldOf (Good a φ)) c w))
    (explicationFWB1 :
      ldValid worldOf
        (fun c w => ∀ (P : Meaning Ctx World) (a : Entity),
          NeedsForPurpose a FWB P c w))
    (explicationFWB2 :
      ldValid worldOf
        (fun c w => ∀ a : Entity, diaP pv (FWB a) c w))
    (explicationFWB3 :
      ldValid worldOf
        (fun c w => ∀ a : Entity,
          diaP pv (fun c' w' => ¬ FWB a c' w') c w))
    (OIOAC :
      ldValid worldOf
        (fun c w => ∀ (φ : Meaning Ctx World),
          Oi ob pv φ c w → Oi ob pv (diaA av φ) c w))
    (explicationInterference :
      modValid
        (fun c w => ∀ (φ : Meaning Ctx World),
          (∃ b : Entity, InterferesWith b φ c w) ↔ ¬ diaA av φ c w)) :
    ldValid worldOf
      (fun c w => ∀ x : Entity, PPA ActsOnPurpose x c w →
        RightTo ob pv InterferesWith x FWB c w) := by
  classical
  intro C
  intro x hxPPA
  rcases hxPPA with ⟨E, hActs⟩

  have _hGoodE : Good x E C (worldOf C) := by
    have hGood1 := explicationGoodness1 C
    exact hGood1 x E hActs

  have hNeedsAllPurposes : ldValid worldOf (fun c w => ∀ P : Meaning Ctx World,
        NeedsForPurpose x FWB P c w) := by
    intro c
    have hFWB1 := explicationFWB1 c
    intro P
    exact hFWB1 P x

  have hGoodFWBValid : ldValid worldOf (Good x (FWB x)) := by
    have hCondValid : ldValid worldOf
        (Ocond ob (FWB x) (boxD worldOf (Good x (FWB x)))) := by
      intro c
      have hDia : diaP pv (FWB x) c (worldOf c) := by
        have hFWB2 := explicationFWB2 c
        exact hFWB2 x
      have hGood3 := explicationGoodness3 c
      exact hGood3 (FWB x) x hDia
    have hAtC : Ocond ob (FWB x)
        (boxD worldOf (Good x (FWB x))) C (worldOf C) :=
      hCondValid C
    have hInst :
        Instantiated (Inter
          ((boxD worldOf (Good x (FWB x))) C)
          ((FWB x) C)) :=
      sem_5ab (ob := ob) sem_5a sem_5b (X := (boxD worldOf (Good x (FWB x)) C))
        (Y := (FWB x C)) hAtC
    rcases hInst with ⟨w, hBox, hFWB⟩
    have hGoodFWBFromBox : ldValid worldOf (Good x (FWB x)) := by
      simpa [boxD, ldValid, ldTrueCtx] using hBox
    have hNeedFWB : ldValid worldOf (NeedsForPurpose x FWB (FWB x)) := by
      intro c
      have hNeeds := hNeedsAllPurposes c
      exact hNeeds (FWB x)
    have hGoodAndNeed : ldValid worldOf (fun c w =>
          Good x (FWB x) c w ∧ NeedsForPurpose x FWB (FWB x) c w) := by
      intro c
      exact ⟨hGoodFWBFromBox c, hNeedFWB c⟩
    have hGood2 := explicationGoodness2
    intro c
    have hG2 := hGood2 c
    have hAnd := hGoodAndNeed c
    exact hG2 (FWB x) FWB x hAnd

  have hBoxDGoodAtC : (boxD worldOf (Good x (FWB x))) C (worldOf C) := by
    simpa [boxD] using hGoodFWBValid

  have hCondAtC :
      Ocond ob (FWB x) (boxD worldOf (Good x (FWB x))) C (worldOf C) := by
    have hDia : diaP pv (FWB x) C (worldOf C) := by
      have hFWB2 := explicationFWB2 C
      exact hFWB2 x
    have hGood3 := explicationGoodness3 C
    exact hGood3 (FWB x) x hDia

  have hOiFWBAtC : Oi ob pv (FWB x) C (worldOf C) := by
    have hBoxP : boxP pv (boxD worldOf (Good x (FWB x))) C (worldOf C) := by
      intro v _hv
      simpa [boxD] using hBoxDGoodAtC
    have hDiaB : diaP pv (FWB x) C (worldOf C) := by
      have hFWB2 := explicationFWB2 C
      exact hFWB2 x
    have hDiaNotB : diaP pv (fun c' w' => ¬ FWB x c' w') C (worldOf C) := by
      have hFWB3 := explicationFWB3 C
      exact hFWB3 x
    have hCJ := CJ_14p (ob := ob) (pv := pv) sem_5e
      (A := boxD worldOf (Good x (FWB x))) (B := FWB x)
    exact hCJ C (worldOf C) ⟨hCondAtC, hBoxP, hDiaB, hDiaNotB⟩

  have hOiDiaAAtC :
      Oi ob pv (diaA av (FWB x)) C (worldOf C) := by
    have hOIOAC := OIOAC C
    exact hOIOAC (FWB x) hOiFWBAtC

  have hDiaA_iff_nonInterference :
      ∀ w, diaA av (FWB x) C w ↔
        NonInterference InterferesWith x FWB C w := by
    intro w
    have hInt := explicationInterference C w (FWB x)
    constructor
    · intro hDia
      intro b hInterf
      have : ∃ b' : Entity, InterferesWith b' (FWB x) C w := ⟨b, hInterf⟩
      exact absurd hDia ((hInt).1 this)
    · intro hNoInterf
      by_cases hDia : diaA av (FWB x) C w
      · exact hDia
      · rcases (hInt).2 hDia with ⟨b, hb⟩
        exact absurd hb (hNoInterf b)

  have hRightToAtC :
      RightTo ob pv InterferesWith x FWB C (worldOf C) := by
    have hSetEq :
        SetEq
          (Inter (pv (worldOf C)) ((diaA av (FWB x)) C))
          (Inter (pv (worldOf C))
            (NonInterference InterferesWith x FWB C)) := by
      intro w
      constructor
      · intro h
        exact ⟨h.1, (hDiaA_iff_nonInterference w).1 h.2⟩
      · intro h
        exact ⟨h.1, (hDiaA_iff_nonInterference w).2 h.2⟩
    have hObPart :
        ob (pv (worldOf C)) ((diaA av (FWB x)) C) ↔
          ob (pv (worldOf C)) (NonInterference InterferesWith x FWB C) :=
      sem_5b (pv (worldOf C)) ((diaA av (FWB x)) C)
        (NonInterference InterferesWith x FWB C) hSetEq
    rcases hOiDiaAAtC with ⟨hOb, hVio⟩
    refine ⟨hObPart.1 hOb, ?_⟩
    rcases hVio with ⟨v, hv, hNotDia⟩
    exact ⟨v, hv, fun hNI => hNotDia ((hDiaA_iff_nonInterference v).2 hNI)⟩

  exact hRightToAtC

/-- PGC_strong wrapped using bundled PGCInterpretation and PGCAssumptions. -/
theorem PGC_strong_ofAssumptions (I : PGCInterpretation) (h : PGCAssumptions I) :
    PGCStatement I .PGC_strong :=
  PGC_strong
    (worldOf         := I.worldOf)
    (av              := I.av) (pv := I.pv) (ob := I.ob)
    (ActsOnPurpose   := I.ActsOnPurpose)
    (NeedsForPurpose := I.NeedsForPurpose)
    (Good            := I.Good) (FWB := I.FWB)
    (InterferesWith  := I.InterferesWith)
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

end Mettapedia.Ethics.Gewirth
