import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.PurePackages
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerAnnotated
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.SystemFNormalization

/-!
# Elaboration of the cumulative tower: the Church–Curry correspondence

The candidate's universe package over a level order, `LevelTower.rules L`, writes abstractions
without their domains. Its annotation `TowerControls.P₀` records them. The level order is a
parameter: the tower with natural-number levels `Tower.rules` and the tower over the ordinal
notations are instances. This file proves that every candidate derivation
over a formed context is the erasure of an annotated derivation (`tower_lifts`): the domain of
every abstraction is reconstructed from the type it is checked at.

The package is pure: it declares no constant and has no root computation (`tower_pure`). The
general theorem for pure packages (`LiftingFacts.ofPure`) needs:

* the universe laws: the tower's level model and cumulativity algebra
  (`Normalization.TowerModel`);
* a reading of the heads: universe levels as the universe, the legacy ground head as the
  ground type (`towerHeadReading`), with head equality trivial on the ground head
  (`tower_groundHeadEq`);
* strong normalization of typed terms (`tower_sn`): the tower is a sub-package of the package
  of System F codes over it (`tower_sub_systemF`), whose typed terms are strongly normalizing
  for a reduction with more root steps (`SystemF.rules_sn`).

Consequences: the injectivity and no-confusion of the annotated type formers
(`towerFormerFacts`), coherence of annotations (`tower_coherence`), and the lifting of formed
contexts, typings, types and equations of types (`tower_lift_ctxFormed`, `tower_lift_typed`,
`tower_lift_isType`, `tower_lift_typeEq`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation

open Presentation Presentation.TypedEquality Presentation.TypedEquality.Annotated
open Presentation.TypedEquality.Normalization (CtxFormed IsType TypeEq RulesSub)
open Presentation.TypedEquality.Impredicative.Domain (Tok Elem.univ Elem.ground Elem.ty_tag
  Elem.ty_univ_univ Elem.isUniv_univ)

variable {L : Type} [UniverseLevel.LevelOrder L]

/-! ## The tower is a pure package -/

/-- **The tower is a pure universe package**: no declared constant, no root computation. -/
theorem tower_pure : (LevelTower.rules L).Pure where
  noConstants := fun _ => rfl
  noSteps := fun h => h

/-- The annotation of the pure tower is the tower's annotation `(TowerControls.P₀ (L := L))`. -/
theorem tower_church : ChurchRules.ofPure (tower_pure (L := L)) = TowerControls.P₀ := rfl

/-- The element of a head of the tower: every universe level is the universe, the legacy
ground head a ground type. -/
def towerRead : (LevelTower.Head L) → List Tok
  | .legacyGround => Elem.ground
  | .sort _ => Elem.univ

/-- **The reading of the tower's heads.** -/
def towerHeadReading : HeadReading (LevelTower.rules L) where
  read := towerRead
  universes := by
    intro h hu
    cases hu
    rfl
  types := by
    intro h
    cases h with
    | legacyGround => exact Elem.ty_tag (k := .ground) trivial Elem.isUniv_univ
    | sort _ => exact Elem.ty_univ_univ
  headEq := by
    intro h h' same
    cases h with
    | legacyGround =>
        cases h' with
        | legacyGround => rfl
        | sort _ => exact same.elim
    | sort l =>
        cases h' with
        | legacyGround => exact same.elim
        | sort _ => rfl
  ground := by
    intro h u _ hh
    cases h with
    | legacyGround => rfl
    | sort l => exact (hh (.sort l)).elim

/-- **Head equality is trivial on the legacy ground head.** -/
theorem tower_groundHeadEq : GroundHeadEq (LevelTower.rules L) := by
  intro h h' same
  cases h with
  | legacyGround =>
      cases h' with
      | legacyGround => exact .inr rfl
      | sort _ => exact same.elim
  | sort l => exact .inl (.sort l)

/-! ## Strong normalization -/

/-- **The tower is a sub-package of the package of System F codes over it.** -/
theorem tower_sub_systemF : RulesSub (LevelTower.rules L) (Impredicative.SystemF.rulesOver L) where
  headTyping := id
  isUniverse := id
  join := id
  cumulative := id
  headEq := id
  constantType := fun h => (nomatch h)
  computation := fun h => h.elim

/-- **Strong normalization of the tower**: every term typed in a formed context is strongly
normalizing for the tower's reduction. -/
theorem tower_sn {n : Nat} {Γ : LevelTower.Ctx L n} {t A : LevelTower.Tm L n} (formed : CtxFormed (LevelTower.rules L) Γ)
    (typed : Typed (LevelTower.rules L) Γ t A) : StrongNormalization.SN (LevelTower.rules L) t :=
  StrongNormalization.SN.of_rootSub (R := (LevelTower.rules L)) (R' := (Impredicative.SystemF.rulesOver L))
    (fun h => h.elim)
    (Impredicative.SystemF.rules_sn (formed.mono tower_sub_systemF)
      (Normalization.Derivable.mono tower_sub_systemF typed)).1

/-! ## Injectivity of the type formers, coherence and the lifting -/

/-- The universe laws of the tower, at the valuation sending every level variable to the least
level. -/
abbrev towerLevels : Normalization.LevelModel (LevelTower.rules L) L :=
  Normalization.TowerModel.levels fun _ => UniverseLevel.LevelOrder.bot

/-- The bottom universe is a universe. -/
theorem tower_universe : (LevelTower.rules L).isUniverse (.sort LevelTower.zero) := .sort _

/-- **Injectivity and no-confusion of the tower's annotated type formers.** -/
theorem towerFormerFacts : CFormerFacts (TowerControls.P₀ (L := L)) :=
  CFormerFacts.ofPure tower_pure towerLevels towerHeadReading tower_groundHeadEq tower_universe

/-- **The facts the lifting needs, for the tower.** -/
theorem towerLiftingFacts : LiftingFacts (TowerControls.P₀ (L := L)) :=
  LiftingFacts.ofPure tower_pure towerLevels Normalization.TowerModel.algebra towerHeadReading
    tower_groundHeadEq tower_universe tower_sn

/-- **Coherence of annotations in the tower**: two annotated terms with one erasure, typed at
one type in one formed context, are equal at it. -/
theorem tower_coherence {n : Nat} {Γ : CCtx (LevelTower.Head L) n}
    (formed : CCtxFormed (TowerControls.P₀ (L := L)) Γ) {t t' A : CTm (LevelTower.Head L) n}
    (typing : CTyped (TowerControls.P₀ (L := L)) Γ t A) (typing' : CTyped (TowerControls.P₀ (L := L)) Γ t' A)
    (same : t.erase = t'.erase) :
    CEqual (TowerControls.P₀ (L := L)) Γ t t' A :=
  towerLiftingFacts.coherent formed typing typing' same

/-- **The Church–Curry correspondence for the tower**: every candidate derivation lifts to an
annotated derivation, over every formed annotated context erasing to its context. -/
theorem tower_lifts {statement : Statement (LevelTower.Head L)}
    (derivation : Derivable (LevelTower.rules L) statement) : Lifts (TowerControls.P₀ (L := L)) statement :=
  lifts towerLevels towerLiftingFacts derivation

/-- **A formed candidate context is the erasure of a formed annotated context.** -/
theorem tower_lift_ctxFormed {n : Nat} {Γ : LevelTower.Ctx L n} (formed : CtxFormed (LevelTower.rules L) Γ) :
    ∃ Γ' : CCtx (LevelTower.Head L) n, CCtxFormed (TowerControls.P₀ (L := L)) Γ' ∧ Γ'.erase = Γ :=
  lift_ctxFormed towerLevels towerLiftingFacts formed

/-- **A typing of a formed candidate context lifts.** -/
theorem tower_lift_typed {n : Nat} {Γ : LevelTower.Ctx L n} {t A : LevelTower.Tm L n}
    (formed : CtxFormed (LevelTower.rules L) Γ) (typing : Typed (LevelTower.rules L) Γ t A) :
    ∃ (Γ' : CCtx (LevelTower.Head L) n) (t' A' : CTm (LevelTower.Head L) n), CCtxFormed (TowerControls.P₀ (L := L)) Γ' ∧
      Γ'.erase = Γ ∧ t'.erase = t ∧ A'.erase = A ∧ CTyped (TowerControls.P₀ (L := L)) Γ' t' A' :=
  lift_typed towerLevels towerLiftingFacts formed typing

/-- **A type of a formed candidate context lifts.** -/
theorem tower_lift_isType {n : Nat} {Γ : LevelTower.Ctx L n} {A : LevelTower.Tm L n}
    (formed : CtxFormed (LevelTower.rules L) Γ) (type : IsType (LevelTower.rules L) Γ A) :
    ∃ (Γ' : CCtx (LevelTower.Head L) n) (A' : CTm (LevelTower.Head L) n), CCtxFormed (TowerControls.P₀ (L := L)) Γ' ∧
      Γ'.erase = Γ ∧ A'.erase = A ∧ CIsType (TowerControls.P₀ (L := L)) Γ' A' :=
  lift_isType towerLevels towerLiftingFacts formed type

/-- **An equation of types of a formed candidate context lifts.** -/
theorem tower_lift_typeEq {n : Nat} {Γ : LevelTower.Ctx L n} {A B : LevelTower.Tm L n}
    (formed : CtxFormed (LevelTower.rules L) Γ) (equal : TypeEq (LevelTower.rules L) Γ A B) :
    ∃ (Γ' : CCtx (LevelTower.Head L) n) (A' B' : CTm (LevelTower.Head L) n), CCtxFormed (TowerControls.P₀ (L := L)) Γ' ∧
      Γ'.erase = Γ ∧ A'.erase = A ∧ B'.erase = B ∧ CTypeEq (TowerControls.P₀ (L := L)) Γ' A' B' :=
  lift_typeEq towerLevels towerLiftingFacts formed equal

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
