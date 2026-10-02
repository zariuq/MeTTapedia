import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerInterpretation.Elaboration
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerInterpretation.Consistency
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.ChurchSoundness
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerOrdinalLevels

/-!
# Every candidate derivation of the tower in the set tower, and relative consistency

The candidate's universe package `Tower.rules` writes abstractions without their domains. Every
derivation of it over a formed context elaborates to a derivation of its annotation
`towerPackage`, the package `TowerControls.P₀` (`tower_elaborates`, from `tower_lifts`), and the
annotated judgment is sound in the set tower (`CDerivable.sound_tower`). So, relative to the
named hypothesis `CofinalInaccessibles`, which enters as a parameter and never as an axiom:

* **soundness of every candidate derivation** (`Derivable.sound_tower`): every derivation of
  `Tower.rules` over a formed context is the erasure of an annotated derivation whose statement
  holds in the tower model, with universe levels interpreted by `universeSet`;
* **the annotated fragment is every derivation** (`inAnnotatedImage`): every derivable candidate
  statement over a formed context is the erasure of a derivation of the annotated judgment
  `CDerivable towerPackage`, its elaboration;
* **relative consistency of the candidate's universe package** (`candidate_consistent`): no
  closed candidate term has type `Π (X : U₀). X`. This is the consistency of the annotated
  fragment (`fragment_consistent`), which covers every derivation.

The level order is a parameter. Soundness reads a typing as membership in a set. On the
universes at closed levels the converse holds too: in a formed context, membership, usability
and equality of universes in the judgment are membership, inclusion and equality of their sets
(`universeAt_mem_iff_universeSet`, `universeAt_below_iff_universeSet`,
`universeAt_typeEq_iff_universeSet`).

Over the ordinal notations below ε₀ the same theorems give the soundness and the relative
consistency of the tower with a universe at every level below ε₀ (`ordinal_sound`,
`ordinal_consistent`). The universe at `ω` is read as the stage of the set tower at `ω`.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation

open Presentation Presentation.TypedEquality Presentation.TypedEquality.Annotated
open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseClosure (CofinalInaccessibles)
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open ZFSetTraceUniverseInterpretation (interpretHead)
open Mettapedia.TypeTheory.UniverseLevel
open ZFSetInterpretation (universeSet universeSet_mem_iff universeSet_subset_iff universeSet_injective)

universe u

variable {L : Type} [UniverseLevel.LevelOrder L]

/-! ## Every candidate derivation -/

/-- **Every candidate derivation over a formed context elaborates** to a derivation of the
tower's annotation over a formed annotated context. -/
theorem tower_elaborates {statement : Statement (LevelTower.Head L)}
    (derivation : Derivable (LevelTower.rules L) statement) (formed : statement.CtxFormed (LevelTower.rules L)) :
    ∃ s : CStatement (LevelTower.Head L), s.CtxFormed (TowerControls.P₀ (L := L)) ∧
      CDerivable (TowerControls.P₀ (L := L)) s ∧ s.erase = statement :=
  Derivable.elaborates towerLevels towerLiftingFacts derivation formed

/-- **Soundness of every candidate derivation of the tower in the set tower.** Under
`CofinalInaccessibles.{u}`, every derivation of `(LevelTower.rules L)` over a formed context is the
erasure of an annotated derivation whose statement holds in the tower model. -/
theorem Derivable.sound_tower (h : CofinalInaccessibles.{u}) {statement : Statement (LevelTower.Head L)}
    (derivation : Derivable (LevelTower.rules L) statement) (formed : statement.CtxFormed (LevelTower.rules L)) :
    ∃ s : CStatement (LevelTower.Head L), CDerivable (TowerControls.P₀ (L := L)) s ∧ s.erase = statement ∧
      Holds (interpretHead h ∅ ∅ (fun _ => (UniverseLevel.LevelOrder.bot : L))) (fun _ => ∅) s :=
  Derivable.sound_elaborated towerLevels towerLiftingFacts (standardTowerModel h) derivation
    formed

/-- **The annotated fragment covers every derivation**: every derivable candidate statement of
the tower over a formed context lies in the annotated fragment `InAnnotatedImage towerPackage`. -/
theorem inAnnotatedImage {statement : Statement (LevelTower.Head L)}
    (derivation : Derivable (LevelTower.rules L) statement) (formed : statement.CtxFormed (LevelTower.rules L)) :
    InAnnotatedImage towerPackage statement :=
  Derivable.inAnnotatedImage towerLevels towerLiftingFacts derivation formed

/-! ## Relative consistency -/

/-- **Relative consistency of the candidate's universe package.** Under
`CofinalInaccessibles.{u}`, no closed candidate term has type `Π (X : U₀). X`: the typing would
lie in the annotated fragment, which has no closed inhabitant of the empty type. -/
theorem candidate_consistent (h : CofinalInaccessibles.{u}) (t : LevelTower.Tm L 0) :
    ¬ Derivable (LevelTower.rules L) (.typing .nil t emptyType.erase) :=
  fun typing => fragment_consistent h t (inAnnotatedImage typing .nil)

/-! ## The judgment and the set tower agree on the universes -/

section Universes

open Normalization (CtxFormed TypeEq)
open Normalization.LevelTower (universeAt universeAt_mem_iff universeAt_below_iff
  universeAt_typeEq_iff)

variable {n : Nat} {Γ : LevelTower.Ctx L n}

/-- The value of the universe at a closed level is the stage of the set tower at that level,
under every valuation of the level variables. -/
theorem interpretHead_universeAt (h : CofinalInaccessibles.{u}) (seed ground : ZFSet.{u})
    (valuation : Nat → L) (c : L) :
    interpretHead h seed ground valuation (.sort (.const c)) = universeSet h seed c := rfl

/-- **Membership of universes**: a universe is a member of another in the judgment exactly
when its set is a member of the other's. -/
theorem universeAt_mem_iff_universeSet (h : CofinalInaccessibles.{u}) (seed : ZFSet.{u})
    (formed : CtxFormed (LevelTower.rules L) Γ) {c d : L} :
    Typed (LevelTower.rules L) Γ (universeAt c) (universeAt d) ↔
      universeSet h seed c ∈ universeSet h seed d :=
  (universeAt_mem_iff formed).trans (universeSet_mem_iff h seed).symm

/-- **Usability of universes**: a universe is usable at another in the judgment exactly when
its set is included in the other's. -/
theorem universeAt_below_iff_universeSet (h : CofinalInaccessibles.{u}) (seed : ZFSet.{u})
    (formed : CtxFormed (LevelTower.rules L) Γ) {c d : L} :
    Below (LevelTower.rules L) Γ (universeAt c) (universeAt d) ↔
      universeSet h seed c ⊆ universeSet h seed d :=
  (universeAt_below_iff formed).trans (universeSet_subset_iff h seed).symm

/-- **Equality of universes**: two universes are equal types in the judgment exactly when
their sets are equal. -/
theorem universeAt_typeEq_iff_universeSet (h : CofinalInaccessibles.{u}) (seed : ZFSet.{u})
    (formed : CtxFormed (LevelTower.rules L) Γ) {c d : L} :
    TypeEq (LevelTower.rules L) Γ (universeAt c) (universeAt d) ↔
      universeSet h seed c = universeSet h seed d :=
  (universeAt_typeEq_iff formed).trans (universeSet_injective h seed).eq_iff.symm

end Universes

/-! ## The tower over the ordinal notations below ε₀ -/

/-- **Soundness of the tower over the ordinal notations in the set tower.** Under
`CofinalInaccessibles.{u}`, every derivation of the tower with a universe at every level below
ε₀, over a formed context, is the erasure of an annotated derivation whose statement holds in
the set tower over the notations. -/
theorem ordinal_sound (h : CofinalInaccessibles.{u}) {statement : Statement (LevelTower.Head Level)}
    (derivation : Derivable (LevelTower.rules Level) statement)
    (formed : statement.CtxFormed (LevelTower.rules Level)) :
    ∃ s : CStatement (LevelTower.Head Level), CDerivable (TowerControls.P₀ (L := Level)) s ∧
      s.erase = statement ∧
      Holds (interpretHead h ∅ ∅ (fun _ => (LevelOrder.bot : Level))) (fun _ => ∅) s :=
  Derivable.sound_tower h derivation formed

/-- **Relative consistency of the tower over the ordinal notations.** Under
`CofinalInaccessibles.{u}`, no closed term of the tower with a universe at every level below ε₀
has type `Π (X : U₀). X`. -/
theorem ordinal_consistent (h : CofinalInaccessibles.{u}) (t : LevelTower.Tm Level 0) :
    ¬ Derivable (LevelTower.rules Level) (.typing .nil t emptyType.erase) :=
  candidate_consistent h t

/-- The universe at `ω` is read as the stage of the set tower at `ω`. -/
theorem universe_omega_value (h : CofinalInaccessibles.{u}) :
    interpretHead h ∅ ∅ (fun _ => (LevelOrder.bot : Level)) (.sort (.const Level.omega)) =
      universeSet h ∅ Level.omega := rfl

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
