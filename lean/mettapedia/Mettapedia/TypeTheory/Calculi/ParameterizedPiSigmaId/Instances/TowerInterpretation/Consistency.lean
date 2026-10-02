import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.Soundness
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerAnnotated
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Models.ZFSetReplayUniverseModel

/-!
# The candidate's universe package in the set tower, and relative consistency

The candidate's cumulative universe package `Tower.rules` has heads for
universe levels (level expressions with variables) and one opaque ground head,
and no declared constants or computation. Its annotation `towerPackage`, the
package `TowerControls.P₀` of the annotated calculus, declares no constant and
has no root step.

**The tower model** (`towerModel`). Given the named hypothesis
`h : CofinalInaccessibles.{u}` (every ordinal lies below an inaccessible
cardinal), a seed set, a ground set in the bottom universe and a valuation of
the level variables, a universe level `l` is interpreted by
`universeSet h seed (l.eval valuation)`: the least closed universe around the
previous one, built from `univOf`. The closure obligations are the existing
`CumulativePiSigmaId.ZFSetReplayUniverseModel.universeModel`; nothing is
assumed about typing, conversion or certificates. The hypothesis is an explicit
parameter of every statement here, never an axiom.

**Relative consistency** (`fragment_consistent`). Under
`CofinalInaccessibles.{u}`, no candidate statement `⊢ t : Π (X : U₀). X` lies in
the annotated fragment of `Tower.rules`: the image under erasure of annotated
derivations (`InAnnotatedImage towerPackage`). The type is empty in the model
because the empty set is a small set (`ev_emptyType`).

Controls: the empty type is well formed, in the annotated judgment and, by
erasure, in the candidate (`emptyType_formed`, `emptyType_formed_candidate`);
the neighbouring type `Π (X : U₀). X → X` is inhabited
(`TowerInterpretation.Examples`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation

open Presentation Presentation.TypedEquality Presentation.TypedEquality.Annotated
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseClosure (CofinalInaccessibles Closed)
open ZFSetInterpretation (universeSet universeSet_closed seed_mem_universeSet)
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open ZFSetTraceUniverseInterpretation (interpretHead)
open ZFSetTraceProducts (tracePiSet)

universe u

variable {L : Type} [LevelOrder L]

/-! ## The annotated universe package -/

/-- The candidate's cumulative universe package, annotated: no declared
constants and no root steps. -/
abbrev towerPackage : ChurchRules (LevelTower.rules L) := TowerControls.P₀

/-! ## The tower model -/

/-- The empty set lies in every level of the tower. -/
theorem empty_mem_universeSet (h : CofinalInaccessibles.{u}) (seed : ZFSet.{u}) (k : L) :
    (∅ : ZFSet.{u}) ∈ universeSet h seed k :=
  (universeSet_closed h seed k).empty_mem (seed_mem_universeSet h seed k)

/-- **The tower model of the universe package**, relative to
`CofinalInaccessibles.{u}`. -/
theorem towerModel (h : CofinalInaccessibles.{u}) (seed ground : ZFSet.{u})
    (valuation : Nat → L) (groundTyped : ground ∈ universeSet h seed (LevelOrder.bot : L))
    (consts : DeclName → ZFSet.{u}) :
    SetModel (interpretHead h seed ground valuation) consts towerPackage where
  universes := ZFSetReplayUniverseModel.universeModel h seed ground valuation groundTyped
  headEq same := ZFSetReplayUniverseFormation.headEq_values h seed ground valuation same
  constants known := by cases known
  steps step := step.elim

/-- The standard instance: seed and ground the empty set, every level
variable at the least level, every constant the empty set. -/
theorem standardTowerModel (h : CofinalInaccessibles.{u}) :
    SetModel (interpretHead h ∅ ∅ (fun _ => (LevelOrder.bot : L))) (fun _ => ∅) towerPackage :=
  towerModel h ∅ ∅ (fun _ => LevelOrder.bot) (empty_mem_universeSet h ∅ LevelOrder.bot) (fun _ => ∅)

/-- **Soundness in the tower.** Under `CofinalInaccessibles.{u}`, every
annotated derivation of the universe package holds in the tower model. -/
theorem CDerivable.sound_tower (h : CofinalInaccessibles.{u}) {s : CStatement (LevelTower.Head L)}
    (d : CDerivable towerPackage s) :
    Holds (interpretHead h ∅ ∅ (fun _ => (LevelOrder.bot : L))) (fun _ => ∅) s :=
  CDerivable.sound (standardTowerModel h) d

/-! ## An empty type, and relative consistency -/

/-- The bottom universe `U₀`. -/
abbrev U0 {n : Nat} : CTm (LevelTower.Head L) n := .head (.sort LevelTower.zero)

/-- `Π (X : U₀). X`: an element of every small type. -/
def emptyType : CTm (LevelTower.Head L) 0 := .pi U0 (.var 0)

/-- The empty type has no element in the tower model: the empty set is a
small set with no element. -/
theorem ev_emptyType (h : CofinalInaccessibles.{u}) (seed ground : ZFSet.{u})
    (valuation : Nat → L) (consts : DeclName → ZFSet.{u}) (z : ZFSet.{u}) :
    z ∉ ev (interpretHead h seed ground valuation) consts emptyType Fin.elim0 := by
  intro member
  change z ∈ tracePiSet (universeSet h seed (LevelTower.zero.eval valuation)) (fun x => x) at member
  have value := traceApp_mem_fibre member (empty_mem_universeSet h seed _)
  exact ZFSet.notMem_empty _ value

/-- **Relative consistency of the annotated judgment.** Under
`CofinalInaccessibles.{u}`, no closed annotated term of the universe package has
type `Π (X : U₀). X`. -/
theorem annotated_consistent (h : CofinalInaccessibles.{u}) (t : CTm (LevelTower.Head L) 0) :
    ¬ CDerivable towerPackage (.typing .nil t emptyType) :=
  CDerivable.no_closed_inhabitant (standardTowerModel h) (ev_emptyType h ∅ ∅ _ _) t

/-- **Relative consistency of the annotated fragment of the candidate.** Under
`CofinalInaccessibles.{u}`, no statement `⊢ t : Π (X : U₀). X` of the candidate
package `(LevelTower.rules L)` is the erasure of an annotated derivation. -/
theorem fragment_consistent (h : CofinalInaccessibles.{u}) (t : LevelTower.Tm L 0) :
    ¬ InAnnotatedImage towerPackage (.typing .nil t emptyType.erase) := by
  rintro ⟨s, d, e⟩
  cases s with
  | typing Γ t' A =>
      simp only [CStatement.erase, Statement.typing.injEq] at e
      obtain ⟨rfl, hΓ, _, hA⟩ := e
      cases Γ with
      | nil =>
          obtain ⟨D, X, rfl, eD, eX⟩ := CTm.erase_eq_pi (eq_of_heq hA)
          obtain rfl := CTm.erase_eq_head eD
          obtain rfl := CTm.erase_eq_var eX
          exact annotated_consistent h t' d
  | equality Γ a b A => simp only [CStatement.erase, reduceCtorEq] at e
  | sub Γ A B => simp only [CStatement.erase, reduceCtorEq] at e

/-! ## Controls -/

/-- The empty type is a well-formed type of the annotated universe package. -/
theorem emptyType_formed :
    CDerivable (towerPackage (L := L))
      (.typing .nil emptyType (.head (.sort (.max (.succ LevelTower.zero) LevelTower.zero)))) :=
  .piForm (.headType (LevelTower.HeadTyping.sort LevelTower.zero)) (LevelTower.IsUniverse.sort _)
    (.var 0) (LevelTower.IsUniverse.sort _) (LevelTower.Join.sorts _ _)

/-- Its erasure is a well-formed type of the candidate package. -/
theorem emptyType_formed_candidate :
    Derivable (LevelTower.rules L)
      (.typing .nil emptyType.erase (.head (.sort (.max (.succ LevelTower.zero) LevelTower.zero)))) :=
  emptyType_formed.erase

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
