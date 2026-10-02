import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerInterpretation.Consistency

/-!
# Closed derivations of the universe package and their values in the tower

Positive controls for the interpretation. Each closed annotated derivation
below erases to a derivation of the candidate package `Tower.rules`, and its
value in the tower model is computed:

* the polymorphic identity `λ (X : U₀). λ (x : X). x` has type
  `Π (X : U₀). X → X`, and its value is the trace of the family of identity
  graphs over the small sets (`ev_polyId`);
* a β-redex at the ground head computes to the ground set (`betaGround`,
  `ev_betaRedex`);
* reflexivity at the ground head is the empty set, the one proof of a true
  identity (`reflGround`, `ev_reflGround`).

Negative control: the neighbouring type `Π (X : U₀). X` has no closed
inhabitant (`Consistency.annotated_consistent`), while `Π (X : U₀). X → X`
does (`polyId_typed`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
namespace Examples

open Presentation Presentation.TypedEquality Presentation.TypedEquality.Annotated
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseClosure (CofinalInaccessibles)
open ZFSetInterpretation (universeSet)
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open ZFSetTraceUniverseInterpretation (interpretHead)
open ZFSetDependentProducts (graph)
open ZFSetTraceProducts (traceLam traceApp tracePiSet)
open ZFSetTraceProofDecoding (truthCode)

universe u

/-- The polymorphic identity `λ (X : U₀). λ (x : X). x`. -/
def polyId : CTm Tower.Head 0 := .lam U0 (.lam (.var 0) (.var 0))

/-- Its type `Π (X : U₀). X → X`. -/
def polyIdType : CTm Tower.Head 0 := .pi U0 (.pi (.var 0) (.var 1))

/-- The level of `X → X` for `X : U₀`. -/
abbrev innerLevel : Tower.Head := .sort (.max Tower.zero Tower.zero)

/-- The level of `Π (X : U₀). X → X`. -/
abbrev outerLevel : Tower.Head := .sort (.max (.succ Tower.zero) (.max Tower.zero Tower.zero))

theorem inner_formed :
    CDerivable towerPackage
      (.typing (.snoc .nil U0) (.pi (.var 0) (.var 1)) (.head innerLevel)) :=
  .piForm (.var 0) (LevelTower.IsUniverse.sort _) (.var 1) (LevelTower.IsUniverse.sort _)
    (LevelTower.Join.sorts _ _)

theorem polyIdType_formed :
    CDerivable towerPackage (.typing .nil polyIdType (.head outerLevel)) :=
  .piForm (.headType (LevelTower.HeadTyping.sort Tower.zero)) (LevelTower.IsUniverse.sort _)
    inner_formed (LevelTower.IsUniverse.sort _) (LevelTower.Join.sorts _ _)

/-- The polymorphic identity is derivable at its type. -/
theorem polyId_typed : CDerivable towerPackage (.typing .nil polyId polyIdType) :=
  .lamIntro (.headType (LevelTower.HeadTyping.sort Tower.zero)) (LevelTower.IsUniverse.sort _)
    polyIdType_formed (LevelTower.IsUniverse.sort _)
    (.lamIntro (.var 0) (LevelTower.IsUniverse.sort _) inner_formed (LevelTower.IsUniverse.sort _) (.var 0))

/-- Its erasure is a candidate derivation. -/
theorem polyId_candidate :
    Derivable Tower.rules (.typing .nil polyId.erase polyIdType.erase) :=
  polyId_typed.erase

/-- **The value of the polymorphic identity**: the trace of the family of
identity graphs over the small sets. -/
theorem ev_polyId (h : CofinalInaccessibles.{u}) :
    ev (interpretHead h ∅ ∅ (fun _ => 0)) (fun _ => ∅) polyId Fin.elim0 =
      traceLam (graph (universeSet h ∅ 0) (fun X => traceLam (graph X (fun x => x)))) :=
  rfl

/-- The value of its type: the trace products of the identity types. -/
theorem ev_polyIdType (h : CofinalInaccessibles.{u}) :
    ev (interpretHead h ∅ ∅ (fun _ => 0)) (fun _ => ∅) polyIdType Fin.elim0 =
      tracePiSet (universeSet h ∅ 0) (fun X => tracePiSet X (fun _ => X)) :=
  rfl

/-- The computed value inhabits the computed type, by soundness. -/
theorem polyId_mem (h : CofinalInaccessibles.{u}) :
    traceLam (graph (universeSet h ∅ 0) (fun X => traceLam (graph X (fun x => x)))) ∈
      tracePiSet (universeSet h ∅ 0) (fun X => tracePiSet X (fun _ => X)) :=
  CDerivable.inhabited (standardTowerModel h) polyId_typed

/-! ## A β-redex at the ground head -/

/-- The ground head. -/
abbrev ground {n : Nat} : CTm Tower.Head n := .head .legacyGround

/-- `λ (X : U₀). X` has type `Π (X : U₀). U₀`. -/
theorem idU0_typed :
    CDerivable (towerPackage (L := Nat)) (.typing .nil (.lam U0 (.var 0)) (.pi U0 U0)) :=
  .lamIntro (.headType (LevelTower.HeadTyping.sort Tower.zero)) (LevelTower.IsUniverse.sort _)
    (.piForm (.headType (LevelTower.HeadTyping.sort Tower.zero)) (LevelTower.IsUniverse.sort _)
      (.headType (LevelTower.HeadTyping.sort Tower.zero)) (LevelTower.IsUniverse.sort _)
      (LevelTower.Join.sorts _ _))
    (LevelTower.IsUniverse.sort _) (.var 0)

/-- `(λ (X : U₀). X) ground ≡ ground : U₀`. -/
theorem betaGround :
    CDerivable towerPackage
      (.equality .nil (.app (.lam U0 (.var 0)) ground) ground U0) :=
  CDerivable.betaPi (A := U0) (a := ground) (body := .var 0) (B := U0)
    (.piForm (.headType (LevelTower.HeadTyping.sort Tower.zero)) (LevelTower.IsUniverse.sort _)
      (.headType (LevelTower.HeadTyping.sort Tower.zero)) (LevelTower.IsUniverse.sort _)
      (LevelTower.Join.sorts _ _))
    (LevelTower.IsUniverse.sort _) (.var 0) (.headType LevelTower.HeadTyping.legacyGround)

/-- Its erasure is a candidate β-equality. -/
theorem betaGround_candidate :
    Derivable Tower.rules
      (.equality .nil (Tm.app (.lam (.var 0)) (.head .legacyGround)) (.head .legacyGround)
        (.head (.sort Tower.zero))) :=
  betaGround.erase

/-- The redex computes to the ground set in the tower model. -/
theorem ev_betaRedex (h : CofinalInaccessibles.{u}) :
    traceApp (traceLam (graph (universeSet h ∅ 0) (fun X => X))) ∅ = (∅ : ZFSet.{u}) :=
  CDerivable.sound_equality (standardTowerModel h) betaGround Fin.elim0
    (sat_nil _ _ Fin.elim0)

/-! ## Reflexivity -/

/-- `refl ground : Id U₀ ground ground`. -/
theorem reflGround :
    CDerivable towerPackage (.typing .nil (.refl ground) (.id U0 ground ground)) :=
  .reflIntro (.headType LevelTower.HeadTyping.legacyGround)

/-- Reflexivity is the empty set, inside the true identity value `{∅}`. -/
theorem ev_reflGround (h : CofinalInaccessibles.{u}) :
    (∅ : ZFSet.{u}) ∈ truthCode ((∅ : ZFSet.{u}) = ∅) :=
  CDerivable.inhabited (standardTowerModel h) reflGround

end Examples
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
