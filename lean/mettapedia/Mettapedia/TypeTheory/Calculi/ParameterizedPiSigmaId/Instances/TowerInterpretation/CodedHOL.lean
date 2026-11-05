import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.CodedHOL
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerInterpretation.Consistency

/-!
# Generated HOL judgments for the actual universe tower

The established tower construction discharges the abstract SetModel premise.
The cofinal-inaccessibles hypothesis, ground smallness, level valuation and
declared constant interpretation stay explicit. This supplies a semantic
instance for the whole annotated tower package, not native proof production.
-/

set_option autoImplicit false
namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
namespace CodedTower
open Presentation TypedEquality.Annotated
open Mettapedia.Logic Mettapedia.Logic.HOL
open Mettapedia.TypeTheory.UniverseLevel
open HOL.Embedding ZFSetUniverseClosure ZFSetInterpretation
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetTraceUniverseInterpretation (interpretHead)
universe u

theorem generated_judgment_holds {L : Type} [LevelOrder L]
    (h : CofinalInaccessibles.{u}) (seed ground : ZFSet.{u}) (levels : Nat → L)
    (groundTyped : ground ∈ universeSet h seed (LevelOrder.bot : L))
    (constants : DeclName → ZFSet.{u}) {statement : CStatement (LevelTower.Head L)}
    (derivation : CDerivable towerPackage statement) {Γ : Ctx Unit}
    (bound : Fin (CodedHOL.statementArity statement) → Term (CodedHOL.Symbol (LevelTower.Head L)) Γ CodedHOL.object)
    (rho : (CodedHOL.model (interpretHead h seed ground levels) constants).Valuation Γ) :
    ((CodedHOL.model (interpretHead h seed ground levels) constants).denote
      (CodedHOL.judgmentAt statement bound) rho).down :=
  CodedHOL.judgmentAt_holds _ _ (towerModel h seed ground levels groundTyped constants) derivation bound rho

#print axioms generated_judgment_holds
end CodedTower
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
