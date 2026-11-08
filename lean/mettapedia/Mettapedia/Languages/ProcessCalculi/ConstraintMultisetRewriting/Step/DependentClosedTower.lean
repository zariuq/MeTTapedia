import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentClosed
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerInterpretation.CandidateSoundness
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerConservativity

/-!
# The closed-point trap over the candidate's universe tower

Over the cumulative universe tower `Tower.rules`, the type `⊥ := Π (X : U₀). X` is formed. Relative
to `CofinalInaccessibles` (every ordinal lies below an inaccessible cardinal; an explicit hypothesis
of each statement, never an axiom), it has no closed term: a closed formation-sensitive derivation
is a derivation of the typed equality, and the set tower refutes it (`bottom_empty`).

At the frame `x : ⊥` with no knowledge, a helper `y : ⊥` valued `x` is admitted, because the empty
store is symbolically solvable, and is not closed-admitted, because the frame has no closed point
(`trap`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

namespace Dependent

namespace TowerTrap

open _root_.CategoryTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.FormationSensitiveContextual
open Mettapedia.Logic.HOL.Embedding.ZFSetUniverseClosure (CofinalInaccessibles)

universe u

/-- `⊥ := Π (X : U₀). X`, formed in the universe above `U₀`. -/
def bottom : TypeOver (empty Tower.rules) :=
  ⟨TowerInterpretation.emptyType.erase, .sort (.max (.succ LevelTower.zero) LevelTower.zero),
    LevelTower.IsUniverse.sort _,
    .piForm (.headType (LevelTower.HeadTyping.sort LevelTower.zero)) (LevelTower.IsUniverse.sort _)
      (.var 0) (LevelTower.IsUniverse.sort _) (LevelTower.Join.sorts _ _)⟩

/-- **`⊥` has no closed term**, relative to `CofinalInaccessibles.{u}`. -/
theorem bottom_empty (h : CofinalInaccessibles.{u}) : IsEmpty (Term (empty Tower.rules) bottom) :=
  ⟨fun t => TowerInterpretation.candidate_consistent h t.code
    (TypedEquality.Normalization.Tower.formationSensitive_toTyped t.typed .nil)⟩

/-- The frame `x : ⊥`, with no knowledge and no occurrences. -/
abbrev obligation : State Tower.rules Nat := ⟨extend (empty Tower.rules) bottom, [], ∅⟩

/-- A helper `y : ⊥`, valued `x`. -/
def copy : Firing obligation := ⟨0, bottom.reindex (projectionHom _ bottom), newest _ bottom, []⟩

/-- **The trap over the tower.** Relative to `CofinalInaccessibles.{u}`, the empty store at the frame
`x : ⊥` is symbolically solvable and has no closed solution, and the helper `y : ⊥ := x` is
admitted and not closed-admitted. -/
theorem trap (h : CofinalInaccessibles.{u}) :
    ((frames Tower.rules).Solvable (a := obligation.frame) [] ∧
      ¬ (frames Tower.rules).ClosedSolvable (empty Tower.rules) (a := obligation.frame) []) ∧
    ((helperStep (rules := Tower.rules)).Admits copy ∧
      ¬ (helperStep (rules := Tower.rules)).ClosedAdmits (empty Tower.rules) copy) :=
  ⟨⟨(obligation_trap bottom).1, fun closed =>
      ((obligation_trap bottom).2.mp closed).elim (bottom_empty h).false⟩,
    trap_helper bottom (bottom_empty h) ∅ copy (by decide) rfl⟩

end TowerTrap

end Dependent

#print axioms Dependent.TowerTrap.bottom_empty
#print axioms Dependent.TowerTrap.trap

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
