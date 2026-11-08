import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentFullRace
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentUpdateLifting

/-!
# Dead helpers at dependent frames: live firings carried forward

A state **extended by a dead helper** `d : D` (`deadExtension`) is the state read at `Γ.D` along the
weakening: its knowledge and labels never mention `d`. A **live** firing is one carried from the
smaller state (`Natural.move` along the weakening), so it never mentions `d` either.

* **Solvability ignores a dead helper** (`solvable_dead`): every solution of the smaller knowledge
  extends to the larger frame by a fresh variable of the dead helper's type, read along the solution
  (`rawLift`); no inhabitant of `D` is needed.
* **A live firing admitted at the smaller state is admitted at the extended one**
  (`dead_admits_of_admits`), and its result is the smaller result extended by the same dead helper
  (`dead_result`). So the extended state simulates the smaller one on live firings, and the relation
  is kept by every move (`dead_moves`).
* **What is not proved here: the converse.** An admitted live firing at the extended state is
  admitted at the smaller one only if the typed judgments strengthen past an unused variable: a made
  row typed at `Γ.D` must be typed at `Γ`, and two solutions differing by a weakening must agree on the
  guards and query regions. No strengthening lemma for typed judgments is in the tree.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
namespace DependentFull

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open TypedContextual.QuotientComprehensionSyntax
open ContextualDependentEta

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head} {levels : LevelModel rules L}
  {O : Type}

/-- **Solvability ignores a dead helper.** -/
theorem solvable_dead {Δ : Context rules} (D : TypeOver Δ) (K : EquationStore (TotalTerm Δ)) :
    (frames levels).Solvable ((frames levels).applyStore (projectionHom Δ D) K) ↔ (frames levels).Solvable K := by
  constructor
  · exact Frames.solvable_of_applyStore (X := frames levels) _
  · rintro ⟨Θ, τ, solved⟩
    refine ⟨_, rawLift τ D, (Frames.models_applyStore (X := frames levels) (projectionHom Δ D) (rawLift τ D) K).mpr ?_⟩
    show (frames levels).Models (rawLift τ D ≫ projectionHom Δ D) K
    rw [ContextualDependentUpdate.lift_projection]
    exact Frames.models_comp (X := frames levels) solved (projectionHom Θ (D.reindex τ))

/-- **The state extended by a dead helper** `d : D`. -/
def deadExtension (s : State rules O) (D : TypeOver s.frame) : State rules O :=
  (s.toLocal.move (projectionHom s.frame D)).toState

variable [DecidableEq O]

/-- **A live firing admitted at a state is admitted at the state extended by a dead helper.** -/
theorem dead_admits_of_admits {s : State rules O} (D : TypeOver s.frame) (f : Natural levels O s.frame)
    (admitted : (plainStep levels O).Admits f) :
    (plainStep levels O).Admits (s := deadExtension s D) (f.move (projectionHom s.frame D)) :=
  Natural.admits_move (projectionHom s.frame D) f admitted
    ((solvable_dead D (f.toPlain.information s.toLocal)).mpr admitted.2.2.1)

/-- **The result of a live firing at the extended state is the smaller result, extended by the same
dead helper.** -/
theorem dead_result {s : State rules O} (D : TypeOver s.frame) (f : Natural levels O s.frame)
    (admitted : (plainStep levels O).Admits f) :
    (plainStep levels O).result (s := deadExtension s D) (f.move (projectionHom s.frame D))
        (dead_admits_of_admits D f admitted) =
      deadExtension ((plainStep levels O).result f admitted) D :=
  congrArg Local.toState (Natural.after_move (projectionHom s.frame D) f s.toLocal admitted.1.2.2.2.2 _)

/-- **The extended state simulates the smaller one on live firings**: every move of the smaller
state has a live counterpart at the extended one, whose result is again the extension by the same
dead helper. -/
theorem dead_moves {s : State rules O} (D : TypeOver s.frame) (f : Natural levels O s.frame)
    (admitted : (plainStep levels O).Admits f) :
    ∃ admitted' : (plainStep levels O).Admits (s := deadExtension s D) (f.move (projectionHom s.frame D)),
      (plainStep levels O).result (s := deadExtension s D) (f.move (projectionHom s.frame D)) admitted' =
        deadExtension ((plainStep levels O).result f admitted) D :=
  ⟨dead_admits_of_admits D f admitted, dead_result D f admitted⟩

end DependentFull

#print axioms DependentFull.solvable_dead
#print axioms DependentFull.dead_admits_of_admits
#print axioms DependentFull.dead_result
#print axioms DependentFull.dead_moves

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
