import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentGeneralPatternRecognition
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentGeneralPatternDispatchControls

/-!
# Recognition of actual scoped equations

The actual equation `F x y ≐ Id T y x` is recognized from its syntax, and
the recognized pattern is solved by the general step. The non-pattern
`F x x ≐ Id T y x` is not recognized; it stays with the caller, pending.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentGeneralPattern.RecognitionControls

open CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentPiSpine ContextualDependentScope
open ContextualDependentGeneralPattern.Controls ContextualDependentGeneralPattern.DispatchControls

/-- `F x y ≐ Id T y x` as an actual active equation. -/
def patternEquation : Active scope.target := ⟨_, straight.application, swapped⟩

/-- `F x x`, a repeated argument. -/
def repeated : Term scope.target (universeAt scope.target) :=
  ⟨(.app (.app (.var 2) (.var 1)) (.var 1) : Tower.Tm 4),
    .appElim (A := (.var 3 : Tower.Tm 4)) (B := (.head (.sort Tower.zero) : Tower.Tm 5))
      (.appElim (A := (.var 3 : Tower.Tm 4)) (B := (.pi (.var 4) (.head (.sort Tower.zero)) : Tower.Tm 5))
        (.var (2 : Fin 4)) (.var (1 : Fin 4)))
      (.var (1 : Fin 4))⟩

def repeatedEquation : Active scope.target := ⟨universeAt scope.target, repeated, ⟨swapped.code, swapped.typed⟩⟩

/-- Recognize, then run the general step; unrecognized equations stay pending. -/
def recognizeAndRun (fuel : Nat) (active : Active scope.target) : Nat :=
  match recognize spine scope active with
  | some recognized => tag (run fuel recognized.pattern recognized.right)
  | none => 2

theorem pattern_recognized : (recognize spine scope patternEquation).isSome = true := by decide +kernel

theorem repeated_not_recognized : (recognize spine scope repeatedEquation).isSome = false := by decide +kernel

theorem recognized_pattern_solved : recognizeAndRun 16 patternEquation = 0 := by rfl'

theorem repeated_stays_pending : recognizeAndRun 16 repeatedEquation = 2 := by rfl'

end ContextualDependentGeneralPattern.RecognitionControls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
