import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentClosedBoundary
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentClosed

/-!
# Joined qualification: the two definitions of closed solvability are one

Closed solvability is defined twice. The step's interface defines it for every frame instance, as a
solution into a designated closed frame (`Interface.Frames.ClosedSolvable`, with closed asks and
closed admission beside it). The dependent unifier's boundary defines it at the typed βη frames, as
a substitution out of the empty context (`ContextualDependentClosedBoundary.ClosedSolvable`).

* `closedSolvable_iff_frames`: at the typed βη frames, whose morphisms `Γ → Δ` are substitutions
  `Δ ⟶ Γ`, the two agree with the empty context as the closed frame. The agreement is definitional.

So the unifier's boundary results (`principal_closed_iff`, `not_closedSolvable_of_not_solvable` and
their controls) are statements about the interface's closed asks at that instance, and the generic
`Interface.Frames.closedSolvable_iff_of_principal` and the unifier's `principal_closed_iff` speak of
the same property.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace TransformQualification.Closed

open _root_.CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-- **The unifier's closed solvability is the interface's**, with the empty context as the closed
frame. -/
theorem closedSolvable_iff_frames {Γ : Context S.R} (K : EquationStore (TotalTerm Γ)) :
    ContextualDependentClosedBoundary.ClosedSolvable K ↔
      (frames S.levels).ClosedSolvable (empty S.R) K :=
  Iff.rfl

#print axioms closedSolvable_iff_frames

end TransformQualification.Closed
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
