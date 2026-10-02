import Mettapedia.GSLT.LanguageDef.Interaction.Freeness
import Mettapedia.GSLT.LanguageDef.Interaction.MigrationInstances
import Mettapedia.GSLT.LanguageDef.EquationInvariant
import Mettapedia.GSLT.LanguageDef.ClosedTermChecker

/-!
# How lambda and rho carry their surfaces

The lambda calculus carries its surface structurally.  Application is a free
binary constructor, no equation acts at its head, and position at an
application is invariant under the static equivalence: the cut needs no
explicit subject because the place itself is the subject.

Rho carries its surface nominally.  Parallel composition is a bag, and the
bag's own laws exchange its components: two processes that are not equal can
be listed in either order.  Position at the contact is not data, so the cut
must say what has to match, and it does: the same name on both sides.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.Framework.LambdaInstance
open Mettapedia.GSLT.LanguageDef.LambdaContinuedInteraction
open Mettapedia.GSLT.LanguageDef.WellSorted
open EquationSemantics

/-! ## Lambda: structural -/

/-- No equation acts at the head of an application, and the lambda calculus
declares no collection algebra. -/
theorem lambda_rigidContact : lambdaInteractivePresentation.RigidContact := by
  refine ⟨?_, by decide⟩
  intro equation membership
  cases membership

/-- **The lambda calculus carries its surface by position.**  The cut names no
subject on either side, and what is equivalent to an application is an
application of an equivalent function to an equivalent argument. -/
theorem lambda_surface_structural :
    lambdaInteractionCut.program.subject.pattern = none ∧
      lambdaInteractionCut.environment.subject.pattern = none ∧
        ∀ {left right : lambdaInteractivePresentation.Term} {function argument : Pattern},
          left.1 = .apply "App" [function, argument] →
            (presentedEquationSetoid defaultBasePremises lambdaInteractivePresentation).r
                left right →
              ∃ function' argument', right.1 = .apply "App" [function', argument'] ∧
                EquationEquiv defaultBasePremises lambdaCalc function function' ∧
                  EquationEquiv defaultBasePremises lambdaCalc argument argument' :=
  ⟨rfl, rfl, fun contact equivalent =>
    lambdaInteractivePresentation.position_invariant lambda_rigidContact contact equivalent⟩

/-! ## Rho: nominal -/

/-- The weight that counts outputs. -/
def countOutputs (label : String) : Nat := if label = "POutput" then 1 else 0

/-- Rho's static equivalence preserves the number of outputs in a term. -/
theorem rho_preserves_outputs {left right : Pattern}
    (equivalent : EquationEquiv defaultBasePremises rhoCalc left right) :
    left.weigh countOutputs = right.weigh countOutputs := by
  apply equationEquiv_weigh countOutputs _ (by decide) _ _ equivalent
  · intro equation membership
    obtain rfl := List.mem_singleton.mp membership
    exact ⟨rfl, by decide, by decide⟩
  · intro rule membership algebra declared unit declaredUnit
    simp only [rhoCalc, List.mem_cons, List.not_mem_nil, or_false] at membership
    rcases membership with rfl | rfl | rfl | rfl | rfl | rfl <;> cases declared
    cases declaredUnit
    decide
  · intro equation membership bindings
    obtain rfl := List.mem_singleton.mp membership
    simp [applyBindings, Pattern.weigh, Pattern.weighList, countOutputs]

/-- An input on the name of the null process. -/
def rhoListener : Pattern :=
  .apply "PInput" [.apply "NQuote" [.apply "PZero" []], .lambda none (.apply "PZero" [])]

/-- An output on the same name. -/
def rhoSender : Pattern :=
  .apply "POutput" [.apply "NQuote" [.apply "PZero" []], .apply "PZero" []]

/-- The two in parallel, as a closed process. -/
def rhoPair : rhoInteractivePresentation.Term :=
  ClosedTerm.ofCheck (.collection .hashBag [rhoListener, rhoSender] none) (by decide +kernel)

/-- The same two in the other order. -/
def rhoPairSwapped : rhoInteractivePresentation.Term :=
  ClosedTerm.ofCheck (.collection .hashBag [rhoSender, rhoListener] none) (by decide +kernel)

/-- The bag law exchanges the two components. -/
theorem rho_pair_swaps :
    (presentedEquationSetoid defaultBasePremises rhoInteractivePresentation).r
      rhoPair rhoPairSwapped := by
  apply Relation.EqvGen.rel
  refine EquationContextStep.inContext .hole (Or.inr ?_)
  exact DerivedInstance.bagPerm (rule := rhoParallelConstructor.1)
    ⟨rhoParallelConstructor.2, "ps", .base "Proc", rfl⟩
    ⟨FreeTypeContext.empty, [], rhoPair.2.1⟩
    (List.Perm.swap _ _ _)

/-- The listener and the sender are not equal. -/
theorem rho_listener_ne_sender :
    ¬ EquationEquiv defaultBasePremises rhoCalc rhoListener rhoSender := by
  intro equivalent
  have counts := rho_preserves_outputs equivalent
  revert counts
  decide

/-- **Rho carries its surface by name.**  Both sides of the cut name the same
subject, and position at the contact is not data: two unequal processes stand
in either order. -/
theorem rho_surface_nominal :
    rhoInteractionCut.program.subject.pattern = some (.fvar "n") ∧
      rhoInteractionCut.environment.subject.pattern = some (.fvar "n") ∧
        ∃ first second : Pattern,
          ∃ ordered swapped : rhoInteractivePresentation.Term,
            ordered.1 = .collection .hashBag [first, second] none ∧
              swapped.1 = .collection .hashBag [second, first] none ∧
                (presentedEquationSetoid defaultBasePremises rhoInteractivePresentation).r
                  ordered swapped ∧
                  ¬ EquationEquiv defaultBasePremises rhoCalc first second :=
  ⟨rfl, rfl, rhoListener, rhoSender, rhoPair, rhoPairSwapped, rfl, rfl, rho_pair_swaps,
    rho_listener_ne_sender⟩

/-- Rho's contact occurs in no authored equation, so `ContactEquationFree`
holds of it; the laws that exchange its components are the bag's own. -/
theorem rho_contactEquationFree : ContactEquationFree rhoInteractivePresentation := by
  intro equation membership
  obtain rfl := List.mem_singleton.mp membership
  decide +kernel

end Mettapedia.GSLT.LanguageDef
