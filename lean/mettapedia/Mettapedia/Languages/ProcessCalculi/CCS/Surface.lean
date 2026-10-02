import Mettapedia.Languages.ProcessCalculi.CCS.Cut
import Mettapedia.GSLT.LanguageDef.Interaction.Freeness
import Mettapedia.GSLT.LanguageDef.EquationInvariant

/-!
# CCS carries its surface by name

Parallel composition in CCS is a bag.  Its own laws exchange the components
of a composition, so two unequal processes stand in either order and position
at the contact is not data.  What must match for a synchronisation is said
explicitly instead: the name carried by the two prefixes.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.CCS

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ContextualStep

/-- The weight that counts co-action prefixes. -/
def countCoActions (label : String) : Nat := if label = "CCoAct" then 1 else 0

/-- The static equivalence of CCS preserves the number of co-action prefixes
in a term. -/
theorem ccs_preserves_coActions {left right : Pattern}
    (equivalent : EquationEquiv defaultBasePremises ccsCalc left right) :
    left.weigh countCoActions = right.weigh countCoActions := by
  apply equationEquiv_weigh countCoActions _ (by decide) _ _ equivalent
  · intro equation membership
    cases membership
  · intro rule membership algebra declared unit declaredUnit
    simp only [ccsCalc, List.mem_cons, List.not_mem_nil, or_false] at membership
    rcases membership with rfl | rfl | rfl | rfl | rfl | rfl <;> cases declared
    cases declaredUnit
    decide
  · intro equation membership
    cases membership

/-- The handshake with its two components exchanged. -/
def handshakeSwapped : Pattern :=
  .collection .hashBag [
    .apply "CCoAct" [nameA, .apply "CAct" [nameA, nil]],
    .apply "CAct" [nameA, nil]] none

/-- The exchanged handshake as a closed process. -/
def handshakeSwappedTerm : ccsInteractivePresentation.Term :=
  ClosedTerm.ofCheck handshakeSwapped (by decide +kernel)

/-- The bag law exchanges the two components of the handshake. -/
theorem handshake_swaps :
    (presentedEquationSetoid defaultBasePremises ccsInteractivePresentation).r
      handshakeTerm handshakeSwappedTerm := by
  apply Relation.EqvGen.rel
  refine EquationContextStep.inContext .hole (Or.inr ?_)
  exact DerivedInstance.bagPerm (rule := ccsParallelConstructor.1)
    ⟨ccsParallelConstructor.2, "ps", .base "Proc", rfl⟩
    ⟨FreeTypeContext.empty, [], handshakeTerm.2.1⟩
    (List.Perm.swap _ _ _)

/-- The two components are not equal: one carries a co-action and the other
does not. -/
theorem handshake_components_differ :
    ¬ EquationEquiv defaultBasePremises ccsCalc
      (.apply "CAct" [nameA, nil])
      (.apply "CCoAct" [nameA, .apply "CAct" [nameA, nil]]) := by
  intro equivalent
  have counts := ccs_preserves_coActions equivalent
  revert counts
  decide

/-- **CCS carries its surface by name.**  Both sides of the cut name the same
subject, and position at the contact is not data. -/
theorem ccs_surface_nominal :
    ccsInteractionCut.program.subject.pattern = some (.fvar "a") ∧
      ccsInteractionCut.environment.subject.pattern = some (.fvar "a") ∧
        ∃ first second : Pattern,
          ∃ ordered swapped : ccsInteractivePresentation.Term,
            ordered.1 = .collection .hashBag [first, second] none ∧
              swapped.1 = .collection .hashBag [second, first] none ∧
                (presentedEquationSetoid defaultBasePremises ccsInteractivePresentation).r
                  ordered swapped ∧
                  ¬ EquationEquiv defaultBasePremises ccsCalc first second :=
  ⟨rfl, rfl, _, _, handshakeTerm, handshakeSwappedTerm, rfl, rfl, handshake_swaps,
    handshake_components_differ⟩

/-- CCS authors no equation, so its contact is free of authored equations in
the sense of `ContactEquationFree`; the laws that exchange its components are
the bag's own. -/
theorem ccs_contactEquationFree : ContactEquationFree ccsInteractivePresentation := by
  intro equation membership
  cases membership

end Mettapedia.Languages.ProcessCalculi.CCS
