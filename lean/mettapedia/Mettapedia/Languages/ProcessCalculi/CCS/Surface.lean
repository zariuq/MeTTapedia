import Mettapedia.Languages.ProcessCalculi.CCS.Cut
import Mettapedia.Languages.ProcessCalculi.CCS.StaticTheory
import Mettapedia.GSLT.LanguageDef.Interaction.Freeness

/-!
# CCS carries its surface by name

Parallel composition in CCS is a bag. Its own laws exchange the components of a composition, so two unequal processes
stand in either order and position at the contact is not data. What must match for a reaction is said explicitly
instead: the name carried by the two prefixes.

Inequivalence is decided by canonical forms (`StaticTheory.static_iff_canon_eq`): `τ.0` and `τ.τ.0` are not related by
the laws of CCS.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.CCS

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.DerivedContexts

/-- `τ.0`. -/
def silentOnce : Pattern := sum [tau nil]

/-- `τ.τ.0`. -/
def silentTwice : Pattern := sum [tau (sum [tau nil])]

/-- `τ.0 | τ.τ.0` as a closed process. -/
def silentPairTerm : ccsInteractivePresentation.Term :=
  ClosedTerm.ofCheck (par [silentOnce, silentTwice]) (by decide +kernel)

/-- `τ.τ.0 | τ.0` as a closed process. -/
def silentPairSwappedTerm : ccsInteractivePresentation.Term :=
  ClosedTerm.ofCheck (par [silentTwice, silentOnce]) (by decide +kernel)

/-- The bag law exchanges the two components. -/
theorem silentPair_swaps :
    (presentedEquationSetoid defaultBasePremises ccsInteractivePresentation).r
      silentPairTerm silentPairSwappedTerm := by
  apply Relation.EqvGen.rel
  refine EquationContextStep.inContext .hole (Or.inr ?_)
  exact DerivedInstance.bagPerm_of_sorted (category := ccsParallelConstructor.1.category)
    ⟨FreeTypeContext.empty, [], silentPairTerm.2.1⟩ (List.Perm.swap _ _ _)

/-- **The two components are not equivalent**, by their canonical forms. -/
theorem silent_components_differ : ¬ EquationEquiv defaultBasePremises ccsCalc silentOnce silentTwice :=
  fun equivalent => absurd
    ((StaticTheory.static_iff_canon_eq (by decide +kernel) (by decide +kernel) (by decide +kernel)).mp equivalent)
    (by decide +kernel)

/-- `(νx)(~x.0 | x.0)`: the private handshake with its components exchanged. -/
def handshakeSwapped : Pattern := nu (par [sum [coact (.bvar 0) nil], sum [act (.bvar 0) nil]])

/-- The exchanged handshake as a closed process. -/
def handshakeSwappedTerm : ccsInteractivePresentation.Term :=
  ClosedTerm.ofCheck handshakeSwapped (by decide +kernel)

/-- **The bag law exchanges the components of the handshake**, under its restriction. -/
theorem handshake_swaps :
    (presentedEquationSetoid defaultBasePremises ccsInteractivePresentation).r
      handshakeTerm handshakeSwappedTerm := by
  apply Relation.EqvGen.rel
  refine EquationContextStep.inContext (.apply "CNu" [] (.lambda none .hole) []) (Or.inr ?_)
  exact DerivedInstance.bagPerm_of_sorted (category := ccsParallelConstructor.1.category)
    ⟨FreeTypeContext.empty, [.base "Name"], checkHasType_sound (by decide +kernel)⟩ (List.Perm.swap _ _ _)

/-- **CCS carries its surface by name.** Both sides of the cut name the same subject, and position at the contact is
not data. -/
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
  ⟨rfl, rfl, _, _, silentPairTerm, silentPairSwappedTerm, rfl, rfl, silentPair_swaps,
    silent_components_differ⟩

end Mettapedia.Languages.ProcessCalculi.CCS
