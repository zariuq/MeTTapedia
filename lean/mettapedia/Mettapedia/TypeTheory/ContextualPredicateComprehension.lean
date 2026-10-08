import Mettapedia.TypeTheory.ContextualPredicatePropositions

/-!
# Guarded comprehension as a pullback of ordinary truth

The context assuming a predicate is the pullback of the generic ordinary
proposition's truth context along that predicate's quotation. The comparison
uses actual guarded selection, its monicity, and the full ordinary proposition
readout. This classifies the represented predicate displays; it does not
identify the represented predicates with all context-category subobjects.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualPredicateComprehension

open Mettapedia.GSLT.Core.ContextualLadder
open ContextualPredicateCapabilities ContextualPredicateAssumptions
open ContextualPredicatePropositions ContextualProductComparison

universe c s t m p
variable {C : Cwf.{c, s, t, m}}
variable {doctrine : PredicateDoctrine.{c, s, t, m, p} C}
variable (propositions : PropositionOperations doctrine)
variable (assumptions : AssumptionOperations doctrine)

def truthContext (context : C.Ctx) : C.Ctx :=
  assumptions.assumed (C.ext context (propositions.omega context))
    (genericPredicate propositions context)

def truthInclusion (context : C.Ctx) :
    C.Sub (truthContext propositions assumptions context)
      (C.ext context (propositions.omega context)) :=
  assumptions.inclusion (genericPredicate propositions context)

def characteristic {context : C.Ctx} (predicate : doctrine.Predicate context) :
    C.Sub context (C.ext context (propositions.omega context)) :=
  selfExtend C (propositions.quote predicate)

theorem characteristic_readout {context : C.Ctx} (predicate : doctrine.Predicate context) :
    doctrine.reindex (characteristic propositions predicate)
      (genericPredicate propositions context) = predicate :=
  genericPredicate_at_quote propositions predicate

theorem characteristic_guard {context : C.Ctx}
    (predicate : doctrine.Predicate context) :
    doctrine.reindex (C.compS (characteristic propositions predicate)
      (assumptions.inclusion predicate)) (genericPredicate propositions context) = ⊤ := by
  rw [doctrine.reindex_comp, characteristic_readout, inclusion_guard]

def guardedCharacteristic {context : C.Ctx} (predicate : doctrine.Predicate context) :
    C.Sub (assumptions.assumed context predicate) (truthContext propositions assumptions context) :=
  assumptions.select (genericPredicate propositions context)
    (C.compS (characteristic propositions predicate) (assumptions.inclusion predicate))
    (characteristic_guard propositions assumptions predicate)

theorem guarding_square {context : C.Ctx} (predicate : doctrine.Predicate context) :
    C.compS (truthInclusion propositions assumptions context)
      (guardedCharacteristic propositions assumptions predicate) =
        C.compS (characteristic propositions predicate) (assumptions.inclusion predicate) :=
  assumptions.select_beta _ _ _

theorem guarding_square_universal {context source : C.Ctx}
    (predicate : doctrine.Predicate context) (base : C.Sub source context)
    (truth : C.Sub source (truthContext propositions assumptions context))
    (commutes : C.compS (truthInclusion propositions assumptions context) truth =
      C.compS (characteristic propositions predicate) base) :
    ∃! factor : C.Sub source (assumptions.assumed context predicate),
      C.compS (assumptions.inclusion predicate) factor = base ∧
        C.compS (guardedCharacteristic propositions assumptions predicate) factor = truth := by
  have guard := arrow_guard assumptions (genericPredicate propositions context) truth
  change doctrine.reindex (C.compS (truthInclusion propositions assumptions context) truth)
    (genericPredicate propositions context) = ⊤ at guard
  rw [commutes, doctrine.reindex_comp, characteristic_readout] at guard
  let factor := assumptions.select predicate base guard
  refine ⟨factor, ⟨assumptions.select_beta _ _ _, ?_⟩, ?_⟩
  · apply assumptions.inclusion_monic (genericPredicate propositions context)
    change C.compS (truthInclusion propositions assumptions context)
      (C.compS (guardedCharacteristic propositions assumptions predicate) factor) =
        C.compS (truthInclusion propositions assumptions context) truth
    rw [← C.comp_assoc, guarding_square, C.comp_assoc, assumptions.select_beta]
    exact commutes.symm
  · intro other projections
    exact select_unique assumptions predicate base guard other projections.1

end Mettapedia.TypeTheory.ContextualPredicateComprehension
