import Mettapedia.TypeTheory.ContextualPredicateAssumptions
import Mettapedia.TypeTheory.ContextualProductComparison

/-!
# Ordinary proposition values and their generic predicate

Reading the generic ordinary proposition variable gives a predicate on its
display. Pulling that predicate along a supplied proposition section recovers
the section's actual logical readout. This concerns the represented predicate
fibre and makes no assertion about unrelated subobjects of the context
category.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualPredicatePropositions

open Mettapedia.GSLT.Core.ContextualLadder
open ContextualPredicateCapabilities ContextualProductComparison

universe c s t m p
variable {C : Cwf.{c, s, t, m}}
variable {doctrine : PredicateDoctrine.{c, s, t, m, p} C}
variable (propositions : PropositionOperations doctrine)

def genericVariable (context : C.Ctx) :
    C.Tm (C.ext context (propositions.omega context))
      (propositions.omega (C.ext context (propositions.omega context))) :=
  cast (congrArg (C.Tm (C.ext context (propositions.omega context)))
    (propositions.omega_substitution (C.wk (propositions.omega context))))
    (C.vz (propositions.omega context))

def genericPredicate (context : C.Ctx) :
    doctrine.Predicate (C.ext context (propositions.omega context)) :=
  propositions.holds (genericVariable propositions context)

theorem genericVariable_at_section {context : C.Ctx}
    (term : C.Tm context (propositions.omega context)) :
    HEq (C.tmSub (genericVariable propositions context) (selfExtend C term)) term := by
  have variableCast := cast_heq
    (congrArg (C.Tm (C.ext context (propositions.omega context)))
      (propositions.omega_substitution (C.wk (propositions.omega context))))
    (C.vz (propositions.omega context))
  exact (TypeOver.tmSub_heq
    (propositions.omega_substitution (C.wk (propositions.omega context))).symm
    variableCast (selfExtend C term)).trans
      (ContextualTypeOperations.vz_selfExtend term)

theorem genericPredicate_at_section {context : C.Ctx}
    (term : C.Tm context (propositions.omega context)) :
    doctrine.reindex (selfExtend C term) (genericPredicate propositions context) =
      propositions.holds term :=
  (propositions.holds_substitution (selfExtend C term)
    (genericVariable propositions context) term
    (genericVariable_at_section propositions term)).symm

theorem genericPredicate_at_quote {context : C.Ctx}
    (predicate : doctrine.Predicate context) :
    doctrine.reindex (selfExtend C (propositions.quote predicate))
      (genericPredicate propositions context) = predicate :=
  (genericPredicate_at_section propositions (propositions.quote predicate)).trans
    (propositions.holds_quote predicate)

theorem genericPredicate_guard_iff {context : C.Ctx}
    (term : C.Tm context (propositions.omega context)) :
    doctrine.reindex (selfExtend C term) (genericPredicate propositions context) = ⊤ ↔
      propositions.holds term = ⊤ := by
  rw [genericPredicate_at_section]

theorem genericPredicate_guard_iff_truth {context : C.Ctx}
    (term : C.Tm context (propositions.omega context)) :
    doctrine.reindex (selfExtend C term) (genericPredicate propositions context) = ⊤ ↔
      term = propositions.quote ⊤ := by
  rw [genericPredicate_guard_iff]
  constructor
  · intro guard
    calc
      term = propositions.quote (propositions.holds term) := (propositions.quote_holds term).symm
      _ = propositions.quote ⊤ := congrArg propositions.quote guard
  · intro selected
    rw [selected, propositions.holds_quote]

end Mettapedia.TypeTheory.ContextualPredicatePropositions
