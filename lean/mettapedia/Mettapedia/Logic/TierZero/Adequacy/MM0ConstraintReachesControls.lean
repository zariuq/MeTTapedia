import Mettapedia.Logic.TierZero.Adequacy.MM0ConstraintReaches
import Mettapedia.Logic.TierZero.Adequacy.MM0RewritingControls

/-!
# Whole-catalog constraint reachability controls

The accepted non-occurrence theorem uses a genuinely admitted MM0 environment
and the actual constraint-catalog run relation. An empty environment has no
derivation or accepted proof. Missing theorem and definition keys do not
produce installed schemas.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.MM0ConstraintReachesControls

open Mettapedia.Languages.MM0.Kernel
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open MM0Rewriting

theorem admitted_nonoccurrence_theorem_is_reachable :
    MM0ConstraintReaches.Reaches CatalogControls.theory TheoremControls.independentContext [] TheoremControls.goal :=
  MM0ConstraintReaches.reaches_complete CatalogControls.theory_formed CatalogControls.target_formed []
    TheoremControls.goal CatalogControls.independent_nf_derivation

private theorem empty_theory_has_no_derivation {expression : Preterm}
    (derived : Derives ({} : Theory).termSignature ({} : Theory).definitionSignature
      ({} : Theory).theoremSignature [] [] expression) : False := by
  induction derived using Derives.rec
      (motive_2 := fun expressions _ => expressions = []) with
  | hypothesis assumed => cases assumed
  | theoremApp known instantiated children earlier => cases known
  | conversion converted child earlier => exact earlier
  | nil => rfl
  | @cons expression expressions child children head tail => exact head.elim

theorem empty_theory_cannot_publish_a_proof (expression : Preterm) :
    ¬MM0ConstraintReaches.Reaches ({} : Theory) [] [] expression := by
  intro accepted
  exact empty_theory_has_no_derivation
    (MM0ConstraintReaches.reaches_sound Theory.empty_wellFormed
      ((Context.check_iff _ _).mp (by decide)) [] expression accepted)

theorem missing_theorem_key_is_not_a_schema (target : Context) :
    MM0ConstraintCatalog.schemaFor ({} : Theory) target (.theorem_ 0) = none := rfl

theorem missing_definition_key_is_not_a_schema (target : Context) :
    MM0ConstraintCatalog.schemaFor CatalogControls.theory target (.unfolding 0) = none := rfl

theorem equal_values_keep_their_multiplicity :
    ∃ world : Finset (IndexedOccurrences.Occurrence MM0Rewriting.Tm),
      labels IndexedOccurrences.label world =
        {proofValue TheoremControls.independentContext TheoremControls.goal,
          proofValue TheoremControls.independentContext TheoremControls.goal} ∧ world.card = 2 := by
  obtain ⟨world, represented⟩ := IndexedOccurrences.realize
    ({proofValue TheoremControls.independentContext TheoremControls.goal,
      proofValue TheoremControls.independentContext TheoremControls.goal} : Multiset Tm)
  exact ⟨world, represented, IndexedOccurrences.duplicate_values_need_distinct_occurrences _ represented⟩

end Mettapedia.Logic.TierZero.Adequacy.MM0ConstraintReachesControls
