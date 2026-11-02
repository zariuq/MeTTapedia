import Mettapedia.Logic.TierZero.Adequacy.MM0ConstraintOccurrenceCompleteness
import Mettapedia.Logic.TierZero.Adequacy.MM0Rewriting
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.IndexedOccurrences

/-!
# MM0 derivability and actual two-sided constraint-catalog reachability

The request-catalog compatibility profile executes ordinary constraint steps
over physical occurrences. Soundness observes the whole run at one model of
its final equation store. Completeness constructs distinct consumption and
fresh output occurrences while preserving shared premise reads.

The endpoints are the independent MM0 judgments, including every rule of the
finite source catalog. The construction retains the actual source sorting,
dependency and constructor data checks. It neither replaces them by a supplied
true code nor claims that per-formal contextual admission, authority-preserving
publication or concrete corpus execution has already been established.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.MM0ConstraintReaches

open Mettapedia.Languages.MM0.Kernel
open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
open Mettapedia.Languages.ProcessCalculi
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open MM0ContextualSupport
open MM0Rewriting
open MM0ConstraintProcess
open MM0ConstraintOccurrenceCompleteness

abbrev Occurrence := IndexedOccurrences.Occurrence Tm
abbrev label : Occurrence → Tm := IndexedOccurrences.label

/-- Acceptance is reachability through the actual activated catalog. Initial
requests and hypotheses are data; the initial equation store is empty. -/
def Reaches (theory : Theory) (target : Context) (hypotheses : List Preterm) (expression : Preterm) : Prop :=
  ∃ (requests : List RequestPacket) (before after : Configuration Tm Occurrence), before.equations = [] ∧
    labels label before.present = requestBag requests + hypothesisBag target hypotheses ∧
    Relation.ReflTransGen (Fires theory target (catalog theory) label) before after ∧
    proofValue target expression ∈ labels label after.present

theorem resolved_request_stays_data (signature : TermSignature) (definitions : Definition.Signature)
    (theorems : TheoremSignature) (target : Context) (hypotheses : List Preterm)
    (candidate : ABTProtectedParameters.Assignment Head target.length)
    (name : String) (arguments : List Tm) :
    ValidValue signature definitions theorems target hypotheses
      ((MM0ConstraintParameters.action target).apply candidate (requestValue name arguments)) := by
  constructor
  · intro expression equal
    have tags : requestTag name = "pf" := Head.judgment.inj (Term.node.inj equal).1
    exact False.elim (requestTag_ne_proof name tags)
  · intro sort left right equal
    have tags : requestTag name = "cv" := Head.judgment.inj (Term.node.inj equal).1
    exact False.elim (requestTag_ne_conversion name tags)

private theorem labels_resolved (target : Context)
    (candidate : ABTProtectedParameters.Assignment Head target.length) (world : Finset Occurrence) :
    labels (fun occurrence => (MM0ConstraintParameters.action target).apply candidate (label occurrence)) world =
      (labels label world).map ((MM0ConstraintParameters.action target).apply candidate) := by
  simp [labels, Multiset.map_map]

theorem reaches_sound {theory : Theory} (wellFormed : theory.WellFormed) {target : Context}
    (formed : Context.WellFormed theory.sortSignature target) (hypotheses : List Preterm) (expression : Preterm)
    (accepted : Reaches theory target hypotheses expression) :
    Derives theory.termSignature theory.definitionSignature theory.theoremSignature target hypotheses expression := by
  obtain ⟨requests, before, after, emptyEquations, initialBag, run, published⟩ := accepted
  have background : (MM0ConstraintParameters.action target).Consistent before.equations := by
    rw [emptyEquations]
    exact ⟨(MM0ConstraintParameters.action target).identity, (MM0ConstraintParameters.action target).models_nil _⟩
  obtain ⟨candidate, models⟩ := run_consistent run background
  have incoming : ∀ value ∈ labels (fun occurrence =>
      (MM0ConstraintParameters.action target).apply candidate (label occurrence)) before.present,
      ValidValue theory.termSignature theory.definitionSignature theory.theoremSignature target hypotheses value := by
    intro value member
    rw [labels_resolved, initialBag] at member
    obtain ⟨original, present, rfl⟩ := Multiset.mem_map.mp member
    rcases Multiset.mem_add.mp present with request | hypothesis
    · obtain ⟨packet, _, rfl⟩ := List.mem_map.mp
        (show original ∈ requests.map (fun packet => requestValue packet.1 packet.2) from request)
      exact resolved_request_stays_data _ _ _ _ _ candidate packet.1 packet.2
    · obtain ⟨assumption, assumed, rfl⟩ := List.mem_map.mp
        (show original ∈ hypotheses.map (proofValue target) from hypothesis)
      rw [MM0ConstraintParameters.proof_value_fixed_of_context formed assumption candidate]
      exact valid_proof (.hypothesis assumed)
  have finalValid := run_preserves wellFormed formed hypotheses run candidate models incoming
  have publishedResolved : proofValue target expression ∈ labels (fun occurrence =>
      (MM0ConstraintParameters.action target).apply candidate (label occurrence)) after.present := by
    rw [labels_resolved]
    exact Multiset.mem_map.mpr ⟨proofValue target expression, published,
      MM0ConstraintParameters.proof_value_fixed_of_context formed expression candidate⟩
  exact (finalValid _ publishedResolved).1 expression rfl

theorem reaches_complete {theory : Theory} (wellFormed : theory.WellFormed) {target : Context}
    (formed : Context.WellFormed theory.sortSignature target) (hypotheses : List Preterm) (expression : Preterm)
    (derived : Derives theory.termSignature theory.definitionSignature theory.theoremSignature target hypotheses expression) :
    Reaches theory target hypotheses expression := by
  obtain ⟨requests, destination, sourceRun, published⟩ :=
    (rewriting_reaches_iff_derives wellFormed formed hypotheses expression).mpr derived
  obtain ⟨world, represented⟩ := IndexedOccurrences.realize (requestBag requests + hypothesisBag target hypotheses)
  let before : Configuration Tm Occurrence := ⟨[], world⟩
  have background : (MM0ConstraintParameters.action target).Consistent before.equations :=
    ⟨(MM0ConstraintParameters.action target).identity, (MM0ConstraintParameters.action target).models_nil _⟩
  obtain ⟨after, lifted, sameDestination⟩ := source_run_lifts wellFormed label IndexedOccurrences.supply
    sourceRun before represented background
  exact ⟨requests, before, after, rfl, represented, lifted, by rw [sameDestination]; exact published⟩

/-- The complete source catalog is adequate on actual two-sided constraint
steps, relative to the same admitted theory and local hypotheses. -/
theorem constraint_reaches_iff_derives {theory : Theory} (wellFormed : theory.WellFormed) {target : Context}
    (formed : Context.WellFormed theory.sortSignature target) (hypotheses : List Preterm) (expression : Preterm) :
    Reaches theory target hypotheses expression ↔
      Derives theory.termSignature theory.definitionSignature theory.theoremSignature target hypotheses expression :=
  ⟨reaches_sound wellFormed formed hypotheses expression, reaches_complete wellFormed formed hypotheses expression⟩

end Mettapedia.Logic.TierZero.Adequacy.MM0ConstraintReaches
