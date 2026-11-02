import Mettapedia.Logic.TierZero.Adequacy.MM0LocatedCompleteness
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SchemaPublicationRuns

/-!
# Full MM0 adequacy through the actual located authority system

The reverse direction constructs protected physical runs of the existing
system from complete-catalog source runs. The forward direction uses only
protected initial hypotheses and the independent whole-system validity
theorem. Initial requests remain untrusted data. The acceptance relation is
defined by actual authority-system runs, not by an alias of derivability.

The canonical completeness store is an unbounded semantic occurrence supply.
It is not a native storage implementation or a rule granting clients authority
from the printed shape of their payloads.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.MM0LocatedReachability

open Mettapedia.Languages.MM0.Kernel
open Mettapedia.Languages.ProcessCalculi
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open MM0Rewriting
open MM0LocatedActivation (Value)
open MM0LocatedCompleteness

theorem source_run_lifts {theory : Theory} (wellFormed : theory.WellFormed) {target : Context}
    (formed : Context.WellFormed theory.sortSignature target) {source destination : Multiset Tm}
    (run : Relation.ReflTransGen (process theory target (catalog theory)).Step source destination) :
    ∀ before : Configuration Value Occurrence, labels payload before.present = source →
      LocatedRequestLifting.Coherent before.equations →
      (MM0LocatedActivation.action target).Consistent before.equations →
      ∃ (after : Configuration Value Occurrence) (actors : List Bool),
        (system theory target).Run payload before actors after ∧
          LocatedRequestLifting.Coherent after.equations ∧ labels payload after.present = destination := by
  induction run with
  | refl =>
      intro before same coherent _
      exact ⟨before, [], .nil _, coherent, same⟩
  | tail prior stepped earlier =>
      intro before same coherent background
      obtain ⟨middle, actors, preceding, middleCoherent, middleBag⟩ := earlier before same coherent background
      rw [← middleBag] at stepped
      have middleConsistent := SchemaPublicationAuthority.System.Run.consistent preceding background
      obtain ⟨after, fired, finalCoherent, finalBag⟩ :=
        source_firing_lifts wellFormed formed middle middleCoherent middleConsistent stepped
      exact ⟨after, actors ++ [true], preceding.append (.cons fired (.nil _)), finalCoherent, finalBag⟩

def Reaches (theory : Theory) (target : Context) (hypotheses : List Preterm) (expression : Preterm) : Prop :=
  ∃ (requests : List RequestPacket) (before after : Configuration Value Occurrence) (actors : List Bool),
    before.equations = [] ∧
    labels payload before.present = requestBag requests + hypothesisBag target hypotheses ∧
    (system theory target).Run payload before actors after ∧
    ∃ output ∈ after.present, location output = .judgments ∧ payload output = proofValue target expression

theorem reaches_complete {theory : Theory} (wellFormed : theory.WellFormed) {target : Context}
    (formed : Context.WellFormed theory.sortSignature target) (hypotheses : List Preterm) (expression : Preterm)
    (derived : Derives theory.termSignature theory.definitionSignature theory.theoremSignature target hypotheses expression) :
    Reaches theory target hypotheses expression := by
  obtain ⟨requests, destination, sourceRun, published⟩ :=
    (rewriting_reaches_iff_derives wellFormed formed hypotheses expression).mpr derived
  obtain ⟨world, represented⟩ := IndexedOccurrences.realize (requestBag requests + hypothesisBag target hypotheses)
  let before : Configuration Value Occurrence := ⟨[], world⟩
  have background : (MM0LocatedActivation.action target).Consistent before.equations :=
    ⟨(MM0LocatedActivation.action target).identity, (MM0LocatedActivation.action target).models_nil _⟩
  obtain ⟨after, actors, run, _, finalBag⟩ := source_run_lifts wellFormed formed sourceRun before represented
    (by intro equation member; cases member) background
  have finalMember : proofValue target expression ∈ labels payload after.present := by
    rw [finalBag]
    exact published
  obtain ⟨output, present, same⟩ := Multiset.mem_map.mp finalMember
  refine ⟨requests, before, after, actors, rfl, represented, run, output, Finset.mem_val.mp present, ?_, same⟩
  change MM0LocatedCatalogShapes.layout (payload output) = .judgments
  rw [same]
  exact MM0LocatedCatalogShapes.proof_layout target expression

theorem reaches_sound {theory : Theory} (wellFormed : theory.WellFormed) {target : Context}
    (formed : Context.WellFormed theory.sortSignature target) (hypotheses : List Preterm) (expression : Preterm)
    (accepted : Reaches theory target hypotheses expression) :
    Derives theory.termSignature theory.definitionSignature theory.theoremSignature target hypotheses expression := by
  obtain ⟨requests, before, after, actors, emptyEquations, initialBag, run, output, present, protectedHere, observed⟩ := accepted
  have background : (MM0LocatedActivation.action target).Consistent before.equations := by
    rw [emptyEquations]
    exact ⟨(MM0LocatedActivation.action target).identity, (MM0LocatedActivation.action target).models_nil _⟩
  have initialValid : MM0LocatedKernel.ProtectedValid theory target hypotheses location payload before := by
    intro assignment _ occurrence member protectedSource
    have valuePresent : payload occurrence ∈ labels payload before.present :=
      Multiset.mem_map.mpr ⟨occurrence, Finset.mem_val.mpr member, rfl⟩
    rw [initialBag] at valuePresent
    rcases Multiset.mem_add.mp valuePresent with request | hypothesis
    · obtain ⟨packet, _, same⟩ := List.mem_map.mp
        (show payload occurrence ∈ requests.map (fun packet => requestValue packet.1 packet.2) from request)
      have located : location occurrence = .requests := by
        change MM0LocatedCatalogShapes.layout (payload occurrence) = .requests
        rw [← same]
        exact MM0LocatedCatalogShapes.request_layout packet.1 packet.2
      change location occurrence = .judgments at protectedSource
      rw [located] at protectedSource
      cases protectedSource
    · obtain ⟨assumption, assumed, same⟩ := List.mem_map.mp
        (show payload occurrence ∈ hypotheses.map (proofValue target) from hypothesis)
      rw [← same, MM0ConstraintParameters.proof_value_fixed_of_context formed assumption assignment]
      exact valid_proof (.hypothesis assumed)
  obtain ⟨assignment, solved⟩ := SchemaPublicationAuthority.System.Run.consistent run background
  apply (system theory target).published_proof_is_derivable wellFormed formed hypotheses payload run initialValid
    assignment solved output present protectedHere expression
  rw [observed]
  exact MM0ConstraintParameters.proof_value_fixed_of_context formed expression assignment

theorem located_kernel_reaches_iff_derives {theory : Theory} (wellFormed : theory.WellFormed) {target : Context}
    (formed : Context.WellFormed theory.sortSignature target) (hypotheses : List Preterm) (expression : Preterm) :
    Reaches theory target hypotheses expression ↔
      Derives theory.termSignature theory.definitionSignature theory.theoremSignature target hypotheses expression :=
  ⟨reaches_sound wellFormed formed hypotheses expression, reaches_complete wellFormed formed hypotheses expression⟩

end Mettapedia.Logic.TierZero.Adequacy.MM0LocatedReachability
