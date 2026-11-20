import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.CleanFragment.Parallel
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.CleanFragment.Reactions
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.CleanFragment.Observations
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.CleanFragment.CompilerFacts
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings.Carrier
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Source

/-!
# Executions and boundaries of the clean rho fragment

Positive controls include duplicate occurrences, a state with real extra
knowledge outside the literal compiler image, and actual source/admin steps.
Negative controls independently test consistency, row determination and the
selected sealed-quotation discipline. None is a claim that another quotation
interpretation or a weaker observer is invalid.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.CleanFragment.Controls

open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalBag
open ByInstantiation (sig G Grounding GroundSolves Closed Similar ObsSimilar groundFrame
  noUnknowns zeroT outputZero outputOutput inputT quoteT bagT pconsT pnilT nameZero
  instantiate_ground instantiateObservation_ground similar_refl obsSimilar_refl)

def literal (present : Finset Nat) (value : Nat → G [] .pr) : RawState :=
  ⟨groundFrame, [], present, fun occurrence => observe (value occurrence)⟩

def literalCertificate (present : Finset Nat) (value : Nat → G [] .pr)
    (safe : ∀ occurrence ∈ present, Closed (value occurrence)) : Certificate (literal present value) where
  value := value
  consistent := ⟨ByInstantiation.someGrounding _, fun _ impossible => nomatch impossible⟩
  determined := by
    intro point _ occurrence _
    exact ⟨value occurrence, congrArg observe (instantiate_ground point _), similar_refl _⟩
  closed := safe

def duplicates := literal {0, 1} (fun _ => outputZero)
def duplicateCertificate : Certificate duplicates := literalCertificate _ _ (by intros; decide)
def duplicatePoint : Point := ⟨duplicates, ⟨duplicateCertificate⟩⟩

theorem duplicates_counted : duplicateCertificate.inventory.1.card = 2 := by
  change (ByInstantiation.inventoryOf {0, 1} (fun _ => outputZero)).card = 2
  have one : primes (ByInstantiation.read outputZero) = {ByInstantiation.read outputZero} :=
    primes_of_isPrime Source.payload_prime
  norm_num [ByInstantiation.inventoryOf, one]

abbrev ghostFrame : Interface.Frames.Frame sig := ⟨Unit, fun _ => ([], .pr)⟩
def ghost : Term (signature sig ghostFrame.arity) [] .pr := generator ghostFrame.arity ()

/-- The unused ghost is bound to a nonzero process, while the visible row
is a different fixed process. Its knowledge is not an empty/refl fixture. -/
def metadata : RawState :=
  ⟨ghostFrame, [(observe ghost, observe (Encodings.embed (D := ghostFrame.arity) outputOutput))], {0},
    fun _ => observe (Encodings.embed (D := ghostFrame.arity) outputZero)⟩

def ghostModel : Grounding ghostFrame := fun _ => outputOutput

def metadataCertificate : Certificate metadata where
  value _ := outputZero
  consistent := ⟨ghostModel, by
    intro equation member
    obtain rfl := List.mem_singleton.mp member
    change ObsSimilar (observe (instantiate ghostModel ghost))
      (observe (instantiate ghostModel (Encodings.embed outputOutput)))
    rw [show instantiate ghostModel ghost = outputOutput from instantiate_generator ghostModel (),
      Encodings.instantiate_embed, Encodings.embed_ground]
    exact obsSimilar_refl _⟩
  determined := by
    intro point _ occurrence _
    exact ⟨outputZero, congrArg observe (Encodings.instantiate_embed point outputZero), similar_refl _⟩
  closed := by intros; decide

def metadataPoint : Point := ⟨metadata, ⟨metadataCertificate⟩⟩

theorem metadata_is_clean : Clean metadata := ⟨metadataCertificate⟩

theorem metadata_counted : metadataCertificate.inventory.1.card = 1 := by
  change (ByInstantiation.inventoryOf {0} (fun _ => outputZero)).card = 1
  have one : primes (ByInstantiation.read outputZero) = {ByInstantiation.read outputZero} :=
    primes_of_isPrime Source.payload_prime
  simp [ByInstantiation.inventoryOf, one]

/-- Set support erases exactly the distinction the occurrence inventory keeps. -/
theorem set_support_erases_multiplicity :
    duplicateCertificate.inventory.1.toFinset = metadataCertificate.inventory.1.toFinset ∧
      ¬ Same duplicatePoint metadataPoint := by
  constructor
  · change (ByInstantiation.inventoryOf {0, 1} (fun _ => outputZero)).toFinset =
      (ByInstantiation.inventoryOf {0} (fun _ => outputZero)).toFinset
    have one : primes (ByInstantiation.read outputZero) = {ByInstantiation.read outputZero} :=
      primes_of_isPrime Source.payload_prime
    simp [ByInstantiation.inventoryOf, one]
  · intro same
    have inventories := (same_iff_inventory _ _ duplicateCertificate metadataCertificate).mp same
    have counts := congrArg (fun bag : Bag => bag.1.card) inventories
    have unequal : (2 : Nat) = 1 := duplicates_counted.symm.trans (counts.trans metadata_counted)
    omega

theorem metadata_not_literal_image (process : RhoProcess) : (compile process).val ≠ metadata := by
  intro same
  have lengths := congrArg (fun state : RawState => state.knowledge.length) same
  rw [compile_knowledge_empty] at lengths
  change 0 = 1 at lengths
  omega

/-- The new onto statement includes this real extra-knowledge state. -/
theorem metadata_is_covered : ∃ process : RhoProcess, Same (compile process) metadataPoint :=
  compile_onto_meaning metadataPoint

def emptyPoint : Point := ⟨literal ∅ (fun _ => zeroT),
  ⟨literalCertificate _ _ (fun _ impossible => False.elim (Finset.notMem_empty _ impossible))⟩⟩

theorem meanings_are_not_collapsed : ¬ Same emptyPoint metadataPoint := by
  intro same
  have inventories := (same_iff_inventory _ _
    (literalCertificate ∅ (fun _ => zeroT) (fun _ impossible => False.elim (Finset.notMem_empty _ impossible)))
    metadataCertificate).mp same
  have counts := congrArg (fun bag : Bag => bag.1.card) inventories
  change (ByInstantiation.inventoryOf ∅ (fun _ => zeroT)).card =
    (ByInstantiation.inventoryOf {0} (fun _ => outputZero)).card at counts
  have one : primes (ByInstantiation.read outputZero) = {ByInstantiation.read outputZero} :=
    primes_of_isPrime Source.payload_prime
  simp [ByInstantiation.inventoryOf, one] at counts

def inconsistent : RawState :=
  ⟨groundFrame, [(observe (zeroT : G [] .pr), observe outputZero)], ∅,
    fun _ => observe (zeroT : G [] .pr)⟩

theorem inconsistency_excluded : ¬ Clean inconsistent := by
  rintro ⟨certificate⟩
  obtain ⟨point, model⟩ := certificate.consistent
  change Grounding groundFrame at point
  change GroundSolves (F := groundFrame) point
    [(observe (zeroT : G [] .pr), observe outputZero)] at model
  have impossible := model _ (List.mem_singleton_self _)
  change ObsSimilar (observe (instantiate point zeroT)) (observe (instantiate point outputZero)) at impossible
  rw [instantiate_ground, instantiate_ground] at impossible
  have shape := ByInstantiation.obsSimilar_closed.mp impossible
  cases shape

def unsettled : RawState := ⟨ghostFrame, [], {0}, fun _ => observe ghost⟩

theorem undetermined_row_excluded : ¬ Clean unsettled := by
  rintro ⟨certificate⟩
  let first : Grounding ghostFrame := fun _ => zeroT
  let second : Grounding ghostFrame := fun _ => outputZero
  obtain ⟨left, leftAt, leftSame⟩ := certificate.determined first
    (fun _ impossible => nomatch impossible) 0 (Finset.mem_singleton_self _)
  obtain ⟨right, rightAt, rightSame⟩ := certificate.determined second
    (fun _ impossible => nomatch impossible) 0 (Finset.mem_singleton_self _)
  have leftImage : instantiateObservation first (unsettled.label 0) = observe zeroT :=
    congrArg observe (instantiate_generator first ())
  have rightImage : instantiateObservation second (unsettled.label 0) = observe outputZero :=
    congrArg observe (instantiate_generator second ())
  have leftValue := observe_injective (leftImage.symm.trans leftAt)
  have rightValue := observe_injective (rightImage.symm.trans rightAt)
  rw [← leftValue] at leftSame
  rw [← rightValue] at rightSame
  have impossible := ByInstantiation.similar_trans leftSame (ByInstantiation.similar_symm rightSame)
  cases impossible

def unsafeTerm : G [] .pr := inputT nameZero Encodings.derivedOutput
def unsafeState := literal {0} (fun _ => unsafeTerm)

theorem crossing_quote_excluded : ¬ Clean unsafeState := by
  rintro ⟨certificate⟩
  let point := ByInstantiation.someGrounding groundFrame
  obtain ⟨term, atRow, similar⟩ := certificate.determined point
    (fun _ impossible => nomatch impossible) 0 (Finset.mem_singleton_self _)
  have image : instantiateObservation point (unsafeState.label 0) = observe unsafeTerm :=
    congrArg observe (instantiate_ground point _)
  have actual := observe_injective (image.symm.trans atRow)
  rw [← actual] at similar
  have safe := ByInstantiation.similar_safe (ByInstantiation.similar_symm similar) 0
    (certificate.closed 0 (Finset.mem_singleton_self _))
  exact (by decide : ¬ Closed unsafeTerm) safe

def packedValue : G [] .pr := bagT (pconsT outputZero (pconsT outputZero pnilT))
def packed := literal {0} (fun _ => packedValue)
def packedCertificate : Certificate packed := literalCertificate _ _ (by intros; decide)
def packedPoint : Point := ⟨packed, ⟨packedCertificate⟩⟩

/-- The two channels differ syntactically but agree by quote/drop. -/
def communicationValues (occurrence : Nat) : G [] .pr :=
  if occurrence = 0 then inputT nameZero ByInstantiation.twinVar
  else ByInstantiation.outputT ByInstantiation.nameDropZero outputZero

def communicationState := literal {0, 1} communicationValues
def communicationCertificate : Certificate communicationState := literalCertificate _ _ (by
  intro occurrence _
  unfold communicationValues
  split <;> decide)
def communicationPoint : Point := ⟨communicationState, ⟨communicationCertificate⟩⟩

def communicationDecision : Decidable
    ((ByInstantiation.commFiring communicationState 0 1 2).Admits ByInstantiation.knowledge communicationState) :=
  ByInstantiation.commDecision communicationCertificate.represents (by decide) (by decide)
    (by decide) (by decide) rfl rfl

def communicationAccepted : Bool := @decide _ communicationDecision

theorem communication_admitted :
    (ByInstantiation.commFiring communicationState 0 1 2).Admits ByInstantiation.knowledge communicationState := by
  exact @of_decide_eq_true _ communicationDecision (by rfl)

theorem certified_communication_executes : ∃ after : Point,
    after.val = (ByInstantiation.commFiring communicationState 0 1 2).result
      ByInstantiation.knowledge communicationState ∧ Move communicationPoint after :=
  every_firing_lifts communicationPoint _ communication_admitted

def differentChannelValues (occurrence : Nat) : G [] .pr :=
  if occurrence = 0 then inputT nameZero ByInstantiation.twinVar
  else ByInstantiation.outputT (quoteT outputZero) outputZero

def differentChannelState := literal {0, 1} differentChannelValues
def differentChannelCertificate : Certificate differentChannelState := literalCertificate _ _ (by
  intro occurrence _
  unfold differentChannelValues
  split <;> decide)

def differentChannelDecision : Decidable
    ((ByInstantiation.commFiring differentChannelState 0 1 2).Admits ByInstantiation.knowledge differentChannelState) :=
  ByInstantiation.commDecision differentChannelCertificate.represents (by decide) (by decide)
    (by decide) (by decide) rfl rfl

def differentChannelAccepted : Bool := @decide _ differentChannelDecision

theorem different_channel_refused :
    ¬ (ByInstantiation.commFiring differentChannelState 0 1 2).Admits ByInstantiation.knowledge differentChannelState := by
  exact @of_decide_eq_false _ differentChannelDecision (by rfl)

/-- A real administrative firing is included and leaves the decoded process
unchanged, while retaining cleanliness of its actual result. -/
theorem heating_is_silent_execution : ∃ after : Point,
    Move packedPoint after ∧ readback packedPoint = readback after := by
  obtain ⟨last, step⟩ := ByInstantiation.heat_exists packedCertificate.represents
    (o := 0) (Finset.mem_singleton_self _) rfl
  have raw := Encodings.administers_moves step
  let after : Point := ⟨last, clean_closed packedPoint.property raw⟩
  refine ⟨after, raw, ?_⟩
  apply readback_eq_of_same
  exact (same_iff_common_process _ _).mpr ⟨packedCertificate.readback,
    ⟨packedCertificate.value, packedCertificate.represents⟩,
    ByInstantiation.reflective_calculus_by_instantiation.2.2.1
      ⟨packedCertificate.value, packedCertificate.represents⟩ step⟩

/-- Source communication with genuinely different, name-equivalent channel
syntax lifts to a nonempty sequence of actual transform firings. -/
theorem source_communication_executes : ∃ after : Point,
    Relation.TransGen Move (compile CanonicalReactionControls.alternateSource) after ∧
      rhoProcessEquations.r (readback after) (CanonicalReactionControls.rule.target empty) := by
  apply source_step_lifts
  exact (source_step_congr (source_roundtrip CanonicalReactionControls.alternateSource)
    (rhoProcessEquations.iseqv.refl _)).mpr Source.communicates_up_to_name_equivalence.2

/-- This reaction contains COMM, rather than merely some silent unpacking. -/
theorem source_communication_is_a_reaction :
    ReactionBetween (compile CanonicalReactionControls.alternateSource)
      (compile (CanonicalReactionControls.rule.target empty)) := by
  apply (reaction_between_iff _ _).mpr
  exact (source_step_congr (source_roundtrip _) (source_roundtrip _)).mpr
    Source.communicates_up_to_name_equivalence.2

/-- A genuine source loop remains divergent inside the invariant domain. -/
theorem omega_remains_divergent : ∃ states : Nat → Point,
    states 0 = compile Encodings.omega ∧ ∀ n, Move (states n) (states (n + 1)) := by
  apply (point_divergence_iff_raw _).mpr
  exact Encodings.divergence_preserved (Encodings.encode_represents Encodings.omega)
    ⟨fun _ => Encodings.omega, rfl, fun _ => Encodings.omega_steps⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.CleanFragment.Controls
