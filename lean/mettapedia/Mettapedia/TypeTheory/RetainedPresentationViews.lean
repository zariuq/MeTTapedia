import Mettapedia.TypeTheory.NamedValueContexts
import Mettapedia.TypeTheory.MonoidIndexedTransportCoherence

/-!
# Retained references and representative recovery

A local observation may omit presentation details while an explicitly retained
versioned reference still names the original presentation. Capture and recovery
below are executable table operations. Capture applies the supplied observation
to the found presentation; recovery neither invokes that observation nor an
evaluator, and does not reconstruct a proof. Accepted fresh publications preserve exact recovery; an
absent key yields no presentation. Arbitrary replacement of an occupied key is
outside that preservation contract and can silently change the presentation.
The preservation theorem relates tables in the same fresh-publication lineage;
a bare key does not authenticate an unrelated table or establish proof authority.

Forgetting the reference is a different operation. Quotienting by an observation
supports recovery of a chosen representative when a suitable section exists,
but exact original recovery requires injectivity of the observation. Concrete
controls use accepted indexed conversion paths with genuinely varying packet
cursors, not an empty carrier or a constant observation.

These are representation and lookup laws, not a global proof irrelevance rule,
garbage-collection policy, runtime allocation requirement, or native J model.
The retained reference is explicit data; which component a scope exposes is a
separate interface decision.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.RetainedPresentationViews

open NamedValueContexts Mettapedia.Machines
open Mettapedia.GSLT.LanguageDef.FiniteEnvironmentCompilation

universe uPresentation uObservation uCoarse

variable {Name Revision : Type} {Presentation : Type uPresentation}
variable {Observation : Type uObservation} {Coarse : Type uCoarse}

/-- The local observation and optional retained presentation reference are
different coordinates. This construction concerns the reference-retaining mode. -/
structure View (Name Revision : Type) (Observation : Type uObservation) where
  value : Observation
  version : StoreReadToken Name Revision

/-- Capture only succeeds when the selected presentation exists. The captured
reference names the current version, not whatever version becomes live later. -/
def captureView (table : ContextTable Name Revision Presentation)
    (current : RevisionEnvironment Name Revision) (name : Name)
    (observe : Presentation → Observation) : Option (View Name Revision Observation) :=
  (table ⟨name, current.current name⟩).map fun presentation =>
    ⟨observe presentation, ⟨name, current.current name⟩⟩

/-- Exact lookup, without evaluator, observer, history or proof-checker input. -/
def recover (table : ContextTable Name Revision Presentation)
    (view : View Name Revision Observation) : Option Presentation :=
  table view.version

/-- Coarsen what the local consumer sees without discarding the retained key. -/
def mapView (forget : Observation → Coarse) (view : View Name Revision Observation) :
    View Name Revision Coarse := ⟨forget view.value, view.version⟩

theorem captureView_eq_some_iff
    (table : ContextTable Name Revision Presentation)
    (current : RevisionEnvironment Name Revision) (name : Name)
    (observe : Presentation → Observation) (view : View Name Revision Observation) :
    captureView table current name observe = some view ↔
      ∃ presentation, table ⟨name, current.current name⟩ = some presentation ∧
        view = ⟨observe presentation, ⟨name, current.current name⟩⟩ := by
  cases found : table ⟨name, current.current name⟩ <;>
    simp [captureView, found, eq_comm]

theorem capture_recovers_original
    (table : ContextTable Name Revision Presentation)
    (current : RevisionEnvironment Name Revision) (name : Name)
    (observe : Presentation → Observation) (view : View Name Revision Observation)
    (presentation : Presentation)
    (found : table ⟨name, current.current name⟩ = some presentation)
    (captured : captureView table current name observe = some view) :
    recover table view = some presentation ∧ view.value = observe presentation := by
  have shape : view = ⟨observe presentation, ⟨name, current.current name⟩⟩ := by
    simpa [captureView, found, eq_comm] using captured
  subst view
  exact ⟨found, rfl⟩

theorem captured_view_is_supported
    (table : ContextTable Name Revision Presentation)
    (current : RevisionEnvironment Name Revision) (name : Name)
    (observe : Presentation → Observation) (view : View Name Revision Observation)
    (captured : captureView table current name observe = some view) :
    ∃ presentation, recover table view = some presentation ∧
      view.value = observe presentation := by
  obtain ⟨presentation, found, shape⟩ :=
    (captureView_eq_some_iff table current name observe view).mp captured
  exact ⟨presentation, capture_recovers_original table current name observe view
    presentation found captured⟩

theorem recovery_uses_captured_context
    (table : ContextTable Name Revision Presentation)
    (current : RevisionEnvironment Name Revision) (view : View Name Revision Observation) :
    recover table view = resolve table current (.versioned view.version) := rfl

theorem recover_mapView (table : ContextTable Name Revision Presentation)
    (forget : Observation → Coarse) (view : View Name Revision Observation) :
    recover table (mapView forget view) = recover table view := rfl

/-- An accepted fresh publication cannot retarget an already supported view. -/
theorem recover_preserved_by_publication [DecidableEq Name] [DecidableEq Revision]
    (table updated : ContextTable Name Revision Presentation)
    (version : StoreReadToken Name Revision) (newPresentation original : Presentation)
    (view : View Name Revision Observation)
    (published : publishVersion? table version newPresentation = some updated)
    (supported : recover table view = some original) :
    recover updated view = some original :=
  publication_preserves_existing table updated version view.version newPresentation original
    published supported

theorem missing_reference_returns_none
    (table : ContextTable Name Revision Presentation) (view : View Name Revision Observation)
    (missing : table view.version = none) : recover table view = none := missing

/-- The local value is not a substitute for the retained store entry. -/
theorem occupied_reference_cannot_be_republished [DecidableEq Name] [DecidableEq Revision]
    (table : ContextTable Name Revision Presentation) (view : View Name Revision Observation)
    (original replacement : Presentation) (supported : recover table view = some original) :
    publishVersion? table view.version replacement = none :=
  publishVersion?_rejects_occupied table view.version original replacement supported

/-! ## Forgetting the reference: recovery only up to observation -/

def observationSetoid (observe : Presentation → Observation) : Setoid Presentation where
  r first second := observe first = observe second
  iseqv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩

abbrev Erased (observe : Presentation → Observation) := Quotient (observationSetoid observe)

def erase (observe : Presentation → Observation) (presentation : Presentation) : Erased observe :=
  Quotient.mk _ presentation

def erasedObservation (observe : Presentation → Observation) : Erased observe → Observation :=
  Quotient.lift observe (fun _ _ same => same)

theorem erased_equal_iff (observe : Presentation → Observation) (first second : Presentation) :
    erase observe first = erase observe second ↔ observe first = observe second := by
  constructor
  · exact Quotient.exact
  · intro same
    exact Quotient.sound (s := observationSetoid observe) same

/-- A chosen section may recover a presentation of the observed meaning.
The section is a real parameter, not an assertion that every quotient has an
executable canonical form. Its required law is used below. -/
def representative (observe : Presentation → Observation)
    (choose : Observation → Presentation) (erased : Erased observe) : Presentation :=
  choose (erasedObservation observe erased)

theorem representative_preserves_observation (observe : Presentation → Observation)
    (choose : Observation → Presentation)
    (sectionLaw : ∀ observation, observe (choose observation) = observation)
    (erased : Erased observe) :
    observe (representative observe choose erased) = erasedObservation observe erased :=
  sectionLaw _

theorem erase_representative (observe : Presentation → Observation)
    (choose : Observation → Presentation)
    (sectionLaw : ∀ observation, observe (choose observation) = observation)
    (erased : Erased observe) : erase observe (representative observe choose erased) = erased := by
  induction erased using Quotient.inductionOn with
  | _ original =>
      apply (erased_equal_iff observe _ original).mpr
      exact sectionLaw _

/-- Recovering every original presentation from the erased value would make
the observation injective. Thus a collision is a genuine obstruction. -/
theorem exact_recovery_implies_injective (observe : Presentation → Observation)
    (decode : Erased observe → Presentation)
    (exactRecovery : ∀ original, decode (erase observe original) = original) :
    Function.Injective observe := by
  intro first second same
  calc
    first = decode (erase observe first) := (exactRecovery first).symm
    _ = decode (erase observe second) := congrArg decode ((erased_equal_iff _ _ _).mpr same)
    _ = second := exactRecovery second

theorem collision_prevents_exact_recovery (observe : Presentation → Observation)
    (first second : Presentation) (same : observe first = observe second)
    (different : first ≠ second) :
    ¬ ∃ decode : Erased observe → Presentation,
      ∀ original, decode (erase observe original) = original := by
  rintro ⟨decode, exactRecovery⟩
  exact different (exact_recovery_implies_injective observe decode exactRecovery same)

/-! ## Accepted conversion paths with nonconstant packet observations -/

namespace Controls

open MonoidIndexedFamilyConversion MonoidIndexedTransportCoherence ConversionDecisionComparison

/-- Presentation stores accepted evidence together with an actual source
cursor. Neither the evidence nor the cursor is recovered by rerunning a program. -/
structure PacketPresentation where
  path : ConversionPath packetXUnit packetX
  cursor : SemanticFibre packetXUnit

def observePacket (presentation : PacketPresentation) : SemanticFibre packetX :=
  transport presentation.path presentation.cursor

def direct : PacketPresentation := ⟨rightUnitPath, MonoidIndexedTransportCoherence.Controls.cursor⟩

def expanded : PacketPresentation :=
  ⟨MonoidIndexedTransportCoherence.Controls.expandedRightUnitPath,
    MonoidIndexedTransportCoherence.Controls.cursor⟩

def zero : PacketPresentation := ⟨rightUnitPath, ⟨0, by decide⟩⟩

theorem direct_expanded_same_value : observePacket direct = observePacket expanded := by
  exact congrArg (fun action : SemanticFibre packetXUnit ≃ SemanticFibre packetX =>
      action MonoidIndexedTransportCoherence.Controls.cursor)
    (transport_parallel rightUnitPath MonoidIndexedTransportCoherence.Controls.expandedRightUnitPath)

theorem expanded_value :
    observePacket expanded = MonoidIndexedTransportCoherence.Controls.targetCursor :=
  direct_expanded_same_value.symm.trans MonoidIndexedTransportCoherence.Controls.application_value

theorem direct_expanded_distinct : direct ≠ expanded := by
  intro same
  exact MonoidIndexedTransportCoherence.Controls.accepted_routes_distinct
    (congrArg PacketPresentation.path same)

theorem packet_observation_not_constant : observePacket zero ≠ observePacket direct := by
  intro same
  have cursors := (transport rightUnitPath).injective same
  have values := congrArg Fin.val cursors
  change 0 = 1 at values
  cases values

/-- Canonicalization retains the observed cursor but chooses the direct
accepted proof. This is a representative, not the original proof decoder. -/
def choosePacket (value : SemanticFibre packetX) : PacketPresentation :=
  ⟨rightUnitPath, (transport rightUnitPath).symm value⟩

theorem choosePacket_section (value : SemanticFibre packetX) :
    observePacket (choosePacket value) = value := Equiv.apply_symm_apply _ _

theorem reconstructed_expanded_uses_direct_path :
    (representative observePacket choosePacket (erase observePacket expanded)).path = rightUnitPath :=
  rfl

theorem reconstructed_expanded_not_original :
    representative observePacket choosePacket (erase observePacket expanded) ≠ expanded := by
  intro same
  exact MonoidIndexedTransportCoherence.Controls.accepted_routes_distinct
    (congrArg PacketPresentation.path same)

theorem reconstruction_preserves_value_but_not_original :
    observePacket (representative observePacket choosePacket (erase observePacket expanded)) =
      observePacket expanded ∧
    representative observePacket choosePacket (erase observePacket expanded) ≠ expanded :=
  ⟨choosePacket_section _, reconstructed_expanded_not_original⟩

theorem erased_packet_has_no_original_decoder :
    ¬ ∃ decode : Erased observePacket → PacketPresentation,
      ∀ original, decode (erase observePacket original) = original :=
  collision_prevents_exact_recovery observePacket direct expanded
    direct_expanded_same_value direct_expanded_distinct

def initialCurrent : RevisionEnvironment Nat Nat := ⟨fun _ => 0⟩

def originalStore : ContextTable Nat Nat PacketPresentation :=
  writeSource (fun _ => none) (⟨7, 0⟩, expanded)

def retained : View Nat Nat (SemanticFibre packetX) := ⟨observePacket expanded, ⟨7, 0⟩⟩

theorem capture_original : captureView originalStore initialCurrent 7 observePacket = some retained := by
  simp [captureView, originalStore, initialCurrent, writeSource, retained]

theorem recover_original_path :
    (recover originalStore retained).map PacketPresentation.path =
      some MonoidIndexedTransportCoherence.Controls.expandedRightUnitPath := by
  simp [recover, originalStore, retained, writeSource, expanded]

def extendedStore : ContextTable Nat Nat PacketPresentation :=
  writeSource originalStore (⟨7, 1⟩, direct)

theorem fresh_publication_accepted :
    publishVersion? originalStore ⟨7, 1⟩ direct = some extendedStore := by
  simp [publishVersion?, originalStore, extendedStore, writeSource]

theorem fresh_live_version_keeps_original :
    recover extendedStore retained = some expanded ∧
      resolve extendedStore (initialCurrent.update 7 1) (.live 7) = some direct := by
  constructor
  · exact recover_preserved_by_publication originalStore extendedStore ⟨7, 1⟩ direct expanded
      retained fresh_publication_accepted (by simp [recover, originalStore, retained, writeSource])
  · simp [resolve, extendedStore, writeSource, RevisionEnvironment.update]

theorem retained_key_missing_is_not_reconstruction :
    recover (fun _ => none : ContextTable Nat Nat PacketPresentation) retained = none ∧
      observePacket (representative observePacket choosePacket (erase observePacket expanded)) =
        retained.value :=
  ⟨rfl, choosePacket_section _⟩

/-- An unsupported table mutation is not detectable from local meaning:
equal observations do not authenticate which original occupied this key. -/
theorem occupied_key_replacement_changes_original_without_changing_observation :
    let replaced := writeSource originalStore (retained.version, direct)
    recover replaced retained = some direct ∧
      observePacket direct = retained.value ∧
      recover replaced retained ≠ some expanded := by
  dsimp
  refine ⟨?_, direct_expanded_same_value, ?_⟩
  · simp [recover, writeSource]
  · simpa [recover, writeSource] using direct_expanded_distinct

theorem safe_publication_rejects_same_key :
    publishVersion? originalStore retained.version direct = none := by
  apply occupied_reference_cannot_be_republished originalStore retained expanded direct
  simp [recover, originalStore, retained, writeSource]

/-- Reusing the same numerical key in an unrelated store does not identify
the same source. This is a store-lineage boundary, not a cryptographic claim. -/
theorem unrelated_store_same_key_is_not_original :
    let unrelated : ContextTable Nat Nat PacketPresentation :=
      writeSource (fun _ => none) (retained.version, direct)
    recover originalStore retained = some expanded ∧
      recover unrelated retained = some direct ∧
      observePacket direct = retained.value ∧
      direct ≠ expanded := by
  dsimp
  refine ⟨?_, ?_, direct_expanded_same_value, direct_expanded_distinct⟩
  · simp [recover, originalStore, retained, writeSource]
  · simp [recover, writeSource]

/-- An executable finite readout: visible cursor and recovered constructor
count. Only this inspection consumer requests the presentation lookup. -/
def capturedReadout : Option (Nat × Option Nat) :=
  (captureView originalStore initialCurrent 7 observePacket).map fun view =>
    (view.value.val, (recover originalStore view).map fun presentation =>
      pathConstructorCount presentation.path)

def retainedAfterPublicationReadout : Option Nat :=
  (recover extendedStore retained).map fun presentation => pathConstructorCount presentation.path

def liveAfterPublicationReadout : Option Nat :=
  (resolve extendedStore (initialCurrent.update 7 1) (.live 7)).map fun presentation =>
    pathConstructorCount presentation.path

def representativeReadout : Nat × Nat :=
  let chosen := representative observePacket choosePacket (erase observePacket expanded)
  (observePacket chosen |>.val, pathConstructorCount chosen.path)

theorem captured_readout_exact : capturedReadout = some (1, some 5) := by
  rw [capturedReadout, capture_original]
  change some ((observePacket expanded).val, some 5) = some (1, some 5)
  rw [expanded_value]
  rfl

theorem distinct_recovery_modes :
    retainedAfterPublicationReadout = some 5 ∧ liveAfterPublicationReadout = some 1 ∧
      representativeReadout = (1, 1) := by
  refine ⟨rfl, rfl, ?_⟩
  change ((observePacket (choosePacket (observePacket expanded))).val,
    pathConstructorCount rightUnitPath) = (1, 1)
  rw [choosePacket_section, expanded_value]
  rfl

#eval capturedReadout
#eval retainedAfterPublicationReadout
#eval liveAfterPublicationReadout
#eval representativeReadout

end Controls

#print axioms capture_recovers_original
#print axioms recover_preserved_by_publication
#print axioms erase_representative
#print axioms collision_prevents_exact_recovery
#print axioms Controls.reconstruction_preserves_value_but_not_original
#print axioms Controls.erased_packet_has_no_original_decoder
#print axioms Controls.fresh_live_version_keeps_original
#print axioms Controls.occupied_key_replacement_changes_original_without_changing_observation

end Mettapedia.TypeTheory.RetainedPresentationViews
