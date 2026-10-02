import Mettapedia.Machines.RunContracts.Diagnostics
import Mathlib.Data.Multiset.MapFold

/-!
# Diagnostic projection without changing exception semantics

The existing diagnostic collector remains the authority for fault occurrences,
counts and status. A diagnostic payload contains reviewed public detail and a
private native exception. Presentation projects the former, without replacing
the native exception used by a dialect's handlers. Public wording can depend
only on the projected diagnostic.

This is diagnostic-channel noninterference, not a secrecy theorem for returned
program values, timing, arbitrary exception strings, or arbitrary serializers.
Identifiers, classifications, origins and public detail must already have been
approved for disclosure. No regular expression is assumed to sanitize Python's
arbitrary `str` method. The native representation and dialect error terms are
left intact. Noninterference compares executions using the same public wording
policy and heading; replacing the policy with a closure containing secrets is
outside that comparison.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ErrorBoundaryContracts.Presentation

open Mettapedia.Machines.RunContracts.Diagnostics

structure Payload (Public Native : Type*) where
  detail : Public
  native : Native
  deriving DecidableEq, Repr

variable {Code Origin Public Native OtherNative Value Fault OtherFault Handler : Type*}
variable {RenderFault : Type*}

abbrev Internal (Code Origin Public Native : Type*) :=
  Diagnostic Code Origin (Payload Public Native)

/-- The public representation deliberately has no field for native payload. -/
def project (d : Internal Code Origin Public Native) : Diagnostic Code Origin Public :=
  ⟨d.id, d.code, d.origin, d.payload.detail⟩

/-- A model of changing private exception representation while retaining its
public diagnostic classification. This is not an executable exception adapter. -/
def mapNative (f : Native → OtherNative) (d : Internal Code Origin Public Native) :
    Internal Code Origin Public OtherNative :=
  ⟨d.id, d.code, d.origin, ⟨d.payload.detail, f d.payload.native⟩⟩

def mapFault (f : Fault → OtherFault) : Event Value Fault → Event Value OtherFault
  | .returned v => .returned v
  | .unhandled d => .unhandled (f d)

def projectCollected (c : Collected (Internal Code Origin Public Native)) :
    Collected (Diagnostic Code Origin Public) :=
  ⟨c.total, c.shown.map project⟩

theorem project_mapNative (f : Native → OtherNative)
    (d : Internal Code Origin Public Native) : project (mapNative f d) = project d := rfl

theorem project_eq_of_public_fields
    (a b : Internal Code Origin Public Native)
    (hid : a.id = b.id) (hcode : a.code = b.code)
    (horigin : a.origin = b.origin) (hdetail : a.payload.detail = b.payload.detail) :
    project a = project b := by
  cases a
  cases b
  simp_all [project]

theorem faultEvidence_map (f : Fault → OtherFault) (events : List (Event Value Fault)) :
    faultEvidence (events.map (mapFault f)) = (faultEvidence events).map f := by
  induction events with
  | nil => simp [faultEvidence]
  | cons e rest ih => cases e <;> simp [mapFault, faultEvidence, ih]

/-- Mapping diagnostics commutes with the actual bounded-detail collector.
In particular, hidden payloads do not influence which occurrences are counted. -/
theorem collect_map (f : Fault → OtherFault) (budget : Nat)
    (events : List (Event Value Fault)) :
    collect budget (events.map (mapFault f)) =
      ⟨(collect budget events).total, (collect budget events).shown.map f⟩ := by
  induction events generalizing budget with
  | nil => simp [collect]
  | cons e rest ih =>
    cases e with
    | returned v => simp [mapFault, collect, ih]
    | unhandled d => cases budget <;> simp [mapFault, collect, ih]

theorem collection_projection (budget : Nat)
    (events : List (Event Value (Internal Code Origin Public Native))) :
    collect budget (events.map (mapFault project)) = projectCollected (collect budget events) :=
  collect_map project budget events

theorem projection_counts (budget : Nat)
    (events : List (Event Value (Internal Code Origin Public Native))) :
    (collect budget (events.map (mapFault project))).total = (faultEvidence events).card := by
  rw [collect_map]
  exact collect_total budget events

theorem projection_omissions (budget : Nat)
    (events : List (Event Value (Internal Code Origin Public Native))) :
    omitted (collect budget (events.map (mapFault project))) =
      omitted (collect budget events) := by
  simp [collect_map, omitted]

theorem projection_status (budget : Nat)
    (events : List (Event Value (Internal Code Origin Public Native))) :
    statusOf (collect budget (events.map (mapFault project))).total =
      evidenceStatus (faultEvidence events) := by
  rw [projection_counts]
  rfl

theorem projection_stable_identifiers (budget : Nat)
    (events : List (Event Value (Internal Code Origin Public Native))) :
    (collect budget (events.map (mapFault project))).shown.map Diagnostic.id =
      (collect budget events).shown.map Diagnostic.id := by
  simp [collect_map, List.map_map, Function.comp_def, project]

theorem projection_stable_classifications (budget : Nat)
    (events : List (Event Value (Internal Code Origin Public Native))) :
    (collect budget (events.map (mapFault project))).shown.map Diagnostic.code =
      (collect budget events).shown.map Diagnostic.code := by
  simp [collect_map, List.map_map, Function.comp_def, project]

/-- The wording callback receives only explicitly public fields. The native
exception remains in the original diagnostic for the dialect's own handlers. -/
def publicReport (heading : String) (wording : Diagnostic Code Origin Public → String)
    (budget : Nat) (events : List (Event Value (Internal Code Origin Public Native))) :
    HumanReport Code Origin Public :=
  renderHuman heading wording (collect budget (events.map (mapFault project)))

theorem public_report_facts (heading : String)
    (wording : Diagnostic Code Origin Public → String) (budget : Nat)
    (events : List (Event Value (Internal Code Origin Public Native))) :
    (publicReport heading wording budget events).facts =
      (renderMachine (projectCollected (collect budget events))).facts := by
  unfold publicReport
  rw [collection_projection]
  exact presentations_agree _ _ _

/-- Redaction cannot invent a fault: every displayed public diagnostic is the
projection of an actual unhandled occurrence, even when projection is not
injective on native exceptions. -/
theorem public_detail_has_original (heading : String)
    (wording : Diagnostic Code Origin Public → String) (budget : Nat)
    (events : List (Event Value (Internal Code Origin Public Native)))
    (d : Diagnostic Code Origin Public)
    (shown : d ∈ (publicReport heading wording budget events).facts.shown) :
    ∃ original, original ∈ faultEvidence events ∧ project original = d := by
  rw [public_report_facts] at shown
  have member : d ∈ (collect budget events).shown.map project := by
    simpa [renderMachine, projectCollected, MachineReport.facts,
      renderMachineEntry, MachineEntry.facts, List.map_map, Function.comp_def] using shown
  obtain ⟨original, stored, projects⟩ := List.mem_map.mp member
  exact ⟨original, displayed_witness_genuine budget events original stored, projects⟩

/-- Presentation does not add a first-fault sequencing obligation. Reordering
events may change retained details but preserves their authoritative count and
fault status, even if the two runs have different display budgets. -/
theorem public_summary_perm (heading : String)
    (wording : Diagnostic Code Origin Public → String) (a b : Nat)
    {xs ys : List (Event Value (Internal Code Origin Public Native))}
    (permutation : xs.Perm ys) :
    (publicReport heading wording a xs).faultCount =
      (publicReport heading wording b ys).faultCount ∧
    (publicReport heading wording a xs).status =
      (publicReport heading wording b ys).status := by
  simp only [publicReport, renderHuman, projection_counts]
  rw [faultEvidence_perm permutation]
  exact ⟨rfl, rfl⟩

theorem private_payload_noninterference (heading : String)
    (wording : Diagnostic Code Origin Public → String) (budget : Nat)
    (f : Native → OtherNative)
    (events : List (Event Value (Internal Code Origin Public Native))) :
    publicReport heading wording budget (events.map (mapFault (mapNative f))) =
      publicReport heading wording budget events := by
  have projected :
      (events.map (mapFault (mapNative f))).map (mapFault project) =
        events.map (mapFault project) := by
    induction events with
    | nil => rfl
    | cons e rest ih => cases e <;> simp [mapFault, mapNative, project, ih]
  simp only [publicReport, projected]

/-- Relational form: arbitrary private changes may vary at every occurrence,
provided the public event stream is equal. Returned values are not inspected
by the collector, but equality here also keeps their positions fixed. -/
theorem equal_public_stream_same_report (heading : String)
    (wording : Diagnostic Code Origin Public → String) (budget : Nat)
    (a : List (Event Value (Internal Code Origin Public Native)))
    (b : List (Event Value (Internal Code Origin Public OtherNative)))
    (same : a.map (mapFault project) = b.map (mapFault project)) :
    publicReport heading wording budget a = publicReport heading wording budget b := by
  simp only [publicReport, same]

theorem wording_cannot_change_authoritative_facts (heading₁ heading₂ : String)
    (wording₁ wording₂ : Diagnostic Code Origin Public → String) (budget : Nat)
    (events : List (Event Value (Internal Code Origin Public Native))) :
    (publicReport heading₁ wording₁ budget events).facts =
      (publicReport heading₂ wording₂ budget events).facts :=
  wording_preserves_facts _ _ _ _ _

/-- An exception-producing formatter is contained at the presentation boundary.
Both callbacks receive only approved public fields; a formatting exception is
not inserted as a new program fault. The fallback is a total pure function.
This models a returned formatting failure, not timeout or foreign liveness. -/
def formatOrFallback
    (format : Diagnostic Code Origin Public → Except RenderFault String)
    (fallback : Diagnostic Code Origin Public → String)
    (d : Diagnostic Code Origin Public) : String :=
  match format d with
  | .ok wording => wording
  | .error _ => fallback d

def resilientPublicReport (heading : String)
    (format : Diagnostic Code Origin Public → Except RenderFault String)
    (fallback : Diagnostic Code Origin Public → String)
    (budget : Nat) (events : List (Event Value (Internal Code Origin Public Native))) :
    HumanReport Code Origin Public :=
  publicReport heading (formatOrFallback format fallback) budget events

theorem formatter_failure_uses_fallback
    (format : Diagnostic Code Origin Public → Except RenderFault String)
    (fallback : Diagnostic Code Origin Public → String)
    (d : Diagnostic Code Origin Public) (e : RenderFault) (failed : format d = .error e) :
    formatOrFallback format fallback d = fallback d := by
  simp [formatOrFallback, failed]

theorem formatter_success_uses_wording
    (format : Diagnostic Code Origin Public → Except RenderFault String)
    (fallback : Diagnostic Code Origin Public → String)
    (d : Diagnostic Code Origin Public) (text : String) (succeeded : format d = .ok text) :
    formatOrFallback format fallback d = text := by
  simp [formatOrFallback, succeeded]

/-- Every mix of formatting successes and failures preserves the authoritative
report facts, including stable diagnostic identity and omitted-detail counts. -/
theorem formatter_outcomes_preserve_facts (heading : String)
    (format : Diagnostic Code Origin Public → Except RenderFault String)
    (fallback : Diagnostic Code Origin Public → String)
    (budget : Nat) (events : List (Event Value (Internal Code Origin Public Native))) :
    (resilientPublicReport heading format fallback budget events).facts =
      (renderMachine (projectCollected (collect budget events))).facts :=
  public_report_facts heading (formatOrFallback format fallback) budget events

theorem formatter_outcomes_preserve_count_status (heading : String)
    (format : Diagnostic Code Origin Public → Except RenderFault String)
    (fallback : Diagnostic Code Origin Public → String)
    (budget : Nat) (events : List (Event Value (Internal Code Origin Public Native))) :
    (resilientPublicReport heading format fallback budget events).faultCount =
      (faultEvidence events).card ∧
    (resilientPublicReport heading format fallback budget events).status =
      evidenceStatus (faultEvidence events) := by
  simp [resilientPublicReport, publicReport, renderHuman, projection_counts, evidenceStatus]

theorem resilient_private_payload_noninterference (heading : String)
    (format : Diagnostic Code Origin Public → Except RenderFault String)
    (fallback : Diagnostic Code Origin Public → String) (budget : Nat)
    (f : Native → OtherNative)
    (events : List (Event Value (Internal Code Origin Public Native))) :
    resilientPublicReport heading format fallback budget (events.map (mapFault (mapNative f))) =
      resilientPublicReport heading format fallback budget events :=
  private_payload_noninterference heading (formatOrFallback format fallback) budget f events

/-- Recovery dispatch consumes the stable semantic classification. This says
nothing about whether replaying an external effect is safe. -/
def handler (classify : Code → Handler) (d : Diagnostic Code Origin Public) : Handler :=
  classify d.code

theorem wording_preserves_handler (classify : Code → Handler)
    (wording : Diagnostic Code Origin Public → String)
    (d : Internal Code Origin Public Native) :
    handler classify (renderHumanEntry wording (project d)).facts = classify d.code := rfl

theorem equal_kind_equal_handler (classify : Code → Handler)
    (a b : Diagnostic Code Origin Public) (same : a.code = b.code) :
    handler classify a = handler classify b := congrArg classify same

/-- Evidence required from the operation protocol, independently of the error
classification. `repeatSafe` may describe an idempotence or deduplication proof;
constructing that evidence for a concrete service is a separate obligation. -/
inductive EffectKnowledge where
  | noEffect
  | repeatSafe
  | unresolved
  deriving DecidableEq, Repr

/-- An eligibility check, not a complete retry supervisor. -/
def replayEligible (transientKind : Bool) : EffectKnowledge → Bool
  | .noEffect => transientKind
  | .repeatSafe => transientKind
  | .unresolved => false

theorem uncertainty_blocks_automatic_replay (transientKind : Bool) :
    replayEligible transientKind .unresolved = false := rfl

/-- A byte projection owns only a finite prefix of already approved detail.
It neither serializes nor retains the native exception graph. -/
def boundedBytes (limit : Nat) (detail : List UInt8) : List UInt8 :=
  detail.take limit

theorem boundedBytes_length (limit : Nat) (detail : List UInt8) :
    (boundedBytes limit detail).length ≤ limit := by
  simp only [boundedBytes, List.length_take]
  exact Nat.min_le_left _ _

/-- Bounded retained detail count and bounded bytes per detail compose. This
bounds payload bytes, independently of framing or serializer overhead. -/
theorem bounded_detail_bytes (limit : Nat) (details : List (List UInt8)) :
    ((details.map (boundedBytes limit)).map List.length).sum ≤ details.length * limit := by
  induction details with
  | nil => simp
  | cons detail rest ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
      have bound := boundedBytes_length limit detail
      omega


namespace Controls

inductive Kind where
  | io
  | invalidInput
  deriving DecidableEq, Repr

abbrev D := Internal Kind Nat String String

def first : D := ⟨7, .io, 3, ⟨"request failed", "https://host/?token=alpha"⟩⟩
def second : D := ⟨7, .io, 3, ⟨"request failed", "https://host/?token=beta"⟩⟩

def reviewedWording (d : Diagnostic Kind Nat String) : String := d.payload
def rawWording (d : D) : String := d.payload.native

theorem raw_exception_text_leaks_private_change :
    project first = project second ∧ rawWording first ≠ rawWording second := by decide

theorem safe_projection_hides_private_change :
    publicReport "failed" reviewedWording 1 ([.unhandled first] : List (Event Nat D)) =
      publicReport "failed" reviewedWording 1 ([.unhandled second] : List (Event Nat D)) := by
  decide

theorem native_exception_is_retained :
    first.payload.native = "https://host/?token=alpha" ∧
    project first = ⟨7, .io, 3, "request failed"⟩ := by decide

theorem zero_display_budget_keeps_duplicate_failures :
    let events : List (Event Nat D) := [.unhandled first, .returned 2, .unhandled first]
    let report := publicReport "failed" reviewedWording 0 events
    report.details = [] ∧ report.faultCount = 2 ∧ report.status = .failed ∧
      report.omittedDetails = 2 := by decide

def retryByWording (wording : String) : Bool := wording == "retry"

theorem message_based_dispatch_is_unstable :
    let d := project first
    (renderHumanEntry (fun _ => "retry") d).classification =
      (renderHumanEntry (fun _ => "do not retry") d).classification ∧
    retryByWording (renderHumanEntry (fun _ => "retry") d).wording ≠
      retryByWording (renderHumanEntry (fun _ => "do not retry") d).wording := by decide

theorem same_transient_kind_different_replay_eligibility :
    replayEligible true .noEffect = true ∧ replayEligible true .unresolved = false := by decide

theorem public_details_still_require_review :
    let unreviewed : D := ⟨7, .io, 3, ⟨"token=alpha", "private"⟩⟩
    (renderHumanEntry reviewedWording (project unreviewed)).wording = "token=alpha" := by decide

def failedFormatter (_ : Diagnostic Kind Nat String) : Except String String :=
  .error "formatter raised with token=private"

theorem faulty_formatter_preserves_original_fault :
    let report := resilientPublicReport "failed" failedFormatter reviewedWording 1
      ([.unhandled first] : List (Event Nat D))
    report.faultCount = 1 ∧ report.status = .failed ∧ report.omittedDetails = 0 ∧
    report.details = [⟨"request failed", 7, .io, 3, "request failed"⟩] := by decide

theorem successful_formatter_retains_its_wording :
    formatOrFallback (fun _ => .ok "public explanation" :
      Diagnostic Kind Nat String → Except String String) reviewedWording (project first) =
      "public explanation" := by decide

end Controls

end Mettapedia.Machines.ErrorBoundaryContracts.Presentation
