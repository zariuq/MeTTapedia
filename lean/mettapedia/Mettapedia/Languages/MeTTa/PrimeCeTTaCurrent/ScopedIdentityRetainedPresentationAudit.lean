import Mettapedia.Languages.MeTTa.PrimeCeTTaCurrent

/-!
# Experimental identity interfaces: pinned executions and remaining boundaries

These are observations of a copied existing CeTTa binary, not a candidate
selection, C refinement proof, or newly rebuilt correctness gate. Source and
binary digests identify the inspected dirty-worktree state. Expected outputs
were authored independently of these runs. Two authority tests and one named
diagnostic-context test differ from those expectations; the discrepancies are
retained rather than rebased into expected behavior.

Ordinary publication-name lookup is a live presentation view. An explicit
user-level store retains a previous actual HOL proof across replacement of
the live publication. That experiment does not implement authenticated stable
handles, garbage-collection laws, or automatic proof reconstruction.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCeTTaCurrent.ScopedIdentityRetainedPresentationAudit

def source : InspectedSourceSnapshot where
  date := "2026-09-12"
  repositoryRevision := "681ac7ea9e259c5ecd35755e87449c62ced56039"
  files := [
    ⟨"src/prime_scoped_judgments.c", "cee4f2ff6231a2c0bb8af9d725a7d25340a91a84582ad641c96d758360e6cc88"⟩,
    ⟨"src/prime_semantics.c", "01ab7e4a74d66c68061e79a5a738b7c9a9fbdb4389587b54a06b278d516f2685"⟩,
    ⟨"src/prime_regular_kernel.c", "c0fb2a09964bf1aebbbe34525debd33fdbb4b7eba8353d82b5b4976f7d5cace3"⟩,
    ⟨"src/eval.c", "736f91e81883b9efbb1973e1f07f1ee62c998481f84ed368c7a3ea5425065c1a"⟩]

def executable : SourceDigest :=
  ⟨"cetta", "3b6ee081618f63e11772358ed9d9090df181dcb6259800ac492a2d197d104b8a"⟩

def transcript : SourceDigest :=
  ⟨"semantic-results.json", "106e0478f6ecc11b021ee7257bbc7961f602ce32c3133a8d2329f122cbb16d04"⟩

/-- Pinned external observations, not an executable semantics or proof of
their source-language meaning. Setup, quiet-mode suppression and complete
commands remain in the hashed input; the actual output is literal. -/
structure ObservedProbe where
  input : SourceDigest
  profile : String
  expected : List String
  actual : List String
  exitCode : Nat
  boundary : String
  deriving Repr

def authorityTags : ObservedProbe where
  input := ⟨"authority_tags.metta", "f2b9e94954a0c9fb488d81ac66434196828326c8fec895e9d5f1584d3bf710f2"⟩
  profile := "prime-default; quiet"
  expected := ["[(Audit raw-theorem Undetermined)]", "[(Audit raw-signature Undetermined)]",
    "[(Audit raw-axiom Undetermined)]", "[(Audit wrong-digest Undetermined)]"]
  actual := ["[(Audit raw-theorem Undetermined)]", "[(Audit raw-signature Established)]",
    "[(Audit raw-axiom Undetermined)]", "[(Audit wrong-digest Undetermined)]"]
  exitCode := 0
  boundary := "Fresh raw theorem and axiom records now require admission, but a user-inserted record tagged signature and carrying the current public signature digest establishes Falsum without a proof or explicit assumption publication. Matching the signature tag is not membership in the actual seed inventory."

def tryAdmission : ObservedProbe where
  input := ⟨"try_admission.metta", "9bcb9e807953f1a79dac0c1ba9b0d4d21ef3a715e2df1f6d856656be8bb474ce"⟩
  profile := "prime-default; quiet"
  expected := ["[(Audit try-then-raw-insert Undetermined)]", "[(Audit explicit-assumption Established)]"]
  actual := ["[(Audit try-then-raw-insert Established)]", "[(Audit explicit-assumption Established)]"]
  exitCode := 0
  boundary := "The nonpublishing try returns a SetPublish record but also calls the admission registry. Inserting that returned record as raw data later succeeds as an admitted assumption. Explicit assumption publication is a separate positive control; the failed expectation concerns try's hidden admission effect, not the legitimacy of assumptions."

def conditionalScope : ObservedProbe where
  input := ⟨"conditional_scope.metta", "a0f4d2e4ef2dcb304a7878e7e5652fb96529cc44ab12c46fd68e398db6f42a03"⟩
  profile := "identity-scoped; quiet"
  expected := ["[True]", "[True]", "[(Audit outer-scope Undetermined)]", "[False]", "[False]"]
  actual := ["[True]", "[True]", "[(Audit outer-scope try)]", "[False]", "[False]"]
  exitCode := 0
  boundary := "Native conditional congruence checks without a uniqueness assumption; its supplied-witness instance checks inside the separate assumed region. Direct and nested conversion remain unchanged. The explicit-space type query under try stays uninterpreted, so its diagnostic wrapper does not preserve this public request's context routing. This is not a proof of non-derivability or an internal Hedberg instance."

def originalInspection : ObservedProbe where
  input := ⟨"inspection_recovery.metta", "d2ec81a01a8a7b6967d5b326f8969fdb76114606b234d06710c9aba1983c7d0e"⟩
  profile := "prime-default; quiet"
  expected := ["[(pf:imp-intro (pf:hyp 0))]", "[(set:known-proof original)]",
    "[(pf:imp-intro (pf:imp-elim (pf:known identity-implication) (pf:hyp 0)))]",
    "[(pf:imp-intro (pf:hyp 0))]", "[True]"]
  actual := ["[(pf:imp-intro (pf:hyp 0))]", "[(set:known-proof original)]",
    "[(pf:imp-intro (pf:imp-elim (pf:known identity-implication) (pf:hyp 0)))]",
    "[(pf:imp-intro (pf:hyp 0))]", "[True]"]
  exitCode := 0
  boundary := "The live theorem name follows replacement with a different accepted HOL proof of the same implication. An explicitly retained proof in an ordinary separate space remains the original presentation. This is a user-level opt-in retention workload, not a new native handle service or certified reconstruction algorithm."

def probes : List ObservedProbe :=
  [authorityTags, tryAdmission, conditionalScope, originalInspection]

private def scopedSource : SourceDigest :=
  ⟨"src/prime_scoped_judgments.c", "cee4f2ff6231a2c0bb8af9d725a7d25340a91a84582ad641c96d758360e6cc88"⟩

def signatureTagBypass : SourceObservation source where
  source := scopedSource
  sourceInSnapshot := by decide
  symbols := ["sj_known_lookup", "sj_synth", "sj_record_admitted", "SJ_KNOWN_ORIGIN", "sj_env_parse"]
  observation := "Known-proof use exempts every record with the signature origin tag from the admitted-record check. Lookup also returns user-inserted records. The positive forged-signature probe exploits their composition; the tag is not checked against the environment's actual seed inventory."
  limitation := "The current digest still rejects the wrong-signature control, and raw theorem/axiom tags now abstain. Those successful checks do not qualify the signature-tag exception. Explicit assumptions remain legitimate; the defect is presenting unadmitted proof-shaped data as established by the seed authority."

def retainedAndLiveProofViews : SourceObservation source where
  source := scopedSource
  sourceInSnapshot := by decide
  symbols := ["sj_set_known_view", "sj_known_lookup", "sj_set_theorem", "SJ_KNOWN_PROOF"]
  observation := "Known-proof returns the proof field of the currently looked-up publication, without invoking the proof checker. A MeTTa program can explicitly copy that actual proof into a separate ordinary space; the originalInspection probe retains it while replacing the live publication with another checked proof of the same implication."
  limitation := "The extra storage is explicit user-program behavior, not an automatic retained-handle API. Name lookup alone does not recover a deleted original, and successful syntax lookup supplies no proof authority, source-byte fidelity or lifetime theorem."

def admittedRecordCost : SourceObservation source where
  source := scopedSource
  sourceInSnapshot := by decide
  symbols := ["sj_record_digest", "sj_record_admitted", "sj_dependencies_current", "sj_synth"]
  observation := "Admission membership serializes and SHA-256 hashes the whole record before the per-space table lookup. Known-theorem reuse recursively checks dependency records. No full proof-checker rerun occurs on this known-use path, but processing retained record syntax and dependencies is not constant work in their sizes."
  limitation := "This source observation does not isolate the share of measured time due to serialization, hashing, lookup, conversion or allocation. The currently copied binary's 817 emitted runtime counters all remain zero on the positive proof control, and scoped counters are not exposed; those zeros are unavailable instrumentation, not evidence of no work."

def diagnosticRouting : SourceObservation source where
  source := scopedSource
  sourceInSnapshot := by decide
  symbols := ["sj_try", "sj_judge", "prime_semantics_judge_typing_direct", "sj_admit"]
  observation := "Try directly invokes the inner checker once in the inspected code. It bypasses ordinary explicit-space routing for type queries. Publishing checks register admission before returning SetPublish, even when the outer try prevents the visible space publication."
  limitation := "Single direct checker invocation is a source-path finding, not a dynamic all-input execution-count theorem. Optional diagnostics must preserve the requested context and their stated effects; not publishing a visible atom is insufficient to establish absence of state changes."

def observations : List (SourceObservation source) :=
  [signatureTagBypass, retainedAndLiveProofViews, admittedRecordCost, diagnosticRouting]

/-- A recorded fixture comparison only; it does not execute the C binary. -/
def recordedAgreement : List Bool := probes.map (fun probe => decide (probe.actual = probe.expected))

#eval recordedAgreement

end Mettapedia.Languages.MeTTa.PrimeCeTTaCurrent.ScopedIdentityRetainedPresentationAudit
