import Mettapedia.Languages.MeTTa.PrimeCeTTaCurrent
import Mettapedia.Languages.MeTTa.PrimeCeTTaCurrent.ScopedJudgmentDraft

/-!
# Second source inspection of the experimental scoped judgments

This snapshot records source observations after the first experimental review.
It neither replaces the earlier recorded executions nor imports a candidate
specification. One later isolated probe uses the existing binary and records
five literal outputs. No C rebuild or full gate is claimed here. Neither
that probe nor the source report's successful specimens establishes an
all-input correspondence.

Retained derivations, exact operation-name ownership and dependency-sensitive
reuse are different properties. In particular, writable proof-shaped records
remain data; neither their shape nor their recorded revision qualifies their
fresh use as theorems. A conversion service tried first is not thereby the
exclusive conversion service. These distinctions are observations about the
pinned draft, not an adopted semantics for Prime.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCeTTaCurrent.ScopedJudgmentDraftSecondPass

def source : InspectedSourceSnapshot where
  date := "2026-09-10"
  repositoryRevision := "681ac7ea9e259c5ecd35755e87449c62ced56039"
  files := [
    ⟨"src/prime_scoped_judgments.c", "b9f8132126f011970e54fc28517ba50e1709b878c561c70a53360261a7f4cba4"⟩,
    ⟨"src/eval.c", "48372b6ccd6e041dbdba0f6717be8431bbb3ee0f43616eb2a2eba5b2b3e963a9"⟩,
    ⟨"src/prime_semantics.c", "6acf5df5de7d2d2112093ad327726c6a147f9e9675c9cdaa2fc5394752000df1"⟩,
    ⟨"src/prime_regular_pattern.c", "b8bce60106249fcc63bc5323a6d210c95707d8f36a188b91cfaacfa5deec2135"⟩,
    ⟨"src/prime_regular_kernel.c", "e444ec9d1c0b01e31e036609aee4fe5bc4ea21a78c109ff3781ba3f77afdd581"⟩,
    ⟨"tests/prime/scoped/live_propositions.metta", "6787193d56e9c7bdcbf9b2ea6539f115f6cb78a509e647bd9677a3ff80954c69"⟩]

private def scopedSource : SourceDigest :=
  ⟨"src/prime_scoped_judgments.c", "b9f8132126f011970e54fc28517ba50e1709b878c561c70a53360261a7f4cba4"⟩

def operationOwnership : SourceObservation source where
  source := scopedSource
  sourceInSnapshot := by decide
  symbols := ["SJ_OWNED_JUDGMENTS", "prime_scoped_judgment_is_head"]
  observation := "Ownership compares the requested name with sixteen explicit operation names. Other set: and lang: names are left to ordinary evaluation; a prefix no longer reserves every user definition."
  limitation := "Exact-name ownership does not itself qualify those operations' mathematical meaning or resolve conflicts with a user definition at an owned name. This is source inspection, not a rerun namespace test."

def retainedProofs : SourceObservation source where
  source := scopedSource
  sourceInSnapshot := by decide
  symbols := ["sj_known_record", "sj_set_theorem", "sj_set_known_view", "sj_set_recheck"]
  observation := "Publication retains name, proposition, origin, submitted proof, dependencies and revision. Known-proof and known-proposition expose stored fields. Recheck invokes the proof checker for a theorem record."
  limitation := "The revision is informational rather than a proof of historical admission. Inspecting the retained proof is not replaying it; rechecking and pf:known follow different source paths."

def currentDependencies : SourceObservation source where
  source := scopedSource
  sourceInSnapshot := by decide
  symbols := ["sj_dependencies_current", "sj_known_lookup", "sj_synth"]
  observation := "Known-theorem use recursively looks up each well-shaped recorded name/proposition dependency. Missing, changed or proposition-ambiguous dependencies cause a residual; unrelated declarations need not invalidate reuse."
  limitation := "Non-expression dependency fields succeed, malformed dependency entries are skipped, and pf:known does not replay the stored proof. Dependency agreement alone does not authenticate a directly inserted theorem record or establish that its recorded list is complete."

def rawRecordUse : SourceObservation source where
  source := scopedSource
  sourceInSnapshot := by decide
  symbols := ["sj_known_lookup", "SJ_KNOWN_LEN", "pf:known", "set:recheck"]
  observation := "Lookup admits any seven-place set:known record found in the space. For records with the same name and proposition it keeps the first even when origins or proofs differ. Known-proof synthesis elaborates the stored proposition after the dependency test."
  limitation := "The separately recorded probe inserts (set:known forged Falsum theorem () () 0): known use prints True, explicit recheck stays inert, and the proof view is empty. This path acts as an unchecked premise, not evidence of checked theorem reuse. Raw insertion should remain available; the open correspondence concerns qualified use, not banning proof-shaped data."

def kernelFirstConversion : SourceObservation source where
  source := scopedSource
  sourceInSnapshot := by decide
  symbols := ["sj_kernel_context", "sj_kernel_convertible", "sj_convertible", "sj_normalize"]
  observation := "The proof checker first asks the regular kernel under a signature/binder context. When that path declines an operand or exhausts its budget, sj_convertible still uses the separate structural normalizer and can establish equality or report a mismatch."
  limitation := "Zero fallback calls in selected specimens is not exclusive kernel ownership. Additional declarations are available through the overlay while sj_kernel_context builds from the fixed signature inventory. Both admission and semantics of any fallback need their own stated contract."

def legacyOwnershipRepair : SourceObservation source where
  source := ⟨"src/prime_semantics.c", "6acf5df5de7d2d2112093ad327726c6a147f9e9675c9cdaa2fc5394752000df1"⟩
  sourceInSnapshot := by decide
  symbols := ["prime_operand_uses_authored_binder", "prime_convert_legacy_he"]
  observation := "The legacy path now declines authored lam forms and annotation-bearing telescope syntax, recursively detected, instead of comparing their uninterpreted spellings as a checked distinction."
  limitation := "This repair belongs to the pinned dirty draft. The previously inspected opt baseline has a different semantics-file digest; this observation does not claim that the baseline has been repaired or that every fallback is qualified."

def nativeMay : SourceObservation source where
  source := scopedSource
  sourceInSnapshot := by decide
  symbols := ["sj_lang_native_type", "sj_lang_step", "PrimeEvaluate", "type:may"]
  observation := "For the registered Prime language, native-type delegates to type:may over PrimeEvaluate and carries its verdict/evidence. Other registered languages decline. Unknown language names instead receive a refuted lookup judgment; no registered language has a realized step service here."
  limitation := "This does not implement a predecessor-quantified box, all OSLF formulas or arbitrary language semantics. Unknown-name rejection is not semantic falsity of an uninterpreted proposition. Source presence does not prove the delegated may observer agrees with the candidate."

def livePropositionProgram : SourceObservation source where
  source := ⟨"tests/prime/scoped/live_propositions.metta", "6787193d56e9c7bdcbf9b2ea6539f115f6cb78a509e647bd9677a3ff80954c69"⟩
  sourceInSnapshot := by decide
  symbols := ["member-claim", "pick", "find-proof", "found-membership", "live-consequence", "set:union"]
  observation := "The authored program constructs propositions from values, branches over witnesses, searches submitted proofs, publishes and inspects them, withdraws a premise, and defines an ordinary finite-data set:union independently of the signature's Union."
  limitation := "No execution is newly recorded here. Empty search output is not a proof of the goal's negation. The executable finite representation still needs an explicit relation to abstract sets; such a relation need not be implemented as trusted delta conversion."

def observations : List (SourceObservation source) :=
  [operationOwnership, retainedProofs, currentDependencies, rawRecordUse,
    kernelFirstConversion, legacyOwnershipRepair, nativeMay, livePropositionProgram]

/-- A fresh-process diagnostic of the existing binary, not a rebuilt-C
correspondence. File and executable digests were recorded; the executable
and scoped source digests were unchanged before and after the probe. -/
def rawRecordRun : ScopedJudgmentDraft.RecordedRun where
  profile := "experimental scoped-judgment second pass; isolated raw-record use/recheck probe"
  sourceSnapshot := source
  executable := some ⟨"cetta", "f9972252daab87e4ca7e71249cd67d98ab32ec2e9b27c9374968e94cbcfa8388"⟩
  input := ⟨"prime-live-record-probe-20260910.metta",
    "4c9510a4453742598d83907a39d0ea7a4584e8ba46ee5b59ba07744bd324165f"⟩
  transcript := ⟨"prime-live-record-probe-20260910.out",
    "78c99d767ad14de1603eff504f291ea1d0e51236946e94874bfdfa7cccebe116"⟩
  -- This non-query record occurs after the first two queries in the hashed input.
  setup := ["(set:known forged Falsum theorem () () 0)"]
  commands := [
    "!(set:proves (pf:all-elim (pf:known PowerI) Empty) (In Empty (Power Empty)))",
    "!(set:proves (pf:all-elim (pf:known PowerI) Empty) (In Empty Empty))",
    "!(set:proves (pf:known forged) Falsum)",
    "!(set:recheck forged)",
    "!(set:known-proof forged)"]
  outputs := ["[True]", "[False]", "[True]", "[(set:recheck forged)]", "[()]"]

def recordedRuns : List ScopedJudgmentDraft.RecordedRun := [rawRecordRun]

/-- Bookkeeping of the recorded transcript, not a Lean execution theorem. -/
theorem rawRecordRun_shape :
    rawRecordRun.commands.length = rawRecordRun.outputs.length ∧
      rawRecordRun.outputs.length = 5 := by decide

end Mettapedia.Languages.MeTTa.PrimeCeTTaCurrent.ScopedJudgmentDraftSecondPass
